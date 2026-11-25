"""Numeric check for `Residual/SmallWritesBiases.lean` and `Residual/DepthMlpBiases.lean`
(S Lemma A.27, third value: MLP blocks with biases, no normalization).

Residual tanh network with biases (one token), parameters (E, b_E, R_l, b_read_l, W_l, b_write_l,
D, b_D).  theta_tau holds tau W_l and tau b_write_l.  Checked on random parameters:
  (a) the limit J_0 of the statement (`smallWritesLimitB`), as a matrix on a batch, has rank
      P - d^2 - (L+1) d;
  (b) J_tau S_tau -> J_0 (S_tau divides the coordinates of the reads and read biases by tau);
  (c) the rank of the Jacobian at theta_tau is P - d^2 - (L+1) d for small tau != 0.
The Jacobian is computed by the complex step (tanh is analytic), in float64.
"""
import numpy as np
rng = np.random.default_rng(11)

def shapes(d, din, dout, widths):
    sh = [('E', (din, d)), ('bE', (d,))]
    for l, m in enumerate(widths):
        sh += [(f'R{l}', (d, m)), (f'br{l}', (m,)), (f'W{l}', (m, d)), (f'bw{l}', (d,))]
    return sh + [('D', (d, dout)), ('bD', (dout,))]

def unpack(v, sh):
    out, k = {}, 0
    for name, s in sh:
        n = int(np.prod(s)); out[name] = v[k:k + n].reshape(s); k += n
    return out

def pack(q, sh):
    return np.concatenate([np.asarray(q[name]).reshape(-1) for name, _ in sh])

def forward(v, sh, X, widths):
    q = unpack(v, sh)
    h = X @ q['E'] + q['bE']
    for l in range(len(widths)):
        h = h + np.tanh(h @ q[f'R{l}'] + q[f'br{l}']) @ q[f'W{l}'] + q[f'bw{l}']
    return h @ q['D'] + q['bD']

def jac(v, sh, X, widths):
    cols = []
    for i in range(v.size):
        w = v.astype(complex); w[i] += 1e-30j
        cols.append(forward(w, sh, X, widths).imag.reshape(-1) / 1e-30)
    return np.array(cols).T

def small(v, sh, tau):
    q = {k: a.copy() for k, a in unpack(v, sh).items()}
    for name in q:
        if name.startswith('W') or name.startswith('bw'):
            q[name] = tau * q[name]
    return pack(q, sh)

def limit(v, sh, X, widths):
    """smallWritesLimitB: the matrix of eta -> ((J_0 eta)(x))_x."""
    q = unpack(v, sh); P = v.size; cols = []
    h = X @ q['E'] + q['bE']
    for i in range(P):
        e = np.zeros(P); e[i] = 1; n = unpack(e, sh)
        out = X @ (n['E'] @ q['D'] + q['E'] @ n['D'])
        out = out + (n['bE'] @ q['D'] + q['bE'] @ n['D'] + n['bD']
                     + sum(n[f'bw{l}'] for l in range(len(widths))) @ q['D'])
        for l in range(len(widths)):
            pre = h @ q[f'R{l}'] + q[f'br{l}']
            dpre = h @ n[f'R{l}'] + n[f'br{l}']
            out = out + ((1 - np.tanh(pre) ** 2) * dpre @ q[f'W{l}'] + np.tanh(pre) @ n[f'W{l}']) @ q['D']
        cols.append(out.reshape(-1))
    return np.array(cols).T

def rank(M, tol=1e-9):
    s = np.linalg.svd(M, compute_uv=False)
    r = int((s > tol * s[0]).sum())
    return r, s[r - 1] / s[0], (s[r] / s[0] if r < len(s) else 0.0)

for (d, din, dout, widths) in [(2, 2, 2, [2, 2]), (2, 3, 3, [3, 1, 2]), (3, 3, 4, [2, 4])]:
    sh = shapes(d, din, dout, widths); P = sum(int(np.prod(s)) for _, s in sh); L = len(widths)
    v = rng.standard_normal(P); X = rng.standard_normal((6 * P // dout + 10, din))
    scale = np.ones(P); k = 0
    for name, s in sh:
        n = int(np.prod(s))
        if name.startswith('R') or name.startswith('br'):
            scale[k:k + n] = 0  # marks the read coordinates
        k += n
    J0 = limit(v, sh, X, widths)
    target = P - d * d - (L + 1) * d
    r0 = rank(J0)
    line = f"d={d} din={din} dout={dout} widths={widths}: P={P} target={target} rank J_0={r0[0]} (gap {r0[1]:.1e}/{r0[2]:.1e})"
    for tau in [1e-1, 1e-2]:
        Jt = jac(small(v, sh, tau), sh, X, widths)
        S = np.where(scale == 0, 1 / tau, 1.0)
        dev = np.abs(Jt * S - J0).max() / np.abs(J0).max()
        rt = rank(Jt * S)
        line += f"; tau={tau}: |J_tau S_tau - J_0|/|J_0|={dev:.1e}, rank J_tau={rt[0]} (gap {rt[1]:.1e}/{rt[2]:.1e})"
    print(line)
