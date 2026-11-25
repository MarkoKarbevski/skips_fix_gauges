"""Numeric check for the statements of `Symmetry/InsideBlocksBiases.lean` and
`Symmetry/BiasesRescaleCount.lean` (S Lemma A.8, the count with `s`).

Networks with biases as in `Network/Biases.lean` (one token):
  h_0 = x E + b_E,  h_{l+1} = h_l M + f(h_l R_l + b_read_l) W_l + b_write_l,  y = h_L D + b_D,
with M = I (residual) or M = 0 (skipless). The Jacobian in weights and biases together is
computed by the complex step (exact to machine precision: the blocks are piecewise polynomial in
the parameters near a point where no pre-activation vanishes).  Checked:
  (a) the directions of the changes of basis, of the translations and of the rescalings of the
      hidden units (with their biases) are in the kernel of the Jacobian;
  (b) the rank of the Jacobian against the bounds  P - d^2 - (L+1) d - s  (residual)  and
      P - (L+1)(d^2 + d) - s  (skipless).
"""
import numpy as np

rng = np.random.default_rng(7)

def relu(z):
    return np.where(z.real > 0, z, 0)

def relusq(z):
    return np.where(z.real > 0, z * z, 0)

def swish(z):
    e = np.exp(-np.abs(z.real) - 1j * np.sign(z.real + (z.real == 0)) * z.imag)   # exp(-|z|), no overflow
    return np.where(z.real >= 0, z / (1 + e), z * e / (1 + e))

KINDS = {  # name: (gated?, activation, degree k or None, s per hidden unit)
    'relu':   (False, relu,   1, 1),
    'relusq': (False, relusq, 2, 1),
    'reglu':  (True,  relu,   1, 2),
    'swiglu': (True,  swish,  None, 1),
}

def shapes(d, din, dout, widths, gated):
    sh = [('E', (din, d)), ('bE', (d,))]
    for l, m in enumerate(widths):
        r = 2 * m if gated else m
        sh += [(f'R{l}', (d, r)), (f'br{l}', (r,)), (f'W{l}', (m, d)), (f'bw{l}', (d,))]
    sh += [('D', (d, dout)), ('bD', (dout,))]
    return sh

def unpack(v, sh):
    out, k = {}, 0
    for name, s in sh:
        n = int(np.prod(s))
        out[name] = v[k:k + n].reshape(s)
        k += n
    return out

def pack(dct, sh):
    return np.concatenate([np.asarray(dct[name]).reshape(-1) for name, _ in sh])

def forward(v, sh, X, widths, gated, act, skip):
    q = unpack(v, sh)
    h = X @ q['E'] + q['bE']
    for l, m in enumerate(widths):
        pre = h @ q[f'R{l}'] + q[f'br{l}']
        f = act(pre[:, :m]) * pre[:, m:] if gated else act(pre)
        h = (h if skip else 0) + f @ q[f'W{l}'] + q[f'bw{l}']
    return h @ q['D'] + q['bD']

def jacobian(v, sh, X, widths, gated, act, skip):
    cols = []
    for i in range(v.size):
        w = v.astype(complex)
        w[i] += 1e-30j
        cols.append(forward(w, sh, X, widths, gated, act, skip).imag.reshape(-1) / 1e-30)
    return np.array(cols).T

def zero(sh):
    return {name: np.zeros(s) for name, s in sh}

def cob_dir(q, sh, Xs, widths):          # cobDirB
    L = len(widths)
    e = zero(sh)
    e['E'] = q['E'] @ Xs[0]
    e['bE'] = q['bE'] @ Xs[0]
    for l in range(L):
        e[f'R{l}'] = -Xs[l] @ q[f'R{l}']
        e[f'W{l}'] = q[f'W{l}'] @ Xs[l + 1]
        e[f'bw{l}'] = q[f'bw{l}'] @ Xs[l + 1]
    e['D'] = -Xs[L] @ q['D']
    return e

def translate_dir(q, sh, g, widths, skip):   # translateDir (skip) / translateAtDir (no skip)
    L = len(widths)
    e = zero(sh)
    e['bE'] = g[0]
    for l in range(L):
        s = sum(g[:l + 1]) if skip else g[l]
        e[f'br{l}'] = -s @ q[f'R{l}']
        e[f'bw{l}'] = g[l + 1]
    e['bD'] = -(sum(g) if skip else g[L]) @ q['D']
    return e

def rescale_dirs(q, sh, widths, gated, k):
    """Basis of the rescaling directions with biases: rescaleDirMlpB, rescaleDirB, rescaleDirGateB."""
    dirs = []
    for l, m in enumerate(widths):
        for i in range(m):
            if not gated:                      # read column and read bias times 1, write row times -k
                e = zero(sh)
                e[f'R{l}'][:, i] = q[f'R{l}'][:, i]
                e[f'br{l}'][i] = q[f'br{l}'][i]
                e[f'W{l}'][i, :] = -k * q[f'W{l}'][i, :]
                dirs.append(e)
            else:
                e = zero(sh)                   # value column and value bias times -1, write row times 1
                e[f'R{l}'][:, m + i] = -q[f'R{l}'][:, m + i]
                e[f'br{l}'][m + i] = -q[f'br{l}'][m + i]
                e[f'W{l}'][i, :] = q[f'W{l}'][i, :]
                dirs.append(e)
                if k is not None:              # gate column and gate bias times 1, write row times -k
                    e = zero(sh)
                    e[f'R{l}'][:, i] = q[f'R{l}'][:, i]
                    e[f'br{l}'][i] = q[f'br{l}'][i]
                    e[f'W{l}'][i, :] = -k * q[f'W{l}'][i, :]
                    dirs.append(e)
    return dirs

def run(kind, d, din, dout, widths, skip, nbatch):
    gated, act, k, sper = KINDS[kind]
    sh = shapes(d, din, dout, widths, gated)
    P = sum(int(np.prod(s)) for _, s in sh)
    L = len(widths)
    v = rng.standard_normal(P)
    q = unpack(v, sh)
    X = rng.standard_normal((nbatch, din)) * 2.0
    J = jacobian(v, sh, X, widths, gated, act, skip)
    scale = np.abs(J).max()
    dirs = []
    if skip:
        for a in range(d):
            for b in range(d):
                Y = np.zeros((d, d)); Y[a, b] = 1
                dirs.append(cob_dir(q, sh, [Y] * (L + 1), widths))
    else:
        for j in range(L + 1):
            for a in range(d):
                for b in range(d):
                    Xs = [np.zeros((d, d)) for _ in range(L + 1)]
                    Xs[j][a, b] = 1
                    dirs.append(cob_dir(q, sh, Xs, widths))
    for j in range(L + 1):
        for a in range(d):
            g = [np.zeros(d) for _ in range(L + 1)]
            g[j][a] = 1
            dirs.append(translate_dir(q, sh, g, widths, skip))
    dirs += rescale_dirs(q, sh, widths, gated, k)
    Dm = np.array([pack(e, sh) for e in dirs]).T
    resid = np.abs(J @ Dm).max() / scale
    rank_dirs = np.linalg.matrix_rank(Dm)
    s = sper * sum(widths)
    bound = P - (d * d + (L + 1) * d + s) if skip else P - ((L + 1) * (d * d + d) + s)
    sv = np.linalg.svd(J, compute_uv=False)
    rank = int((sv > 1e-9 * sv[0]).sum())
    gap = (sv[rank - 1] / sv[0], (sv[rank] / sv[0]) if rank < len(sv) else 0.0)
    print(f"{kind:7s} d={d} din={din} dout={dout} widths={widths} skip={skip}: P={P} "
          f"dirs={len(dirs)} independent={rank_dirs} |J dirs|/|J|={resid:.1e} "
          f"rank={rank} bound={bound} {'OK' if rank <= bound else 'ABOVE'} "
          f"{'=' if rank == bound else '<'} gap={gap[0]:.1e}/{gap[1]:.1e}")

for kind in ['relu', 'relusq', 'reglu', 'swiglu']:
    for skip in [True, False]:
        run(kind, 2, 3, 3, [3, 3], skip, 400)
        run(kind, 2, 2, 2, [2], skip, 300)
        run(kind, 3, 3, 4, [4, 3], skip, 600)
