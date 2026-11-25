# Numeric check of the statements on pre-LayerNorm networks (dimension paper, Proposition A.3;
# skips paper, Proposition A.15), 25 November 2026.
#   LN_l(h) = N_eps(h Z) diag(gamma_l) + beta_l,  Z = I - 11^T/d,  N_eps(v) = v / sqrt(|v|^2/d + eps)
#   h_0 = x E + b_E;  h_{l+1} = s h_l + tanh(LN_l(h_l) R_l + br_l) W_l + bw_l;  y = LN_L(h_L) D + b_D
# (i)  the pre-RMSNorm network with E Z, b_E Z, reads diag(gamma_l) R_l, read biases
#      br_l + beta_l R_l, writes W_l Z, write biases bw_l Z, readout diag(gamma_L) D, readout bias
#      b_D + beta_L D computes the same function, and its hidden states have mean zero.
# (ii) with U (d x (d-1), orthonormal columns spanning the rows of mean zero), c = sqrt(d/(d-1)):
#      the pre-RMSNorm network of dimension d - 1 with eps' = eps d/(d-1), E U, b_E U, reads
#      c U^T diag(gamma_l) R_l, read biases br_l + beta_l R_l, writes W_l U, write biases bw_l U,
#      readout c U^T diag(gamma_L) D, readout bias b_D + beta_L D computes the same function.
# (iii) the rank of the Jacobian of the LayerNorm network in all its parameters (weights, biases,
#      gains, LayerNorm biases) equals that of the reduced network of (ii) at the image, with
#      skips and without (complex step).
import numpy as np
rng = np.random.default_rng(3)

def N(h, eps):
    return h / np.sqrt((h * h).sum(axis=-1, keepdims=True) / h.shape[-1] + eps)

def ln_net(p, x, s, eps):
    d = p['E'].shape[1]; Z = np.eye(d) - np.ones((d, d)) / d
    L = len(p['R'])
    h = x @ p['E'] + p['bE']
    for l in range(L):
        n = N(h @ Z, eps) * p['g'][l] + p['be'][l]
        h = s * h + np.tanh(n @ p['R'][l] + p['br'][l]) @ p['W'][l] + p['bw'][l]
    n = N(h @ Z, eps) * p['g'][L] + p['be'][L]
    return n @ p['D'] + p['bD']

def rms_net(q, x, s, eps, hidden=False):
    L = len(q['R'])
    h = x @ q['E'] + q['bE']; hs = [h]
    for l in range(L):
        h = s * h + np.tanh(N(h, eps) @ q['R'][l] + q['br'][l]) @ q['W'][l] + q['bw'][l]; hs.append(h)
    return hs if hidden else N(h, eps) @ q['D'] + q['bD']

def centred(p):
    d = p['E'].shape[1]; Z = np.eye(d) - np.ones((d, d)) / d; L = len(p['R'])
    return dict(E=p['E'] @ Z, bE=p['bE'] @ Z,
                R=[np.diag(p['g'][l]) @ p['R'][l] for l in range(L)],
                br=[p['br'][l] + p['be'][l] @ p['R'][l] for l in range(L)],
                W=[p['W'][l] @ Z for l in range(L)], bw=[p['bw'][l] @ Z for l in range(L)],
                D=np.diag(p['g'][L]) @ p['D'], bD=p['bD'] + p['be'][L] @ p['D'])

def reduced(p, U):
    d = p['E'].shape[1]; L = len(p['R']); c = np.sqrt(d / (d - 1))
    return dict(E=p['E'] @ U, bE=p['bE'] @ U,
                R=[c * U.T @ np.diag(p['g'][l]) @ p['R'][l] for l in range(L)],
                br=[p['br'][l] + p['be'][l] @ p['R'][l] for l in range(L)],
                W=[p['W'][l] @ U for l in range(L)], bw=[p['bw'][l] @ U for l in range(L)],
                D=c * U.T @ np.diag(p['g'][L]) @ p['D'], bD=p['bD'] + p['be'][L] @ p['D'])

def basis(d):
    Z = np.eye(d) - np.ones((d, d)) / d
    w, v = np.linalg.eigh(Z)
    return v[:, 1:]            # the eigenvalue 0 comes first

def draw(L, d, din, dout, wid):
    return dict(E=rng.normal(size=(din, d)), bE=rng.normal(size=d),
                R=[rng.normal(size=(d, wid)) for _ in range(L)], br=[rng.normal(size=wid) for _ in range(L)],
                W=[rng.normal(size=(wid, d)) for _ in range(L)], bw=[rng.normal(size=d) for _ in range(L)],
                D=rng.normal(size=(d, dout)), bD=rng.normal(size=dout),
                g=[rng.normal(size=d) for _ in range(L + 1)], be=[rng.normal(size=d) for _ in range(L + 1)])

e1 = e1h = e2 = eU = 0.0
for (L, d, din, dout, wid) in [(1, 3, 2, 2, 3), (2, 4, 3, 3, 5), (3, 3, 4, 2, 2)]:
    U = basis(d); Z = np.eye(d) - np.ones((d, d)) / d
    eU = max(eU, np.abs(U.T @ U - np.eye(d - 1)).max(), np.abs(U @ U.T - Z).max())
    for eps in [0.0, 0.3]:
        for s in [0.0, 1.0]:
            p = draw(L, d, din, dout, wid); x = rng.normal(size=(4, din))
            y = ln_net(p, x, s, eps)
            q = centred(p)
            e1 = max(e1, np.abs(rms_net(q, x, s, eps) - y).max())
            e1h = max(e1h, max(np.abs(h.sum(axis=1)).max() for h in rms_net(q, x, s, eps, hidden=True)))
            e2 = max(e2, np.abs(rms_net(reduced(p, U), x, s, eps * d / (d - 1)) - y).max())
print('U^T U = I and U U^T = Z: %.1e' % eU)
print('(i) same function: %.1e; row sums of the hidden states: %.1e' % (e1, e1h))
print('(ii) same function in dimension d - 1 with eps d/(d-1): %.1e' % e2)

# (iii)
def keys(p): return [k for k in ['E', 'bE', 'R', 'br', 'W', 'bw', 'D', 'bD', 'g', 'be'] if k in p]
def flat(p): return np.concatenate([np.asarray(m).ravel() for k in keys(p) for m in (p[k] if isinstance(p[k], list) else [p[k]])])
def unflat(v, p):
    out = {}; i = 0
    for k in keys(p):
        if isinstance(p[k], list):
            out[k] = []
            for m in p[k]:
                out[k].append(v[i:i + m.size].reshape(m.shape)); i += m.size
        else:
            out[k] = v[i:i + p[k].size].reshape(p[k].shape); i += p[k].size
    return out
def jac_rank(f, p, X):
    th = flat(p).astype(complex); P = th.size; cols = []
    for j in range(P):
        e = np.zeros(P, dtype=complex); e[j] = 1e-30j
        cols.append(np.concatenate([f(unflat(th + e, p), x.astype(complex)).ravel() for x in X]).imag / 1e-30)
    sv = np.linalg.svd(np.array(cols).T, compute_uv=False)
    # the rank is read at the largest gap between consecutive singular values (the skipless
    # networks under normalization are badly conditioned: a fixed threshold cut a cluster)
    svp = np.maximum(sv, 1e-300)
    r = int(np.argmax(svp[:-1] / svp[1:])) + 1
    return P, r, sv[r - 1], (sv[r] if r < len(sv) else 0.0)
for (L, d, din, dout, wid) in [(1, 3, 3, 3, 3), (1, 4, 4, 4, 3), (2, 3, 3, 3, 2)]:
    U = basis(d); eps = 0.3
    p = draw(L, d, din, dout, wid); q = reduced(p, U)
    out = []
    for s in [0.0, 1.0]:
        PL = flat(p).size
        X = [2.0 * rng.normal(size=(2, din)) for _ in range(4 * PL // (2 * dout) + 3)]
        a = jac_rank(lambda t, x: ln_net(t, x, s, eps), p, X)
        b = jac_rank(lambda t, x: rms_net(t, x, s, eps * d / (d - 1)), q, X)
        out.append((a, b))
        print('(iii)', (L, d, din, dout, wid), 's = %d' % s, 'LayerNorm network: P = %d, rank %d (sv %.1e | %.1e);' % a,
              'reduced network: P = %d, rank %d (sv %.1e | %.1e)' % b, 'EQUAL' if a[1] == b[1] else 'DIFFERENT')
    print('      difference of the ranks (residual - skipless): LayerNorm %d, reduced %d' % (out[1][0][1] - out[0][0][1], out[1][1][1] - out[0][1][1]))
