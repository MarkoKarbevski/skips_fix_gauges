# Numeric check: the upper bounds for networks of attention blocks (dimension paper, Theorem 4.3; skips paper, Theorem 4.2),
# s = 2 * sum_l H_l d_h^2: rank <= P - (L+1) d^2 - s without skips, <= P - d^2 - s with identity skips (no normalization);
# one block: equality expected (dimension Theorem 5.1 / C.1, skips Theorem B.1 (i)).
# Jacobian in the weights by central differences (float64), singular values compared with a threshold.
import numpy as np
rng = np.random.default_rng(21)
def weights(Z, mask):
    W = np.where(mask, np.exp(Z), 0.0); return W/W.sum(axis=1, keepdims=True)
def unpack(v, shapes):
    out = []; k = 0
    for sh in shapes:
        n = int(np.prod(sh)); out.append(v[k:k+n].reshape(sh)); k += n
    return out
def net(v, shapes, X, mask, s, L, Hh, dh):
    P = unpack(v, shapes); E, D = P[0], P[-1]; h = X @ E
    for l in range(L):
        WQ, WK, WV, WO = P[1+4*l:5+4*l]; out = 0
        for i in range(Hh):
            sl = slice(i*dh, (i+1)*dh)
            out = out + weights((h @ WQ[:, sl]) @ (h @ WK[:, sl]).T/np.sqrt(dh), mask) @ (h @ WV[:, sl]) @ WO[sl, :]
        h = s*h + out
    return h @ D
for (T, d, dIn, dOut, L, Hh, dh, maskname) in [(3, 2, 2, 2, 1, 2, 1, 'none'), (3, 2, 2, 2, 1, 2, 1, 'causal'), (3, 3, 3, 3, 1, 2, 2, 'causal'), (3, 2, 2, 2, 2, 2, 1, 'causal'), (4, 2, 2, 2, 2, 1, 2, 'none')]:
    mask = np.ones((T, T), bool) if maskname == 'none' else np.tril(np.ones((T, T), bool))
    shapes = [(dIn, d)] + [(d, Hh*dh), (d, Hh*dh), (d, Hh*dh), (Hh*dh, d)]*L + [(d, dOut)]
    P = sum(int(np.prod(sh)) for sh in shapes); v0 = rng.normal(size=P)
    Xs = [rng.normal(size=(T, dIn)) for _ in range(3*P//(T*dOut) + 6)]
    for s in [0.0, 1.0]:
        J = np.zeros((len(Xs)*T*dOut, P)); eps = 1e-6
        for c in range(P):
            e = np.zeros(P); e[c] = eps
            J[:, c] = np.concatenate([((net(v0 + e, shapes, X, mask, s, L, Hh, dh) - net(v0 - e, shapes, X, mask, s, L, Hh, dh))/(2*eps)).ravel() for X in Xs])
        sv = np.linalg.svd(J, compute_uv=False)
        bound = P - ((L + 1)*d*d if s == 0 else d*d) - 2*L*Hh*dh*dh
        rank = int((sv > 1e-6*sv[0]).sum())
        print(f"T={T} d={d} L={L} H={Hh} dh={dh} mask={maskname} skips={int(s)}: P={P} rank={rank} bound={bound} sv[bound-1]/sv[0]={sv[bound-1]/sv[0]:.1e} sv[bound]/sv[0]={(sv[bound]/sv[0] if bound < P else 0):.1e}")
