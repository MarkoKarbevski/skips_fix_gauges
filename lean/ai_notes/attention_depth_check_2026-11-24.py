# Numeric check (24 November 2026) of the value claimed in Residual/DepthAttention.lean:
# a residual network of L attention blocks without normalization has, at random parameters,
# Jacobian rank P - d^2 - 2 sum_l H_l d_{h,l}^2 (heads of width d_h <= d, any total width).
# Jacobian by central differences (step 1e-5), rank read with a gap check.
import numpy as np
rng = np.random.default_rng(11)
def weights(Z, sees):
    T = Z.shape[0]; P = np.zeros_like(Z)
    for t in range(T):
        idx = [s for s in range(T) if sees(t, s)]
        e = np.exp(Z[t, idx]); P[t, idx] = e / e.sum()
    return P
def net(par, x, sees, dims, heads):
    T, d, din, dout = dims
    E, blocks, D = par
    h = x @ E
    for (Q, K, V, O), (H, dh) in zip(blocks, heads):
        out = np.zeros((T, d))
        for i in range(H):
            Z = (h @ Q[i]) @ (h @ K[i]).T / np.sqrt(dh)
            out += weights(Z, sees) @ h @ V[i] @ O[i]
        h = h + out
    return h @ D
def draw(dims, heads):
    T, d, din, dout = dims
    g = lambda *s: 0.6 * rng.normal(size=s)   # moderate weights: the scores stay small
    return [g(din, d),
            [[g(H, d, dh), g(H, d, dh), g(H, d, dh), g(H, dh, d)] for (H, dh) in heads], g(d, dout)]
def flat(par):
    E, blocks, D = par
    return np.concatenate([E.ravel()] + [a.ravel() for b in blocks for a in b] + [D.ravel()])
def unflat(vec, par):
    E, blocks, D = par; k = 0
    def take(a):
        nonlocal k
        out = vec[k:k + a.size].reshape(a.shape); k += a.size; return out
    return [take(E), [[take(a) for a in b] for b in blocks], take(D)]
masks = {'none': lambda t, s: True, 'causal': lambda t, s: s <= t}
for name, sees in masks.items():
    for dims, heads in [((2, 2, 2, 2), [(1, 1), (1, 1)]), ((3, 2, 3, 2), [(2, 1), (1, 2)]),
                        ((2, 3, 3, 3), [(1, 2), (2, 1), (1, 1)]), ((3, 2, 2, 3), [(1, 2), (1, 2), (1, 2)])]:
        T, d, din, dout = dims
        par = draw(dims, heads); th = flat(par); P = th.size
        X = [0.8 * rng.normal(size=(T, din)) for _ in range(40)]
        J = np.zeros((40 * T * dout, P)); hh = 1e-5
        for j in range(P):
            e = np.zeros(P); e[j] = hh
            fp = np.concatenate([net(unflat(th + e, par), x, sees, dims, heads).ravel() for x in X])
            fm = np.concatenate([net(unflat(th - e, par), x, sees, dims, heads).ravel() for x in X])
            J[:, j] = (fp - fm) / (2 * hh)
        sv = np.linalg.svd(J, compute_uv=False)
        r = P - d * d - 2 * sum(H * dh * dh for H, dh in heads)
        print(name, dims, heads, 'P =', P, 'claimed', r, 'sv[r-1] = %.2e' % sv[r - 1], 'sv[r] = %.2e' % sv[r],
              'gap = %.1e' % (sv[r - 1] / sv[r]))
