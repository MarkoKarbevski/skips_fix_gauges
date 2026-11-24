# Numeric check (24 November 2026) of the value claimed in Residual/BlocksAloneAttention.lean
# (skips paper, Corollary 4.10 (ii)): a residual network of L attention blocks without
# normalization, WITHOUT embedding and readout (h_0 = x, y = h_L), has at random block
# parameters Jacobian rank P - 2 sum_l H_l d_{h,l}^2, with P the number of block parameters.
# Jacobian with respect to the reads and writes only, by central differences (step 1e-5),
# rank read with a gap check. Also the full network at E = D = I, for comparison:
# rank P_full - d^2 - s there would give the same count of flat directions inside the blocks.
import numpy as np
rng = np.random.default_rng(23)
def weights(Z, sees):
    T = Z.shape[0]; P = np.zeros_like(Z)
    for t in range(T):
        idx = [s for s in range(T) if sees(t, s)]
        e = np.exp(Z[t, idx]); P[t, idx] = e / e.sum()
    return P
def net(blocks, x, sees, T, d, heads):
    h = x.copy()
    for (Q, K, V, O), (H, dh) in zip(blocks, heads):
        out = np.zeros((T, d))
        for i in range(H):
            Z = (h @ Q[i]) @ (h @ K[i]).T / np.sqrt(dh)
            out += weights(Z, sees) @ h @ V[i] @ O[i]
        h = h + out
    return h
def draw(d, heads):
    g = lambda *s: 0.6 * rng.normal(size=s)
    return [[g(H, d, dh), g(H, d, dh), g(H, d, dh), g(H, dh, d)] for (H, dh) in heads]
def flat(blocks):
    return np.concatenate([a.ravel() for b in blocks for a in b])
def unflat(vec, blocks):
    k = 0
    def take(a):
        nonlocal k
        out = vec[k:k + a.size].reshape(a.shape); k += a.size; return out
    return [[take(a) for a in b] for b in blocks]
masks = {'none': lambda t, s: True, 'causal': lambda t, s: s <= t}
for name, sees in masks.items():
    for (T, d), heads in [((2, 2), [(1, 1), (1, 1)]), ((2, 2), [(2, 1), (2, 1)]), ((3, 2), [(2, 1), (1, 2)]),
                          ((2, 3), [(1, 2), (2, 1), (1, 1)]), ((3, 2), [(1, 2), (1, 2), (1, 2)]),
                          ((2, 4), [(2, 2), (2, 2)]), ((2, 3), [(3, 1)])]:
        par = draw(d, heads); th = flat(par); P = th.size
        nb = 60
        X = [0.8 * rng.normal(size=(T, d)) for _ in range(nb)]
        J = np.zeros((nb * T * d, P)); hh = 1e-5
        for j in range(P):
            e = np.zeros(P); e[j] = hh
            fp = np.concatenate([net(unflat(th + e, par), x, sees, T, d, heads).ravel() for x in X])
            fm = np.concatenate([net(unflat(th - e, par), x, sees, T, d, heads).ravel() for x in X])
            J[:, j] = (fp - fm) / (2 * hh)
        sv = np.linalg.svd(J, compute_uv=False)
        s = 2 * sum(H * dh * dh for H, dh in heads)
        r = P - s
        tail = sv[r] if r < len(sv) else 0.0
        print(name, 'T,d =', (T, d), heads, 'P =', P, 's =', s, 'claimed', r,
              'sv[r-1] = %.2e' % sv[r - 1], 'sv[r] = %.2e' % tail,
              'gap = %.1e' % (sv[r - 1] / max(tail, 1e-300)))
