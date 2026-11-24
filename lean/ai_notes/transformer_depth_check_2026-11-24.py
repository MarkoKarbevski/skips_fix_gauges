# Numeric check (24 November 2026) of the values claimed in Residual/DepthTransformer.lean and
# Residual/DepthTransformerGated.lean: a residual network whose blocks are attention blocks and
# MLP blocks (tanh), or attention blocks and gated blocks (SiLU gate), in any order and also side
# by side in one block, without normalization, has at random parameters Jacobian rank
#   P - d^2 - 2 sum_l H_l d_{h,l}^2            (tanh units)
#   P - d^2 - 2 sum_l H_l d_{h,l}^2 - #units   (gated units).
# Jacobian by central differences (step 1e-5), rank read with a gap check.
import numpy as np
rng = np.random.default_rng(31)
def weights(Z, sees):
    T = Z.shape[0]; P = np.zeros_like(Z)
    for t in range(T):
        idx = [s for s in range(T) if sees(t, s)]
        e = np.exp(Z[t, idx]); P[t, idx] = e / e.sum()
    return P
silu = lambda z: z / (1 + np.exp(-z))
def net(par, x, sees, d, spec, gated):
    E, blocks, D = par
    h = x @ E
    for blk, (H, dh, m) in zip(blocks, spec):
        out = np.zeros_like(h)
        Q, K, V, O = blk[:4]
        for i in range(H):
            Z = (h @ Q[i]) @ (h @ K[i]).T / np.sqrt(dh)
            out += weights(Z, sees) @ h @ V[i] @ O[i]
        if m > 0:
            if gated:
                G, Vv, W = blk[4:]
                out += (silu(h @ G) * (h @ Vv)) @ W
            else:
                R, W = blk[4:]
                out += np.tanh(h @ R) @ W
        h = h + out
    return h @ D
def draw(d, din, dout, spec, gated):
    g = lambda *s: 0.6 * rng.normal(size=s)
    blocks = []
    for (H, dh, m) in spec:
        b = [g(H, d, dh), g(H, d, dh), g(H, d, dh), g(H, dh, d)]
        b += ([g(d, m), g(d, m), g(m, d)] if gated else [g(d, m), g(m, d)])
        blocks.append(b)
    return [g(din, d), blocks, g(d, dout)]
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
# spec: per block (H, d_h, hidden units); (H, dh, 0) is an attention block, (0, 1, m) an MLP block
cases = [((2, 2, 2, 2), [(1, 1, 0), (0, 1, 3)]),            # attention, then MLP
         ((2, 2, 2, 2), [(0, 1, 2), (2, 1, 0), (0, 1, 2)]), # MLP, attention, MLP
         ((3, 2, 3, 2), [(1, 2, 0), (0, 1, 3), (2, 1, 0)]),
         ((2, 3, 3, 3), [(1, 2, 2), (0, 1, 4)]),            # heads and units side by side
         ((2, 2, 3, 3), [(1, 1, 1)])]
for gated in [False, True]:
    for name, sees in masks.items():
        for (T, d, din, dout), spec in cases:
            par = draw(d, din, dout, spec, gated); th = flat(par); P = th.size
            nb = 60
            X = [0.8 * rng.normal(size=(T, din)) for _ in range(nb)]
            J = np.zeros((nb * T * dout, P)); hh = 1e-5
            for j in range(P):
                e = np.zeros(P); e[j] = hh
                fp = np.concatenate([net(unflat(th + e, par), x, sees, d, spec, gated).ravel() for x in X])
                fm = np.concatenate([net(unflat(th - e, par), x, sees, d, spec, gated).ravel() for x in X])
                J[:, j] = (fp - fm) / (2 * hh)
            sv = np.linalg.svd(J, compute_uv=False)
            s = 2 * sum(H * dh * dh for H, dh, m in spec) + (sum(m for H, dh, m in spec) if gated else 0)
            r = P - d * d - s
            print('gated' if gated else 'tanh ', name, (T, d, din, dout), spec, 'P =', P, 'claimed', r,
                  'sv[r-1] = %.2e' % sv[r - 1], 'sv[r] = %.2e' % sv[r], 'gap = %.1e' % (sv[r - 1] / sv[r]))
