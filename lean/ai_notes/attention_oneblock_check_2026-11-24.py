# Numeric check of the statements of OneBlock/Attention.lean (24 November 2026):
# (a) eval_attention_oneBlock, (b) eval_attention_two_tokens (equation (8)), for three masks,
# (c) dAttnScore, dAttnValue against finite differences,
# (d) the value of the functional dimension for one block, skipless and residual,
#     with the exact Jacobian (complex step is not used; autograd by hand is avoided:
#     the Jacobian is taken by central differences in float64 with step 1e-6 and the rank
#     read with a gap check).
import numpy as np
rng = np.random.default_rng(7)

def weights(Z, sees):
    T = Z.shape[0]; P = np.zeros_like(Z)
    for t in range(T):
        idx = [s for s in range(T) if sees(t, s)]
        if idx:
            e = np.exp(Z[t, idx]); P[t, idx] = e / e.sum()
    return P

def net(par, x, sees, s, dims):
    T, d, din, dout, H, dh = dims
    E, Q, K, V, O, D = par
    h0 = x @ E
    out = np.zeros((T, d))
    for i in range(H):
        Z = (h0 @ Q[i]) @ (h0 @ K[i]).T / np.sqrt(dh)
        out += weights(Z, sees) @ h0 @ V[i] @ O[i]
    return (s * h0 + out) @ D

def draw(dims):
    T, d, din, dout, H, dh = dims
    return [rng.normal(size=(din, d)), rng.normal(size=(H, d, dh)), rng.normal(size=(H, d, dh)),
            rng.normal(size=(H, d, dh)), rng.normal(size=(H, dh, d)), rng.normal(size=(d, dout))]

def BC(par, dims):
    T, d, din, dout, H, dh = dims
    E, Q, K, V, O, D = par
    B = [E @ Q[i] @ K[i].T @ E.T / np.sqrt(dh) for i in range(H)]
    C = [E @ V[i] @ O[i] @ D for i in range(H)]
    return B, C

masks = {'none': lambda t, s: True, 'causal': lambda t, s: s <= t,
         'odd': lambda t, s: (t == s) or (s == 0) or (t == 2 and s == 3)}
worst = 0.0
for name, sees in masks.items():
    for dims in [(4, 3, 4, 5, 2, 2), (5, 2, 2, 3, 3, 1), (4, 3, 3, 3, 1, 3)]:
        T, d, din, dout, H, dh = dims
        for s in [0.0, 1.0, -0.7]:
            par = draw(dims); E, Q, K, V, O, D = par
            B, C = BC(par, dims)
            x = rng.normal(size=(T, din))
            # (a)
            rhs = s * x @ E @ D + sum(weights(x @ B[i] @ x.T, sees) @ x @ C[i] for i in range(H))
            worst = max(worst, np.abs(net(par, x, sees, s, dims) - rhs).max())
            # (b) token t2 sees itself and t1 != t2
            for t2 in range(T):
                others = [t for t in range(T) if t != t2 and sees(t2, t)]
                if not sees(t2, t2) or not others:
                    continue
                k = len(others)
                u = rng.normal(size=din); v = rng.normal(size=din)
                xin = np.array([u if t == t2 else u - v for t in range(T)])
                Ssum = sum(C)
                y = u @ (s * E @ D + Ssum) - 0.5 * v @ Ssum + sum(
                    0.5 * np.tanh(0.5 * (u @ B[i] @ v - np.log(k))) * (v @ C[i]) for i in range(H))
                worst = max(worst, np.abs(net(par, xin, sees, s, dims)[t2] - y).max())
print('(a), (b): largest error', worst)

# (c)
dims = (3, 3, 4, 4, 2, 2); T, d, din, dout, H, dh = dims
par = draw(dims); eta = draw(dims)
E, Q, K, V, O, D = par; eE, eQ, eK, eV, eO, eD = eta
h = 1e-6
Bp, Cp = BC([p + h * e for p, e in zip(par, eta)], dims)
Bm, Cm = BC([p - h * e for p, e in zip(par, eta)], dims)
errc = 0.0
for i in range(H):
    dB = (eE @ Q[i] @ K[i].T @ E.T + E @ eQ[i] @ K[i].T @ E.T + E @ Q[i] @ eK[i].T @ E.T
          + E @ Q[i] @ K[i].T @ eE.T) / np.sqrt(dh)
    dC = eE @ V[i] @ O[i] @ D + E @ eV[i] @ O[i] @ D + E @ V[i] @ eO[i] @ D + E @ V[i] @ O[i] @ eD
    errc = max(errc, np.abs((Bp[i] - Bm[i]) / (2 * h) - dB).max(), np.abs((Cp[i] - Cm[i]) / (2 * h) - dC).max())
print('(c): largest error', errc)

# (d)
def flatpar(par): return np.concatenate([p.ravel() for p in par])
def unflat(vec, par):
    out = []; k = 0
    for p in par:
        out.append(vec[k:k + p.size].reshape(p.shape)); k += p.size
    return out
def jac_rank(par, sees, s, dims, nb=40):
    T, d, din, dout, H, dh = dims
    th = flatpar(par); P = th.size
    X = [rng.normal(size=(T, din)) for _ in range(nb)]
    J = np.zeros((nb * T * dout, P)); hh = 1e-5
    for j in range(P):
        e = np.zeros(P); e[j] = hh
        fp = np.concatenate([net(unflat(th + e, par), x, sees, s, dims).ravel() for x in X])
        fm = np.concatenate([net(unflat(th - e, par), x, sees, s, dims).ravel() for x in X])
        J[:, j] = (fp - fm) / (2 * hh)
    sv = np.linalg.svd(J, compute_uv=False)
    return P, sv
for name in ['none', 'causal']:
    sees = masks[name]
    for dims in [(2, 2, 2, 2, 2, 1), (3, 2, 3, 2, 1, 2), (2, 3, 3, 4, 2, 2), (3, 3, 3, 3, 3, 1), (2, 2, 3, 3, 3, 2)]:
        T, d, din, dout, H, dh = dims
        for s, sym in [(0.0, 2 * d * d + 2 * H * dh * dh), (1.0, d * d + 2 * H * dh * dh)]:
            par = draw(dims)
            P, sv = jac_rank(par, sees, s, dims)
            r = P - sym
            gap = sv[r - 1] / max(sv[r], 1e-300) if r < len(sv) else float('inf')
            print(name, dims, 's =', s, 'P =', P, 'claimed', r, 'sv[r-1] = %.2e' % sv[r - 1],
                  'sv[r] = %.2e' % (sv[r] if r < len(sv) else 0.0), 'gap = %.1e' % gap)
