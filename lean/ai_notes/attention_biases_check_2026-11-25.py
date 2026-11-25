# Numeric check for one attention block with biases (skips paper, Theorem B.1 (i), "2 d_model +
# 2 H d_h lower for attention"; proof, "Part (i) for attention blocks", Reduction and Step 1),
# and for the count of Lemma A.8 for attention blocks at depth 2. 25 November 2026.
#
# The network, in the frame of the Lean library (Network/Biases.lean, Network/Attention.lean):
#   h_0 = x E + b_E;  head i: q = h W_Q,i + b_Q,i, k = h W_K,i + b_K,i, v = h W_V,i + b_V,i,
#   scores q k^T / sqrt(d_h), weights their softmax over the tokens seen, output (weights v) W_O,i;
#   h_l = s h_{l-1} + sum_i (head i) + b_O^l;  y = h_L D + b_D.   s = 0 skipless, s = 1 residual.
#
# (a) the reduction of the paper for one block:
#     y_t = s (x_t E D + b_E D) + sum_i sum_s a_ts x_s C_i + gamma_0, the weights a_ts being the
#     softmax of x_t B_i x_s^T + beta_i x_s^T, with beta_i = (b_E W_Q,i + b_Q,i) W_K,i^T E^T/sqrt(d_h)
#     and gamma_0 = sum_i (b_E W_V,i + b_V,i) W_O,i D + b_O D + b_D, when every token sees a token.
# (a2) equation (16) of the paper with biases, at a token that sees itself and k other tokens:
#     y_2 = u K - v S / 2 + sum_i tanh(((u B_i + beta_i) v^T - log k) / 2) v C_i / 2 + gamma.
# (b) the directions of the symmetries are in the kernel of the Jacobian in (weights, biases),
#     and they span a space of the claimed dimension:
#     changes of basis, translations, the two changes of basis in every head (acting on the
#     biases of the queries, keys and values too), the shifts of the key biases, and the value
#     biases moved into the output bias.
# (c) the rank of the Jacobian (exact derivatives by the complex step, h = 1e-30):
#     one block: P - 2 d^2 - 2 H d_h^2 - 2 d - 2 H d_h without the skip,
#                P - d^2 - 2 H d_h^2 - 2 d - 2 H d_h with it;
#     two blocks: compared with the bounds (L + 1)(d^2 + d) + sum (2 H d_h^2 + 2 H d_h) and
#                d^2 + (L + 1) d + sum (2 H d_h^2 + 2 H d_h).
# (d) a mask in which one token sees no token: the value biases moved into the output bias are
#     then not a symmetry.
import numpy as np
rng = np.random.default_rng(11)


def weights(Z, sees):
    T = Z.shape[0]
    P = np.zeros_like(Z)
    for t in range(T):
        idx = [s for s in range(T) if sees(t, s)]
        if idx:
            z = Z[t, idx]
            e = np.exp(z - z.real.max())   # the softmax is unchanged, and no overflow
            P[t, idx] = e / e.sum()
    return P


def shapes(dims):
    T, d, din, dout, Hs, dhs = dims
    L = len(Hs)
    sh = [('E', (din, d)), ('bE', (d,))]
    for l in range(L):
        H, dh = Hs[l], dhs[l]
        sh += [(f'Q{l}', (H, d, dh)), (f'K{l}', (H, d, dh)), (f'V{l}', (H, d, dh)),
               (f'O{l}', (H, dh, d)), (f'bQ{l}', (H, dh)), (f'bK{l}', (H, dh)),
               (f'bV{l}', (H, dh)), (f'bO{l}', (d,))]
    sh += [('D', (d, dout)), ('bD', (dout,))]
    return sh


def draw(dims, zero_biases=False):
    p = {}
    for name, s in shapes(dims):
        p[name] = rng.normal(size=s)
        if zero_biases and name.startswith('b'):
            p[name] = np.zeros(s)
    return p


def zero(dims):
    return {name: np.zeros(s) for name, s in shapes(dims)}


def flat(p, dims):
    return np.concatenate([p[name].ravel() for name, _ in shapes(dims)])


def unflat(vec, dims):
    p = {}
    k = 0
    for name, s in shapes(dims):
        n = int(np.prod(s))
        p[name] = vec[k:k + n].reshape(s)
        k += n
    return p


def net(p, x, sees, s, dims):
    T, d, din, dout, Hs, dhs = dims
    h = x @ p['E'] + p['bE']
    for l in range(len(Hs)):
        out = 0
        for i in range(Hs[l]):
            q = h @ p[f'Q{l}'][i] + p[f'bQ{l}'][i]
            k = h @ p[f'K{l}'][i] + p[f'bK{l}'][i]
            v = h @ p[f'V{l}'][i] + p[f'bV{l}'][i]
            out = out + weights(q @ k.T / np.sqrt(dhs[l]), sees) @ v @ p[f'O{l}'][i]
        h = s * h + out + p[f'bO{l}']
    return h @ p['D'] + p['bD']


def jacobian(p, sees, s, dims, X):
    th = flat(p, dims).astype(complex)
    P = th.size
    J = np.zeros((len(X) * dims[0] * dims[3], P))
    hh = 1e-30
    for j in range(P):
        e = np.zeros(P, dtype=complex)
        e[j] = 1j * hh
        q = unflat(th + e, dims)
        J[:, j] = np.concatenate([net(q, x.astype(complex), sees, s, dims).ravel() for x in X]).imag / hh
    return J


def directions(p, s, dims):
    """The directions of the symmetries at p, as flat vectors, with the claimed dimension."""
    T, d, din, dout, Hs, dhs = dims
    L = len(Hs)
    out = []
    E_ = np.eye
    # changes of basis: X_0, ..., X_L (skipless), one X (residual)
    def cob(Xs):
        e = zero(dims)
        e['E'] = p['E'] @ Xs[0]
        e['bE'] = p['bE'] @ Xs[0]
        for l in range(L):
            for nm in 'QKV':
                e[f'{nm}{l}'] = -np.einsum('ab,ibk->iak', Xs[l], p[f'{nm}{l}'])
            e[f'O{l}'] = p[f'O{l}'] @ Xs[l + 1]
            e[f'bO{l}'] = p[f'bO{l}'] @ Xs[l + 1]
        e['D'] = -Xs[L] @ p['D']
        return e
    for a in range(d):
        for b in range(d):
            M = np.zeros((d, d)); M[a, b] = 1
            if s == 0:
                for l in range(L + 1):
                    Xs = [np.zeros((d, d)) for _ in range(L + 1)]; Xs[l] = M
                    out.append(cob(Xs))
            else:
                out.append(cob([M] * (L + 1)))
    # translations: g_k at h_k (skipless: h_k only; residual: h_k, ..., h_L)
    for k in range(L + 1):
        for a in range(d):
            g = np.zeros(d); g[a] = 1
            e = zero(dims)
            if k == 0:
                e['bE'] = g
            else:
                e[f'bO{k - 1}'] = g
            readers = [k] if s == 0 else list(range(k, L + 1))   # block l reads h_l (l < L)
            for l in readers:
                if l < L:
                    for nm in 'QKV':
                        e[f'b{nm}{l}'] = -np.einsum('a,iak->ik', g, p[f'{nm}{l}'])
                else:
                    e['bD'] = -g @ p['D']
            out.append(e)
    for l in range(L):
        H, dh = Hs[l], dhs[l]
        for i in range(H):
            for a in range(dh):
                for b in range(dh):
                    G = np.zeros((dh, dh)); G[a, b] = 1
                    # queries and keys: W_Q G, -W_K G^T; b_Q G, -b_K G^T
                    e = zero(dims)
                    e[f'Q{l}'][i] = p[f'Q{l}'][i] @ G
                    e[f'K{l}'][i] = -p[f'K{l}'][i] @ G.T
                    e[f'bQ{l}'][i] = p[f'bQ{l}'][i] @ G
                    e[f'bK{l}'][i] = -p[f'bK{l}'][i] @ G.T
                    out.append(e)
                    # values and outputs: W_V G, -G W_O; b_V G
                    e = zero(dims)
                    e[f'V{l}'][i] = p[f'V{l}'][i] @ G
                    e[f'O{l}'][i] = -G @ p[f'O{l}'][i]
                    e[f'bV{l}'][i] = p[f'bV{l}'][i] @ G
                    out.append(e)
            for a in range(dh):
                # the shift of the key bias
                e = zero(dims)
                e[f'bK{l}'][i, a] = 1
                out.append(e)
                # the value bias moved into the output bias: b_V + nu, b_O - nu W_O
                e = zero(dims)
                e[f'bV{l}'][i, a] = 1
                e[f'bO{l}'] = -p[f'O{l}'][i][a]
                out.append(e)
    return np.array([flat(e, dims) for e in out])


def claimed(s, dims):
    T, d, din, dout, Hs, dhs = dims
    L = len(Hs)
    inside = sum(2 * H * dh * dh + 2 * H * dh for H, dh in zip(Hs, dhs))
    return ((L + 1) * (d * d + d) if s == 0 else d * d + (L + 1) * d) + inside


masks = {'none': lambda t, s: True, 'causal': lambda t, s: s <= t,
         'odd': lambda t, s: (t == s) or (s == 0) or (t == 2 and s == 3)}

# (a)
worst = 0.0
worst2 = 0.0
for name, sees in masks.items():
    for dims in [(4, 3, 4, 5, [2], [2]), (5, 2, 2, 3, [3], [1]), (4, 3, 3, 3, [1], [3])]:
        T, d, din, dout, Hs, dhs = dims
        H, dh = Hs[0], dhs[0]
        for s in [0.0, 1.0]:
            p = draw(dims)
            x = rng.normal(size=(T, din))
            E, D, bE = p['E'], p['D'], p['bE']
            y = s * (x @ E @ D + bE @ D) + p['bO0'] @ D + p['bD']
            for i in range(H):
                Q, K, V, O = p['Q0'][i], p['K0'][i], p['V0'][i], p['O0'][i]
                B = E @ Q @ K.T @ E.T / np.sqrt(dh)
                beta = (bE @ Q + p['bQ0'][i]) @ K.T @ E.T / np.sqrt(dh)
                C = E @ V @ O @ D
                y = y + weights(x @ B @ x.T + np.outer(np.ones(T), x @ beta), sees) @ x @ C \
                    + (bE @ V + p['bV0'][i]) @ O @ D
            worst = max(worst, np.abs(net(p, x, sees, s, dims) - y).max())
            # (a2) equation (16) with biases: token t2 sees itself and k other tokens; the input
            # has the row u at t2 and u - v elsewhere
            for t2 in range(T):
                others = [t for t in range(T) if t != t2 and sees(t2, t)]
                if not sees(t2, t2) or not others:
                    continue
                k = len(others)
                u = rng.normal(size=din); v = rng.normal(size=din)
                xin = np.array([u if t == t2 else u - v for t in range(T)])
                Cs = [E @ p['V0'][i] @ p['O0'][i] @ D for i in range(H)]
                Bs = [E @ p['Q0'][i] @ p['K0'][i].T @ E.T / np.sqrt(dh) for i in range(H)]
                betas = [(bE @ p['Q0'][i] + p['bQ0'][i]) @ p['K0'][i].T @ E.T / np.sqrt(dh)
                         for i in range(H)]
                gamma = s * bE @ D + sum((bE @ p['V0'][i] + p['bV0'][i]) @ p['O0'][i] @ D
                                         for i in range(H)) + p['bO0'] @ D + p['bD']
                y2 = u @ (s * E @ D + sum(Cs)) - 0.5 * v @ sum(Cs) + gamma + sum(
                    0.5 * np.tanh(0.5 * (u @ Bs[i] @ v + betas[i] @ v - np.log(k))) * (v @ Cs[i])
                    for i in range(H))
                worst2 = max(worst2, np.abs(net(p, xin, sees, s, dims)[t2] - y2).max())
print('(a) the reduction with biases: largest error %.1e' % worst)
print('(a2) equation (16) with biases, at the second token: largest error %.1e' % worst2)
import sys
if len(sys.argv) > 1 and sys.argv[1] == 'a':
    sys.exit(0)

# (b), (c)
print('(b), (c): P, the claimed dimension of the symmetries, the rank of their directions, the')
print('          largest |J direction|, the rank of J and the two singular values at the claim')
cases = [(2, 2, 2, 2, [2], [1]), (3, 2, 3, 2, [1], [2]), (2, 3, 3, 4, [2], [2]),
         (3, 3, 3, 3, [3], [1]), (2, 2, 3, 3, [3], [2]),
         (3, 2, 2, 2, [2, 2], [1, 1]), (2, 2, 3, 2, [1, 2], [2, 1]), (3, 3, 3, 3, [2, 3], [2, 1])]
for name in ['none', 'causal']:
    sees = masks[name]
    for dims in cases:
        T, d, din, dout, Hs, dhs = dims
        for zb in [False, True]:
            for s in [0.0, 1.0]:
                p = draw(dims, zero_biases=zb)
                P = flat(p, dims).size
                nb = max(8, (3 * P) // (T * dout) + 2)
                X = [rng.normal(size=(T, din)) for _ in range(nb)]
                J = jacobian(p, sees, s, dims, X)
                Dir = directions(p, s, dims)
                c = claimed(s, dims)
                rdir = np.linalg.matrix_rank(Dir, tol=1e-9)
                leak = np.abs(J @ Dir.T).max()
                sv = np.linalg.svd(J, compute_uv=False)
                r = P - c
                rank = int((sv > 1e-9 * sv[0]).sum())
                print(name, dims, 'biases 0' if zb else 'biases random', 's = %d' % s, 'P = %d' % P,
                      'claimed %d' % c, 'rank of directions %d' % rdir, 'leak %.1e' % leak,
                      'rank J = %d (P - claimed = %d)' % (rank, r),
                      'sv %.1e | %.1e' % (sv[r - 1], sv[r] if r < len(sv) else 0.0),
                      'EQUAL' if rank == r else 'LOWER' if rank < r else 'HIGHER')

# (d) token 0 sees no token
blind = lambda t, s: (t != 0) and (s <= t)
dims = (3, 2, 2, 2, [2], [1])
for s in [0.0, 1.0]:
    p = draw(dims)
    P = flat(p, dims).size
    X = [rng.normal(size=(dims[0], dims[2])) for _ in range(3 * P)]
    J = jacobian(p, blind, s, dims, X)
    Dir = directions(p, s, dims)
    leak = np.abs(J @ Dir.T).max(axis=0)
    sv = np.linalg.svd(J, compute_uv=False)
    rank = int((sv > 1e-9 * sv[0]).sum())
    print('(d) a token that sees no token, s = %d: P = %d, claimed %d, rank J = %d (P - claimed = %d);'
          % (s, P, claimed(s, dims), rank, P - claimed(s, dims)),
          'directions that are not flat: %d of %d' % (int((leak > 1e-8).sum()), len(leak)))
