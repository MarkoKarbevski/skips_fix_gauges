# Numeric check of the statements on networks of mixed blocks (skips paper, Appendix A.1 and
# Theorem A.5 (i), (ii)), without normalization. 25 November 2026.
#   mixed network: h_0 = x E, h_l = h_{l-1} U_l V_l + tanh(h_{l-1} R_l) W_l, y = h_L D;
#   T_{G,K}: E G_0, G_{l-1}^{-1} R_l, W_l G_l, G_L^{-1} D, G_{l-1}^{-1} U_l K_l, K_l^{-1} V_l G_l;
#   Lambda_l = A_{l+1} ... A_L (A_l = U_l V_l), Lambda_L = I;
#   Phi(theta) = (E Lambda_0, Lambda_{l-1}^{-1} R_l, W_l Lambda_l, D), a residual network.
# (1) T_{G,K} preserves the function; (U K, K^{-1} V) preserves it.
# (2) T with G = Lambda, K_l = U_l^{-1} Lambda_{l-1} sets U, V to I and the rest to Phi(theta);
#     the mixed network at theta equals the residual network at Phi(theta).
# (3) Phi(T_{G,K} theta) = Phi(theta) when G_L = I; from Phi(theta~) = Phi(theta) the paper's
#     G_l = Lambda_l Lambda~_l^{-1}, K_l = U_l^{-1} G_{l-1} U~_l give theta~ = T_{G,K}(theta).
# (4) the rank of the Jacobian of the mixed network at theta equals that of the residual network
#     at Phi(theta) (complex step, h = 1e-30), and both are P - d^2 for tanh blocks.
import numpy as np
rng = np.random.default_rng(5)
inv = np.linalg.inv

def draw(L, d, din, dout, wid):
    return dict(E=rng.normal(size=(din, d)), D=rng.normal(size=(d, dout)),
                R=[rng.normal(size=(d, wid)) for _ in range(L)],
                W=[rng.normal(size=(wid, d)) for _ in range(L)],
                U=[rng.normal(size=(d, d)) for _ in range(L)],
                V=[rng.normal(size=(d, d)) for _ in range(L)])

def mixed(p, x):
    h = x @ p['E']
    for U, V, R, W in zip(p['U'], p['V'], p['R'], p['W']):
        h = h @ U @ V + np.tanh(h @ R) @ W
    return h @ p['D']

def residual(q, x):
    h = x @ q['E']
    for R, W in zip(q['R'], q['W']):
        h = h + np.tanh(h @ R) @ W
    return h @ q['D']

def T(p, G, K):
    L = len(p['R'])
    return dict(E=p['E'] @ G[0], D=inv(G[L]) @ p['D'],
                R=[inv(G[l]) @ p['R'][l] for l in range(L)],
                W=[p['W'][l] @ G[l + 1] for l in range(L)],
                U=[inv(G[l]) @ p['U'][l] @ K[l] for l in range(L)],
                V=[inv(K[l]) @ p['V'][l] @ G[l + 1] for l in range(L)])

def Lam(p):
    L = len(p['R']); d = p['E'].shape[1]
    lam = [None] * (L + 1); lam[L] = np.eye(d)
    for l in range(L - 1, -1, -1):
        lam[l] = p['U'][l] @ p['V'][l] @ lam[l + 1]
    return lam

def Phi(p):
    L = len(p['R']); lam = Lam(p)
    return dict(E=p['E'] @ lam[0], D=p['D'], R=[inv(lam[l]) @ p['R'][l] for l in range(L)],
                W=[p['W'][l] @ lam[l + 1] for l in range(L)])

def dist(a, b, keys):
    return max(np.abs(np.asarray(u) - np.asarray(v)).max()
               for k in keys for u, v in (zip(a[k], b[k]) if isinstance(a[k], list) else [(a[k], b[k])]))

e1 = e2 = e3 = e3b = 0.0
for (L, d, din, dout, wid) in [(1, 2, 2, 2, 3), (2, 3, 3, 4, 2), (3, 2, 3, 2, 4), (3, 3, 4, 3, 3)]:
    p = draw(L, d, din, dout, wid)
    x = rng.normal(size=(5, din))
    G = [rng.normal(size=(d, d)) for _ in range(L + 1)]; K = [rng.normal(size=(d, d)) for _ in range(L)]
    e1 = max(e1, np.abs(mixed(T(p, G, K), x) - mixed(p, x)).max())
    I = [np.eye(d)] * (L + 1)
    e1 = max(e1, np.abs(mixed(T(p, I, K), x) - mixed(p, x)).max())
    lam = Lam(p)
    q = T(p, lam, [inv(p['U'][l]) @ lam[l] for l in range(L)])
    ph = Phi(p)
    e2 = max(e2, dist(q, ph, ['E', 'D', 'R', 'W']),
             max(np.abs(M - np.eye(d)).max() for M in q['U'] + q['V']),
             np.abs(mixed(p, x) - residual(ph, x)).max())
    G[L] = np.eye(d)
    pt = T(p, G, K)
    e3 = max(e3, dist(Phi(pt), ph, ['E', 'D', 'R', 'W']))
    lt = Lam(pt)
    G2 = [lam[l] @ inv(lt[l]) for l in range(L + 1)]
    K2 = [inv(p['U'][l]) @ G2[l] @ pt['U'][l] for l in range(L)]
    e3b = max(e3b, dist(T(p, G2, K2), pt, ['E', 'D', 'R', 'W', 'U', 'V']), np.abs(G2[L] - np.eye(d)).max())
print('(1) T_{G,K} preserves the function: %.1e' % e1)
print('(2) the gauge fix gives U = V = I and Phi(theta); mixed(theta) = residual(Phi(theta)): %.1e' % e2)
print('(3) Phi(T_{G,K} theta) = Phi(theta) for G_L = I: %.1e; theta~ = T_{G,K}(theta) with the paper\'s G, K: %.1e' % (e3, e3b))

# (4)
keysM = ['E', 'D', 'R', 'W', 'U', 'V']; keysR = ['E', 'D', 'R', 'W']
def flat(p, keys): return np.concatenate([np.asarray(m).ravel() for k in keys for m in (p[k] if isinstance(p[k], list) else [p[k]])])
def unflat(v, p, keys):
    out = {}; i = 0
    for k in keys:
        if isinstance(p[k], list):
            out[k] = []
            for m in p[k]:
                out[k].append(v[i:i + m.size].reshape(m.shape)); i += m.size
        else:
            out[k] = v[i:i + p[k].size].reshape(p[k].shape); i += p[k].size
    return out
def jac(f, p, keys, X):
    th = flat(p, keys).astype(complex); P = th.size; cols = []
    for j in range(P):
        e = np.zeros(P, dtype=complex); e[j] = 1e-30j
        cols.append(np.concatenate([f(unflat(th + e, p, keys), x.astype(complex)).ravel() for x in X]).imag / 1e-30)
    return np.array(cols).T
for (L, d, din, dout, wid) in [(1, 2, 2, 2, 3), (2, 2, 3, 2, 2), (2, 3, 3, 3, 3)]:
    p = draw(L, d, din, dout, wid); ph = Phi(p)
    PM = flat(p, keysM).size; PR = flat(ph, keysR).size
    X = [rng.normal(size=(2, din)) for _ in range(3 * PM // (2 * dout) + 3)]
    sm = np.linalg.svd(jac(mixed, p, keysM, X), compute_uv=False)
    sr = np.linalg.svd(jac(residual, ph, keysR, X), compute_uv=False)
    rm = int((sm > 1e-9 * sm[0]).sum()); rr = int((sr > 1e-9 * sr[0]).sum())
    print('(4)', (L, d, din, dout, wid), 'P of the residual network %d, of the mixed network %d (= P + 2 L d^2);' % (PR, PM),
          'rank mixed %d, rank residual %d, P - d^2 = %d' % (rm, rr, PR - d * d),
          'sv at the rank %.1e | %.1e' % (sm[rm - 1], sm[rm] if rm < len(sm) else 0.0))
