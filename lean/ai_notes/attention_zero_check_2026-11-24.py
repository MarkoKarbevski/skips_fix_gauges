# Numeric check of the derivative at X = 0 of a network of attention blocks along a b (absorb paper, proof of Theorem 4.2):
# claim: d/dtau eval(tau * a b) at 0 = a * (xi * b E prod_l (s I + xi lam V_l) D), for U a = lam a, U = softmax(0) with the mask,
# s = 1 (skips) or 0 (no skips), xi = 1 (no normalization) or 1/sqrt(eps) (pre-RMSNorm).
import numpy as np
rng = np.random.default_rng(7)
def weights(Z, mask):
    W = np.where(mask, np.exp(Z), 0.0); return W/W.sum(axis=1, keepdims=True)
def norm(h, eps): return h/np.sqrt((h*h).mean(axis=1, keepdims=True) + eps)
def net(X, E, blocks, D, mask, s, eps):
    chi = (lambda h: h) if eps is None else (lambda h: norm(h, eps))
    h = X @ E
    for heads in blocks:
        n = chi(h); out = 0
        for WQ, WK, WV, WO in heads:
            dh = WQ.shape[1]
            out = out + weights((n @ WQ) @ (n @ WK).T/np.sqrt(dh), mask) @ (n @ WV) @ WO
        h = s*h + out
    return chi(h) @ D
T, d, dIn, dOut, L = 4, 3, 3, 2, 3
for maskname in ['none', 'causal']:
    mask = np.ones((T, T), bool) if maskname == 'none' else np.tril(np.ones((T, T), bool))
    U = weights(np.zeros((T, T)), mask)
    evals, evecs = np.linalg.eig(U)
    for eps in [None, 0.6]:
        xi = 1.0 if eps is None else 1/np.sqrt(eps)
        E = rng.normal(size=(dIn, d)); D = rng.normal(size=(d, dOut))
        blocks = [[tuple(rng.normal(size=sh) for sh in [(d, 2), (d, 2), (d, 2), (2, d)]) for _ in range(2)] for _ in range(L)]
        V = [sum(WV @ WO for _, _, WV, WO in heads) for heads in blocks]
        b = rng.normal(size=dIn)
        for s in [1.0, 0.0]:
            worst = 0.0
            for k in range(T):
                lam = evals[k].real; a = evecs[:, k].real
                M = np.eye(d)
                for Vl in V: M = M @ (s*np.eye(d) + xi*lam*Vl)
                claim = np.outer(a, xi*(b @ E @ M @ D))
                tau = 1e-5
                fd = (net(tau*np.outer(a, b), E, blocks, D, mask, s, eps) - net(-tau*np.outer(a, b), E, blocks, D, mask, s, eps))/(2*tau)
                worst = max(worst, np.abs(fd - claim).max()/max(1e-12, np.abs(claim).max() if np.abs(claim).max() > 1e-9 else 1.0))
            print(f"mask={maskname} eps={eps} s={int(s)}: eigenvalues {np.round(np.sort(evals.real), 4)}; largest relative difference {worst:.1e}")
