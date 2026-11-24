# Numeric check: one residual ReLU / ReLU^2 block under pre-RMSNorm (eps > 0), one token.
# Claim (skips paper, Theorem B.1 (ii)): rank of the Jacobian = P - d(d-1)/2 - s, s = number of hidden units,
# for a block of any width. Exact Jacobian by forward mode, float64.
import numpy as np
rng = np.random.default_rng(3)
def N(h, eps): return h/np.sqrt(h @ h/len(h) + eps)
def dN(h, k, eps):
    rho = np.sqrt(h @ h/len(h) + eps); return k/rho - h*(h @ k)/(len(h)*rho**3)
def jvp(kind, th, et, x, eps):
    E, R, W, D = th; dE, dR, dW, dD = et
    h0 = x @ E; dh0 = x @ dE
    n = N(h0, eps); dn = dN(h0, dh0, eps)
    z = n @ R; dz = dn @ R + n @ dR
    if kind == 'relu': s = np.maximum(z, 0); ds = (z > 0)*dz
    else: s = np.maximum(z, 0)**2; ds = 2*np.maximum(z, 0)*dz
    h1 = h0 + s @ W; dh1 = dh0 + ds @ W + s @ dW
    return dN(h1, dh1, eps) @ D + N(h1, eps) @ dD
for kind in ['relu', 'relusq']:
    for d, q in [(2, 1), (3, 2), (3, 4), (4, 6)]:
        eps = 0.7; dIn = dOut = d
        th = [rng.normal(size=s) for s in [(dIn, d), (d, q), (q, d), (d, dOut)]]
        P = sum(a.size for a in th); cols = []
        for i, a in enumerate(th):
            for idx in np.ndindex(a.shape):
                et = [np.zeros_like(b) for b in th]; et[i][idx] = 1.0
                cols.append(np.concatenate([jvp(kind, th, et, x, eps) for x in X])) if False else None
        X = rng.normal(size=(300, dIn)); J = np.zeros((300*dOut, P)); c = 0
        for i, a in enumerate(th):
            for idx in np.ndindex(a.shape):
                et = [np.zeros_like(b) for b in th]; et[i][idx] = 1.0
                J[:, c] = np.concatenate([jvp(kind, th, et, x, eps) for x in X]); c += 1
        sv = np.linalg.svd(J, compute_uv=False); rank = int((sv > 1e-9*sv[0]).sum())
        claim = P - d*(d - 1)//2 - q
        print(f"{kind} d={d} q={q}: P={P} rank={rank} claim={claim} gap={sv[rank-1]/max(sv[rank], 1e-300) if rank < P else float('inf'):.1e}")
