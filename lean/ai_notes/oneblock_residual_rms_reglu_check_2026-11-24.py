# Numeric check: one residual ReGLU block under pre-RMSNorm (eps > 0), one token.
# Claim (skips paper, Theorem B.1 (ii)): rank of the Jacobian = P - d(d-1)/2 - s, s = 2 * (number of hidden units)
# (one rescaling of the gate and one of the value for each unit), for a block of any width.
# Also the skipless network with the same shapes: rank <= P - d(d-1) - s (Theorem A.17 (ii)).
# Exact Jacobian by forward mode, float64.
import numpy as np
rng = np.random.default_rng(5)
def N(h, eps): return h/np.sqrt(h @ h/len(h) + eps)
def dN(h, k, eps):
    rho = np.sqrt(h @ h/len(h) + eps); return k/rho - h*(h @ k)/(len(h)*rho**3)
def jvp(skip, th, et, x, eps):
    E, Rg, Rv, W, D = th; dE, dRg, dRv, dW, dD = et
    h0 = x @ E; dh0 = x @ dE
    n = N(h0, eps); dn = dN(h0, dh0, eps)
    z = n @ Rg; dz = dn @ Rg + n @ dRg
    v = n @ Rv; dv = dn @ Rv + n @ dRv
    s = np.maximum(z, 0)*v; ds = (z > 0)*dz*v + np.maximum(z, 0)*dv
    h1 = skip*h0 + s @ W; dh1 = skip*dh0 + ds @ W + s @ dW
    return dN(h1, dh1, eps) @ D + N(h1, eps) @ dD
for d, q in [(2, 1), (2, 3), (3, 2), (3, 4), (4, 6)]:
    eps = 0.7; dIn = dOut = d
    th = [rng.normal(size=s) for s in [(dIn, d), (d, q), (d, q), (q, d), (d, dOut)]]
    P = sum(a.size for a in th); X = rng.normal(size=(400, dIn))
    for skip in [1.0, 0.0]:
        J = np.zeros((400*dOut, P)); c = 0
        for i, a in enumerate(th):
            for idx in np.ndindex(a.shape):
                et = [np.zeros_like(b) for b in th]; et[i][idx] = 1.0
                J[:, c] = np.concatenate([jvp(skip, th, et, x, eps) for x in X]); c += 1
        sv = np.linalg.svd(J, compute_uv=False); rank = int((sv > 1e-9*sv[0]).sum())
        claim = P - d*(d - 1)//2 - 2*q if skip else P - d*(d - 1) - 2*q
        rel = '=' if skip else '<='
        gap = sv[rank-1]/max(sv[rank], 1e-300) if rank < P else float('inf')
        print(f"skip={int(skip)} d={d} q={q}: P={P} rank={rank} claim {rel} {claim} gap={gap:.1e}")
