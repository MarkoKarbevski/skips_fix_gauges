# Numeric check: residual networks of ReLU / ReLU^2 blocks with small writes (skips paper, Lemma A.30).
# Claim: at theta_tau (every write multiplied by tau), for small tau != 0, the Jacobian on a batch off the kinks
# has rank P - d^2 - s, s = total number of hidden units, for blocks of any widths. One token, no normalization.
# Exact Jacobian by forward mode, float64.
import numpy as np
rng = np.random.default_rng(11)
def act(kind, z, dz):
    if kind == 'relu': return np.maximum(z, 0), (z > 0)*dz
    return np.maximum(z, 0)**2, 2*np.maximum(z, 0)*dz
def jvp(kind, E, Rs, Ws, D, dE, dRs, dWs, dD, x):
    h = x @ E; dh = x @ dE
    for R, W, dR, dW in zip(Rs, Ws, dRs, dWs):
        z = h @ R; dz = dh @ R + h @ dR
        s, ds = act(kind, z, dz)
        h, dh = h + s @ W, dh + ds @ W + s @ dW
    return dh @ D + h @ dD
for kind in ['relu', 'relusq']:
    for d, qs, tau in [(2, [1, 2], 0.05), (3, [2, 4], 0.05), (3, [4, 3, 5], 0.02), (4, [5, 6], 0.05)]:
        dIn = dOut = d; L = len(qs)
        E = rng.normal(size=(dIn, d)); D = rng.normal(size=(d, dOut))
        Rs = [rng.normal(size=(d, q)) for q in qs]; Ws = [tau*rng.normal(size=(q, d)) for q in qs]
        th = [E] + Rs + Ws + [D]; P = sum(a.size for a in th)
        X = rng.normal(size=(60*P//d + 50, dIn)); J = np.zeros((len(X)*dOut, P)); c = 0
        for i, a in enumerate(th):
            for idx in np.ndindex(a.shape):
                et = [np.zeros_like(b) for b in th]; et[i][idx] = 1.0
                J[:, c] = np.concatenate([jvp(kind, E, Rs, Ws, D, et[0], et[1:1+L], et[1+L:1+2*L], et[-1], x) for x in X]); c += 1
        sv = np.linalg.svd(J, compute_uv=False); claim = P - d*d - sum(qs)
        rank = int((sv > 1e-10*sv[0]).sum())
        print(f"{kind} d={d} widths={qs} tau={tau}: P={P} rank={rank} claim={claim} sv[claim-1]/sv[0]={sv[claim-1]/sv[0]:.1e} sv[claim]/sv[0]={sv[claim]/sv[0]:.1e}")
