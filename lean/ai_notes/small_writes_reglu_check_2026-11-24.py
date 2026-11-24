# Numeric check: residual networks of ReGLU blocks with small writes (skips paper, Lemma A.30).
# Claim: at theta_tau (every write multiplied by tau), for small tau != 0, the Jacobian on a batch off the kinks
# has rank P - d^2 - s, s = 2 * (total number of hidden units), for blocks of any widths. One token, no normalization.
# Exact Jacobian by forward mode, float64.
import numpy as np
rng = np.random.default_rng(13)
def jvp(E, Gs, Vs, Ws, D, dE, dGs, dVs, dWs, dD, x):
    h = x @ E; dh = x @ dE
    for G, V, W, dG, dV, dW in zip(Gs, Vs, Ws, dGs, dVs, dWs):
        z = h @ G; dz = dh @ G + h @ dG
        v = h @ V; dv = dh @ V + h @ dV
        s = np.maximum(z, 0)*v; ds = (z > 0)*dz*v + np.maximum(z, 0)*dv
        h, dh = h + s @ W, dh + ds @ W + s @ dW
    return dh @ D + h @ dD
for d, qs, tau in [(2, [1, 2], 0.05), (3, [2, 4], 0.05), (3, [4, 3, 5], 0.02), (4, [5, 6], 0.05)]:
    dIn = dOut = d; L = len(qs)
    E = rng.normal(size=(dIn, d)); D = rng.normal(size=(d, dOut))
    Gs = [rng.normal(size=(d, q)) for q in qs]; Vs = [rng.normal(size=(d, q)) for q in qs]
    Ws = [tau*rng.normal(size=(q, d)) for q in qs]
    th = [E] + Gs + Vs + Ws + [D]; P = sum(a.size for a in th)
    X = rng.normal(size=(60*P//d + 50, dIn)); J = np.zeros((len(X)*dOut, P)); c = 0
    for i, a in enumerate(th):
        for idx in np.ndindex(a.shape):
            et = [np.zeros_like(b) for b in th]; et[i][idx] = 1.0
            J[:, c] = np.concatenate([jvp(E, Gs, Vs, Ws, D, et[0], et[1:1+L], et[1+L:1+2*L], et[1+2*L:1+3*L], et[-1], x) for x in X]); c += 1
    sv = np.linalg.svd(J, compute_uv=False); claim = P - d*d - 2*sum(qs)
    rank = int((sv > 1e-10*sv[0]).sum())
    print(f"reglu d={d} widths={qs} tau={tau}: P={P} rank={rank} claim={claim} sv[claim-1]/sv[0]={sv[claim-1]/sv[0]:.1e} sv[claim]/sv[0]={sv[claim]/sv[0]:.1e}")
