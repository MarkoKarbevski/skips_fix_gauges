"""Check for `Symmetry/BiasesSymmetries.lean`: the three invariances of networks with biases,
with the Lean definitions written out (`hiddenB`, `evalB`, `Biases.cob`, `Biases.translate`,
`Biases.translateAt`); tanh blocks, no normalization, two tokens, float64.
 (1) residual network: translation of h_k, ..., h_L by g (Lemma A.8);
 (2) skipless network: translation of the one hidden state h_k;
 (3) changes of basis G_0, ..., G_L with stream matrices M (M -> G_{l}^{-1} M G_{l+1}).
"""
import numpy as np
rng = np.random.default_rng(3)
T, din, d, dout, L = 2, 3, 4, 2, 3
widths = [5, 3, 4]
E = rng.normal(size=(din, d)); D = rng.normal(size=(d, dout))
R = [rng.normal(size=(d, m)) for m in widths]; W = [rng.normal(size=(m, d)) for m in widths]
bE = rng.normal(size=d); bD = rng.normal(size=dout)
bR = [rng.normal(size=m) for m in widths]; bW = [rng.normal(size=d) for _ in widths]

def hiddenB(M, E, R, W, D, bE, bR, bW, bD, x):
    hs = [x @ E + bE]
    for l in range(L):
        h = hs[-1]
        hs.append(h @ M[l] + (np.tanh(h @ R[l] + bR[l]) @ W[l] + bW[l]))
    return hs
def evalB(M, E, R, W, D, bE, bR, bW, bD, x):
    return hiddenB(M, E, R, W, D, bE, bR, bW, bD, x)[-1] @ D + bD

x = rng.normal(size=(T, din)); g = rng.normal(size=d)
I = [np.eye(d)] * L; Z = [np.zeros((d, d))] * L
y1 = evalB(I, E, R, W, D, bE, bR, bW, bD, x); y0 = evalB(Z, E, R, W, D, bE, bR, bW, bD, x)
err1 = err2 = errh1 = errh2 = 0.0
for k in range(L + 1):
    # translate (residual): hidden index k; block l reads hidden l (castSucc) and writes hidden l+1 (succ)
    bE2 = bE + g if k == 0 else bE
    bR2 = [bR[l] - g @ R[l] if k <= l else bR[l] for l in range(L)]
    bW2 = [bW[l] + g if l + 1 == k else bW[l] for l in range(L)]
    bD2 = bD - g @ D
    err1 = max(err1, np.abs(evalB(I, E, R, W, D, bE2, bR2, bW2, bD2, x) - y1).max())
    h = hiddenB(I, E, R, W, D, bE, bR, bW, bD, x); h2 = hiddenB(I, E, R, W, D, bE2, bR2, bW2, bD2, x)
    errh1 = max(errh1, max(np.abs(h2[m] - h[m] - (g if k <= m else 0)).max() for m in range(L + 1)))
    # translateAt (skipless)
    bR3 = [bR[l] - g @ R[l] if l == k else bR[l] for l in range(L)]
    bD3 = bD - g @ D if k == L else bD
    err2 = max(err2, np.abs(evalB(Z, E, R, W, D, bE2, bR3, bW2, bD3, x) - y0).max())
    h = hiddenB(Z, E, R, W, D, bE, bR, bW, bD, x); h3 = hiddenB(Z, E, R, W, D, bE2, bR3, bW2, bD3, x)
    errh2 = max(errh2, max(np.abs(h3[m] - h[m] - (g if m == k else 0)).max() for m in range(L + 1)))
print("(1) residual, translate:   max |y' - y| = %.2e, hidden states %.2e" % (err1, errh1))
print("(2) skipless, translateAt: max |y' - y| = %.2e, hidden states %.2e" % (err2, errh2))
# (3) cob with K = G, stream matrices M random
M = [rng.normal(size=(d, d)) for _ in range(L)]
G = [rng.normal(size=(d, d)) for _ in range(L + 1)]; Gi = [np.linalg.inv(a) for a in G]
M2 = [Gi[l] @ M[l] @ G[l + 1] for l in range(L)]
y = evalB(M, E, R, W, D, bE, bR, bW, bD, x)
y2 = evalB(M2, E @ G[0], [Gi[l] @ R[l] for l in range(L)], [W[l] @ G[l + 1] for l in range(L)],
           Gi[L] @ D, bE @ G[0], bR, [bW[l] @ G[l + 1] for l in range(L)], bD, x)
print("(3) changes of basis:      max |y' - y| = %.2e" % np.abs(y2 - y).max())
