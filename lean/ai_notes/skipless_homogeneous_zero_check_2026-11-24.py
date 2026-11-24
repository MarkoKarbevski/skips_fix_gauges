# S Theorem B.1 (iv), the skipless network with eps = 0 and a positively homogeneous block:
# the change of basis G at h_0 (E -> E G, W_read -> G^{-1} W_read) preserves the function exactly,
# for every invertible G, also at inputs with a zero row (Lean's rmsNorm 0 maps a zero row to 0).
import numpy as np
rng = np.random.default_rng(7)
def N0(h):
    out = np.zeros_like(h)
    for t in range(h.shape[0]):
        s = np.sqrt(np.mean(h[t] ** 2))
        if s > 0: out[t] = h[t] / s
    return out
def net(x, E, R, W, D, k):
    return N0(np.maximum(N0(x @ E) @ R, 0.0) ** k @ W) @ D
worst = 0.0
for k in (1, 2):
    for (T, d, din, dout, m) in ((1, 2, 3, 2, 3), (2, 3, 4, 3, 5), (3, 4, 4, 5, 2)):
        E, R, W, D = rng.normal(size=(din, d)), rng.normal(size=(d, m)), rng.normal(size=(m, d)), rng.normal(size=(d, dout))
        G = np.eye(d) + 0.4 * rng.normal(size=(d, d))
        assert abs(np.linalg.det(G)) > 1e-3
        for trial in range(200):
            x = rng.normal(size=(T, din))
            if trial % 10 == 0: x[0] = 0.0          # a zero input row
            a = net(x, E, R, W, D, k); b = net(x, E @ G, np.linalg.inv(G) @ R, W, D, k)
            worst = max(worst, np.abs(a - b).max())
print("largest difference of the outputs over 1200 inputs:", worst)
