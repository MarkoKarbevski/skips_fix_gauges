# S Theorem B.1 (iv), the residual network with eps = 0 and one ReLU or ReLU^2 block:
# rank of the Jacobian in the weights on a batch, by complex-step derivatives (exact to rounding),
# against P - (d(d-1)/2 + 1) - s, s = number of hidden units. Inputs are random: off the kinks.
import numpy as np
rng = np.random.default_rng(11)
def N0(h):
    return h * np.sqrt(h.shape[1]) / np.sqrt(np.sum(h * h, axis=1, keepdims=True))
def act(z, k):
    return np.where(z.real > 0, z, 0) ** k
def net(x, E, R, W, D, k):
    h0 = x @ E
    h1 = h0 + act(N0(h0) @ R, k) @ W
    return N0(h1) @ D
def rank_on_batch(d, m, din, dout, T, k, nb):
    shapes = [(din, d), (d, m), (m, d), (d, dout)]
    th = [rng.normal(size=s) for s in shapes]
    P = sum(a * b for a, b in shapes)
    rows = []
    for _ in range(nb):
        x = rng.normal(size=(T, din))
        cols = []
        for j, s in enumerate(shapes):
            for a in range(s[0]):
                for b in range(s[1]):
                    tc = [t.astype(complex) for t in th]
                    tc[j][a, b] += 1e-30j
                    cols.append(net(x, *tc, k).imag.ravel() / 1e-30)
        rows.append(np.array(cols).T)
    J = np.vstack(rows)
    sv = np.linalg.svd(J, compute_uv=False)
    r = int(np.sum(sv > 1e-9 * sv[0]))
    gap = sv[r - 1] / sv[r] if r < len(sv) and sv[r] > 0 else float('inf')
    return P, r, gap
bad = 0
for k in (1, 2):
    for (d, m, T) in ((2, 1, 1), (2, 2, 1), (2, 3, 2), (3, 1, 1), (3, 2, 2), (3, 3, 1), (3, 4, 2), (4, 3, 1)):
        din, dout = d + 1, d
        P, r, gap = rank_on_batch(d, m, din, dout, T, k, nb=6 * (din * d + 2 * d * m + d * dout))
        want = P - (d * (d - 1) // 2 + 1) - m
        bad += (r != want)
        print(f"k={k} d={d} hidden={m} T={T}: P={P} rank={r} expected={want} gap={gap:.1e}")
print("cases that differ:", bad)
