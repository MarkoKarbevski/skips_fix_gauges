"""One block narrower than d (the network without a dead unit, S Proposition A.33 (ii), A.35):
is the direction of the changes of basis and of the rescalings still injective (ReLU-type MLP
blocks, rescaleDirMlp with degree k)? Injective means rank = (L+1) d^2 + s."""
import numpy as np
rng = np.random.default_rng(11)
def rank(k, d, dIn, dOut, hs):
    L = len(hs)
    E = rng.standard_normal((dIn, d)); D = rng.standard_normal((d, dOut))
    R = [rng.standard_normal((d, h)) for h in hs]; W = [rng.standard_normal((h, d)) for h in hs]
    nX = (L + 1) * d * d; n = nX + sum(hs)
    cols = []
    for j in range(n):
        v = np.zeros(n); v[j] = 1.0
        X = v[:nX].reshape(L + 1, d, d); o = nX; out = [E @ X[0]]
        for l, h in enumerate(hs):
            al = v[o:o + h]; o += h
            out += [-X[l] @ R[l] + R[l] * al[None, :], W[l] @ X[l + 1] - k * al[:, None] * W[l]]
        out.append(-X[L] @ D)
        cols.append(np.concatenate([a.ravel() for a in out]))
    s = np.linalg.svd(np.array(cols).T, compute_uv=False)
    return int((s > 1e-9 * s[0]).sum()), n
for k in (1, 2):
    for (d, dIn, dOut, hs) in [(3, 3, 3, [3, 2, 3]), (3, 3, 3, [3, 2]), (3, 3, 1, [3, 2]),
                               (3, 3, 1, [3, 2, 3]), (3, 3, 3, [2, 2, 3]), (3, 3, 3, [3, 2, 2, 3]),
                               (4, 4, 4, [4, 3, 4]), (4, 4, 4, [4, 2, 4]), (4, 4, 4, [3, 3])]:
        r, n = rank(k, d, dIn, dOut, hs)
        print('k =', k, 'd, d_in, d_out =', d, dIn, dOut, 'widths', hs, ': rank', r, 'of', n,
              'INJECTIVE' if r == n else 'NOT INJECTIVE (%d short)' % (n - r))
