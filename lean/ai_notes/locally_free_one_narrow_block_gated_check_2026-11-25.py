"""One block narrower than d, gated blocks: is the direction of the changes of basis with the
rescalings of the values (and of the gates, for a gate of degree k) still injective when E and D
have rank d? Sign conventions of cobDir, rescaleDir, rescaleDirGate. Injective means
rank = (L+1) d^2 + s (s = hidden units, or twice that with the gate rescalings)."""
import numpy as np
rng = np.random.default_rng(5)
def rank(kind, k, d, dIn, dOut, hs):
    L = len(hs)
    E = rng.standard_normal((dIn, d)); D = rng.standard_normal((d, dOut))
    R = [rng.standard_normal((d, 2 * h)) for h in hs]; W = [rng.standard_normal((h, d)) for h in hs]
    nX = (L + 1) * d * d; nA = sum(hs); nB = sum(hs) if kind == 'reglu' else 0
    n = nX + nA + nB
    cols = []
    for j in range(n):
        v = np.zeros(n); v[j] = 1.0
        X = v[:nX].reshape(L + 1, d, d); o = nX; al = []; be = []
        for h in hs:
            al.append(v[o:o + h]); o += h
        for h in hs:
            if kind == 'reglu':
                be.append(v[o:o + h]); o += h
            else:
                be.append(np.zeros(h))
        out = [E @ X[0]]
        for l, h in enumerate(hs):
            dR = -X[l] @ R[l]
            dR[:, h:] += -R[l][:, h:] * al[l][None, :]
            dR[:, :h] += R[l][:, :h] * be[l][None, :]
            dW = W[l] @ X[l + 1] + al[l][:, None] * W[l] - k * be[l][:, None] * W[l]
            out += [dR, dW]
        out.append(-X[L] @ D)
        cols.append(np.concatenate([a.ravel() for a in out]))
    s = np.linalg.svd(np.array(cols).T, compute_uv=False)
    return int((s > 1e-9 * s[0]).sum()), n
for kind, k in (('gated', 0), ('reglu', 1), ('reglu', 2)):
    for (d, dIn, dOut, hs) in [(3, 3, 3, [3, 2, 3]), (3, 3, 3, [3, 1, 3]), (3, 3, 3, [3, 2]),
                               (3, 3, 1, [3, 2]), (3, 3, 3, [2, 3]), (3, 3, 3, [3, 1, 1, 3]),
                               (4, 4, 4, [4, 3, 4]), (2, 2, 2, [2, 1, 2])]:
        r, n = rank(kind, k, d, dIn, dOut, hs)
        print(kind, 'k =', k, 'd, d_in, d_out =', d, dIn, dOut, 'widths', hs, ': rank', r, 'of', n,
              'INJECTIVE' if r == n else 'NOT INJECTIVE (%d short)' % (n - r))
