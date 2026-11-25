"""Check of S Lemma A.18, second sentence, in infinitesimal form, for the symmetries inside blocks.

The direction of the changes of basis X_0..X_L and of the rescalings, as a linear map of
(X, alpha[, beta]), at random reads, writes and readout with E = 0 (so nothing comes from the
embedding), d_out >= d, widths >= d. Injective means rank = (L+1) d^2 + s.
Sign conventions as in the Lean definitions cobDir, rescaleDir, rescaleDirMlp, rescaleDirGate.
Also: the example that shows why the read columns of a ReGLU block must be in general position.
"""
import numpy as np
rng = np.random.default_rng(7)

def direction(kind, k, E, reads, writes, D, X, al, be):
    L = len(reads)
    out = [E @ X[0]]
    for l in range(L):
        R, W = reads[l], writes[l]
        h = W.shape[0]
        dR = -X[l] @ R
        dW = W @ X[l + 1]
        if kind == 'mlp':            # rescaleDirMlp k: read col * alpha, write row * (-k alpha)
            dR = dR + R * al[l][None, :]
            dW = dW - k * al[l][:, None] * W
        if kind in ('gated', 'reglu'):   # rescaleDir: value col * (-alpha), write row * alpha
            dR = dR.copy(); dR[:, h:] += -R[:, h:] * al[l][None, :]
            dW = dW + al[l][:, None] * W
        if kind == 'reglu':          # rescaleDirGate k: gate col * beta, write row * (-k beta)
            dR[:, :h] += R[:, :h] * be[l][None, :]
            dW = dW - k * be[l][:, None] * W
        out += [dR, dW]
    out.append(-X[L] @ D)
    return np.concatenate([o.ravel() for o in out])

def rank_of(kind, k, d, dIn, dOut, hs, reads=None):
    L = len(hs)
    E = np.zeros((dIn, d))
    if reads is None:
        reads = [rng.standard_normal((d, h if kind == 'mlp' else 2 * h)) for h in hs]
    writes = [rng.standard_normal((h, d)) for h in hs]
    D = rng.standard_normal((d, dOut))
    nX = (L + 1) * d * d
    nA = sum(hs)
    nB = sum(hs) if kind == 'reglu' else 0
    n = nX + nA + nB
    cols = []
    for j in range(n):
        v = np.zeros(n); v[j] = 1.0
        X = v[:nX].reshape(L + 1, d, d)
        al, be, o = [], [], nX
        for h in hs:
            al.append(v[o:o + h]); o += h
        for h in hs:
            be.append(v[o:o + h] if kind == 'reglu' else np.zeros(h)); o += h if kind == 'reglu' else 0
        cols.append(direction(kind, k, E, reads, writes, D, X, al, be))
    M = np.array(cols).T
    s = np.linalg.svd(M, compute_uv=False)
    return int((s > 1e-9 * s[0]).sum()), n, s[-1] / s[0]

for kind, k in [('gated', 0), ('mlp', 1), ('mlp', 2), ('reglu', 1)]:
    for (d, dIn, dOut, hs) in [(2, 1, 2, [2, 3]), (3, 1, 3, [3, 4]), (3, 2, 4, [3, 3, 5]), (4, 1, 4, [4])]:
        r, n, gap = rank_of(kind, k, d, dIn, dOut, hs)
        print(kind, 'k =', k, 'd, d_in, d_out, widths =', d, dIn, dOut, hs, ': rank', r, 'of', n,
              'smallest/largest singular value %.1e' % gap, 'INJECTIVE' if r == n else 'NOT INJECTIVE')

# ReGLU, d = 2, one block of width 2, read columns not in general position:
# gates (e1, e2), values (e2, e1). The kernel has X_0 = diag(1, -1), beta = alpha = (1, -1).
R = np.array([[1., 0., 0., 1.], [0., 1., 1., 0.]])
r, n, gap = rank_of('reglu', 1, 2, 1, 2, [2], reads=[R])
print('reglu, read columns (e1, e2 | e2, e1): rank', r, 'of', n, 'INJECTIVE' if r == n else 'NOT INJECTIVE')
# For every degree k (twenty-seventh audit): two units, both with gate column e1 and value column e2.
# The kernel has X_0 = diag(1, -k), beta = (1, 1), alpha = (k, k).
R2 = np.array([[1., 1., 0., 0.], [0., 0., 1., 1.]])
for k in (1, 2, 3):
    r, n, gap = rank_of('reglu', k, 2, 1, 2, [2], reads=[R2])
    print('reglu, k =', k, ', read columns (e1, e1 | e2, e2): rank', r, 'of', n,
          'INJECTIVE' if r == n else 'NOT INJECTIVE')
    r, n, gap = rank_of('reglu', k, 2, 1, 2, [2], reads=[R])
    print('reglu, k =', k, ', read columns (e1, e2 | e2, e1): rank', r, 'of', n,
          'INJECTIVE' if r == n else 'NOT INJECTIVE')
