# The four conditions of `UnitsGeneralPosition` (OneBlock/UnitsGeneralPosition.lean) at random
# weights: W_read (d x q, columns w_i), W_write (q x d, rows a_i), q >= d >= 2.
# 1. w_i pairwise non-collinear; 2. any at most d rows a_i independent; 3. M_S = sum_{i in S} w_i a_i
# invertible for |S| >= d; 4. (a_i M_S^{-1}) . w_i != 0 for i outside S, |S| >= d.
# Printed: the smallest absolute value met in each condition (a singular value or the number).
import itertools, numpy as np
rng = np.random.default_rng(20261124)
for d in (2, 3, 4):
    for q in range(d, d + 4):
        worst = [np.inf] * 4
        for trial in range(20):
            Wr = rng.standard_normal((d, q)); Ww = rng.standard_normal((q, d))
            for i, j in itertools.combinations(range(q), 2):
                worst[0] = min(worst[0], np.linalg.svd(np.stack([Wr[:, i], Wr[:, j]]), compute_uv=False)[-1])
            for r in range(1, d + 1):
                for S in itertools.combinations(range(q), r):
                    worst[1] = min(worst[1], np.linalg.svd(Ww[list(S)], compute_uv=False)[-1])
            for r in range(d, q + 1):
                for S in itertools.combinations(range(q), r):
                    M = sum(np.outer(Wr[:, i], Ww[i]) for i in S)
                    worst[2] = min(worst[2], np.linalg.svd(M, compute_uv=False)[-1])
                    for i in range(q):
                        if i not in S:
                            worst[3] = min(worst[3], abs((Ww[i] @ np.linalg.inv(M)) @ Wr[:, i]))
        print(f"d={d} q={q}: smallest values over 20 draws: " + ", ".join(
            f"({k+1}) {w:.2e}" if np.isfinite(w) else f"({k+1}) no case" for k, w in enumerate(worst)))
