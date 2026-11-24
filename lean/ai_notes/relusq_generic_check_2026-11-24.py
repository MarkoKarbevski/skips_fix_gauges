# Generic condition of the proof of A Theorem C.2 (iii): for disjoint S, U with |U| < 2d,
# the vectors tau_o (o in d) and phi(w_i, b_i) (i in U) are linearly independent.
import itertools, numpy as np
rng = np.random.default_rng(7)
def phi(w, b):
    return np.concatenate([np.outer(w, w).ravel(), 2*b*w])
def check(d, m):
    Wr = rng.standard_normal((d, m)); b = rng.standard_normal(m)
    Ww = rng.standard_normal((m, d)); M = rng.standard_normal((d, d))
    worst = np.inf; n = 0
    for S in itertools.chain.from_iterable(itertools.combinations(range(m), k) for k in range(m+1)):
        rest = [i for i in range(m) if i not in S]
        for k in range(0, min(len(rest), 2*d-1)+1):
            for U in itertools.combinations(rest, k):
                vecs = []
                for o in range(d):
                    t = np.concatenate([np.zeros(d*d), M[:, o]])
                    for i in S: t = t + Ww[i, o]*phi(Wr[:, i], b[i])
                    vecs.append(t)
                for i in U: vecs.append(phi(Wr[:, i], b[i]))
                A = np.array(vecs)
                s = np.linalg.svd(A, compute_uv=False)
                worst = min(worst, s[-1]/s[0]); n += 1
                assert np.linalg.matrix_rank(A, tol=1e-9) == len(vecs), (S, U)
    return n, worst
for d, m in [(1, 3), (2, 4), (2, 5), (3, 5), (3, 6)]:
    n, worst = check(d, m)
    print(f"d={d} m={m}: {n} pairs (S,U), all independent; smallest ratio of singular values {worst:.2e}")
