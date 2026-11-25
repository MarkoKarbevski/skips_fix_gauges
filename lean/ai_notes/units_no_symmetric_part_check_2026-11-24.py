# Step 4 of the proof of S Theorem B.1 (iii), eps > 0, for tanh and GELU units (also fewer units than
# coordinates).  Units sigma(x.c_i) a_i, c_i in R^n, a_i in R^k.  Equation (17), row by row:
#   sum_i [ sigma(x.c_i) psi_a_i + sigma'(x.c_i) (x.psi_c_i) a_i ] = (x X x^T) sum_i sigma'(x.c_i)(x.c_i) a_i
# for x in an open set (here: 80 points of the open ball |x|^2 < n), X symmetric.
# Claim (`UnitsNoSymmetricPart`): X = 0.  With X = 0 Lemma B.3 gives psi = 0 too, so the linear
# system in (X, psi_c, psi_a) has only the zero solution: its smallest singular value is far from 0.
import itertools, mpmath as mp
mp.mp.dps = 60
def gelu(z):  return z * mp.ncdf(z)
def dgelu(z): return mp.ncdf(z) + z * mp.npdf(z)
def dtanh(z): return 1 - mp.tanh(z) ** 2
import random
def run(name, s, ds, n, k, q, seed):
    rng = random.Random(seed)
    r = lambda: mp.mpf(rng.randint(-900, 900)) / 300
    c = [[r() for _ in range(n)] for _ in range(q)]
    a = [[r() for _ in range(k)] for _ in range(q)]
    sym = [(i, j) for i in range(n) for j in range(i, n)]
    N = len(sym) + q * n + q * k
    rows = []
    for _ in range(80):
        while True:
            x = [mp.mpf(rng.randint(-1000, 1000)) / 1000 * mp.sqrt(n) for _ in range(n)]
            if sum(v * v for v in x) < n: break
        z = [sum(x[t] * c[i][t] for t in range(n)) for i in range(q)]
        for l in range(k):
            row = [mp.mpf(0)] * N
            for m, (i, j) in enumerate(sym):       # - (x X x^T) sum_i sigma'(z_i) z_i a_i[l]
                coef = x[i] * x[j] * (1 if i == j else 2)
                row[m] = -coef * sum(ds(z[i2]) * z[i2] * a[i2][l] for i2 in range(q))
            for i in range(q):
                for t in range(n):                 # sigma'(z_i) x_t a_i[l]  (psi_c_i[t])
                    row[len(sym) + i * n + t] = ds(z[i]) * x[t] * a[i][l]
                row[len(sym) + q * n + i * k + l] = s(z[i])   # psi_a_i[l]
            rows.append(row)
    A = mp.matrix(rows)
    sv = mp.svd_r(A, compute_uv=False)
    svs = sorted([sv[i] for i in range(len(sv))])
    return N, svs[0], svs[-1]
ok = True
for name, s, ds in (("tanh", mp.tanh, dtanh), ("GELU", gelu, dgelu)):
    for (n, k, q) in ((2, 2, 1), (2, 2, 2), (2, 2, 3), (3, 3, 1), (3, 3, 2), (3, 3, 4)):
        for seed in (1, 2):
            N, smin, smax = run(name, s, ds, n, k, q, 100 * n + 10 * q + seed)
            good = smin > mp.mpf(10) ** (-40)
            ok = ok and good
            print(f"{name} n={n} k={k} q={q} seed={seed}: unknowns {N}, smallest singular value "
                  f"{mp.nstr(smin, 5)}, largest {mp.nstr(smax, 5)}: "
                  f"{'only the zero solution' if good else 'A SOLUTION'}", flush=True)
print("ALL: only the zero solution" if ok else "SOME CASE HAS A SOLUTION", flush=True)
