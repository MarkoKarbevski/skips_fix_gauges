# Step 4 of the proof of S Theorem B.1 (iii), eps > 0, for SwiGLU and GeGLU units (also fewer units
# than coordinates).  Units sigma(x.g_i)(x.v_i) a_i, g_i, v_i in R^n, a_i in R^k.  Equation (17):
#   sum_i [ sigma(x.g_i)(x.v_i) psi_a_i + (sigma'(x.g_i)(x.psi_g_i)(x.v_i) + sigma(x.g_i)(x.psi_v_i)) a_i ]
#     = (x X x^T) sum_i (sigma'(x.g_i)(x.g_i)(x.v_i) + sigma(x.g_i)(x.v_i)) a_i
# for x in an open set (here 100 points of the open ball |x|^2 < n), X symmetric.
# Claim (`GatedUnitsNoSymmetricPart`): X = 0.  With X = 0 the solutions are the rescalings of the
# values (psi_v_i = -alpha_i v_i, psi_a_i = alpha_i a_i): dimension q.  So the linear system in
# (X, psi_g, psi_v, psi_a) has exactly q singular values that vanish, and the X-part of its kernel is 0.
import random, mpmath as mp
mp.mp.dps = 60
def silu(z):  return z / (1 + mp.e ** (-z))
def dsilu(z):
    s = 1 / (1 + mp.e ** (-z)); return s + z * s * (1 - s)
def gelu(z):  return z * mp.ncdf(z)
def dgelu(z): return mp.ncdf(z) + z * mp.npdf(z)
def run(s, ds, n, k, q, seed):
    rng = random.Random(seed)
    r = lambda: mp.mpf(rng.randint(-900, 900)) / 300
    g = [[r() for _ in range(n)] for _ in range(q)]
    v = [[r() for _ in range(n)] for _ in range(q)]
    a = [[r() for _ in range(k)] for _ in range(q)]
    sym = [(i, j) for i in range(n) for j in range(i, n)]
    nx = len(sym); N = nx + 2 * q * n + q * k
    rows = []
    for _ in range(100):
        while True:
            x = [mp.mpf(rng.randint(-1000, 1000)) / 1000 * mp.sqrt(n) for _ in range(n)]
            if sum(t * t for t in x) < n: break
        zg = [sum(x[t] * g[i][t] for t in range(n)) for i in range(q)]
        zv = [sum(x[t] * v[i][t] for t in range(n)) for i in range(q)]
        for l in range(k):
            row = [mp.mpf(0)] * N
            rhs = sum((ds(zg[i]) * zg[i] * zv[i] + s(zg[i]) * zv[i]) * a[i][l] for i in range(q))
            for m, (i, j) in enumerate(sym):
                row[m] = -x[i] * x[j] * (1 if i == j else 2) * rhs
            for i in range(q):
                for t in range(n):
                    row[nx + i * n + t] = ds(zg[i]) * x[t] * zv[i] * a[i][l]          # psi_g_i[t]
                    row[nx + q * n + i * n + t] = s(zg[i]) * x[t] * a[i][l]            # psi_v_i[t]
                row[nx + 2 * q * n + i * k + l] = s(zg[i]) * zv[i]                     # psi_a_i[l]
            rows.append(row)
    A = mp.matrix(rows)
    U, S, V = mp.svd_r(A, compute_uv=True)
    sv = [S[i] for i in range(len(S))]
    small = [i for i, t in enumerate(sv) if t < mp.mpf(10) ** (-40)]
    big = min(t for t in sv if t >= mp.mpf(10) ** (-40))
    xpart = max([abs(V[i, m]) for i in small for m in range(nx)] or [mp.mpf(0)])
    return N, len(small), big, xpart
ok = True
for name, s, ds in (("SwiGLU", silu, dsilu), ("GeGLU", gelu, dgelu)):
    for (n, k, q) in ((2, 2, 1), (2, 2, 2), (2, 2, 3), (3, 3, 1), (3, 3, 2), (3, 3, 4)):
        N, nsmall, big, xpart = run(s, ds, n, k, q, 100 * n + 10 * q + 7)
        good = nsmall == q and xpart < mp.mpf(10) ** (-30)
        ok = ok and good
        print(f"{name} n={n} k={k} q={q}: unknowns {N}, vanishing singular values {nsmall} (rescalings: {q}), "
              f"smallest other {mp.nstr(big, 4)}, largest X-entry in the kernel {mp.nstr(xpart, 3)}: "
              f"{'X = 0' if good else 'DIFFERENT'}", flush=True)
print("ALL: the kernel is the rescalings, X = 0" if ok else "SOME CASE DIFFERENT", flush=True)
