"""Exact check of the statement `UnitsRescaleSphere` (the step "Since ||n||^2 has no real linear
factor, it divides q(n), so X_0 is a multiple of I" of the proof of Theorem B.1 (iii), case
eps = 0, of the skips paper, with Lemma B.3), 24 November 2026.

For hidden units sigma(x.c_i) a_i, i = 1..q, with c_i in Q^n nonzero and pairwise non-collinear,
a_i in Q^m nonzero, sigma = ReLU (k = 1) or ReLU^2 (k = 2), the unknowns are a symmetric n x n
matrix X, vectors psi_i in Q^n and beta_i in Q^m, and the equations are, at every x with no
x.c_i = 0,
  (x.x) sum_i [ sigma(x.c_i) beta_i + sigma'(x.c_i) (x.psi_i) a_i ]
      = k (x X x^T) sum_i sigma(x.c_i) a_i .
Claim: the solutions are X = c0 I, psi_i = lam_i c_i, beta_i = k (c0 - lam_i) a_i, a space of
dimension q + 1. Integer weights and integer inputs, six inputs per unknown and forty more. The
claimed solutions are checked by substitution over the integers (so the space has dimension at
least q + 1), and the rank of the system is computed modulo the prime 2^61 - 1, which is at most
its rank over Q (so the space has dimension at most the number shown).
"""
import random, sys
random.seed(5)
PR = 2 ** 61 - 1
def rv(n, lo=-4, hi=4):
    while True:
        v = [random.randint(lo, hi) for _ in range(n)]
        if any(v): return v
def dot(a, b): return sum(x * y for x, y in zip(a, b))
def sig(k, z): return (z ** k) if z > 0 else 0
def dsig(k, z): return (k * z ** (k - 1)) if z > 0 else 0
def rank2(v, w): return any(v[i] * w[j] - v[j] * w[i] != 0 for i in range(len(v)) for j in range(len(v)))
def rank_mod(rows, ncols):
    rows = [[e % PR for e in r] for r in rows]; rk = 0
    for col in range(ncols):
        piv = next((i for i in range(rk, len(rows)) if rows[i][col]), None)
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][col], PR - 2, PR)
        rows[rk] = [e * inv % PR for e in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][col]:
                f = rows[i][col]
                rows[i] = [(e - f * g) % PR for e, g in zip(rows[i], rows[rk])]
        rk += 1
    return rk
def system(k, n, m, q, c, a, xs):
    # unknowns: X (upper triangle, n(n+1)/2), psi (q*n), beta (q*m)
    pairs = [(i, j) for i in range(n) for j in range(i, n)]
    N = len(pairs) + q * n + q * m
    rows = []
    for x in xs:
        xx = dot(x, x)
        for o in range(m):
            r = [0] * N
            Bo = sum(sig(k, dot(x, c[i])) * a[i][o] for i in range(q))
            for t, (i, j) in enumerate(pairs):
                r[t] = -k * Bo * x[i] * x[j] * (1 if i == j else 2)
            for i in range(q):
                z = dot(x, c[i])
                for j in range(n): r[len(pairs) + i * n + j] = xx * dsig(k, z) * x[j] * a[i][o]
                r[len(pairs) + q * n + i * m + o] = xx * sig(k, z)
            rows.append(r)
    return rows, pairs
bad = 0
for k in (1, 2):
    for (n, m, q) in ((1, 1, 1), (2, 1, 1), (2, 2, 1), (2, 2, 2), (2, 2, 3), (3, 2, 2), (3, 3, 3), (3, 3, 4), (2, 3, 5), (4, 3, 6)):
        for trial in range(3):
            while True:
                c = [rv(n) for _ in range(q)]
                if all(rank2(c[i], c[j]) for i in range(q) for j in range(i)): break
            a = [rv(m) for _ in range(q)]
            Nunk = n * (n + 1) // 2 + q * n + q * m
            xs = []
            while len(xs) < 6 * Nunk + 40:
                x = [random.randint(-40, 40) for _ in range(n)]
                if all(dot(x, ci) != 0 for ci in c): xs.append(x)
            rows, pairs = system(k, n, m, q, c, a, xs)
            dim = Nunk - rank_mod(rows, Nunk)
            ok = True
            for which in range(q + 1):
                c0 = 1 if which == 0 else 0; lam = [1 if which == i + 1 else 0 for i in range(q)]
                v = [c0 if i == j else 0 for (i, j) in pairs]
                for i in range(q): v += [lam[i] * cj for cj in c[i]]
                for i in range(q): v += [k * (c0 - lam[i]) * ao for ao in a[i]]
                if any(dot(r, v) != 0 for r in rows): ok = False
            flag = '' if (dim == q + 1 and ok) else '  <-- DIFFERENT'
            bad += flag != ''
            print(f"k={k} n={n} m={m} q={q} trial {trial}: unknowns {Nunk}, inputs {len(xs)}, solutions {dim}, expected {q + 1}, claimed solutions in the kernel: {ok}{flag}")
            sys.stdout.flush()
print('different:', bad)
