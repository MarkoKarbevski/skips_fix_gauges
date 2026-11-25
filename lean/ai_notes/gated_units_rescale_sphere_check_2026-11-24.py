"""Exact check of the statement `reglu_unitsRescaleSphere` for ReGLU units (the step "Since
||n||^2 has no real linear factor, it divides q(n), so X_0 is a multiple of I" of the proof of
Theorem B.1 (iii), case eps = 0, of the skips paper, with Lemma B.3 for gated units), 24 November
2026.

For hidden units relu(x.g_i) (x.v_i) a_i, i = 1..q, with gates g_i in Z^n nonzero and pairwise
non-collinear, values v_i nonzero and not proportional to their gates, a_i in Z^m nonzero, the
unknowns are a symmetric n x n matrix X, vectors pg_i, pv_i in Q^n and beta_i in Q^m, and the
equations are, at every x with no x.g_i = 0,
  (x.x) sum_i [ step(x.g_i) (x.pg_i) (x.v_i) a_i + relu(x.g_i) (x.pv_i) a_i + relu(x.g_i) (x.v_i) beta_i ]
      = 2 (x X x^T) sum_i relu(x.g_i) (x.v_i) a_i .
Claim: the solutions are X = c0 I, pg_i = lam_i g_i, pv_i = mu_i v_i,
beta_i = (2 c0 - lam_i - mu_i) a_i, a space of dimension 2q + 1. Integer weights and inputs, six
inputs per unknown and forty more. The claimed solutions are checked by substitution over the
integers, and the rank of the system is computed modulo the prime 2^61 - 1 (at most the rank over
Q, so the space has dimension at most the number shown).
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
def system(n, m, q, g, v, a, xs):
    pairs = [(i, j) for i in range(n) for j in range(i, n)]
    N = len(pairs) + 2 * q * n + q * m
    rows = []
    for x in xs:
        xx = dot(x, x)
        for o in range(m):
            r = [0] * N
            Bo = sum(sig(1, dot(x, g[i])) * dot(x, v[i]) * a[i][o] for i in range(q))
            for t, (i, j) in enumerate(pairs):
                r[t] = -2 * Bo * x[i] * x[j] * (1 if i == j else 2)
            for i in range(q):
                z = dot(x, g[i]); w = dot(x, v[i])
                for j in range(n):
                    r[len(pairs) + i * n + j] = xx * dsig(1, z) * x[j] * w * a[i][o]
                    r[len(pairs) + q * n + i * n + j] = xx * sig(1, z) * x[j] * a[i][o]
                r[len(pairs) + 2 * q * n + i * m + o] = xx * sig(1, z) * w
            rows.append(r)
    return rows, pairs
bad = 0
for (n, m, q) in ((2, 1, 1), (2, 2, 1), (2, 2, 2), (2, 2, 3), (3, 2, 2), (3, 3, 3), (3, 3, 4), (2, 3, 5), (4, 3, 5)):
    for trial in range(3):
        while True:
            g = [rv(n) for _ in range(q)]; v = [rv(n) for _ in range(q)]
            if all(rank2(g[i], g[j]) for i in range(q) for j in range(i)) and all(rank2(g[i], v[i]) for i in range(q)): break
        a = [rv(m) for _ in range(q)]
        Nunk = n * (n + 1) // 2 + 2 * q * n + q * m
        xs = []
        while len(xs) < 6 * Nunk + 40:
            x = [random.randint(-40, 40) for _ in range(n)]
            if all(dot(x, gi) != 0 for gi in g): xs.append(x)
        rows, pairs = system(n, m, q, g, v, a, xs)
        dim = Nunk - rank_mod(rows, Nunk)
        ok = True
        for which in range(2 * q + 1):
            c0 = 1 if which == 0 else 0
            lam = [1 if which == i + 1 else 0 for i in range(q)]; mu = [1 if which == q + i + 1 else 0 for i in range(q)]
            vec = [c0 if i == j else 0 for (i, j) in pairs]
            for i in range(q): vec += [lam[i] * e for e in g[i]]
            for i in range(q): vec += [mu[i] * e for e in v[i]]
            for i in range(q): vec += [(2 * c0 - lam[i] - mu[i]) * e for e in a[i]]
            if any(dot(r, vec) != 0 for r in rows): ok = False
        flag = '' if (dim == 2 * q + 1 and ok) else '  <-- DIFFERENT'
        bad += flag != ''
        print(f"n={n} m={m} q={q} trial {trial}: unknowns {Nunk}, inputs {len(xs)}, solutions {dim}, expected {2 * q + 1}, claimed solutions in the kernel: {ok}{flag}")
        sys.stdout.flush()
print('different:', bad)
