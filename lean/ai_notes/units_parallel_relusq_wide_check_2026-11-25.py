# Exact check of the step "The kinks stay" and "One scale" (proof of S Theorem B.1 (iv), the
# skipless network, equality) for ReLU^2 units in general position, MORE units than coordinates.
# Units sigma(x.c_i) a_i with sigma(z) = max(z, 0)^2, c_i in Q^n, a_i in Q^m, i < q.
# Output h(x) = sum_i sigma(x.c_i) a_i; derivative along (psi, beta):
#   J(x) = sum_i [sigma(x.c_i) beta_i + sigma'(x.c_i) (x.psi_i) a_i],  sigma'(z) = 2 max(z, 0).
# Hypothesis of `UnitsParallelAt`: J(x) is a multiple of h(x) at every x off the kinks with
# h(x) != 0, i.e. J_a(x) h_b(x) - J_b(x) h_a(x) = 0 for all coordinates a < b: linear equations
# in the unknowns (psi, beta).
# Claim: the solutions are psi_i = lam_i c_i, beta_i = (c0 - 2 lam_i) a_i: dimension q + 1.
# The rank of the equations at many integer points x is computed modulo the prime 2^61 - 1 (a
# lower bound on the rank, so an upper bound on the solutions); the q + 1 claimed solutions are
# substituted exactly (a lower bound).
import random, sys
P = (1 << 61) - 1

def rank_mod(rows, ncols):
    rows = [[v % P for v in r] for r in rows]
    rank = 0
    for col in range(ncols):
        piv = None
        for r in range(rank, len(rows)):
            if rows[r][col]:
                piv = r; break
        if piv is None: continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], P - 2, P)
        rows[rank] = [v * inv % P for v in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][col]:
                f = rows[r][col]
                rows[r] = [(v - f * w) % P for v, w in zip(rows[r], rows[rank])]
        rank += 1
    return rank

def run(n, m, q, seed, general=True):
    rng = random.Random(seed)
    def collinear(u, v):
        return all(u[k] * v[l] - u[l] * v[k] == 0 for k in range(n) for l in range(k + 1, n))
    while True:
        c = [[rng.randint(-9, 9) for _ in range(n)] for _ in range(q)]
        a = [[rng.randint(-9, 9) for _ in range(m)] for _ in range(q)]
        # general position: the columns c_i pairwise non-collinear (also not opposite), no a_i = 0.
        # Without it the count is higher: with one collinear pair of columns, n = m = 2, q = 6 and
        # q = 8 gave 9 and 11 solutions against 7 and 9.
        if general and any(collinear(c[i], c[j]) for i in range(q) for j in range(i + 1, q)):
            continue
        if any(all(v == 0 for v in a[i]) for i in range(q)): continue
        break
    nunk = q * n + q * m          # psi_i (n each), then beta_i (m each)
    rows = []; pats = set(); maxact = 0
    def eqs(x):
        y = [sum(x[k] * c[i][k] for k in range(n)) for i in range(q)]
        if any(v == 0 for v in y): return []
        act = [i for i in range(q) if y[i] > 0]
        h = [sum(y[i] ** 2 * a[i][l] for i in act) for l in range(m)]
        if all(v == 0 for v in h): return []
        pats.add(tuple(act))
        # J_l as a linear form in the unknowns
        Jl = []
        for l in range(m):
            row = [0] * nunk
            for i in act:
                for k in range(n):
                    row[i * n + k] += 2 * y[i] * x[k] * a[i][l]
                row[q * n + i * m + l] += y[i] ** 2
            Jl.append(row)
        out = []
        for l1 in range(m):
            for l2 in range(l1 + 1, m):
                out.append([Jl[l1][u] * h[l2] - Jl[l2][u] * h[l1] for u in range(nunk)])
        return out
    for _ in range(60 * nunk):
        x = [rng.randint(-40, 40) for _ in range(n)]
        rows.extend(eqs(x))
    r = rank_mod(rows, nunk)
    maxact = max(len(p) for p in pats)
    # the claimed solutions, substituted exactly at fresh points
    def sol_ok(lam, c0):
        psi = [[lam[i] * c[i][k] for k in range(n)] for i in range(q)]
        beta = [[(c0 - 2 * lam[i]) * a[i][l] for l in range(m)] for i in range(q)]
        vec = [v for i in range(q) for v in psi[i]] + [v for i in range(q) for v in beta[i]]
        for _ in range(200):
            x = [rng.randint(-40, 40) for _ in range(n)]
            for row in eqs(x):
                if sum(row[u] * vec[u] for u in range(nunk)) != 0: return False
        return True
    ok = sol_ok([0] * q, 1) and all(sol_ok([1 if j == i else 0 for j in range(q)], 0) for i in range(q))
    return len(pats), maxact, nunk - r, q + 1, ok

allok = True
for (n, m, q) in [(2, 2, 2), (2, 2, 3), (2, 2, 4), (2, 2, 5), (2, 2, 6), (2, 2, 8), (2, 3, 4), (3, 2, 4),
                  (3, 3, 3), (3, 3, 4), (3, 3, 5), (3, 3, 7), (4, 4, 5), (4, 4, 7)]:
    for seed in range(2):
        npat, maxact, null, want, ok = run(n, m, q, 1000 * n + 100 * m + 10 * q + seed)
        flag = 'ok' if (null == want and ok) else 'DIFFERENT'
        if flag != 'ok': allok = False
        print(f"n={n} m={m} q={q} seed={seed}: patterns {npat}, most active units {maxact}, "
              f"solutions <= {null}, claimed {want}, claimed solutions exact: {ok}  {flag}")
print('ALL EQUAL' if allok else 'SOME DIFFERENT')
