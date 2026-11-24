# Exact check of the step "The kinks stay" and "One scale" (proof of S Theorem B.1 (iv), the
# skipless network, equality) for ReLU units in general position, MORE units than coordinates.
# Units sigma(x.c_i) a_i, c_i in Q^n, a_i in Q^m, i < q.  On the region with active set S the
# output is b = x M_S, M_S = sum_{i in S} c_i (x) a_i, and the derivative along (psi, beta) is
# J = x N_S, N_S = sum_{i in S} (psi_i (x) a_i + c_i (x) beta_i).  "J parallel to b on the region":
#   |S| >= 2 (M_S of rank >= 2):  N_S = mu_S M_S, one unknown number mu_S;
#   |S| == 1 (S = {j}):           N_S = phi (x) a_j, one unknown vector phi.
# Claim: the solutions (psi, beta) are psi_i = lam_i c_i, beta_i = (c0 - lam_i) a_i: dimension q+1.
# The rank is computed modulo the prime 2^61 - 1 (a lower bound on the rank, so an upper bound on the
# solutions); the q + 1 claimed solutions are substituted exactly (a lower bound).
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

def regions(c, n, q, rng):
    pats = set()
    for _ in range(20000):
        x = [rng.randint(-60, 60) for _ in range(n)]
        s = [sum(x[k] * c[i][k] for k in range(n)) for i in range(q)]
        if all(v != 0 for v in s):
            pats.add(tuple(i for i in range(q) if s[i] > 0))
    return sorted(pats)

def run(n, m, q, seed):
    rng = random.Random(seed)
    # draw until the units are in general position: the c_i pairwise non-collinear, every a_i
    # nonzero, the a_i pairwise non-collinear (then M_S has rank >= 2 on every region with two
    # active units, which is counted below as a control)
    while True:
        c = [[rng.randint(-5, 5) for _ in range(n)] for _ in range(q)]
        a = [[rng.randint(-5, 5) for _ in range(m)] for _ in range(q)]
        good = all(rank_mod([c[i][:], c[j][:]], n) == 2 and rank_mod([a[i][:], a[j][:]], m) == 2
                   for i in range(q) for j in range(i))
        if good: break
    pats = [S for S in regions(c, n, q, rng) if len(S) >= 1]
    base = q * n + q * m
    extra = [1 if len(S) >= 2 else n for S in pats]
    N = base + sum(extra)
    rows = []; off = base; low = 0
    for S, e in zip(pats, extra):
        MS = [[sum(c[i][k] * a[i][l] for i in S) for l in range(m)] for k in range(n)]
        if len(S) >= 2 and rank_mod([r[:] for r in MS], m) < 2: low += 1
        for k in range(n):
            for l in range(m):
                r = [0] * N
                for i in S:
                    r[i * n + k] += a[i][l]
                    r[q * n + i * m + l] += c[i][k]
                if len(S) >= 2: r[off] -= MS[k][l]
                else: r[off + k] -= a[S[0]][l]
                rows.append(r)
        off += e
    # the claimed solutions solve the system exactly (integers): lam_i = 1 for one i; c0 = 1
    def residual(lam, c0):
        psi = [[lam[i] * c[i][k] for k in range(n)] for i in range(q)]
        beta = [[(c0 - lam[i]) * a[i][l] for l in range(m)] for i in range(q)]
        for S in pats:
            for k in range(n):
                for l in range(m):
                    NS = sum(psi[i][k] * a[i][l] + c[i][k] * beta[i][l] for i in S)
                    if len(S) >= 2:
                        if NS != c0 * sum(c[i][k] * a[i][l] for i in S): return False
                    else:
                        j = S[0]
                        if NS != c0 * c[j][k] * a[j][l]: return False   # phi = c0 c_j
        return True
    sol_ok = residual([0] * q, 1) and all(residual([1 if j == i else 0 for j in range(q)], 0) for i in range(q))
    null_upper = N - rank_mod(rows, N)
    return len(pats), low, null_upper, q + 1, sol_ok

ok = True
cases = [(2, 2, 3), (2, 2, 4), (2, 2, 5), (3, 3, 4), (3, 3, 5), (3, 3, 7), (4, 4, 5), (4, 4, 6)]
for (n, m, q) in cases:
    for seed in range(3):
        npat, low, null, want, sol_ok = run(n, m, q, 1000 * n + 10 * q + seed)
        flag = 'ok' if null == want and sol_ok else 'DIFFERENT'
        if flag != 'ok': ok = False
        print(f"n={n} m={m} q={q} seed={seed}: regions {npat}, of rank < 2 with two active units {low}, "
              f"solutions at most {null} (rank modulo 2^61-1), claimed solutions {want} "
              f"(substituted exactly: {sol_ok}): {flag}", flush=True)
print("ALL OK" if ok else "SOME DIFFERENT", flush=True)
