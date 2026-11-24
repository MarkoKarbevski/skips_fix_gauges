"""Check of the route for lean/SkipsLean/Depth/TanhPathBlock.lean (dimension paper, Appendix D.6,
"Parameters that satisfy all conditions, in the case (0)", one tanh block), 24 November 2026.

On the family V = W^T (W a d x q read, q >= d >= 2), with g(n) = tanh(n W) V:
(1) (R2): <g(n), n> = sum_j tanh(n c_j) (n c_j) > 0 for n != 0 when W has rank d.
(2) (R3) at n* = (1, ..., 1): the square map Phi_W(v) = Dg(n*)(v - m n*) - m g(n*), m = <v, n*>/d,
    is injective at W = [I | 0] (exactly) and has a nonzero determinant at random W and at lam * W for
    several lam (so lam -> det Phi_{lam W} is not identically zero). If Phi_W is injective then a
    v orthogonal to n* with Dg(n*) v = a g(n*) is 0: this is tested on the null space numerically.
(3) (S3): for a unit xi0 with all xi0 c_j != 0 and s_j = sign(xi0 c_j): <s W^T, xi0> = sum |xi0 c_j| > 0,
    and for complex w with |w_j - s_j| <= rho = min(1, kappa |b| / (2 (1 + kappa) C)), b = s W^T,
    C = sum_j |c_j|, the row w W^T has |Im| < kappa |Re| (sampled).
mpmath, 30 digits.
"""
import mpmath as mp, random
mp.mp.dps = 30
random.seed(3)
def rnd(m, n): return mp.matrix([[mp.mpf(random.gauss(0, 1)) for _ in range(n)] for _ in range(m)])
ok = True
def Phi(W, lam=1):
    d, q = W.rows, W.cols
    W = lam * W; V = W.T
    n = mp.matrix([[1] * d])
    z = n * W
    g = mp.matrix([[mp.tanh(z[0, j]) for j in range(q)]]) * V
    M = mp.zeros(d, d)
    for i in range(d):
        v = mp.zeros(1, d); v[0, i] = 1
        m = sum(v[0, k] for k in range(d)) / d
        u = v - m * n
        uW = u * W
        Dg = mp.matrix([[(1 - mp.tanh(z[0, j]) ** 2) * uW[0, j] for j in range(q)]]) * V
        r = Dg - m * g
        for k in range(d): M[i, k] = r[0, k]
    return M
for d, q in [(2, 2), (2, 4), (3, 3), (3, 5), (4, 6)]:
    W0 = mp.zeros(d, q)
    for i in range(d): W0[i, i] = 1
    d0 = mp.det(Phi(W0))
    W = rnd(d, q)
    dets = [mp.det(Phi(W, lam)) for lam in [1, 2, 4]]
    # (1)
    r2 = True
    for _ in range(50):
        n = rnd(1, d); z = n * W
        r2 = r2 and sum(mp.tanh(z[0, j]) * z[0, j] for j in range(q)) > 0
    # (3)
    xi0 = rnd(1, d); xi0 = xi0 / mp.sqrt((xi0 * xi0.T)[0, 0])
    c = xi0 * W; s = mp.matrix([[mp.sign(c[0, j]) for j in range(q)]])
    b = s * W.T
    pos = (b * xi0.T)[0, 0] - sum(abs(c[0, j]) for j in range(q))
    kappa = mp.mpf(1) / 3
    C = sum(mp.sqrt(sum(W[i, j] ** 2 for i in range(d))) for j in range(q))
    nb = mp.sqrt((b * b.T)[0, 0])
    rho = min(mp.mpf(1), kappa * nb / (2 * (1 + kappa) * C))
    cone = True
    for _ in range(200):
        w = mp.matrix([[s[0, j] + rho * mp.rect(mp.mpf(random.random()), random.uniform(0, 2 * mp.pi)) for j in range(q)]])
        row = w * W.T
        re = mp.sqrt(sum(mp.re(row[0, i]) ** 2 for i in range(d))); im = mp.sqrt(sum(mp.im(row[0, i]) ** 2 for i in range(d)))
        cone = cone and (im < kappa * re)
    good = (abs(d0) > mp.mpf(10) ** -10) and all(abs(x) > mp.mpf(10) ** -20 for x in dets) and r2 and abs(pos) < mp.mpf(10) ** -20 and cone
    print(f"d={d} q={q}: det Phi at [I|0] = {mp.nstr(d0, 5)}; at random W, lam=1,2,4: {[mp.nstr(x, 4) for x in dets]}; (R2) {r2}; <sW^T,xi0> - sum|xi0 c_j| = {mp.nstr(pos, 3)}; cone {cone}:", 'OK' if good else 'MISMATCH')
    ok = ok and good
print('ALL AS EXPECTED' if ok else 'SOME MISMATCH')

# ---- second route (the explicit pair) ----
# W = lam [I_d | mu_1 1 ... mu_m 1], V = [I_d ; eta a_j], a_j = 1 + (j+1) e_2, mu_j > 1, eta > 0 with
# eta * sum_j max_i a_j(i) < tanh(1)/2, lam >= 1. Checked: (R2) every g(n) on the sphere has a coordinate
# of absolute value > 0 (the one with |n_i| >= 1); (R3) at n0 = 1: Dg(n0) v = lam sech^2(lam) v for v
# orthogonal to n0, and <g(n0), n0> > 0; (S3): for |w_j - 1| <= rho = min(1/2, kappa/4) the row w V has
# |Im| < kappa |Re|.
print("explicit pair:")
ok2 = True
for d, m in [(2, 0), (2, 2), (3, 1), (4, 3)]:
    q = d + m
    mus = [mp.sqrt(p) + 1 for p in [2, 3, 5][:m]]
    a = [[mp.mpf(1) + (j + 1 if i == 1 else 0) for i in range(d)] for j in range(m)]
    eta = (mp.tanh(1) / 2) / (sum(max(r) for r in a) + 1)
    for lam in [1, 2, 5]:
        W = mp.zeros(d, q); V = mp.zeros(q, d)
        for i in range(d): W[i, i] = lam; V[i, i] = 1
        for j in range(m):
            for i in range(d): W[i, d + j] = lam * mus[j]; V[d + j, i] = eta * a[j][i]
        def g(n):
            z = n * W
            return mp.matrix([[mp.tanh(z[0, j]) for j in range(q)]]) * V
        r2 = True
        for _ in range(100):
            n = rnd(1, d); n = n * mp.sqrt(d) / mp.sqrt((n * n.T)[0, 0])
            i = max(range(d), key=lambda k: abs(n[0, k]))
            r2 = r2 and abs(n[0, i]) >= 1 and abs(g(n)[0, i]) > mp.tanh(1) / 2 - mp.mpf(10) ** -20
        n0 = mp.matrix([[1] * d]); z0 = n0 * W
        r3 = (g(n0) * n0.T)[0, 0] > 0
        for _ in range(20):
            v = rnd(1, d); v = v - ((v * n0.T)[0, 0] / d) * n0
            vW = v * W
            Dg = mp.matrix([[(1 - mp.tanh(z0[0, j]) ** 2) * vW[0, j] for j in range(q)]]) * V
            r3 = r3 and max(abs(Dg[0, k] - lam * (1 - mp.tanh(lam) ** 2) * v[0, k]) for k in range(d)) < mp.mpf(10) ** -20
        kappa = mp.mpf(1) / 5; rho = min(mp.mpf(1) / 2, kappa / 4)
        cone = True
        for _ in range(200):
            w = mp.matrix([[1 + rho * mp.rect(mp.mpf(random.random()), random.uniform(0, 2 * mp.pi)) for _ in range(q)]])
            row = w * V
            re = mp.sqrt(sum(mp.re(row[0, i]) ** 2 for i in range(d))); im = mp.sqrt(sum(mp.im(row[0, i]) ** 2 for i in range(d)))
            cone = cone and im < kappa * re
        good = r2 and r3 and cone
        print(f"d={d} m={m} lam={lam}: (R2) {r2}; (R3) {r3}; cone {cone}:", 'OK' if good else 'MISMATCH')
        ok2 = ok2 and good
print('EXPLICIT PAIR AS EXPECTED' if ok2 else 'EXPLICIT PAIR: SOME MISMATCH')
