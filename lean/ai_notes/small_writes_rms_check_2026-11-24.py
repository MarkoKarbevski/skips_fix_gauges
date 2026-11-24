"""Check of the statements of lean/SkipsLean/Residual/SmallWritesNorm.lean and Depth*RMS.lean (skips paper,
Lemma A.27, second value, and Theorem 4.7 under pre-RMSNorm, eps > 0, no biases), 24 November 2026.

Residual network of L blocks under pre-RMSNorm: h_l = h_{l-1} + f(N(h_{l-1}) R_l) W_l, y = N(h_L) D.
theta_tau holds tau*W_l. (1) K_tau eta = DF(theta_tau)(eta_E, eta_read/tau, eta_write, eta_D) tends to
(J_0 eta)(x) = DN(h)(x eta_E + sum_l (Df(n R_l)(n eta_R_l) W_l + f(n R_l) eta_W_l)) D + N(h) eta_D, h = xE, n = N(h).
(2) rank J_0 on a batch = P - d(d-1)/2 - s. (3) the same rank for DF at theta_tau, small tau, and at tau = 1.
Exact derivatives (forward mode), mpmath with 40 digits.
"""
import mpmath as mp, random
mp.mp.dps = 40
random.seed(5)
def rnd(m, n): return mp.matrix([[mp.mpf(random.gauss(0, 1)) for _ in range(n)] for _ in range(m)])
def Z(m, n): return mp.zeros(m, n)
def sig(z): return z / (1 + mp.e ** (-z))
def dsig(z):
    s = 1 / (1 + mp.e ** (-z)); return s + z * s * (1 - s)
def act(kind, M):
    if kind == 'tanh': return mp.matrix([[mp.tanh(M[0, i]) for i in range(M.cols)]])
    q = M.cols // 2
    return mp.matrix([[sig(M[0, i]) * M[0, q + i] for i in range(q)]])
def dact(kind, M, N):
    if kind == 'tanh': return mp.matrix([[(1 - mp.tanh(M[0, i]) ** 2) * N[0, i] for i in range(M.cols)]])
    q = M.cols // 2
    return mp.matrix([[dsig(M[0, i]) * N[0, i] * M[0, q + i] + sig(M[0, i]) * N[0, q + i] for i in range(q)]])
def dot(a, b): return sum(a[0, i] * b[0, i] for i in range(a.cols))
def Nrm(h, eps): return h / mp.sqrt(dot(h, h) / h.cols + eps)
def dNrm(h, k, eps):
    d = h.cols; rho = mp.sqrt(dot(h, h) / d + eps)
    return k / rho - h * (dot(h, k) / (d * rho ** 3))
def deriv(kind, th, eta, x, eps):
    E, R, W, D = th; eE, eR, eW, eD = eta
    h = x * E; dh = x * eE
    for l in range(len(R)):
        n = Nrm(h, eps); dn = dNrm(h, dh, eps)
        pre = n * R[l]; dpre = dn * R[l] + n * eR[l]
        hn = h + act(kind, pre) * W[l]
        dh = dh + dact(kind, pre, dpre) * W[l] + act(kind, pre) * eW[l]
        h = hn
    return dNrm(h, dh, eps) * D + Nrm(h, eps) * eD
def J0(kind, th, eta, x, eps):
    E, R, W, D = th; eE, eR, eW, eD = eta
    h = x * E; n = Nrm(h, eps); k = x * eE
    for l in range(len(R)):
        pre = n * R[l]
        k = k + dact(kind, pre, n * eR[l]) * W[l] + act(kind, pre) * eW[l]
    return dNrm(h, k, eps) * D + n * eD
def basis(din, d, rs, hs, dout):
    out = []
    def zero(): return [Z(din, d), [Z(d, r) for r in rs], [Z(h, d) for h in hs], Z(d, dout)]
    for i in range(din):
        for j in range(d):
            e = zero(); e[0][i, j] = 1; out.append(e)
    for l, r in enumerate(rs):
        for i in range(d):
            for j in range(r):
                e = zero(); e[1][l][i, j] = 1; out.append(e)
    for l, h in enumerate(hs):
        for i in range(h):
            for j in range(d):
                e = zero(); e[2][l][i, j] = 1; out.append(e)
    for i in range(d):
        for j in range(dout):
            e = zero(); e[3][i, j] = 1; out.append(e)
    return out
def svals(cols):
    M = mp.matrix(len(cols[0]), len(cols))
    for j, c in enumerate(cols):
        for i, v in enumerate(c): M[i, j] = v
    return sorted([abs(s) for s in mp.svd_r(M, compute_uv=False)], reverse=True)
ok = True
for kind, din, d, dout, hs, eps in (('tanh', 3, 2, 2, [1, 2], '0.5'), ('tanh', 3, 3, 3, [2, 1], '0.1'), ('gated', 2, 2, 2, [1, 2], '0.5'), ('gated', 3, 3, 3, [1, 1], '1')):
    eps = mp.mpf(eps); rs = hs if kind == 'tanh' else [2 * h for h in hs]
    th = [rnd(din, d), [rnd(d, r) for r in rs], [rnd(h, d) for h in hs], rnd(d, dout)]
    B = basis(din, d, rs, hs, dout); P = len(B)
    s = 0 if kind == 'tanh' else sum(hs)
    expected = P - d * (d - 1) // 2 - s
    X = [3 * rnd(1, din) for _ in range(P + 6)]
    cols0 = [[v for x in X for v in J0(kind, th, e, x, eps)] for e in B]
    sv0 = svals(cols0); a, b = sv0[expected - 1], (sv0[expected] if expected < len(sv0) else mp.mpf(0))
    print(f"{kind} d_in={din} d={d} d_out={dout} hidden={hs} eps={mp.nstr(eps,3)}: P={P}, expected rank {expected}")
    print(f"   J_0: singular value {expected} = {mp.nstr(a,5)}, next = {mp.nstr(b,5)}")
    ok = ok and b < a * mp.mpf('1e-20')
    ratios = []
    for tau in (mp.mpf('1e-6'), mp.mpf('1e-9'), mp.mpf(1)):
        tht = [th[0], th[1], [tau * w for w in th[2]], th[3]]
        colsJ = [[v for x in X for v in deriv(kind, tht, e, x, eps)] for e in B]
        svJ = svals(colsJ); aj, bj = svJ[expected - 1], (svJ[expected] if expected < len(svJ) else mp.mpf(0))
        line = f"   tau={mp.nstr(tau,3)}: J_tau: singular value {expected} = {mp.nstr(aj,5)}, next = {mp.nstr(bj,5)}"
        if tau < 1:
            colsK = [[v for x in X for v in deriv(kind, tht, [e[0], [m / tau for m in e[1]], e[2], e[3]], x, eps)] for e in B]
            diff = max(abs(u - v) for c1, c2 in zip(colsK, cols0) for u, v in zip(c1, c2))
            ratios.append(diff / tau); line += f";  max|K_tau - J_0| = {mp.nstr(diff,5)}"
        print(line)
        ok = ok and bj < aj * mp.mpf('1e-20')
    ok = ok and abs(ratios[0] - ratios[1]) < mp.mpf('0.01') * ratios[1]
print("ALL AS EXPECTED" if ok else "MISMATCH")
