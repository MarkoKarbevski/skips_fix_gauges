"""Check of the statements of lean/SkipsLean/OneBlock/ResidualRMS*.lean (skips paper, Theorem 4.6 (ii) /
B.1 (ii): one residual block under pre-RMSNorm, eps > 0, no biases), 24 November 2026.

y = N(h1) D, h1 = xE + f(N(xE) W_read) W_write, N = RMSNorm with eps on every token.
Expected rank of the Jacobian in the parameters on a batch: P - d(d-1)/2 - s
(s = 0 for tanh blocks, s = number of hidden units for SiLU-gated blocks).
Exact derivatives (forward mode, written out), mpmath with 40 digits.
"""
import mpmath as mp, random
mp.mp.dps = 40
random.seed(11)
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
def Nrm(h, eps):
    rho = mp.sqrt(dot(h, h) / h.cols + eps); return h / rho
def dNrm(h, k, eps):
    d = h.cols; rho = mp.sqrt(dot(h, h) / d + eps)
    return k / rho - h * (dot(h, k) / (d * rho ** 3))
def deriv(kind, th, eta, x, eps):
    E, R, W, D = th; eE, eR, eW, eD = eta
    h = x * E; dh = x * eE
    n = Nrm(h, eps); dn = dNrm(h, dh, eps)
    pre = n * R; dpre = dn * R + n * eR
    h1 = h + act(kind, pre) * W
    dh1 = dh + dact(kind, pre, dpre) * W + act(kind, pre) * eW
    return dNrm(h1, dh1, eps) * D + Nrm(h1, eps) * eD
def basis(din, d, r, q, dout):
    out = []
    def zero(): return [Z(din, d), Z(d, r), Z(q, d), Z(d, dout)]
    for (k, (m, n)) in enumerate(((din, d), (d, r), (q, d), (d, dout))):
        for i in range(m):
            for j in range(n):
                e = zero(); e[k][i, j] = 1; out.append(e)
    return out
ok = True
for kind, din, d, dout, q, eps in (('tanh', 3, 2, 2, 2, '0.5'), ('tanh', 3, 3, 3, 2, '0.01'), ('gated', 2, 2, 3, 2, '0.5'), ('gated', 3, 3, 3, 1, '1')):
    eps = mp.mpf(eps); r = q if kind == 'tanh' else 2 * q
    th = [rnd(din, d), rnd(d, r), rnd(q, d), rnd(d, dout)]
    B = basis(din, d, r, q, dout); P = len(B)
    s = 0 if kind == 'tanh' else q
    expected = P - d * (d - 1) // 2 - s
    X = [3 * rnd(1, din) for _ in range(P + 6)]
    M = mp.matrix(len(X) * dout, P)
    for j, e in enumerate(B):
        col = [v for x in X for v in deriv(kind, th, e, x, eps)]
        for i, v in enumerate(col): M[i, j] = v
    sv = sorted([abs(v) for v in mp.svd_r(M, compute_uv=False)], reverse=True)
    a = sv[expected - 1]; b = sv[expected] if expected < len(sv) else mp.mpf(0)
    print(f"{kind} d_in={din} d={d} d_out={dout} hidden={q} eps={mp.nstr(eps,3)}: P={P}, expected rank {expected}: singular value {expected} = {mp.nstr(a,5)}, next = {mp.nstr(b,5)}")
    ok = ok and b < a * mp.mpf('1e-20')
print("ALL AS EXPECTED" if ok else "MISMATCH")
