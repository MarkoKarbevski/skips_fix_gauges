"""Check for the statements on a learned skip (skips paper, Theorem 4.6 (ii) last sentence / B.1 (iii),
one block under pre-RMSNorm, eps > 0, no biases), 24 November 2026.

y = N(h1) D, h1 = x E A + f(N(xE) W_read) W_write, N = RMSNorm with eps on every token; the skip A
is a parameter, full or upper triangular. P counts E, W_read, W_write, D (not A).
Expected rank of the Jacobian in (theta, A) on a batch, at generic parameters:
  full A:        (P + d^2) - d(d-1) - s        = P + d - s
  triangular A:  (P + d(d+1)/2) - d(d-1)/2 - s = P + d - s
(the residual network has P - d(d-1)/2 - s, so the learned skip adds d(d+1)/2), and at A = 0:
  rank = (rank of the skipless network) + d^2 for a full A.
Exact derivatives (forward mode, written out), mpmath with 40 digits.
"""
import mpmath as mp, random, sys
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
def Nrm(h, eps):
    rho = mp.sqrt(dot(h, h) / h.cols + eps); return h / rho
def dNrm(h, k, eps):
    d = h.cols; rho = mp.sqrt(dot(h, h) / d + eps)
    return k / rho - h * (dot(h, k) / (d * rho ** 3))
def deriv(kind, th, eta, x, eps):
    E, R, W, D, A = th; eE, eR, eW, eD, eA = eta
    h = x * E; dh = x * eE
    n = Nrm(h, eps); dn = dNrm(h, dh, eps)
    pre = n * R; dpre = dn * R + n * eR
    h1 = h * A + act(kind, pre) * W
    dh1 = dh * A + h * eA + dact(kind, pre, dpre) * W + act(kind, pre) * eW
    return dNrm(h1, dh1, eps) * D + Nrm(h1, eps) * eD
def basis(din, d, r, q, dout, skip):
    out = []
    def zero(): return [Z(din, d), Z(d, r), Z(q, d), Z(d, dout), Z(d, d)]
    for (k, (m, n)) in enumerate(((din, d), (d, r), (q, d), (d, dout), (d, d))):
        for i in range(m):
            for j in range(n):
                if k == 4 and (skip == 'none' or (skip == 'tri' and j < i)): continue
                e = zero(); e[k][i, j] = 1; out.append(e)
    return out
def rank_gap(kind, th, B, din, dout, eps, expected):
    X = [3 * rnd(1, din) for _ in range(len(B) + 6)]
    M = mp.matrix(len(X) * dout, len(B))
    for j, e in enumerate(B):
        col = [v for x in X for v in deriv(kind, th, e, x, eps)]
        for i, v in enumerate(col): M[i, j] = v
    sv = sorted([abs(v) for v in mp.svd_r(M, compute_uv=False)], reverse=True)
    r = sum(1 for v in sv if v > sv[0] * mp.mpf('1e-25'))
    a = sv[r - 1]; b = sv[r] if r < len(sv) else mp.mpf(0)
    return r, mp.nstr(a, 4), mp.nstr(b, 4)
ok = True
for kind, din, d, dout, q, eps in (('tanh', 2, 2, 2, 2, '0.5'), ('tanh', 3, 3, 3, 3, '0.2'), ('gated', 2, 2, 3, 2, '0.5'), ('tanh', 3, 3, 3, 2, '0.5')):
    eps = mp.mpf(eps); r = q if kind == 'tanh' else 2 * q
    P = din * d + d * r + q * d + d * dout; s = 0 if kind == 'tanh' else q
    th = [rnd(din, d), rnd(d, r), rnd(q, d), rnd(d, dout), rnd(d, d)]
    exp_full = P + d - s
    res = {}
    res['full, generic A'] = rank_gap(kind, th, basis(din, d, r, q, dout, 'full'), din, dout, eps, exp_full)
    thT = th[:4] + [mp.matrix([[th[4][i, j] if j >= i else 0 for j in range(d)] for i in range(d)])]
    res['triangular, generic A'] = rank_gap(kind, thT, basis(din, d, r, q, dout, 'tri'), din, dout, eps, exp_full)
    th0 = th[:4] + [Z(d, d)]
    res['skipless (A = 0, theta only)'] = rank_gap(kind, th0, basis(din, d, r, q, dout, 'none'), din, dout, eps, None)
    res['full, at A = 0'] = rank_gap(kind, th0, basis(din, d, r, q, dout, 'full'), din, dout, eps, None)
    thI = th[:4] + [mp.eye(d)]
    res['residual (A = I, theta only)'] = rank_gap(kind, thI, basis(din, d, r, q, dout, 'none'), din, dout, eps, None)
    print(f"{kind} d_in={din} d={d} d_out={dout} hidden={q} eps={mp.nstr(eps,3)}: P={P}, s={s}, P+d-s={exp_full}, residual value P-d(d-1)/2-s={P - d*(d-1)//2 - s}")
    for k, v in res.items(): print(f"    {k}: rank {v[0]} (last singular value {v[1]}, next {v[2]})")
    sys.stdout.flush()
