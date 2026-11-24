"""Check, 24 November 2026: Theorem B.1 (iii) of the skips paper for eps = 0 and analytic blocks.
The theorem says "at most d(d+1)/2 - 1" for the difference between the network with a learned skip
and the residual network; a reader computed that the difference is exactly d(d+1)/2 - 1 for tanh,
GELU and SwiGLU. Here: tanh and gated (SiLU gate) blocks, eps = 0, the rank with a full learned
skip, with an upper triangular skip, and of the residual network at the same weights. Functions
and exact derivatives as in learned_skip_oneblock_check_2026-11-24.py (40 digits).
If the symmetries are the only flat directions, the values are
  residual:    P - (d(d-1)/2 + 1) - s
  full A:      (P + d^2) - (d(d-1) + 2) - s
  triangular:  (P + d(d+1)/2) - (d(d-1)/2 + 2) - s
with s = 0 for tanh and s = number of hidden units for the gated block.
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

eps = mp.mpf(0)
for kind, din, d, dout, q in (('tanh', 2, 2, 2, 2), ('tanh', 3, 3, 3, 2), ('gated', 2, 2, 3, 2), ('tanh', 2, 2, 2, 1), ('gated', 3, 3, 3, 1)):
    r = q if kind == 'tanh' else 2 * q
    P = din * d + d * r + q * d + d * dout; s = 0 if kind == 'tanh' else q
    th = [rnd(din, d), rnd(d, r), rnd(q, d), rnd(d, dout), rnd(d, d)]
    thT = th[:4] + [mp.matrix([[th[4][i, j] if j >= i else 0 for j in range(d)] for i in range(d)])]
    thI = th[:4] + [mp.eye(d)]
    eres = P - d * (d - 1) // 2 - 1 - s; efull = P + d * d - d * (d - 1) - 2 - s
    res = [('residual (A = I, theta only)', rank_gap(kind, thI, basis(din, d, r, q, dout, 'none'), din, dout, eps, eres), eres),
           ('full, generic A', rank_gap(kind, th, basis(din, d, r, q, dout, 'full'), din, dout, eps, efull), efull),
           ('triangular, generic A', rank_gap(kind, thT, basis(din, d, r, q, dout, 'tri'), din, dout, eps, efull), efull)]
    print(f"{kind} d_in={din} d={d} d_out={dout} hidden={q} eps=0: P={P}, s={s}; d(d+1)/2 - 1 = {d*(d+1)//2 - 1}")
    for name, v, exp in res: print('   ', name, v, 'value of the count:', exp)
    sys.stdout.flush()
