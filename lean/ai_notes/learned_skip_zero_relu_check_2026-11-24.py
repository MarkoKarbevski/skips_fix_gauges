"""Check for the equality of Theorem B.1 (iii) of the skips paper at eps = 0 ("with equality for
ReLU, ReLU^2 and ReGLU blocks"), one block under pre-RMSNorm with eps = 0, no biases, 24 November
2026. Functions and exact derivatives as in learned_skip_relu_attention_check_2026-11-24.py, with
eps = 0.

y = N(h1) D, h1 = x E A + f(N(xE) W_read) W_write, N = RMSNorm with eps = 0 on the token; the skip A
is a parameter (full, or upper triangular), or fixed to I (the residual network). P counts E,
W_read, W_write, D (not A). Expected ranks of the Jacobian on a batch, at generic parameters:
  residual (A = I fixed):   P - (d(d-1)/2 + 1) - s
  full learned A:           (P + d^2) - (d(d-1) + 2) - s          = residual + d(d+1)/2 - 1
  triangular learned A:     (P + d(d+1)/2) - (d(d-1)/2 + 2) - s   = residual + d(d+1)/2 - 1
with s = number of hidden units for ReLU and ReLU^2, twice that number for ReGLU.
Also: the full family at the skip A = I. Hidden widths below d, equal to d and above d.
Exact derivatives (forward mode), mpmath with 40 digits, eight random inputs per parameter (no
hidden unit at its kink), two draws of the weights per case.
"""
import mpmath as mp, random, sys
mp.mp.dps = 40
random.seed(11)
def rnd(m, n, sc=1.0): return mp.matrix([[mp.mpf(random.gauss(0, sc)) for _ in range(n)] for _ in range(m)])
def Z(m, n): return mp.zeros(m, n)
def relu(z): return z if z > 0 else mp.mpf(0)
def step(z): return mp.mpf(1) if z > 0 else mp.mpf(0)
def act(kind, M):
    if kind == 'relu': return mp.matrix([[relu(M[0, i]) for i in range(M.cols)]])
    if kind == 'relusq': return mp.matrix([[relu(M[0, i]) ** 2 for i in range(M.cols)]])
    q = M.cols // 2   # reglu: relu(gate) * value
    return mp.matrix([[relu(M[0, i]) * M[0, q + i] for i in range(q)]])
def dact(kind, M, N):
    if kind == 'relu': return mp.matrix([[step(M[0, i]) * N[0, i] for i in range(M.cols)]])
    if kind == 'relusq': return mp.matrix([[2 * relu(M[0, i]) * N[0, i] for i in range(M.cols)]])
    q = M.cols // 2
    return mp.matrix([[step(M[0, i]) * N[0, i] * M[0, q + i] + relu(M[0, i]) * N[0, q + i] for i in range(q)]])
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
def basis(shapes, d, skip):
    out = []
    def zero(): return [Z(m, n) for (m, n) in shapes] + [Z(d, d)]
    for (k, (m, n)) in enumerate(list(shapes) + [(d, d)]):
        for i in range(m):
            for j in range(n):
                if k == len(shapes) and (skip == 'none' or (skip == 'tri' and j < i)): continue
                e = zero(); e[k][i, j] = 1; out.append(e)
    return out
def rank_of(M):
    sv = sorted([abs(v) for v in mp.svd_r(M, compute_uv=False)], reverse=True)
    r = sum(1 for v in sv if v > sv[0] * mp.mpf('1e-25'))
    a = sv[r - 1]; b = sv[r] if r < len(sv) else mp.mpf(0)
    return r, mp.nstr(a, 4), mp.nstr(b, 4)
def rank_mlp(kind, th, B, din, dout, eps):
    X = [3 * rnd(1, din) for _ in range(8 * len(B))]   # ReLU kinds: many inputs per region of the kinks
    M = mp.matrix(len(X) * dout, len(B))
    for j, e in enumerate(B):
        col = [v for x in X for v in deriv(kind, th, e, x, eps)]
        for i, v in enumerate(col): M[i, j] = v
    return rank_of(M)


print('MLP kinds at eps = 0 (exact derivatives, 40 digits)')
eps = mp.mpf(0)
for kind, din, d, dout, q in (('relu', 2, 2, 2, 3), ('relu', 3, 3, 3, 2), ('relu', 3, 3, 3, 3), ('relusq', 2, 2, 3, 2),
                              ('relusq', 3, 3, 3, 4), ('reglu', 2, 2, 2, 2), ('reglu', 3, 3, 3, 1), ('relu', 2, 2, 2, 1)):
  for draw in range(2):
    r = 2 * q if kind == 'reglu' else q
    shapes = ((din, d), (d, r), (q, d), (d, dout))
    P = sum(m * n for m, n in shapes); s = 2 * q if kind == 'reglu' else q
    th = [rnd(m, n) for m, n in shapes] + [rnd(d, d)]
    thT = th[:4] + [mp.matrix([[th[4][i, j] if j >= i else 0 for j in range(d)] for i in range(d)])]
    thI = th[:4] + [mp.eye(d)]
    eres = P - d * (d - 1) // 2 - 1 - s
    efull = P + d * d - d * (d - 1) - 2 - s
    etri = P + d * (d + 1) // 2 - d * (d - 1) // 2 - 2 - s
    assert efull == etri == eres + d * (d + 1) // 2 - 1
    res = [('residual (A = I, theta only)', rank_mlp(kind, thI, basis(shapes, d, 'none'), din, dout, eps), eres),
           ('full, generic A', rank_mlp(kind, th, basis(shapes, d, 'full'), din, dout, eps), efull),
           ('full, at A = I', rank_mlp(kind, thI, basis(shapes, d, 'full'), din, dout, eps), efull),
           ('triangular, generic A', rank_mlp(kind, thT, basis(shapes, d, 'tri'), din, dout, eps), etri)]
    print(f"{kind} d_in={din} d={d} d_out={dout} hidden={q} eps=0 draw {draw}: P={P}, s={s}")
    for name, v, exp in res:
        print(f"    {name}: rank {v[0]}, expected {exp}{'' if v[0] == exp else '  <-- DIFFERENT'} (last singular value {v[1]}, next {v[2]})")
    sys.stdout.flush()
