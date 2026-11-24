"""Check for the statements on a learned skip for the kinds of block that need the paper's route
(skips paper, Theorem 4.6 (ii) last sentence / B.1 (iii), one block under pre-RMSNorm, eps > 0, no
biases), 24 November 2026: ReLU, ReLU^2, ReGLU blocks and attention blocks.

y = N(h1) D, h1 = x E A + f(N(xE) W_read) W_write, N = RMSNorm with eps on every token; the skip A
is a parameter (full, or upper triangular), or fixed to I (the residual network). P counts E,
W_read, W_write, D (not A). Expected ranks of the Jacobian on a batch, at generic parameters:
  residual (A = I fixed):   P - d(d-1)/2 - s
  full learned A:           (P + d^2) - d(d-1) - s        = residual + d(d+1)/2
  triangular learned A:     (P + d(d+1)/2) - d(d-1)/2 - s = residual + d(d+1)/2
with s = number of hidden units for ReLU and ReLU^2 (one rescaling per unit), s = twice that number
for ReGLU (the gate and the value of a unit are rescaled separately) and
s = 2 H d_h^2 for attention (GL(d_h) between queries and keys, and between values and outputs).
Also: the full family at the skip A = I (the claim "at the same theta, for every invertible A").

MLP kinds: exact derivatives (forward mode, written out), mpmath with 40 digits; the random inputs
have no hidden unit at its kink. The batch has eight inputs per parameter. A small batch gives a lower rank when
a region of the kinks is a narrow cone: with one input per parameter plus six, the first ReLU case
gave 17 at A = I (19 with 60 inputs, also at A = 2I, a diagonal, a rotation and a symmetric A), and
with three inputs per parameter a ReGLU case gave 13 and 16 in place of 15 and 18 (15, 18, 18 with
80 inputs, for three draws of the weights, two batches each). Attention: central differences with step 1e-20 at 60 digits (error
about 1e-40, far below the gap).
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

print('MLP kinds (exact derivatives, 40 digits)')
for kind, din, d, dout, q, eps in (('relu', 2, 2, 2, 3, '0.5'), ('relu', 3, 3, 3, 2, '0.3'), ('relusq', 2, 2, 3, 2, '0.5'),
                                   ('relusq', 3, 3, 3, 4, '0.2'), ('reglu', 2, 2, 2, 2, '0.5'), ('reglu', 3, 3, 3, 1, '0.4')):
    eps = mp.mpf(eps); r = 2 * q if kind == 'reglu' else q
    shapes = ((din, d), (d, r), (q, d), (d, dout))
    P = sum(m * n for m, n in shapes); s = 2 * q if kind == 'reglu' else q
    th = [rnd(m, n) for m, n in shapes] + [rnd(d, d)]
    thT = th[:4] + [mp.matrix([[th[4][i, j] if j >= i else 0 for j in range(d)] for i in range(d)])]
    thI = th[:4] + [mp.eye(d)]
    res = [('residual (A = I, theta only)', rank_mlp(kind, thI, basis(shapes, d, 'none'), din, dout, eps), P - d * (d - 1) // 2 - s),
           ('full, generic A', rank_mlp(kind, th, basis(shapes, d, 'full'), din, dout, eps), P + d - s),
           ('full, at A = I', rank_mlp(kind, thI, basis(shapes, d, 'full'), din, dout, eps), P + d - s),
           ('triangular, generic A', rank_mlp(kind, thT, basis(shapes, d, 'tri'), din, dout, eps), P + d - s)]
    print(f"{kind} d_in={din} d={d} d_out={dout} hidden={q} eps={mp.nstr(eps,3)}: P={P}, s={s}")
    for name, v, exp in res:
        print(f"    {name}: rank {v[0]}, expected {exp}{'' if v[0] == exp else '  <-- DIFFERENT'} (last singular value {v[1]}, next {v[2]})")
    sys.stdout.flush()

# ---- attention ----
mp.mp.dps = 60
def rowN(h, eps):
    out = mp.matrix(h.rows, h.cols)
    for t in range(h.rows):
        rho = mp.sqrt(sum(h[t, j] ** 2 for j in range(h.cols)) / h.cols + eps)
        for j in range(h.cols): out[t, j] = h[t, j] / rho
    return out
def attn_net(th, x, eps, sees, H, dh):
    E = th[0]; D = th[1 + 4 * H]; A = th[2 + 4 * H]
    h0 = x * E; n = rowN(h0, eps); T = x.rows; d = E.cols
    out = mp.zeros(T, d)
    for i in range(H):
        Q, K, V, O = th[1 + 4 * i: 5 + 4 * i]
        S = (n * Q) * (n * K).T / mp.sqrt(dh)
        Pm = mp.zeros(T, T)
        for t in range(T):
            idx = [u for u in range(T) if sees(t, u)]
            ex = [mp.e ** S[t, u] for u in idx]; tot = sum(ex)
            for u, v in zip(idx, ex): Pm[t, u] = v / tot
        out += Pm * (n * V) * O
    return rowN(h0 * A + out, eps) * D
def rank_attn(th, shapes, d, skip, eps, sees, H, dh, T, din, dout):
    B = basis(shapes, d, skip)
    X = [rnd(T, din, 1.5) for _ in range(len(B) // (T * dout) + 5)]
    hh = mp.mpf('1e-20')
    M = mp.matrix(len(X) * T * dout, len(B))
    for j, e in enumerate(B):
        tp = [a + hh * b for a, b in zip(th, e)]; tm = [a - hh * b for a, b in zip(th, e)]
        col = []
        for x in X:
            yp = attn_net(tp, x, eps, sees, H, dh); ym = attn_net(tm, x, eps, sees, H, dh)
            col += [(yp[a, b] - ym[a, b]) / (2 * hh) for a in range(T) for b in range(dout)]
        for i, v in enumerate(col): M[i, j] = v
    return rank_of(M)
print('attention (central differences, step 1e-20, 60 digits)')
masks = {'none': lambda t, u: True, 'causal': lambda t, u: u <= t}
for mask, T, din, d, dout, H, dh, eps in (('none', 2, 2, 2, 2, 1, 1, '0.5'), ('causal', 2, 2, 2, 2, 2, 1, '0.5'),
                                          ('causal', 3, 2, 2, 2, 1, 2, '0.4'), ('none', 2, 3, 3, 3, 1, 2, '0.5')):
    eps = mp.mpf(eps); sees = masks[mask]
    shapes = [(din, d)] + [(d, dh), (d, dh), (d, dh), (dh, d)] * H + [(d, dout)]
    P = sum(m * n for m, n in shapes); s = 2 * H * dh * dh
    th = [rnd(m, n, 0.8) for m, n in shapes] + [rnd(d, d)]
    thI = th[:-1] + [mp.eye(d)]
    res = [('residual (A = I, theta only)', rank_attn(thI, shapes, d, 'none', eps, sees, H, dh, T, din, dout), P - d * (d - 1) // 2 - s),
           ('full, generic A', rank_attn(th, shapes, d, 'full', eps, sees, H, dh, T, din, dout), P + d - s),
           ('full, at A = I', rank_attn(thI, shapes, d, 'full', eps, sees, H, dh, T, din, dout), P + d - s)]
    print(f"attention mask={mask} T={T} d_in={din} d={d} d_out={dout} H={H} d_h={dh} eps={mp.nstr(eps,3)}: P={P}, s={s}")
    for name, v, exp in res:
        print(f"    {name}: rank {v[0]}, expected {exp}{'' if v[0] == exp else '  <-- DIFFERENT'} (last singular value {v[1]}, next {v[2]})")
    sys.stdout.flush()
