"""Second batches for the one case of learned_skip_zero_relu_check_2026-11-24.py in which the
random batch gave a rank below the proved value: one residual ReLU block, d_in = d = d_out = 2,
three hidden units, eps = 0, second draw of the weights (rank 14 on 160 random inputs; the value at
almost every parameter is P - (d(d-1)/2 + 1) - s = 15). A rank on a batch is a lower bound: a
narrow region between two kinks gets few random inputs. Here: the same weights (the random stream
is replayed), the angles of the kink lines in the plane of h0, the number of inputs of the first
batch in each region, and the rank on a batch of 400 inputs whose rows x E are spread evenly over
the directions (twice, with two offsets).
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



eps = mp.mpf(0)
kind, din, d, dout, q = 'relu', 2, 2, 2, 3
shapes = ((din, d), (d, q), (q, d), (d, dout))
P = sum(m * n for m, n in shapes); s = q
state = None
for draw in range(2):
    th = [rnd(m, n) for m, n in shapes] + [rnd(d, d)]
    thI = th[:4] + [mp.eye(d)]
    if draw == 0:
        # replay the random stream of the first draw: four batches, 8 inputs per parameter
        for B in (basis(shapes, d, 'none'), basis(shapes, d, 'full'), basis(shapes, d, 'full'), basis(shapes, d, 'tri')):
            for _ in range(8 * len(B)): rnd(1, din)
E, R, W, D, A = thI
B = basis(shapes, d, 'none')
X1 = [3 * rnd(1, din) for _ in range(8 * len(B))]   # the batch that gave rank 14
def region(x):
    pre = (x * E) * R
    return tuple(1 if pre[0, i] > 0 else 0 for i in range(q))
from collections import Counter
print('P =', P, ' s =', s, ' expected', P - d * (d - 1) // 2 - 1 - s)
print('angles of the kink lines (degrees, mod 180):', sorted(float(mp.atan2(-R[0, i], R[1, i]) * 180 / mp.pi) % 180 for i in range(q)))
print('inputs of the first batch by region (active units):', sorted(Counter(region(x) for x in X1).items()))
def rank_on(X):
    M = mp.matrix(len(X) * dout, len(B))
    for j, e in enumerate(B):
        col = [v for x in X for v in deriv(kind, thI, e, x, eps)]
        for i, v in enumerate(col): M[i, j] = v
    return rank_of(M)
print('first batch again:', rank_on(X1))
Einv = E ** -1
for off in ('0.37', '0.11'):
    X = []
    for j in range(400):
        a = (j + mp.mpf(off)) * 2 * mp.pi / 400
        h = mp.matrix([[mp.cos(a), mp.sin(a)]]) * (1 + mp.mpf(j % 7) / 3)
        X.append(h * Einv)
    print('400 inputs spread over the directions, offset', off, ': regions', sorted(Counter(region(x) for x in X).items()))
    print('    rank', rank_on(X))
    sys.stdout.flush()
