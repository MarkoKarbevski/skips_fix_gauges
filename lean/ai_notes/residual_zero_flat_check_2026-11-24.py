# S Theorem B.1 (v), residual side, eps = 0: rank of the Jacobian in the weights of one residual
# tanh block (and of the skipless one), by central differences at 50 digits.
from mpmath import mp, mpf, matrix, tanh, sqrt, svd_r
import random
mp.dps = 50
def rnd(r, c, rng):
    M = matrix(r, c)
    for i in range(r):
        for j in range(c): M[i, j] = mpf(rng.gauss(0, 1))
    return M
def N0(h):
    out = matrix(h.rows, h.cols)
    d = h.cols
    for t in range(h.rows):
        s = sqrt(sum(h[t, j]**2 for j in range(d)) / d)
        for j in range(d): out[t, j] = h[t, j] / s
    return out
def net(theta, shapes, x, skip):
    (din, d, m, dout) = shapes
    k = 0
    def take(r, c):
        nonlocal k
        M = matrix(r, c)
        for i in range(r):
            for j in range(c):
                M[i, j] = theta[k]; k += 1
        return M
    E = take(din, d); Wr = take(d, m); Ww = take(m, d); D = take(d, dout)
    h0 = x * E
    pre = N0(h0) * Wr
    act = matrix(pre.rows, pre.cols)
    for i in range(pre.rows):
        for j in range(pre.cols): act[i, j] = tanh(pre[i, j])
    h1 = (h0 if skip else 0 * h0) + act * Ww
    return N0(h1) * D
def rank(shapes, T, skip, nb, seed):
    rng = random.Random(seed)
    (din, d, m, dout) = shapes
    P = din*d + d*m + m*d + d*dout
    theta = [mpf(rng.gauss(0, 1)) for _ in range(P)]
    xs = [rnd(T, din, rng) for _ in range(nb)]
    step = mpf(10)**(-20)
    rows = []
    cols = []
    for p in range(P):
        tp = list(theta); tm = list(theta)
        tp[p] += step; tm[p] -= step
        col = []
        for x in xs:
            yp = net(tp, shapes, x, skip); ym = net(tm, shapes, x, skip)
            diff = (yp - ym) / (2*step)
            col += [diff[i, j] for i in range(diff.rows) for j in range(diff.cols)]
        cols.append(col)
    J = matrix(len(cols[0]), P)
    for p in range(P):
        for r in range(len(cols[0])): J[r, p] = cols[p][r]
    s = svd_r(J, compute_uv=False)
    sv = sorted([s[i] for i in range(len(s))], reverse=True)
    r = sum(1 for v in sv if v > sv[0] * mpf(10)**(-25))
    gap = sv[r-1] / sv[r] if r < len(sv) and sv[r] != 0 else None
    return P, r, sv[r-1] / sv[0], (sv[r] / sv[0] if r < len(sv) else None)
for shapes, T in [((2, 2, 3, 2), 1), ((3, 3, 4, 3), 1), ((2, 2, 3, 2), 2)]:
    (din, d, m, dout) = shapes
    co = d*(d-1)//2 + 1
    for skip in (True, False):
        P, r, last, nxt = rank(shapes, T, skip, nb=4*10, seed=5)
        exp = P - co if skip else P - 2*co
        print(f"d={d} m={m} T={T} {'residual' if skip else 'skipless'}: P={P} rank={r} expected {'=' if skip else '<='} {exp}; "
              f"last kept sv ratio {mp.nstr(last, 3)}, next {mp.nstr(nxt, 3) if nxt is not None else '-'}")
