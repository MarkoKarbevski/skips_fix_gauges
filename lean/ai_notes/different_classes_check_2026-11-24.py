"""Check of the statements of lean/SkipsLean/Residual/SkiplessEnds.lean and DifferentClasses(RMS).lean
(skips paper, Theorem 4.11 (i) and Theorem A.28 (ii), (iv); MLP blocks tanh, GELU and SiLU-gated blocks,
without normalization and under pre-RMSNorm with eps > 0, without biases), 24 November 2026.

For networks x -> x E, h -> M h + f(chi(h) W_read) W_write (M = 1 residual, M = 0 skipless), -> chi(h) D,
with chi the identity or RMSNorm, s = the number of gated units (0 for tanh and GELU), and
k = d^2 without normalization, k = d(d-1)/2 under pre-RMSNorm:
(1) the Jacobian of the outputs of the SKIPLESS network on a batch has rank at most P - 2k - s at every
    parameter tried: random ones, E of rank 1, all writes zero, D of rank 1 (also with fewer than d
    hidden units in a block);
(2) the Jacobian of the RESIDUAL network of the same widths has rank P - k - s on the same batch at random
    parameters (d >= 2), which exceeds the bound of (1).
Derivatives are exact (forward mode, written out); mpmath with 40 digits; a rank is the number of
singular values above 1e-25 times the largest, and the gap around the cut is printed.
"""
import mpmath as mp, random, sys
mp.mp.dps = 40
random.seed(11)

def rnd(m, n): return mp.matrix([[mp.mpf(random.gauss(0, 1)) for _ in range(n)] for _ in range(m)])
def Phi(z): return (1 + mp.erf(z / mp.sqrt(2))) / 2
def phi(z): return mp.exp(-z * z / 2) / mp.sqrt(2 * mp.pi)
ACT = {'tanh': (mp.tanh, lambda z: 1 - mp.tanh(z) ** 2),
       'gelu': (lambda z: z * Phi(z), lambda z: Phi(z) + z * phi(z))}

EPS = mp.mpf(1) / 3
def chi(norm, h, dh):
    """chi(h) and D chi(h)[dh] for one token row; chi = identity or RMSNorm with eps = 1/3"""
    if not norm: return h, dh
    d = h.cols
    rho = mp.sqrt(EPS + sum(h[0, i] ** 2 for i in range(d)) / d)
    hk = sum(h[0, i] * dh[0, i] for i in range(d))
    return h / rho, dh / rho - h * (hk / (d * rho ** 3))

def sig(z): return z / (1 + mp.e ** (-z))
def dsig(z):
    s = 1 / (1 + mp.e ** (-z)); return s + z * s * (1 - s)

def block(kind, pre, dpre):
    """f(pre) and Df(pre)[dpre]; for 'swiglu' the first half of the columns are gates, the second values"""
    if kind == 'swiglu':
        q = pre.cols // 2
        a = mp.matrix([[sig(pre[0, i]) * pre[0, q + i] for i in range(q)]])
        da = mp.matrix([[dsig(pre[0, i]) * dpre[0, i] * pre[0, q + i] + sig(pre[0, i]) * dpre[0, q + i] for i in range(q)]])
        return a, da
    s, ds = ACT[kind]
    return (mp.matrix([[s(pre[0, i]) for i in range(pre.cols)]]),
            mp.matrix([[ds(pre[0, i]) * dpre[0, i] for i in range(pre.cols)]]))

def forward(kind, norm, M, th, x, eta):
    """derivative along eta of the output at th = (E, reads, writes, D); M = 1 residual, 0 skipless"""
    E, R, W, D = th; eE, eR, eW, eD = eta
    h = x * E; dh = x * eE
    for l in range(len(R)):
        c, dc = chi(norm, h, dh)
        a, da = block(kind, c * R[l], dc * R[l] + c * eR[l])
        h, dh = M * h + a * W[l], M * dh + da * W[l] + a * eW[l]
    c, dc = chi(norm, h, dh)
    return dc * D + c * eD

def basis(shapes, g):
    """the coordinate directions of the parameter space; g = 2 for gated blocks (gate and value columns)"""
    (dIn, d), hid, dOut = shapes
    zero = lambda: (mp.zeros(dIn, d), [mp.zeros(d, g * q) for q in hid], [mp.zeros(q, d) for q in hid], mp.zeros(d, dOut))
    out = []
    for i in range(dIn):
        for j in range(d):
            e = zero(); e[0][i, j] = 1; out.append(e)
    for l, q in enumerate(hid):
        for i in range(d):
            for j in range(g * q):
                e = zero(); e[1][l][i, j] = 1; out.append(e)
        for i in range(q):
            for j in range(d):
                e = zero(); e[2][l][i, j] = 1; out.append(e)
    for i in range(d):
        for j in range(dOut):
            e = zero(); e[3][i, j] = 1; out.append(e)
    return out

def rank(kind, norm, M, th, xs, B):
    J = mp.zeros(len(xs) * th[3].cols, len(B))
    for c, eta in enumerate(B):
        col = []
        for x in xs:
            y = forward(kind, norm, M, th, x, eta)
            col += [y[0, j] for j in range(y.cols)]
        for r_, v in enumerate(col): J[r_, c] = v
    sv = sorted([abs(v) for v in mp.svd_r(J, compute_uv=False)], reverse=True)
    if sv[0] == 0: return 0, (mp.mpf(0), mp.mpf(0))  # the Jacobian is zero (all writes zero, depth 2)
    r = sum(1 for v in sv if v > sv[0] * mp.mpf(10) ** (-25))
    gap = (sv[r - 1] / sv[0], (sv[r] / sv[0]) if r < len(sv) else mp.mpf(0))
    return r, gap

ok = True
CASES = {'tanh': [(2, 2, 2, [3]), (3, 2, 2, [1, 3]), (3, 3, 3, [4, 1])],
         'gelu': [(2, 2, 2, [3]), (2, 2, 3, [2, 2]), (3, 3, 3, [2])],
         'swiglu': [(2, 2, 2, [2]), (3, 2, 2, [1, 2]), (3, 3, 3, [2, 1])]}
for norm in [False, True]:
    for kind in ['tanh', 'gelu', 'swiglu']:
        g = 2 if kind == 'swiglu' else 1
        for (dIn, d, dOut, hid) in CASES[kind]:
            P = dIn * d + sum((g + 1) * d * q for q in hid) + d * dOut
            s = sum(hid) if kind == 'swiglu' else 0
            k = d * (d - 1) // 2 if norm else d * d
            B = basis(((dIn, d), hid, dOut), g)
            assert len(B) == P
            xs = [rnd(1, dIn) for _ in range(P + 6)]
            def draw():
                return (rnd(dIn, d), [rnd(d, g * q) for q in hid], [rnd(q, d) for q in hid], rnd(d, dOut))
            r_res, g_res = rank(kind, norm, 1, draw(), xs, B)
            pts = {'random': draw()}
            e = draw(); pts['E of rank 1'] = (rnd(dIn, 1) * rnd(1, d), e[1], e[2], e[3])
            e = draw(); pts['writes zero'] = (e[0], e[1], [0 * w for w in e[2]], e[3])
            e = draw(); pts['D of rank 1'] = (e[0], e[1], e[2], rnd(d, 1) * rnd(1, dOut))
            line = (f"{'RMSNorm' if norm else 'no norm'} {kind} dIn={dIn} d={d} dOut={dOut} hid={hid} P={P} s={s}: "
                    f"residual rank {r_res} (P-k-s={P - k - s}, gap {mp.nstr(g_res[0], 3)} / {mp.nstr(g_res[1], 3)}); "
                    f"skipless bound P-2k-s={P - 2 * k - s}:")
            good = (r_res == P - k - s)
            for name, eta in pts.items():
                r0, g0 = rank(kind, norm, 0, eta, xs, B)
                line += f" {name} {r0} (gap {mp.nstr(g0[0], 3)} / {mp.nstr(g0[1], 3)});"
                good = good and (r0 <= P - 2 * k - s) and (r0 < r_res)
            print(line, 'OK' if good else 'MISMATCH'); sys.stdout.flush()
            ok = ok and good
print('ALL AS EXPECTED' if ok else 'SOME MISMATCH')
