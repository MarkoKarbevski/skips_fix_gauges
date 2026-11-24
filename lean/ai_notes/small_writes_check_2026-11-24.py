"""Check of the statements of lean/SkipsLean/Residual/SmallWrites.lean (Lemma A.27 of the skips paper,
blocks without normalization and without biases), 24 November 2026.

For a residual network of L blocks, theta_tau holds tau*W_write in place of every write.
(1) K_tau eta = DF(theta_tau)(eta_E, eta_read/tau, eta_write, eta_D) tends to the formula J_0 of
    `smallWritesLimit` as tau -> 0 (the difference is O(tau)).
(2) rank J_0 on a batch = P - d^2 for tanh blocks and P - d^2 - s for SiLU-gated blocks
    (s = number of hidden units), with a clear gap in the singular values.
(3) rank DF(theta_tau) on the batch is the same for small tau != 0.
Derivatives are exact (forward mode, written out); mpmath with 40 digits.
"""
import mpmath as mp, random, sys
mp.mp.dps = 40
random.seed(7)

def rnd(m, n): return mp.matrix(m, n, ) if False else mp.matrix([[mp.mpf(random.gauss(0, 1)) for _ in range(n)] for _ in range(m)])
def Z(m, n): return mp.zeros(m, n)
def sig(z): return z / (1 + mp.e ** (-z))
def dsig(z):
    s = 1 / (1 + mp.e ** (-z)); return s + z * s * (1 - s)

def act(kind, M):
    """f(M) for one token row M (1 x r); returns 1 x q"""
    if kind == 'tanh':
        return mp.matrix([[mp.tanh(M[0, i]) for i in range(M.cols)]])
    q = M.cols // 2
    return mp.matrix([[sig(M[0, i]) * M[0, q + i] for i in range(q)]])
def dact(kind, M, N):
    """Df(M)[N]"""
    if kind == 'tanh':
        return mp.matrix([[(1 - mp.tanh(M[0, i]) ** 2) * N[0, i] for i in range(M.cols)]])
    q = M.cols // 2
    return mp.matrix([[dsig(M[0, i]) * N[0, i] * M[0, q + i] + sig(M[0, i]) * N[0, q + i] for i in range(q)]])

def forward(kind, th, x, eta=None):
    """value and derivative along eta of the residual network at th = (E, reads, writes, D)"""
    E, R, W, D = th
    h = x * E
    if eta is None:
        for l in range(len(R)):
            h = h + act(kind, h * R[l]) * W[l]
        return h * D
    eE, eR, eW, eD = eta
    dh = x * eE
    for l in range(len(R)):
        pre = h * R[l]
        dpre = dh * R[l] + h * eR[l]
        hn = h + act(kind, pre) * W[l]
        dh = dh + dact(kind, pre, dpre) * W[l] + act(kind, pre) * eW[l]
        h = hn
    return dh * D + h * eD

def J0(kind, th, eta, x):
    E, R, W, D = th; eE, eR, eW, eD = eta
    y = x * (eE * D + E * eD)
    for l in range(len(R)):
        pre = x * E * R[l]
        y = y + (dact(kind, pre, x * E * eR[l]) * W[l] + act(kind, pre) * eW[l]) * D
    return y

def basis(shapes):
    """all unit directions of the parameter space"""
    (din, d), hs, rs, dout = shapes
    out = []
    def zero():
        return [Z(din, d), [Z(d, r) for r in rs], [Z(h, d) for h in hs], Z(d, dout)]
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

def rank_gap(s, r):
    return s[r - 1], (s[r] if r < len(s) else mp.mpf(0))

ok = True
for kind, din, d, dout, hs in (('tanh', 3, 2, 2, [1, 3]), ('tanh', 2, 2, 3, [2, 1, 1]), ('gated', 3, 2, 2, [1, 2]), ('gated', 2, 2, 2, [2, 2])):
    rs = hs if kind == 'tanh' else [2 * h for h in hs]
    th = [rnd(din, d), [rnd(d, r) for r in rs], [rnd(h, d) for h in hs], rnd(d, dout)]
    B = basis(((din, d), hs, rs, dout)); P = len(B)
    s = 0 if kind == 'tanh' else sum(hs)
    expected = P - d * d - s
    X = [rnd(1, din) for _ in range(P + 6)]
    # (2) rank of J_0
    cols0 = [[v for x in X for v in J0(kind, th, e, x)] for e in B]
    sv0 = svals(cols0); a, b = rank_gap(sv0, expected)
    # (1), (3) at small tau
    res = []
    for tau in (mp.mpf('1e-6'), mp.mpf('1e-9')):
        tht = [th[0], th[1], [tau * w for w in th[2]], th[3]]
        colsJ = [[v for x in X for v in forward(kind, tht, x, e)] for e in B]
        colsK = [[v for x in X for v in forward(kind, tht, x, [e[0], [m / tau for m in e[1]], e[2], e[3]])] for e in B]
        diff = max(abs(u - v) for c1, c2 in zip(colsK, cols0) for u, v in zip(c1, c2))
        svJ = svals(colsJ); aj, bj = rank_gap(svJ, expected)
        res.append((tau, diff, aj, bj))
    print(f"{kind} d_in={din} d={d} d_out={dout} hidden={hs}: P={P}, expected rank P-d^2-s={expected}")
    print(f"   J_0: singular value {expected} = {mp.nstr(a, 5)}, next = {mp.nstr(b, 5)}")
    for tau, diff, aj, bj in res:
        print(f"   tau={mp.nstr(tau, 3)}: max|K_tau - J_0| = {mp.nstr(diff, 5)};  J_tau: singular value {expected} = {mp.nstr(aj, 5)}, next = {mp.nstr(bj, 5)}")
    # criteria: a gap of at least 20 orders of magnitude after the expected rank, for J_0 and for J_tau;
    # K_tau - J_0 linear in tau (the same ratio diff/tau at both values of tau, within 1 percent)
    r1, r2 = res[0][1] / res[0][0], res[1][1] / res[1][0]
    ok = ok and b < a * mp.mpf('1e-20') and all(bj < aj * mp.mpf('1e-20') for tau, diff, aj, bj in res) and abs(r1 - r2) < mp.mpf('0.01') * r2
print("ALL AS EXPECTED" if ok else "MISMATCH")
