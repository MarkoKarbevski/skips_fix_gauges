"""Check for `Residual/BlocksAlone*.lean` (S Lemma A.27, fourth value, for MLP and gated blocks;
S Theorem A.28 (i)).

Networks without an embedding and a readout (h_0 = x, y = h_L), one token; the parameters are the
reads and the writes, P their number. Rank of the Jacobian in the parameters on a batch:
 (1) residual, GELU blocks:            expected P        (fourth value, s = 0)
 (2) residual, GeGLU blocks (gated):   expected P - s,   s = number of hidden units
 (3) skipless, GELU blocks, L >= 2:    at most P - 1     (expected P - (L - 1) d^2 for widths >= d)
 (4) skipless at a parameter with W_write^1 = 0 and W_read^2 = 0: at most P - 1
Derivatives by complex step (the activations are entire), 40 digits.
"""
import mpmath as mp, random
mp.mp.dps = 40
random.seed(11)

def gelu(z): return z * (1 + mp.erf(z / mp.sqrt(2))) / 2
def rnd(m, n): return mp.matrix([[mp.mpf(random.gauss(0, 1)) for _ in range(n)] for _ in range(m)])

def unpack(vec, d, widths, gated):
    blocks, k = [], 0
    for m in widths:
        rc = 2 * m if gated else m
        R = mp.matrix(d, rc)
        for i in range(d):
            for j in range(rc):
                R[i, j] = vec[k]; k += 1
        W = mp.matrix(m, d)
        for i in range(m):
            for j in range(d):
                W[i, j] = vec[k]; k += 1
        blocks.append((R, W))
    return blocks

def net(x, vec, d, widths, gated, skip):
    h = x
    for (R, W), m in zip(unpack(vec, d, widths, gated), widths):
        z = h * R
        if gated:
            a = mp.matrix(1, m)
            for i in range(m):
                a[0, i] = gelu(z[0, i]) * z[0, m + i]
        else:
            a = z.apply(gelu)
        h = (h if skip else 0 * h) + a * W
    return h

def jac_rank(vec, d, widths, gated, skip, nb):
    P = len(vec)
    X = [rnd(1, d) for _ in range(nb)]
    J = mp.matrix(nb * d, P)
    st = mp.mpf(10) ** (-25)
    for p in range(P):
        v = list(vec); v[p] = v[p] + mp.mpc(0, st)
        for b, x in enumerate(X):
            y = net(x, v, d, widths, gated, skip)
            for j in range(d):
                J[b * d + j, p] = mp.im(y[0, j]) / st
    s = mp.svd_r(J, compute_uv=False)
    if s[0] == 0:
        return 0, (mp.mpf(0), mp.mpf(0))
    r = sum(1 for k in range(len(s)) if s[k] > mp.mpf(10) ** (-18) * s[0])
    gap = (s[r - 1] / s[0], (s[r] / s[0]) if r < len(s) else mp.mpf(0))
    return r, gap

def count(d, widths, gated):
    return sum(d * (2 * m if gated else m) + m * d for m in widths)

for (d, widths) in [(2, [2, 3]), (2, [1, 2]), (3, [3, 3])]:
    P = count(d, widths, False)
    vec = [mp.mpf(random.gauss(0, 1)) for _ in range(P)]
    r, gap = jac_rank(vec, d, widths, False, True, P)
    print("(1) residual GELU  d=%d widths=%s  P=%d  rank=%d  (gap %s, %s)" % (d, widths, P, r, mp.nstr(gap[0], 3), mp.nstr(gap[1], 3)))
    r, gap = jac_rank(vec, d, widths, False, False, P)
    L = len(widths)
    print("(3) skipless GELU  d=%d widths=%s  P=%d  rank=%d  P-(L-1)d^2=%d  (gap %s, %s)" % (d, widths, P, r, P - (L - 1) * d * d, mp.nstr(gap[0], 3), mp.nstr(gap[1], 3)))
d, widths = 2, [2, 2]
P = count(d, widths, True)
vec = [mp.mpf(random.gauss(0, 1)) for _ in range(P)]
r, gap = jac_rank(vec, d, widths, True, True, P)
print("(2) residual GeGLU d=%d widths=%s  P=%d  s=%d  rank=%d  (gap %s, %s)" % (d, widths, P, sum(widths), r, mp.nstr(gap[0], 3), mp.nstr(gap[1], 3)))
# (4) W_write^1 = 0 and W_read^2 = 0
d, widths = 2, [2, 3]
P = count(d, widths, False)
vec = [mp.mpf(random.gauss(0, 1)) for _ in range(P)]
# layout: R1 (d*m1), W1 (m1*d), R2 (d*m2), W2 (m2*d)
m1, m2 = widths
for k in range(d * m1, d * m1 + m1 * d): vec[k] = mp.mpf(0)
for k in range(d * m1 + m1 * d, d * m1 + m1 * d + d * m2): vec[k] = mp.mpf(0)
r, gap = jac_rank(vec, d, widths, False, False, P)
print("(4) skipless GELU with W_write^1 = 0, W_read^2 = 0: P=%d rank=%d" % (P, r))
