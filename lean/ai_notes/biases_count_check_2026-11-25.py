"""Check for `Symmetry/BiasesFlat.lean` (S Lemma A.8, the count): the rank of the Jacobian in the
weights and biases of tanh networks with biases, one token, on a batch of random inputs
(derivatives by complex step, 40 digits).
Expected: residual  P - d^2 - (L+1) d;  skipless  P - (L+1)(d^2 + d);  P counts the biases.
"""
import mpmath as mp, random
mp.mp.dps = 40
random.seed(5)

def shapes(din, d, dout, widths):
    s = [('E', din, d), ('bE', 1, d)]
    for m in widths:
        s += [('R', d, m), ('bR', 1, m), ('W', m, d), ('bW', 1, d)]
    s += [('D', d, dout), ('bD', 1, dout)]
    return s

def unpack(vec, sh):
    out, k = [], 0
    for (_, r, c) in sh:
        M = mp.matrix(r, c)
        for i in range(r):
            for j in range(c):
                M[i, j] = vec[k]; k += 1
        out.append(M)
    return out

def net(x, vec, sh, L, skip):
    mats = unpack(vec, sh)
    h = x * mats[0] + mats[1]
    for l in range(L):
        R, bR, W, bW = mats[2 + 4 * l: 6 + 4 * l]
        h = (h if skip else 0 * h) + ((h * R + bR).apply(mp.tanh) * W + bW)
    return h * mats[-2] + mats[-1]

def rank(vec, sh, L, skip, din, dout, nb):
    P = len(vec); X = [mp.matrix([[mp.mpf(random.gauss(0, 1)) for _ in range(din)]]) for _ in range(nb)]
    J = mp.matrix(nb * dout, P); st = mp.mpf(10) ** (-25)
    for q in range(P):
        v = list(vec); v[q] = v[q] + mp.mpc(0, st)
        for b, x in enumerate(X):
            y = net(x, v, sh, L, skip)
            for j in range(dout):
                J[b * dout + j, q] = mp.im(y[0, j]) / st
    s = mp.svd_r(J, compute_uv=False)
    r = sum(1 for k in range(len(s)) if s[k] > mp.mpf(10) ** (-18) * s[0])
    return r, mp.nstr(s[r - 1] / s[0], 3), mp.nstr(s[r] / s[0], 3) if r < len(s) else '0'

for (din, d, dout, widths) in [(2, 2, 2, [2, 3]), (2, 2, 2, [3]), (3, 2, 2, [2, 2])]:
    sh = shapes(din, d, dout, widths); L = len(widths)
    P = sum(r * c for (_, r, c) in sh)
    vec = [mp.mpf(random.gauss(0, 1)) for _ in range(P)]
    r1 = rank(vec, sh, L, True, din, dout, P // dout + 4)
    r0 = rank(vec, sh, L, False, din, dout, P // dout + 4)
    print("d=%d L=%d widths=%s d_in=%d d_out=%d P=%d | residual rank %d (expected %d; gap %s, %s) | skipless rank %d (expected %d; gap %s, %s)"
          % (d, L, widths, din, dout, P, r1[0], P - d * d - (L + 1) * d, r1[1], r1[2], r0[0], P - (L + 1) * (d * d + d), r0[1], r0[2]))
