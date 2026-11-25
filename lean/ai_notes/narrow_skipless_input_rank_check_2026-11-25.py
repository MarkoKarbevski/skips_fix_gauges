"""Check for `Residual/FewerHiddenUnitsNarrow.lean` (S Theorem A.28 (iii), skipless blocks with
fewer than d hidden units).

(1) Residual network of GELU blocks, one token: the Jacobian of the output with respect to the
    input at x = 0 is  E prod_l (I + gelu'(0) W_read^l W_write^l) D,  gelu'(0) = 1/2.
(2) Skipless network of GELU blocks with one block of m' < d hidden units: the Jacobian with
    respect to the input has rank at most m' at every input.
(3) Several tokens: an MLP block acts on every token, so the ranks are multiplied by |T|.
Derivatives by complex step (GELU is entire), 50 digits.
"""
import mpmath as mp
mp.mp.dps = 50
import random
random.seed(7)

def gelu(z):
    return z * (1 + mp.erf(z / mp.sqrt(2))) / 2

def rnd(m, n):
    return mp.matrix([[mp.mpf(random.gauss(0, 1)) for _ in range(n)] for _ in range(m)])

def net(x, E, blocks, D, skip):
    h = x * E
    for (R, W) in blocks:
        a = (h * R).apply(gelu)
        h = (h if skip else 0 * h) + a * W
    return h * D

def jac_x(x, E, blocks, D, skip):
    din, dout = E.rows, D.cols
    J = mp.matrix(din, dout)
    hstep = mp.mpf(10) ** (-30)
    for i in range(din):
        xp = x.copy(); xp[0, i] += mp.mpc(0, hstep)
        y = net(xp, E, blocks, D, skip)
        for j in range(dout):
            J[i, j] = mp.im(y[0, j]) / hstep
    return J

def rank(M, tol=mp.mpf(10) ** (-25)):
    s = mp.svd_r(M, compute_uv=False)
    return sum(1 for k in range(len(s)) if s[k] > tol * max(1, s[0]))

d, din, dout = 3, 4, 5
widths = [2, 4, 3]
E, D = rnd(din, d), rnd(d, dout)
blocks = [(rnd(d, m), rnd(m, d)) for m in widths]
# (1)
J = jac_x(mp.zeros(1, din), E, blocks, D, True)
P = mp.eye(d)
for (R, W) in blocks:
    P = P * (mp.eye(d) + R * W / 2)
F = E * P * D
print("(1) max |J - E prod(I + R W / 2) D| =", mp.nstr(max(abs(J[i, j] - F[i, j])
      for i in range(din) for j in range(dout)), 5), " rank J =", rank(J), " d =", d)
# (2)
for trial in range(3):
    x = rnd(1, din)
    Js = jac_x(x, E, blocks, D, False)
    print("(2) skipless, widths", widths, ": rank of the input Jacobian at a random input =",
          rank(Js), " smallest width =", min(widths))
# a skipless network whose blocks all have at least d units, for comparison
blocks2 = [(rnd(d, m), rnd(m, d)) for m in [3, 4, 3]]
print("    skipless, widths [3, 4, 3]: rank =", rank(jac_x(rnd(1, din), E, blocks2, D, False)))
