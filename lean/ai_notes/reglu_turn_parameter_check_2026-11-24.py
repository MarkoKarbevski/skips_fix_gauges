"""Independent check, 24 November 2026, of the ReGLU parameter of the twenty-second audit (part A)
at which the block does not turn the rows of two sectors: one residual ReGLU block, d = 2, six
hidden units, eps = 0. Exact rational arithmetic.

With v = x E (one token), n = N_0(v) and B(u) = sum_i relu(u.g_i) (u.v_i) a_i (degree 2), the
hidden state is h_1 = v + B(n) = v + (2 / v.v) B(v). The direction psi moves the value column of
unit 1 by (1, 0), row 1 of W_write by (0, 1), the gate column of unit 2 by (-1/6, 0) and row 2 of
W_write by (0, -1/6). Claims checked here:
 (1) on the sectors with active gates {1, 3, 4} and {2, 5, 6}, B(u) is parallel to u;
 (2) at every input off the kinks, the derivative of h_1 along psi is parallel to h_1 (so the
     final normalization removes it and psi is flat);
 (3) psi is not zero on the block: its derivative of B is nonzero at some input.
"""
from fractions import Fraction as F
import random
random.seed(3)
g = [(1, 6), (-1, 6), (6, -5), (7, 4), (-7, 4), (-3, -2)]
v = [(0, 1), (1, 6), (2, -1), (1, 3), (3, 1), (-1, 2)]
a = [(F(1), F(0)), (F(6), F(1)), (F(-17426, 47495), F(2363, 20355)), (F(-9892, 28497), F(-9452, 47495)),
     (F(28624, 1365), F(13064, 1365)), (F(102334, 1365), F(13129, 195))]
dv = {0: (F(1), F(0))}; da = {0: (F(0), F(1)), 1: (F(0), F(-1, 6))}; dg = {1: (F(-1, 6), F(0))}
def dot(x, y): return x[0] * y[0] + x[1] * y[1]
def B(u):
    out = [F(0), F(0)]
    for i in range(6):
        z = dot(u, g[i])
        if z > 0:
            for o in range(2): out[o] += z * dot(u, v[i]) * a[i][o]
    return out
def dB(u):
    out = [F(0), F(0)]
    for i in range(6):
        z = dot(u, g[i])
        if z > 0:
            w = dot(u, v[i])
            zg = dot(u, dg[i]) if i in dg else F(0)
            wv = dot(u, dv[i]) if i in dv else F(0)
            ai = da.get(i, (F(0), F(0)))
            for o in range(2): out[o] += (zg * w + z * wv) * a[i][o] + z * w * ai[o]
    return out
def active(u): return tuple(i + 1 for i in range(6) if dot(u, g[i]) > 0)
det = lambda x, y: x[0] * y[1] - x[1] * y[0]
sectors = {}; par = True; flat = True; nonzero = False; n = 0
while n < 4000:
    u = (F(random.randint(-60, 60), random.randint(1, 9)), F(random.randint(-60, 60), random.randint(1, 9)))
    if any(dot(u, gi) == 0 for gi in g) or u == (0, 0): continue
    n += 1
    s = active(u); sectors[s] = sectors.get(s, 0) + 1
    b = B(u)
    if s in ((1, 3, 4), (2, 5, 6)) and det(u, b) != 0: par = False
    h1 = [u[o] + 2 / dot(u, u) * b[o] for o in range(2)]
    k = [2 / dot(u, u) * e for e in dB(u)]
    if det(h1, k) != 0: flat = False
    if k != [0, 0]: nonzero = True
print('inputs', n, '; sectors met:', len(sectors), sorted(sectors.items()))
print('(1) B(u) parallel to u on the sectors {1,3,4} and {2,5,6}:', par)
print('(2) the derivative of h_1 along psi is parallel to h_1 at every input:', flat)
print('(3) the derivative of the block along psi is not zero at some input:', nonzero)
