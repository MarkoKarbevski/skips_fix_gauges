# Numeric check of the scaling used for Lemma D.12 under pre-RMSNorm (case (+)):
# along a ray n = t*xi, with w~ = t*(W0 + y), w~' = 1_A + x', the left side L of the identity for
# one block equals t^2 * Psi(1/t, y, x') with Psi real-analytic at 1/t = 0.
# Checked: t^-2 * L has a limit as t -> infinity and approaches it like a power series in 1/t
# (successive differences shrink by the factor of t), for a gated block (m = 2) and an MLP block
# (m = 1), one token, d = 2, three hidden units, one block after it, generic Z and eta.
from mpmath import mp, mpf, sqrt, diff, matrix
mp.dps = 50
d = 2; eps = mpf('0.7')
def rms(h):
    r = sqrt((h[0]**2 + h[1]**2)/d + eps); return (h[0]/r, h[1]/r)
import random
random.seed(3)
R = lambda: mpf(random.uniform(-1, 1))
# block k (the one on the ray): gate columns c, value columns e, write rows a; and directions
c = [(R(), R()) for _ in range(3)]; e = [(R(), R()) for _ in range(3)]; a = [(R(), R()) for _ in range(3)]
etac = [(R(), R()) for _ in range(3)]; etae = [(R(), R()) for _ in range(3)]; etaa = [(R(), R()) for _ in range(3)]
Z = [[R(), R()], [R(), R()]]
# the network after the block: one tanh-like analytic block and a readout, with a direction eta'
c2 = [(R(), R()) for _ in range(3)]; a2 = [(R(), R()) for _ in range(3)]
dc2 = [(R(), R()) for _ in range(3)]; da2 = [(R(), R()) for _ in range(3)]
from mpmath import tanh
def B(h, tau=mpf(0)):
    n = rms(h); out = [mpf(0), mpf(0)]
    for j in range(3):
        cj = (c2[j][0] + tau*dc2[j][0], c2[j][1] + tau*dc2[j][1])
        aj = (a2[j][0] + tau*da2[j][0], a2[j][1] + tau*da2[j][1])
        z = n[0]*cj[0] + n[1]*cj[1]
        out[0] += tanh(z)*aj[0]; out[1] += tanh(z)*aj[1]
    n2 = rms(out)
    return n2  # readout D = I
xi = (mpf('0.8'), mpf('0.5'))
dot = lambda u, v: u[0]*v[0] + u[1]*v[1]
def tangent(n):  # n Z - <n Z, n> n / d
    nZ = (n[0]*Z[0][0] + n[1]*Z[1][0], n[0]*Z[0][1] + n[1]*Z[1][1])
    q = dot(nZ, n)/d
    return (nZ[0] - q*n[0], nZ[1] - q*n[1])
def L(t, y, xp, gated):
    n = (t*xi[0], t*xi[1]); nt = tangent(n)
    active = [dot(xi, c[j]) > 0 for j in range(3)]
    v = []; vdot = []
    for j in range(3):
        W0 = dot(xi, c[j]) if active[j] else mpf(0)
        w = t*(W0 + y[j]); wp = (1 if active[j] else 0) + xp[j]
        zg = dot(nt, c[j]) + dot(n, etac[j])
        if gated:
            iota = dot(n, e[j]); zv = dot(nt, e[j]) + dot(n, etae[j])
            v.append(w*iota); vdot.append(wp*zg*iota + w*zv)
        else:
            v.append(w); vdot.append(wp*zg)
    h = (sum(v[j]*a[j][0] for j in range(3)), sum(v[j]*a[j][1] for j in range(3)))
    u = (sum(vdot[j]*a[j][0] + v[j]*etaa[j][0] for j in range(3)),
         sum(vdot[j]*a[j][1] + v[j]*etaa[j][1] for j in range(3)))
    res = []
    for i in range(2):
        dh = diff(lambda s: B((h[0] + s*u[0], h[1] + s*u[1]))[i], 0)
        dth = diff(lambda s: B(h, s)[i], 0)
        res.append(dh + dth)
    return res
y = [mpf('0.01'), mpf('-0.02'), mpf('0.015')]; xp = [mpf('0.3'), mpf('-0.2'), mpf('0.1')]
for name, gated in [('gated block (m = 2)', True), ('MLP block (m = 1)', False)]:
    print(name)
    prev = None
    for t in [10, 100, 1000, 10000]:
        val = [x/mpf(t)**2 for x in L(mpf(t), y, xp, gated)]
        line = '  t=%6d  t^-2 L = (%s, %s)' % (t, mp.nstr(val[0], 12), mp.nstr(val[1], 12))
        if prev is not None:
            line += '   change: %s' % mp.nstr(max(abs(val[0]-prev[0]), abs(val[1]-prev[1])), 3)
        print(line); prev = val
