# Numeric check of the statement `exists_far_frozen_bounds` (Lemma D.11 for real hidden states,
# with the derivative in the hidden state), for SwiGLU (p = 1) and GeGLU (p = 2), at theta-dagger
# with d = 2, three hidden units per block, two blocks, one token.  mpmath, 60 digits.
from mpmath import mp, mpf, matrix, exp, erfc, sqrt, pi, log, diff
mp.dps = 60
mu = mpf(2).sqrt()   # mu, with 1, mu independent over Q
def silu(z): return z/(1+exp(-z))
def gelu(z): return z*(1-erfc(z/sqrt(2))/2)
C = [(mpf(1),mpf(0)),(mpf(0),mpf(1)),(-mu,-mu)]      # gate columns
E = [(mpf(1),mpf(1))]*3                               # value columns
Arow = [(mpf(1),mpf(0)),(mpf(0),mpf(1)),(mpf(1),mpf(1))]  # write rows
ACT = [0,1]
def block(h, gate, frozen, pert=None):
    out = [mpf(0),mpf(0)]
    for j in range(3):
        c = C[j]; e = E[j]; a = Arow[j]
        if pert is not None:  # perturb the weights of this block along a fixed direction
            c = (c[0]+pert*mpf('0.3')*(j+1), c[1]-pert*mpf('0.2'))
            e = (e[0]+pert*mpf('0.1'), e[1]+pert*mpf('0.4')*(j+1))
            a = (a[0]-pert*mpf('0.5'), a[1]+pert*mpf('0.7'))
        z = h[0]*c[0]+h[1]*c[1]; v = h[0]*e[0]+h[1]*e[1]
        if frozen:
            g = z if j in ACT else mpf(0)
        else:
            g = gate(z)
        out[0] += g*v*a[0]; out[1] += g*v*a[1]
    return out
def net(h, gate, frozen, k, pert=None):
    # network after h_k, two blocks, D = I
    for l in range(k, 2):
        h = block(h, gate, frozen, pert)
    return h
def nrm(v): return max(abs(x) for x in v)
H = (mpf(1), mpf(2)); U = (mpf('0.01'), mpf('-0.02'))
for name, gate, p in [('SwiGLU', silu, 1), ('GeGLU', gelu, 2)]:
    for k in [0, 1]:
        print(name, 'k =', k)
        for t in [4, 8, 16]:
            h = (t*(H[0]+U[0]), t*(H[1]+U[1]))
            dv = nrm([a-b for a,b in zip(net(h,gate,False,k), net(h,gate,True,k))])
            # derivative in h along v = (1, -1)
            f = lambda s, fr: net((h[0]+s, h[1]-s), gate, fr, k)
            dh = nrm([diff(lambda s: f(s,False)[i], 0) - diff(lambda s: f(s,True)[i], 0) for i in range(2)])
            # derivative in the weights along the fixed direction
            g = lambda s, fr: net(h, gate, fr, k, pert=s)
            dth = nrm([diff(lambda s: g(s,False)[i], 0) - diff(lambda s: g(s,True)[i], 0) for i in range(2)])
            fmt = lambda x: 'log=%8.2f' % float(log(x)) if x > 0 else 'zero'
            print('  t=%2d  value %s  d/dh %s  d/dtheta %s   (-log/t^p: %.3f %.3f %.3f)' % (
                t, fmt(dv), fmt(dh), fmt(dth),
                float(-log(dv)/t**p), float(-log(dh)/t**p), float(-log(dth)/t**p)))
