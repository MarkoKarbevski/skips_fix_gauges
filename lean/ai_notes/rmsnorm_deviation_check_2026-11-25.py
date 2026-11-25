"""Check of S Lemma A.2 (ii): for G = c Q, Q orthogonal, a row h with r^2 = |h|^2 / d,
N_eps(h G) = (c sqrt(r^2 + eps) / sqrt(c^2 r^2 + eps)) N_eps(h) Q, so the deviation
|N_eps(hG) - N_eps(h) Q| / |N_eps(h)| is |delta(eps)|, delta = c sqrt(r^2+eps)/sqrt(c^2 r^2+eps) - 1,
and |delta(eps)| - eps/(2 r^2) |1 - c^-2| is O(eps^2) as eps -> 0+ (not as eps -> 0-)."""
from mpmath import mp, mpf, sqrt, matrix, qr, randmatrix, norm
mp.dps = 40
def N(eps, h):
    d = len(h)
    r2 = sum(x * x for x in h) / d
    return [x / sqrt(r2 + eps) for x in h]
def mul(h, M):
    d = len(h)
    return [sum(h[i] * M[i, j] for i in range(d)) for j in range(d)]
d = 4
Q, _ = qr(randmatrix(d, d))
h = [mpf(3) / 7, mpf(-2) / 3, mpf(5) / 4, mpf(1) / 9]
r2 = sum(x * x for x in h) / d
for c in [mpf(1) / 3, mpf(2), mpf(-3) / 2]:
    for eps in [mpf(1) / 2, mpf(1) / 100]:
        G = Q * c
        lhs = N(eps, mul(h, G))
        NQ = mul(N(eps, h), Q)
        fac = c * sqrt(r2 + eps) / sqrt(c * c * r2 + eps)
        err = max(abs(lhs[j] - fac * NQ[j]) for j in range(d))
        dev = sqrt(sum((lhs[j] - NQ[j]) ** 2 for j in range(d))) / sqrt(sum(x * x for x in N(eps, h)))
        print('c =', float(c), 'eps =', float(eps), ': identity error %.1e' % float(err),
              '; deviation - |delta| = %.1e' % float(dev - abs(fac - 1)))
for c in [mpf(1) / 3, mpf(2), mpf(1)]:
    print('c =', float(c), 'r^2 =', float(r2))
    for s in [1, -1]:
        out = []
        for k in [2, 4, 6, 8]:
            eps = s * mpf(10) ** (-k)
            delta = c * sqrt(r2 + eps) / sqrt(c * c * r2 + eps) - 1
            out.append(float((abs(delta) - eps / (2 * r2) * abs(1 - c ** (-2))) / eps ** 2))
        print('   eps -> 0%s: (|delta| - eps/(2 r^2)|1 - c^-2|) / eps^2 =' % ('+' if s > 0 else '-'),
              ['%.4g' % x for x in out])
