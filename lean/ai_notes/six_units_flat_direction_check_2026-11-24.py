# Check of the six-unit parameter of the twenty-first audit (part A): the extra direction is flat.
from mpmath import mp, mpf, matrix, sqrt, rand
mp.dps = 60
E = matrix([[2, 1], [1, 3]]); D = matrix([[1, -2], [3, 1]])
c = [(1, 6), (-1, 6), (6, -5), (7, 4), (-7, 4), (-3, -2)]
a = [(6, -1), (6, 1), (mpf(232)/59, mpf(-45)/59), (mpf(-241)/59, mpf(47)/59), (mpf(-61)/13, mpf(-17)/26), (mpf(112)/13, mpf(31)/26)]
C = matrix(2, 6); A = matrix(6, 2)
for i in range(6):
    C[0, i], C[1, i] = c[i]; A[i, 0], A[i, 1] = a[i]
dC = matrix(2, 6); dA = matrix(6, 2)
dC[0, 0] = mpf(1)/6; dC[0, 1] = -mpf(1)/6; dA[0, 1] = mpf(1)/6; dA[1, 1] = -mpf(1)/6
def N0(h):
    s = sqrt((h[0]**2 + h[1]**2) / 2); return matrix([[h[0]/s, h[1]/s]])
def out(x, Cm, Am):
    h0 = x * E; n = N0(h0); pre = n * Cm
    act = matrix(1, 6)
    for i in range(6): act[0, i] = pre[0, i] if pre[0, i] > 0 else 0
    h1 = h0 + act * Am
    return N0(h1) * D, pre
tau = mpf(10)**(-25); worst = 0; bid = 0; nk = 0
for trial in range(400):
    x = matrix([[2*rand()-1, 2*rand()-1]]) * 5
    o0, pre = out(x, C, A)
    if min(abs(pre[0, i]) for i in range(6)) < mpf(10)**(-6): nk += 1; continue
    op, _ = out(x, C + tau*dC, A + tau*dA); om, _ = out(x, C - tau*dC, A - tau*dA)
    der = (op - om) / (2*tau)
    worst = max(worst, abs(der[0, 0]), abs(der[0, 1]))
    # is the block a multiple of the row here?  b(n) parallel to n
    n = N0(x*E); b = (matrix(1, 6))
    act = [max(pre[0, i], 0) for i in range(6)]
    bv = matrix([[sum(act[i]*A[i, 0] for i in range(6)), sum(act[i]*A[i, 1] for i in range(6))]])
    if abs(bv[0, 0]*n[0, 1] - bv[0, 1]*n[0, 0]) < mpf(10)**(-40): bid += 1
print("inputs off the kinks:", 400 - nk, "largest |derivative of the output along the direction|:", mp.nstr(worst, 5))
print("inputs at which the block output is parallel to the row:", bid)
