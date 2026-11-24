# Numeric check of the statement of absorb Theorem 4.2 (iii) as stated in Lean
# (Absorb/ShortSequences.lean, 24 November 2026): causal mask on n tokens, residual network of
# L attention blocks, skipless network of L' + 1 blocks, n <= L or (n = L + 1 and L <= L').
# Construction: zero scores, two heads of dimension one per block, model dimension m + 2.
import numpy as np
from numpy.polynomial import polynomial as Pn
rng = np.random.default_rng(3)

def causalU(n):
    U = np.zeros((n, n))
    for t in range(n):
        U[t, :t + 1] = 1.0 / (t + 1)
    return U

def poly_short(n, L, Lp):  # returns coefficients of Q (low to high), gamma
    z = np.array([1.0 / (t + 1) for t in range(n)])
    vals = z ** (Lp + 1)
    if n == 0:
        return np.array([1.0]), 1.0
    # Lagrange interpolant of z^(Lp+1) at the nodes: degree < n
    V = np.vander(z, n, increasing=True)
    P = np.linalg.solve(V, vals)
    if n <= L:
        prod = np.array([1.0])
        for t in range(n):
            prod = Pn.polymul(prod, np.array([1.0, -(t + 1.0)]))
        Q = Pn.polyadd(P, (1 - P[0]) * prod)
        return Q, 1.0
    else:  # n = L + 1, L <= Lp
        assert abs(P[0]) > 1e-12
        return P / P[0], 1.0 / P[0]

def nets(n, L, Lp, m, a, b):
    d = m + 2; din = a + 1; dout = b + 1
    U = causalU(n)
    Q, gam = poly_short(n, L, Lp)
    Q = np.trim_zeros(Q, 'b') if np.any(np.abs(Q) > 0) else Q
    assert len(Q) - 1 <= L and abs(Q[0] - 1) < 1e-9
    for t in range(n):
        zt = 1.0 / (t + 1)
        assert abs(Pn.polyval(zt, Q) - gam * zt ** (Lp + 1)) < 1e-9 * max(1, abs(gam))
    roots = Pn.polyroots(Q) if len(Q) > 1 else np.array([])
    c = [-1.0 / r for r in roots] + [0.0] * (L - len(roots))
    Pi = np.zeros((d, d)); Pi[0, 0] = Pi[1, 1] = 1
    J = np.zeros((d, d)); J[0, 1] = -1; J[1, 0] = 1
    Vs = [np.real(ci) * Pi + np.imag(ci) * J for ci in c]
    E = np.zeros((din, d)); E[0, 0] = 1
    w = rng.normal(size=dout); D = np.zeros((d, dout)); D[0, :] = w
    def res(X):
        h = X @ E
        for V in Vs:
            h = h + U @ h @ V
        return h @ D
    def skl(X):
        h = X @ E
        for l in range(Lp + 1):
            h = U @ h @ ((gam if l == 0 else 1.0) * Pi)
        return h @ D
    return res, skl, E, D, gam, din

worst = 0.0; cases = 0
for n in range(1, 6):
    for L in range(0, 6):
        for Lp in range(0, 6):
            if not (n <= L or (n == L + 1 and L <= Lp)):
                continue
            for m in (0, 2):
                res, skl, E, D, gam, din = nets(n, L, Lp, m, 1, 2)
                X = rng.normal(size=(n, din))
                r, s = res(X), skl(X)
                scale = max(1.0, np.abs(s).max())
                worst = max(worst, np.abs(r - s).max() / scale)
                assert np.abs(E @ D).max() > 0 and gam != 0
                X0 = np.zeros((n, din)); X0[0, 0] = 1
                assert np.abs(res(X0)).max() > 1e-9   # not the zero function
                cases += 1
print('cases', cases, 'largest relative difference', worst)

# The remark after the theorem: for n = 2, h - 3 U h = -2 U^2 h
U = causalU(2)
print('n = 2: |1 - 3U + 2U^2| =', np.abs(np.eye(2) - 3 * U + 2 * U @ U).max())

# A degenerate instance for n <= L: V_l = -l Pi for l = 1..n gives the zero function with E D != 0
n, L, d = 3, 4, 2
U = causalU(n); Pi = np.eye(2)
E = np.array([[1.0, 0.0]]); D = np.array([[1.0], [0.0]])
X = rng.normal(size=(n, 1)); h = X @ E
for l in range(1, L + 1):
    h = h + U @ h @ ((-l if l <= n else 0) * Pi)
print('degenerate instance: |output| =', np.abs(h @ D).max(), ' E D =', (E @ D).ravel())
