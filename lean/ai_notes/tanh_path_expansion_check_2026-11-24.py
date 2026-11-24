"""Check of the expansion (43) of the dimension paper (Appendix D.6) and of the real form of its two
leading coefficients, as used in lean/SkipsLean/Depth/StepZeroTanhPath.lean, 24 November 2026.

For orthonormal real rows xi, xi' in R^d, nu = xi + i xi', nub = xi - i xi',
n(t) = (sqrt(d)/2)(t nu + nub/t), a real d x d matrix Z, reads W and a direction eta_W (d x q):
  zdot(n) = (n Z - (<n Z, n>/d) n) W + n eta_W      (equation (20), <u, v> = u v^T without conjugation)
(1) zdot(n(t)) = t^3 c3 + t c1 + c_1/t + c_3/t^3 with, for q(a, b) = <a Z, b>,
    c3  = -(sqrt(d)/8) q(nu, nu) nu W,
    c1  = (sqrt(d)/2) [ nu (Z W + eta_W) - (1/4) ((q(nu,nub) + q(nub,nu)) nu + q(nu,nu) nub) W ],
    c_1 = (sqrt(d)/2) [ nub (Z W + eta_W) - (1/4) ((q(nu,nub) + q(nub,nu)) nub + q(nub,nub) nu) W ],
    c_3 = -(sqrt(d)/8) q(nub, nub) nub W.
(2) q(nu,nu) = (xi Z xi^T - xi' Z xi'^T) + i (xi Z xi'^T + xi' Z xi^T), and
    q(nu,nub) + q(nub,nu) = 2 (xi Z xi^T + xi' Z xi'^T).
(3) <n(t), n(t)> = d, and at real t, n(t) = sqrt(d) ((t + 1/t)/2 xi + i (t - 1/t)/2 xi').
(4) With zeta = exp(-2 s z) and s = +-1: tanh z = s (1 - zeta)/(1 + zeta); and for real r with
    |r - s| < rho/4 <= 1/4, zeta = (s - r)/(s + r) has |zeta| < rho/3 and s (1 - zeta)/(1 + zeta) = r.
Random instances, numpy complex128; the largest absolute error is printed.
"""
import numpy as np
rng = np.random.default_rng(5)
worst = 0.0
for d, q in [(2, 2), (3, 4), (5, 3)]:
    for _ in range(20):
        A = rng.normal(size=(d, 2)); Q, _r = np.linalg.qr(A)
        xi, xip = Q[:, 0], Q[:, 1]
        Z = rng.normal(size=(d, d)); W = rng.normal(size=(d, q)); eW = rng.normal(size=(d, q))
        nu, nub = xi + 1j * xip, xi - 1j * xip
        qf = lambda a, b: (a @ Z) @ b
        sd = np.sqrt(d)
        c3 = -(sd / 8) * qf(nu, nu) * (nu @ W)
        c1 = (sd / 2) * (nu @ (Z @ W + eW) - 0.25 * ((qf(nu, nub) + qf(nub, nu)) * nu + qf(nu, nu) * nub) @ W)
        cm1 = (sd / 2) * (nub @ (Z @ W + eW) - 0.25 * ((qf(nu, nub) + qf(nub, nu)) * nub + qf(nub, nub) * nu) @ W)
        cm3 = -(sd / 8) * qf(nub, nub) * (nub @ W)
        for t in [1.0, 1.7, 3.2, 0.4 + 0.9j, -1.3 + 0.2j]:
            n = (sd / 2) * (t * nu + nub / t)
            zdot = (n @ Z - ((n @ Z) @ n / d) * n) @ W + n @ eW
            worst = max(worst, np.abs(zdot - (t**3 * c3 + t * c1 + cm1 / t + cm3 / t**3)).max())
            worst = max(worst, abs(n @ n - d))
            if np.isreal(t):
                t = float(np.real(t))
                worst = max(worst, np.abs(n - sd * ((t + 1 / t) / 2 * xi + 1j * (t - 1 / t) / 2 * xip)).max())
        worst = max(worst, abs(qf(nu, nu) - ((xi @ Z @ xi - xip @ Z @ xip) + 1j * (xi @ Z @ xip + xip @ Z @ xi))))
        worst = max(worst, abs(qf(nu, nub) + qf(nub, nu) - 2 * (xi @ Z @ xi + xip @ Z @ xip)))
for s in [1.0, -1.0]:
    for _ in range(200):
        z = s * abs(rng.normal()) * 2 + 0.3 * s + 1j * rng.normal() * 3
        zeta = np.exp(-2 * s * z)
        worst = max(worst, abs(np.tanh(z) - s * (1 - zeta) / (1 + zeta)))
        rho = rng.uniform(0.01, 1.0); r = s + rng.uniform(-1, 1) * rho / 4
        zeta = (s - r) / (s + r)
        assert abs(zeta) < rho / 3
        worst = max(worst, abs(s * (1 - zeta) / (1 + zeta) - r))
print("largest absolute error:", worst)
print("ALL AS EXPECTED" if worst < 1e-9 else "MISMATCH")
