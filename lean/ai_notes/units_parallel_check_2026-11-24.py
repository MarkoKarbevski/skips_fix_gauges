# Numeric check of "Lemma B.3 up to a multiple" (UnitsParallel), 24 November 2026.
# Claim: for linearly independent columns c_i in R^n and rows a_i in R^m (q >= 2 units), the
# pairs (psi_c, beta) with  J(x) := sum_i sigma(x c_i) beta_i + sigma'(x c_i) (x psi_c_i) a_i
# parallel to b(x) := sum_i sigma(x c_i) a_i  at every x off the kinks form a space of
# dimension q + 1 (psi_c_i = lam_i c_i, beta_i = (c0 - k lam_i) a_i), for ReLU (k=1), ReLU^2 (k=2).
# The condition J(x) ^ b(x) = 0 (all 2x2 minors) is linear in (psi_c, beta).
import numpy as np
rng = np.random.default_rng(7)
def check(n, m, q, k, npts=400):
    c = rng.standard_normal((q, n)); a = rng.standard_normal((q, m))
    rows = []
    nun = q * n + q * m
    for _ in range(npts):
        x = rng.standard_normal(n) * 2
        u = c @ x
        act = (u > 0).astype(float)
        s = act * u ** k; sp = act * k * u ** (k - 1)
        b = s @ a
        # J = sum_i s_i beta_i + sp_i (x . psi_c_i) a_i ; linear map from unknowns to R^m
        Jmat = np.zeros((m, nun))
        for i in range(q):
            for e in range(m):
                Jmat[e, q * n + i * m + e] += s[i]
            Jmat[:, i * n:(i + 1) * n] += sp[i] * np.outer(a[i], x)
        for e in range(m):
            for f in range(e + 1, m):
                rows.append(Jmat[e] * b[f] - Jmat[f] * b[e])
    M = np.array(rows)
    sv = np.linalg.svd(M, compute_uv=False)
    tol = sv[0] * 1e-9
    null = nun - int((sv > tol).sum())
    gap = sv[sv > tol][-1] / sv[0]
    return null, q + 1, gap
for (n, m, q) in [(2, 2, 2), (3, 3, 3), (4, 3, 2), (3, 4, 2), (4, 4, 4), (5, 3, 3), (3, 3, 1), (2, 2, 1)]:
    for k in (1, 2):
        null, want, gap = check(n, m, q, k)
        print(f"n={n} m={m} q={q} k={k}: solution space {null}, claimed {want} (q >= 2 only), smallest kept sv ratio {gap:.1e}")
