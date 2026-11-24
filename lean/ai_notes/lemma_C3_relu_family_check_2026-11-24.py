"""Numerical check of the Lean statements of Lemma C.3 for ReLU, ReLU^2 and ReGLU
(dimension paper, Appendix C), before they are given to be proved.

G(phi, x) = x M + gamma + sum_i sigma(z_i) a_i,  z_i = x c_i + beta_i            (ReLU, ReLU^2)
G(phi, x) = x M + gamma + sum_i sigma(z_i) (x e_i + beta'_i) a_i                 (ReGLU)

The derivative of G along psi is linear in psi. It is stacked at many inputs x, none of them at a
kink, and the dimension of its kernel is computed (singular values in double precision; inputs and weights are rationals):
q for ReLU and for ReLU^2 (one rescaling per hidden unit), 2q for ReGLU.
For ReGLU also: (e_i, beta'_i) proportional to (c_i, beta_i), the case the lemma excludes.
"""
import random
from fractions import Fraction as Fr
import numpy as np


def kernel_dim(n, k, q, kind, mode="generic", seed=1, npts=None):
    R = random.Random(seed)
    rnd = lambda: Fr(R.randint(-9, 9), R.randint(1, 5))
    nz = lambda: Fr(R.choice([-1, 1]) * R.randint(1, 9), R.randint(1, 5))
    c = [[nz() for _ in range(n)] for _ in range(q)]
    beta = [rnd() for _ in range(q)]
    a = [[nz() for _ in range(k)] for _ in range(q)]
    e = [[nz() for _ in range(n)] for _ in range(q)]
    betap = [rnd() for _ in range(q)]
    if mode == "proportional":
        r = [nz() for _ in range(q)]
        e = [[r[i] * c[i][m] for m in range(n)] for i in range(q)]
        betap = [r[i] * beta[i] for i in range(q)]
    gated = kind == "reglu"
    nun = n * k + k + q * n + q + q * k + (q * n + q if gated else 0)
    npts = npts or 40 * nun
    if kind == "relusq":
        s = lambda z: max(z, 0) ** 2
        ds = lambda z: 2 * max(z, 0)
    else:
        s = lambda z: max(z, 0)
        ds = lambda z: Fr(1) if z > 0 else Fr(0)
    rows = []
    while len(rows) < npts * k:
        x = [Fr(R.randint(-60, 60), 7) for _ in range(n)]
        z = [sum(x[m] * c[i][m] for m in range(n)) + beta[i] for i in range(q)]
        if any(zi == 0 for zi in z):
            continue
        for o in range(k):
            row = [Fr(0)] * nun
            off = 0
            for m in range(n):
                row[off + m * k + o] = x[m]
            off += n * k
            row[off + o] = Fr(1)
            off += k
            oc, ob, oa = off, off + q * n, off + q * n + q
            oe, obp = oa + q * k, oa + q * k + q * n
            for i in range(q):
                w = (sum(x[m] * e[i][m] for m in range(n)) + betap[i]) if gated else Fr(1)
                for m in range(n):
                    row[oc + i * n + m] = ds(z[i]) * x[m] * w * a[i][o]
                row[ob + i] = ds(z[i]) * w * a[i][o]
                row[oa + i * k + o] = s(z[i]) * w
                if gated:
                    for m in range(n):
                        row[oe + i * n + m] = s(z[i]) * x[m] * a[i][o]
                    row[obp + i] = s(z[i]) * a[i][o]
            rows.append(row)
    J = np.array([[float(v) for v in row] for row in rows])
    s = np.linalg.svd(J, compute_uv=False)
    small = int((s < s[0] * 1e-9).sum()) + (nun - len(s) if len(s) < nun else 0)
    gap = s[nun - small - 1] / s[0] if small < nun else float("nan")
    return nun, small, float("%.2e" % gap), (float("%.1e" % (s[nun - small] / s[0])) if small else "-")


if __name__ == "__main__":
    print("(unknowns, kernel dimension, smallest nonzero singular value / largest, largest zero one / largest)")
    for (n, k, q) in [(1, 1, 1), (2, 1, 2), (2, 2, 3), (3, 2, 4)]:
        print("ReLU    n,k,q =", (n, k, q), kernel_dim(n, k, q, "relu"), " expected kernel", q)
        print("ReLU^2  n,k,q =", (n, k, q), kernel_dim(n, k, q, "relusq"), " expected kernel", q)
    for (n, k, q) in [(1, 1, 1), (2, 1, 2), (2, 2, 3)]:
        print("ReGLU   n,k,q =", (n, k, q), kernel_dim(n, k, q, "reglu"), " expected kernel", 2 * q)
        print("ReGLU   proportional (e,b') = r (c,b):", kernel_dim(n, k, q, "reglu", mode="proportional"),
              " (excluded by the lemma)")
