"""Numerical check of the Lean statements of Lemma C.3 for GELU and for GeGLU
(dimension paper, Appendix C), before they are given to be proved.

G(phi, x) = x M + gamma + sum_i sigma(x c_i + beta_i) a_i               (GELU)
G(phi, x) = x M + gamma + sum_i sigma(x c_i + beta_i)(x e_i + beta'_i) a_i   (GeGLU)

The derivative of G along psi is linear in psi. We stack it at many inputs x and compute the
dimension of its kernel: 0 for GELU, the number q of hidden units for GeGLU (the rescalings
of the values). For GeGLU we also take (e_i, beta'_i) proportional to (c_i, beta_i), the case
that the paper excludes, and e_i = 0, the case that the Lean statement excludes.
"""
import mpmath as mp

mp.mp.dps = 60
Phi = lambda z: mp.ncdf(z)
phi = lambda z: mp.npdf(z)
gelu = lambda z: z * Phi(z)
dgelu = lambda z: Phi(z) + z * phi(z)


def rnd(*shape, seed=[0]):
    seed[0] += 1
    mp.mp.dps = 60
    import random
    r = random.Random(seed[0])
    if len(shape) == 1:
        return [mp.mpf(r.uniform(-1, 1)) for _ in range(shape[0])]
    return [[mp.mpf(r.uniform(-1, 1)) for _ in range(shape[1])] for _ in range(shape[0])]


def dot(u, v):
    return sum(ui * vi for ui, vi in zip(u, v))


def kernel_dim(n, k, q, gated, mode="generic", npts=None):
    c = rnd(q, n); beta = rnd(q); a = rnd(q, k)
    e = rnd(q, n); betap = rnd(q)
    if mode == "proportional":      # (e_i, beta'_i) = r_i (c_i, beta_i)
        r = rnd(q)
        e = [[r[i] * c[i][m] for m in range(n)] for i in range(q)]
        betap = [r[i] * beta[i] for i in range(q)]
    if mode == "e_zero":            # e_0 = 0, beta'_0 != 0
        e[0] = [mp.mpf(0)] * n
    # unknowns: psiM (n k), psigamma (k), psic (q n), psibeta (q), psia (q k), [psie (q n), psibeta' (q)]
    nun = n * k + k + q * n + q + q * k + (q * n + q if gated else 0)
    npts = npts or (nun // k + 12)
    import random
    R = random.Random(12345)
    rows = []
    for _ in range(npts):
        x = [mp.mpf(R.uniform(-3, 3)) for _ in range(n)]
        for o in range(k):
            row = [mp.mpf(0)] * nun
            off = 0
            for m in range(n):                      # x psiM
                row[off + m * k + o] = x[m]
            off += n * k
            row[off + o] = mp.mpf(1)                # psigamma
            off += k
            oc, ob, oa = off, off + q * n, off + q * n + q
            oe, obp = oa + q * k, oa + q * k + q * n
            for i in range(q):
                z = dot(x, c[i]) + beta[i]
                w = (dot(x, e[i]) + betap[i]) if gated else mp.mpf(1)
                for m in range(n):
                    row[oc + i * n + m] = dgelu(z) * x[m] * w * a[i][o]
                row[ob + i] = dgelu(z) * w * a[i][o]
                row[oa + i * k + o] = gelu(z) * w
                if gated:
                    for m in range(n):
                        row[oe + i * n + m] = gelu(z) * x[m] * a[i][o]
                    row[obp + i] = gelu(z) * a[i][o]
            rows.append(row)
    J = mp.matrix(rows)
    s = mp.svd_r(J, compute_uv=False)
    s = sorted([s[i] for i in range(len(s))], reverse=True)
    small = [x for x in s if x < s[0] * mp.mpf(10) ** (-25)]
    gap = (s[len(s) - len(small) - 1] / s[0]) if len(small) < len(s) else None
    return nun, len(small), mp.nstr(gap, 5), (mp.nstr(small[0] / s[0], 5) if small else "-")


if __name__ == "__main__":
    print("unknowns, kernel dimension, smallest nonzero singular value / largest, largest 'zero' one / largest")
    for (n, k, q) in [(2, 1, 1), (2, 2, 3), (3, 2, 4), (3, 1, 5)]:
        print("GELU   n,k,q =", (n, k, q), kernel_dim(n, k, q, gated=False), " expected kernel 0")
    for (n, k, q) in [(2, 1, 1), (2, 2, 3), (3, 2, 4)]:
        print("GeGLU  n,k,q =", (n, k, q), kernel_dim(n, k, q, gated=True), " expected kernel", q)
        print("GeGLU  proportional (e,b') = r (c,b):", kernel_dim(n, k, q, gated=True, mode="proportional"), " expected kernel", q)
        print("GeGLU  with e_0 = 0:", kernel_dim(n, k, q, gated=True, mode="e_zero"))
