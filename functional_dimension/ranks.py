"""Ranks of the Jacobian of networks without skip connections, against the bound P - (L+1) dim G - s.

For the paper "On the Functional Dimension of a Family of Analytic Neural Networks": the table of its appendix
"Numerical ranks".
Networks: a linear embedding E, L blocks, a linear readout D, no biases; N is the identity or RMSNorm with eps.
Blocks: tanh, GELU, SwiGLU, GeGLU (one token), and attention with H heads of total width d (T tokens).
The Jacobian of the map from all parameters to the outputs on a batch of Gaussian inputs is formed by
automatic differentiation in double precision. The rank is read at the largest gap of the spectrum, the
largest ratio of two consecutive singular values. For every network the script prints the bound, this rank
and the size of the gap. G is GL(d) without normalization, O(d) for eps > 0 and CO(d) for eps = 0.

Run, from the repository root:  python3 functional_dimension/ranks.py   (about 30 seconds on a CPU)
"""
import math
import sys
import torch

torch.set_default_dtype(torch.float64)


def gelu(z):
    return z * 0.5 * (1.0 + torch.erf(z / math.sqrt(2.0)))


def silu(z):
    return z * torch.sigmoid(z)


def shapes(kind, d_in, d, widths, d_out, heads):
    shp = [(d_in, d)]
    for q in widths:
        if kind in ("tanh", "gelu"):
            shp += [(d, q), (q, d)]
        elif kind in ("swiglu", "geglu"):
            shp += [(d, q), (d, q), (q, d)]
        else:  # attention: q is ignored, heads of width d // heads
            dh = d // heads
            shp += [(heads, d, dh), (heads, d, dh), (heads, d, dh), (heads, dh, d)]
    return shp + [(d, d_out)]


def unpack(vec, shp):
    out, i = [], 0
    for s in shp:
        n = math.prod(s)
        out.append(vec[i:i + n].reshape(s))
        i += n
    return out


def norm(h, eps):
    if eps is None:
        return h
    d = h.shape[-1]
    return h * ((h * h).sum(-1, keepdim=True) / d + eps) ** -0.5


def net(vec, shp, x, kind, eps, L):
    m = unpack(vec, shp)
    h = x @ m[0]
    i = 1
    for _ in range(L):
        n = norm(h, eps)
        if kind == "tanh":
            h = torch.tanh(n @ m[i]) @ m[i + 1]
            i += 2
        elif kind == "gelu":
            h = gelu(n @ m[i]) @ m[i + 1]
            i += 2
        elif kind in ("swiglu", "geglu"):
            gate = silu(n @ m[i]) if kind == "swiglu" else gelu(n @ m[i])
            h = (gate * (n @ m[i + 1])) @ m[i + 2]
            i += 3
        else:
            WQ, WK, WV, WO = m[i:i + 4]
            dh = WQ.shape[-1]
            out = 0.0
            for a in range(WQ.shape[0]):
                scores = (n @ WQ[a]) @ (n @ WK[a]).transpose(-1, -2) / math.sqrt(dh)
                out = out + torch.softmax(scores, dim=-1) @ (n @ WV[a]) @ WO[a]
            h = out
            i += 4
    return norm(h, eps) @ m[i]


def run(kind, d, L, width, eps, seed, heads=1, T=1):
    g = torch.Generator().manual_seed(seed)
    d_in = d_out = d + 2
    shp = shapes(kind, d_in, d, [width] * L, d_out, heads)
    vec = torch.cat([(torch.randn(s, generator=g) / math.sqrt(s[-2])).reshape(-1) for s in shp])
    P = vec.numel()
    dimG = d * d if eps is None else d * (d - 1) // 2 + (1 if eps == 0 else 0)
    if kind in ("tanh", "gelu"):
        s = 0
    elif kind in ("swiglu", "geglu"):
        s = L * width
    else:
        s = 2 * L * heads * (d // heads) ** 2
    bound = P - (L + 1) * dimG - s
    n_in = max(3 * P // (d_out * T) + 8, 40)
    x = torch.randn((n_in, T, d_in), generator=g)
    if T == 1:
        x = x[:, 0, :]
    J = torch.autograd.functional.jacobian(lambda v: net(v, shp, x, kind, eps, L).reshape(-1), vec)
    sv = torch.linalg.svdvals(J)[:P]
    ratios = sv[:-1] / sv[1:].clamp_min(1e-300)
    rank = int(torch.argmax(ratios)) + 1
    return P, bound, rank, float(ratios[rank - 1])


def main():
    cases = []
    for kind in ("tanh", "gelu", "swiglu", "geglu"):
        for eps in (None, 0.1, 0.0):
            for (d, L, width) in ((3, 2, 3), (3, 3, 6), (4, 2, 4), (4, 3, 8)):
                for seed in (0, 1):
                    cases.append((kind, d, L, width, eps, seed, 1, 1))
    for (L, heads) in ((1, 1), (1, 2), (2, 2), (3, 2), (2, 4)):
        for seed in (0, 1):
            cases.append(("attention", 4, L, 0, None, seed, heads, 3))
    groups = {}
    verbose = "-v" in sys.argv
    for (kind, d, L, width, eps, seed, heads, T) in cases:
        P, bound, rank, gap = run(kind, d, L, width, eps, seed, heads, T)
        good = rank == bound and gap > 1e4
        norm_name = "none" if eps is None else "RMSNorm, eps = %g" % eps
        key = (kind, norm_name) if kind != "attention" else (kind, "none, L = %d" % L)
        n, k, worst = groups.get(key, (0, 0, float("inf")))
        groups[key] = (n + 1, k + good, min(worst, gap))
        if verbose or not good:
            extra = "H = %d, T = %d" % (heads, T) if kind == "attention" else "d_hidden = %d" % width
            print("%-9s d = %d  L = %d  %-14s %-18s seed %d   P = %4d  bound = %4d  rank = %4d  gap = %.1e  %s"
                  % (kind, d, L, extra, norm_name, seed, P, bound, rank, gap, "ok" if good else "CHECK"))
            sys.stdout.flush()
    for (kind, norm_name), (n, k, worst) in groups.items():
        print("%-9s %-20s %2d of %2d at the bound, smallest gap %.0e" % (kind, norm_name, k, n, worst))


if __name__ == "__main__":
    main()
