"""Lemma A.2 without floating-point floor: for the same 8-block networks and inputs as almost_sym_fast.py, the largest
singular value of the Jacobian on the directions at each h_l, from the formula of part (b) (J eta_S = a_S(x) y(x)),
over the orthonormalized directions, relative to s_1 of the whole Jacobian. Results to formula_curves.json."""
import json, math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import torch
from torch.func import jvp, vjp
from fdim_large import build, GATED, ACTS
torch.set_default_dtype(torch.float64)
d, L, B = 16, 8, 256
EPS = [1e-1, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8, 1e-10, 1e-12]
NETS = [("relu", "ll", 64, 1), ("relu2", "pairs", 64, 2), ("reglu", "pairs", 42, 2)]
iu = torch.triu_indices(d, d)
basis = []
for i, j in zip(*iu.tolist()):
    S = torch.zeros(d, d); S[i, j] = S[j, i] = 1.0
    basis.append(S / S.norm())
S1 = {json.loads(l)["key"]: json.loads(l)["s1"] for l in open("almost_sym.jsonl")}
out = {}
for act, init, m, k in NETS:
    for eps in EPS:
        if f"{act}_{eps:g}" not in S1:
            continue
        theta, f = build(d, m, L, d, d, "none", "rms", act, 0, eps, init=init, ll_noise=0.3 if init == "ll" else 0.1)
        units = 2 * m if act in GATED else m
        names = [("E", (d, d))] + sum([[(f"U{l}", (d, units)), (f"W{l}", (m, d))] for l in range(L)], []) + [("D", (d, d))]
        sl, o = {}, 0
        for n_, sh in names:
            n = math.prod(sh); sl[n_] = (o, o + n, sh); o += n
        P = o
        get = lambda t, n_: t[sl[n_][0]:sl[n_][1]].view(sl[n_][2])
        X = torch.randn(B, d, generator=torch.Generator().manual_seed(10_000))
        F = lambda t: torch.vmap(f, in_dims=(None, 0))(t, X)
        Y = F(theta)
        N = lambda h: h * torch.rsqrt((h * h).mean(-1, keepdim=True) + eps)
        a = ACTS[act]; hs = [X @ get(theta, "E")]
        for l in range(L):
            z = N(hs[-1]) @ get(theta, f"U{l}")
            hs.append((a(z[..., :m]) * z[..., m:] if act in GATED else a(z)) @ get(theta, f"W{l}"))
        r2 = [(h * h).mean(-1) for h in hs]
        s1 = S1[f"{act}_{eps:g}"]                                   # s_1 from the autodiff run, same network and inputs
        res = []
        for l in range(L):
            wname = "E" if l == 0 else f"W{l - 1}"
            etas, cols = [], []
            later = torch.ones(B)
            for i in range(l + 1, L + 1):
                later = later * eps / (r2[i] + eps)
            for S in basis:
                eta = torch.zeros(P)
                eta[sl[wname][0]:sl[wname][1]] = (get(theta, wname) @ S).reshape(-1)
                eta[sl[f"U{l}"][0]:sl[f"U{l}"][1]] = (-S @ get(theta, f"U{l}")).reshape(-1)
                etas.append(eta)
                coef = -(k ** (L - l)) * ((hs[l] @ S) * hs[l]).sum(-1) / (d * (r2[l] + eps)) * later
                cols.append((coef[:, None] * Y).reshape(-1))
            _, R = torch.linalg.qr(torch.stack(etas, 1))
            C = torch.stack(cols, 1)
            JQ = torch.linalg.solve_triangular(R, C.T, upper=True, left=True).T if False else C @ torch.linalg.inv(R)
            res.append(float(torch.linalg.svdvals(JQ)[0]) / s1)
        out[f"{act}_{eps:g}"] = dict(act=act, eps=eps, s1=s1, smax_rel=res)
        print(act, f"{eps:.0e}", " ".join(f"{math.log10(x):7.1f}" for x in res), flush=True)
json.dump(out, open("formula_curves.json", "w"))
