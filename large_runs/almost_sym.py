"""Lemma lem:homrms in the 8-block skipless networks of the large runs (d = 16, pre-RMSNorm), seed 0, 256 inputs.
For each hidden state h_l read by a block, the d(d+1)/2 directions G = e^{tS}, S symmetric: (1) the derivative of the
outputs along them by autodiff against the formula of the lemma; (2) the largest singular value of the Jacobian on
these directions (orthonormalized in parameter space), relative to the largest singular value s_1 of the whole
Jacobian, for eps from 1e-1 to 1e-12. Results to almost_sym.json."""
import json, math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, torch
from torch.func import jvp, vjp
from fdim_large import build, GATED, ACTS
torch.set_default_dtype(torch.float64)
d, L, B = 16, 8, 256
EPS = [1e-1, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8, 1e-10, 1e-12]
NETS = [("relu", "ll", 64, 1), ("relu2", "pairs", 64, 2), ("reglu", "pairs", 42, 2), ("gelu", "ll", 64, None)]
iu = torch.triu_indices(d, d)
basis = []
for i, j in zip(*iu.tolist()):
    S = torch.zeros(d, d); S[i, j] = S[j, i] = 1.0 if i != j else 1.0
    basis.append(S / S.norm())
out = {}
done = set()
if os.path.exists("almost_sym.jsonl"):
    done = {json.loads(l)["key"] for l in open("almost_sym.jsonl")}
for act, init, m, k in NETS:
    for eps in EPS:
        if f"{act}_{eps:g}" in done:
            continue
        noise = 0.3 if init == "ll" else 0.1
        theta, f = build(d, m, L, d, d, "none", "rms", act, 0, eps, init=init, ll_noise=noise)
        units = 2 * m if act in GATED else m
        names = [("E", (d, d))] + sum([[(f"U{l}", (d, units)), (f"W{l}", (m, d))] for l in range(L)], []) + [("D", (d, d))]
        sl, o = {}, 0
        for n_, sh in names:
            n = math.prod(sh); sl[n_] = (o, o + n, sh); o += n
        P = o
        get = lambda t, n_: t[sl[n_][0]:sl[n_][1]].view(sl[n_][2])
        X = torch.randn(B, d, generator=torch.Generator().manual_seed(10_000))
        F = lambda t: torch.vmap(f, in_dims=(None, 0))(t, X)              # (B, q)
        Y = F(theta)
        # hidden states, as in fdim_large.build
        N = lambda h: h * torch.rsqrt((h * h).mean(-1, keepdim=True) + eps)
        a = ACTS[act]; hs = [X @ get(theta, "E")]
        for l in range(L):
            z = N(hs[-1]) @ get(theta, f"U{l}")
            hs.append((a(z[..., :m]) * z[..., m:] if act in GATED else a(z)) @ get(theta, f"W{l}"))
        r2 = [(h * h).mean(-1) for h in hs]
        # s_1 of the whole Jacobian, by power iteration with jvp and vjp
        v = torch.randn(P, generator=torch.Generator().manual_seed(1)); v /= v.norm()
        _, pull = vjp(F, theta)
        for _ in range(40):
            Jv = jvp(F, (theta,), (v,))[1]
            w = pull(Jv)[0]; s1 = math.sqrt(float(w.norm())); v = w / w.norm()
        res = []
        for l in range(L):
            wname = "E" if l == 0 else f"W{l - 1}"
            etas, rel = [], []
            for S in basis:
                eta = torch.zeros(P)
                eta[sl[wname][0]:sl[wname][1]] = (get(theta, wname) @ S).reshape(-1)
                eta[sl[f"U{l}"][0]:sl[f"U{l}"][1]] = (-S @ get(theta, f"U{l}")).reshape(-1)
                etas.append(eta)
                if k is not None and len(rel) < 12:                      # the formula of the lemma, on 12 of the S
                    Jeta = jvp(F, (theta,), (eta,))[1]
                    hSh = ((hs[l] @ S) * hs[l]).sum(-1)
                    coef = -(k ** (L - l)) * hSh / (d * (r2[l] + eps))
                    for i in range(l + 1, L + 1):
                        coef = coef * eps / (r2[i] + eps)
                    pred = coef[:, None] * Y
                    if float(pred.norm()) > 1e-9 * float(Jeta.norm() + 1e-300) and float(pred.norm()) > 1e-13 * s1:
                        rel.append(float((Jeta - pred).norm() / pred.norm()))
            Q, _ = torch.linalg.qr(torch.stack(etas, 1))               # orthonormal directions in parameter space
            JQ = torch.vmap(lambda v: jvp(F, (theta,), (v,))[1].reshape(-1))(Q.T).T
            smax = float(torch.linalg.svdvals(JQ)[0])
            res.append(dict(l=l, later=L - l, smax_rel=smax / s1, formula_rel_err=max(rel) if rel else None))
        out[f"{act}_{eps:g}"] = rec = dict(act=act, eps=eps, s1=s1, states=res,
                                    r2_min=[float(r.min()) for r in r2], r2_median=[float(r.median()) for r in r2])
        with open("almost_sym.jsonl", "a") as fh:
            fh.write(json.dumps(dict(rec, key=f"{act}_{eps:g}")) + "\n")
        print(f"{act:5s} eps {eps:7.0e}: s1 {s1:.2e}; log10 smax/s1 by hidden state 0..7: "
              + " ".join(f"{math.log10(max(r['smax_rel'], 1e-300)):6.1f}" for r in res)
              + (f"; formula rel err <= {max([r['formula_rel_err'] for r in res if r['formula_rel_err'] is not None], default=float('nan')):.1e}" if k else ""), flush=True)


