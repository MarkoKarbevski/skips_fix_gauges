"""Depths 2 and 4 for the main body, with every setting of the 8-block runs of make_queue3.py (d_model = 16, hidden
width 4 d_model, or int(2/3 * 4 d_model) for gated blocks; starts, write scales and batch sizes as there).
Families L2 and L4; depth 2 first for all activations, then depth 4."""
import json, math

ACTS = ["gelu", "swiglu", "relu", "relu2", "geglu", "tanh", "reglu"]
GATED = {"swiglu", "geglu", "reglu"}
DEG2 = {"relu2", "swiglu", "geglu", "reglu"}
LL_OK = {"gelu", "relu", "tanh"}
SEEDS = [0, 1, 2]


def cfg(L, act, skip, norm, seed, start=None):
    d = 16
    c = dict(arch="mlp", L=L, d=d, rows_factor=1.08, family=f"L{L}", m=int(2 * 4 * d / 3) if act in GATED else 4 * d,
             skip=skip, norm=norm, eps=1e-5, act=act, seed=seed)
    if skip == "none":
        start = start or ("ll" if act in LL_OK else "pairs")
        c.update({"ll": dict(init="ll", ll_noise=0.3), "pairs": dict(init="pairs", ll_noise=0.1),
                  "gauss": dict(branch_scale=1.0)}[start])
    else:
        c.update(branch_scale=1 / L if (act in DEG2 and norm == "none") else 1 / math.sqrt(L))
    return c


q = []
for L in (2, 4):
    for act in ACTS:
        q += [cfg(L, act, skip, norm, seed) for seed in SEEDS for norm in ("none", "rms")
              for skip in ("none", "id", "full", "tri")]
        if act == "gelu":
            q += [cfg(L, "gelu", "none", norm, seed, start="gauss") for seed in SEEDS for norm in ("none", "rms")]
json.dump(q, open("queue4.json", "w"), indent=0)
print(len(q), "runs")
