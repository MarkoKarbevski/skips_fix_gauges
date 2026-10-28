"""The queue with hidden widths as in practice: 4 d_model hidden units in vanilla blocks (GELU, ReLU, ReLU^2, tanh), as
in nanoGPT, and int(2/3 * 4 d_model) in gated blocks (SwiGLU, GeGLU, ReGLU), as in Llama without its rounding to a
multiple of 256, which gives a gated block about the parameters of a vanilla one.

Families (python3 make_queue3.py DEEP_L DEEP_D):
  L8    MLP, 8 blocks, d_model = 16
  deep  MLP, DEEP_L blocks, d_model = DEEP_D
  tf    transformer, 4 layers (8 blocks), d_model = 16, 4 heads, 8 tokens; GELU (nanoGPT) and SwiGLU (Llama) MLPs

Starts. Residual networks: N(0, 1/fan_in), writes times 1/sqrt(L) (L blocks), or 1/L for blocks of degree 2 without
normalization, whose residual stream otherwise overflows. MLP networks without skips: looks-linear (fdim_large.build)
for GELU, ReLU and tanh, odd pairs (noise 0.1) for ReLU^2 and the gated blocks, which keeps the directions of the
hidden states from collapsing; transformers without skips: N(0, 1/fan_in). GELU networks without skips are also run
from the Gaussian start, for comparison. Under RMSNorm the batch is sized for d_model - 1 rows per token.
Order: GELU first in all families, then the other activations, the most used first.
"""
import json, math, sys

DEEP_L, DEEP_D = (int(a) for a in sys.argv[1:3])
ACTS = ["gelu", "swiglu", "relu", "relu2", "geglu", "tanh", "reglu"]
TF_ACTS = ["gelu", "swiglu"]
GATED = {"swiglu", "geglu", "reglu"}
DEG2 = {"relu2", "swiglu", "geglu", "reglu"}
LL_OK = {"gelu", "relu", "tanh"}
FAM = {"L8": dict(arch="mlp", L=8, d=16, rows_factor=1.08),
       "deep": dict(arch="mlp", L=DEEP_L, d=DEEP_D, rows_factor=1.15),
       "tf": dict(arch="tf", L=4, d=16, H=4, T=8, rows_factor=1.1)}
SEEDS = [0, 1, 2]


def width(d, act):
    return int(2 * (4 * d) / 3) if act in GATED else 4 * d


def cfg(fam, act, skip, norm, seed, start=None):
    f = dict(FAM[fam])
    blocks = 2 * f["L"] if f["arch"] == "tf" else f["L"]
    c = dict(f, family=fam, m=width(f["d"], act), skip=skip, norm=norm, eps=1e-5, act=act, seed=seed)
    if f["arch"] == "mlp" and skip == "none":
        start = start or ("ll" if act in LL_OK else "pairs")
    start = start or "gauss"
    if skip == "none" and start == "ll":
        c.update(init="ll", ll_noise=0.3)
    elif skip == "none" and start == "pairs":
        c.update(init="pairs", ll_noise=0.1)
    elif skip == "none":
        c.update(branch_scale=1.0)
    else:
        c.update(branch_scale=1 / blocks if (act in DEG2 and norm == "none") else 1 / math.sqrt(blocks))
    return c


def grid(fam, act, seeds=SEEDS):
    return [cfg(fam, act, skip, norm, seed) for seed in seeds for norm in ("none", "rms")
            for skip in ("none", "id", "full", "tri")]


q = []
q += grid("deep", "gelu") + grid("tf", "gelu") + grid("L8", "gelu")
q += [cfg(fam, "gelu", "none", norm, seed, start="gauss") for fam in ("deep", "L8") for seed in SEEDS
      for norm in ("none", "rms")]
q += grid("tf", "swiglu")
for act in ACTS[1:]:
    q += grid("deep", act) + grid("L8", act)
json.dump(q, open("queue3.json", "w"), indent=0)
print(len(q), "runs")
