"""At eps -> 0 (eps = 1e-12): ranks of skipless, identity, full learned and triangular learned skips under pre-RMSNorm,
for homogeneous blocks (ReLU, ReLU^2) and a non-homogeneous one (tanh), against the eps = 0 counts:
  skipless, homogeneous:      P - L d^2 - (o + 1) - s   (GL(d) at h_0..h_{L-1}, CO(d) at h_L)
  skipless, other:            P - (L + 1)(o + 1) - s    (CO(d) at every hidden state)
  identity skips:             P - (o + 1) - s
  full learned skips:         P + L d^2 - (L + 1)(o + 1) - s
  triangular learned skips:   P + L d(d+1)/2 - o - (L + 1) - s
with o = d(d-1)/2 and P the parameters of the skipless network."""
import json, sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fdim_large import run

L, d, m = 3, 4, 8
o = d * (d - 1) // 2
rows = []
for act in ["relu", "relu2", "tanh"]:
    s = L * m if act in ("relu", "relu2") else 0
    homog = act in ("relu", "relu2")
    for skip, init in [("none", "gauss"), ("none", "ll"), ("id", "gauss"), ("full", "gauss"), ("tri", "gauss")]:
        if init == "ll" and act == "relu2":
            continue
        ranks, gaps, P = [], [], None
        for seed in range(3):
            cfg = dict(family="chk", L=L, d=d, m=m, skip=skip, norm="rms", eps=1e-12, act=act, seed=seed,
                       init=init, ll_noise=0.3, rows_factor=1.5)
            res, _ = run(cfg)
            ranks.append(res["rank"]); gaps.append(res["gap"]); P = res["P"]
        P0 = P - (L * d * d if skip == "full" else L * d * (d + 1) // 2 if skip == "tri" else 0)
        pred = {"none": P0 - L * d * d - (o + 1) - s if homog else P0 - (L + 1) * (o + 1) - s,
                "id": P0 - (o + 1) - s,
                "full": P0 + L * d * d - (L + 1) * (o + 1) - s,
                "tri": P0 + L * d * (d + 1) // 2 - o - (L + 1) - s}[skip]
        r = Counter(ranks).most_common(1)[0][0]
        rows.append((act, skip, init, P, pred, ranks, [f"{g:.0e}" for g in gaps]))
        print(f"{act:6s} {skip:4s} {init:5s} P={P:4d} eps=0 count {pred:4d}  ranks {ranks}  gaps {[f'{g:.0e}' for g in gaps]}"
              f"  {'match' if all(x == pred for x in ranks) else ''}", flush=True)
json.dump(rows, open("/tmp/claude-0/-home-claude/01d5dd02-d105-5c0c-9608-5a8254b5ab6c/scratchpad/fdim/check_eps0_learned.json", "w"))
