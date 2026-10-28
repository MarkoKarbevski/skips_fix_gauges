"""One block under pre-RMSNorm: ranks of identity, full learned and triangular learned skips against the counts.
eps > 0 (1e-2): identity P - o - s, full P + d^2 - 2o - s, triangular P + d(d+1)/2 - o - s.
eps -> 0 (1e-12): identity P - (o+1) - s, full P + d^2 - 2(o+1) - s, triangular P + d(d+1)/2 - o - 2 - s.
P is the parameter count of the residual network, o = d(d-1)/2."""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fdim_large import run, S_PER_UNIT

L, d, m = 1, 4, 8
o = d * (d - 1) // 2
for eps in (1e-2, 1e-12):
    for act in ["tanh", "gelu", "relu", "relu2", "reglu", "swiglu"]:
        s = L * m * S_PER_UNIT[act]
        out = []
        for skip in ["id", "full", "tri"]:
            ranks = []
            for seed in range(3):
                res, _ = run(dict(family="one", L=L, d=d, m=m, skip=skip, norm="rms", eps=eps, act=act, seed=seed,
                                  rows_factor=2.0))
                ranks.append(res["rank"]); P = res["P"]
            P0 = P - (d * d if skip == "full" else d * (d + 1) // 2 if skip == "tri" else 0)
            if eps > 1e-6:
                pred = {"id": P0 - o - s, "full": P0 + d * d - 2 * o - s, "tri": P0 + d * (d + 1) // 2 - o - s}[skip]
            else:
                pred = {"id": P0 - (o + 1) - s, "full": P0 + d * d - 2 * (o + 1) - s,
                        "tri": P0 + d * (d + 1) // 2 - o - 2 - s}[skip]
            out.append(f"{skip}: {Counter(ranks).most_common(1)[0][0]}/{pred}{'' if all(r == pred for r in ranks) else ' MISS ' + str(ranks)}")
        print(f"eps={eps:.0e} {act:6s} " + "   ".join(out), flush=True)
