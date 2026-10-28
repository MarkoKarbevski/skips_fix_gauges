"""One block (d = 4, m = 8) under pre-RMSNorm at eps = 1e-12, without skips and with identity skips.
Predicted for eps -> 0: homogeneous blocks (ReLU, ReLU^2, ReGLU) P - d^2 - (o+1) - s without skips, since the
normalization before the block drops out; other blocks P - 2(o+1) - s; with skips P - (o+1) - s. o = d(d-1)/2."""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fdim_large import run, S_PER_UNIT
d, m = 4, 8
o = d * (d - 1) // 2
for act in ["relu", "relu2", "reglu", "tanh", "gelu", "swiglu"]:
    s = m * S_PER_UNIT[act]
    hom = act in ("relu", "relu2", "reglu")
    for skip in ["none", "id"]:
        outs = [run(dict(family="one", L=1, d=d, m=m, skip=skip, norm="rms", eps=1e-12, act=act, seed=sd,
                         rows_factor=2.0))[0] for sd in range(3)]
        P = outs[0]["P"]
        pred = (P - d * d - (o + 1) - s if hom else P - 2 * (o + 1) - s) if skip == "none" else P - (o + 1) - s
        print(f"{act:6s} {skip:4s} ranks {[x['rank'] for x in outs]}  predicted {pred}  gaps {[round(x['gap'],1) for x in outs]}", flush=True)
