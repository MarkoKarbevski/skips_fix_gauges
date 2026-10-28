"""Checks for Theorem C.1(c): learned skips over identity skips under pre-RMSNorm.
1. One GeGLU block (the other MLP blocks are in check_oneblock_learned.py): ranks of identity, full and triangular
   skips at eps = 1e-2 and 1e-12. Expected differences: d(d+1)/2 and d(d+1)/2 - 1.
2. One transformer layer (an attention block and a GELU MLP block, 2 blocks): the same at eps = 1e-2, where the
   expected difference is 2 d(d+1)/2.
Prints rank / predicted rank, and the differences full - id and tri - id."""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fdim_large import run

d = 4
step = d * (d + 1) // 2


def ranks(cfg_base, seeds):
    out = {}
    for skip in ["id", "full", "tri"]:
        rs, preds = [], []
        for seed in seeds:
            res, _ = run(dict(cfg_base, skip=skip, seed=seed, rows_factor=2.0))
            rs.append(res["rank"]); preds.append(res["pred"])
        out[skip] = (rs, preds[0])
    return out


def report(name, out, blocks, eps):
    want = blocks * (step if eps > 1e-6 else step - 1)
    rid = out["id"][0]
    line = [f"{name:28s}"]
    for skip in ["id", "full", "tri"]:
        rs, pred = out[skip]
        line.append(f"{skip} {Counter(rs).most_common(1)[0][0]}/{pred}")
    dfull = sorted({a - b for a, b in zip(out["full"][0], rid)})
    dtri = sorted({a - b for a, b in zip(out["tri"][0], rid)})
    line.append(f"full-id {dfull} tri-id {dtri} (expected {want})")
    print("   ".join(line), flush=True)


for eps in (1e-2, 1e-12):
    out = ranks(dict(family="one", L=1, d=d, m=8, norm="rms", eps=eps, act="geglu"), range(3))
    report(f"GeGLU, 1 block, eps={eps:.0e}", out, 1, eps)
out = ranks(dict(arch="tf", family="tf", L=1, d=d, m=8, H=2, T=4, norm="rms", eps=1e-2, act="gelu"), range(2))
report("attention+GELU, eps=1e-02", out, 2, 1e-2)
