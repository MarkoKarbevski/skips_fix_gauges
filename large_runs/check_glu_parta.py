"""One SwiGLU or GeGLU block (d = 4, m = 8), no normalization, no biases: skipless P - 2d^2 - m, residual P - d^2 - m;
and under RMSNorm (eps = 1e-2) the residual network P - d(d-1)/2 - m. Three seeds each."""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fdim_large import run
for act in ["swiglu", "geglu"]:
    for norm, skips in [("none", ["none", "id"]), ("rms", ["id"])]:
        for skip in skips:
            out = [run(dict(family="one", L=1, d=4, m=8, skip=skip, norm=norm, eps=1e-2, act=act, seed=s,
                            rows_factor=2.0))[0] for s in range(3)]
            print(f"{act:6s} {norm:4s} {skip:4s} ranks {[o['rank'] for o in out]} predicted {out[0]['pred']}", flush=True)
