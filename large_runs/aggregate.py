"""Collect the spectra of fdim_large.py into one .npz, with the statistics over draws that the figures need.

For every network (family, depth L, widths d and m, normalization, skip, activation) the file holds
  <net>_median, <net>_min, <net>_max   log10 of s_i / s_1 at every index i: median, smallest and largest over the draws
  <net>_draws                          the same for every draw, one row per draw (float32)
  <net>_ranks, <net>_gaps              rank read at the largest gap, and that gap, in every draw
  <net>_info                           [P, predicted rank, rows of the Jacobian, inputs]
with <net> = <family>_L<L>_d<d>_m<m>_<norm>_<skip>_<act>[_ll<noise>], <norm> = none or rms<eps>, and the suffix
_ll<noise> for networks started looks-linear (fdim_large.build). Usage: python3 aggregate.py RUN_DIR [RUN_DIR ...] OUT.npz
"""
import json, os, sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fdim_large import key, net_name

*dirs, out = sys.argv[1:]
# one result per run: a run redone after a crash has two lines, and the last one counts; a line cut short by a crash,
# or a run whose spectrum file was never written, is left out
latest = {}
for d in dirs:
    for line in open(os.path.join(d, "results.jsonl")):
        try:
            r = json.loads(line)
        except json.JSONDecodeError:
            continue
        path = os.path.join(d, "spec", key(r) + ".npy")
        if os.path.exists(path):
            latest[key(r)] = (r, path)
runs = defaultdict(list)
for r, path in latest.values():
    runs[net_name(r)].append((r, np.load(path)))
data, meta = {}, {}
for net, items in sorted(runs.items()):
    items.sort(key=lambda t: t[0]["seed"])
    r0 = items[0][0]
    ok = [(r, s) for r, s in items if r.get("finite", True)]   # draws whose signal overflowed have no spectrum
    if ok:
        n = min(len(s) for _, s in ok)
        S = np.stack([s[:n] for _, s in ok]).astype(np.float32)
        data[net + "_median"] = np.median(S, 0).astype(np.float32)
        data[net + "_min"], data[net + "_max"] = S.min(0), S.max(0)
        data[net + "_draws"] = S
    data[net + "_ranks"] = np.array([r["rank"] for r, _ in items])
    data[net + "_gaps"] = np.array([r["gap"] for r, _ in items])
    data[net + "_info"] = np.array([r0["P"], r0["pred"], r0["rows"], r0["B"]])
    meta[net] = {k: r0[k] for k in ("family", "L", "d", "m", "p", "q", "norm", "skip", "act", "eps", "P", "pred",
                                    "rows", "B") if k in r0}
    meta[net].update(branch_scale=r0.get("branch_scale", 1.0), init=r0.get("init", "gauss"),
                     overflowed=sum(not r.get("finite", True) for r, _ in items), arch=r0.get("arch", "mlp"),
                     n_nonfinite=[r.get("n_nonfinite", 0) for r, _ in items],
                     max_abs_out=max(r.get("max_abs_out", float("nan")) for r, _ in items),
                     max_abs_J=max(r.get("max_abs_J", float("nan")) for r, _ in items),
                     H=r0.get("H"), T=r0.get("T"),
                     ll_noise=r0.get("ll_noise"), seeds=[r["seed"] for r, _ in items],
                     ranks=[r["rank"] for r, _ in items], matches=sum(r["match"] for r, _ in items),
                     min_gap=min((r["gap"] for r, _ in ok), default=float("nan")), max_t_svd=max(r["t_svd"] for r, _ in items),
                     max_t_jac=max(r["t_jac"] for r, _ in items), max_rss_gb=max(r["maxrss_gb"] for r, _ in items))
data["meta_json"] = np.array(json.dumps(meta))
np.savez_compressed(out, **data)
for net, m in meta.items():
    nan = f"  NON-FINITE in {m['overflowed']}/{len(m['seeds'])} draws" if m["overflowed"] else ""
    print(f"{net:48s} P={m['P']:6d} pred={m['pred']:6d} ranks={m['ranks']} match {m['matches']}/{len(m['seeds'])} "
          f"min gap {m['min_gap']:.1e}  max|y| {m['max_abs_out']:.1e}{nan}")
