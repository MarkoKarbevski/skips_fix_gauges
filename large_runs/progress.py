"""Progress of the queues: runs done, runs left and an estimate of the time left, from the timings of finished runs.
Usage: python3 progress.py [--short]
"""
import json, os, statistics, sys
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from fdim_large import GATED, key  # noqa: E402

QUEUES = [("queue_eps.json", "runs/eps"), ("queue3.json", "runs/v3")]


def results(d):
    out = {}
    path = os.path.join(HERE, d, "results.jsonl")
    if os.path.exists(path):
        for line in open(path):
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            out[key(r)] = r
    return out


def main():
    done = {d: results(d) for _, d in QUEUES}
    pool = [r for res in done.values() for r in res.values()]
    by = defaultdict(lambda: defaultdict(list))
    for r in pool:
        t = r["t_jac"] + r["t_svd"]
        by[0][(r["family"], r["L"], r["d"], r["m"], r["skip"], r["norm"], r.get("eps"), r["act"], r.get("init", "gauss"))].append(t)
        by[1][(r["family"], r["L"], r["d"], r["m"], r["skip"], r["norm"], r["act"], r.get("init", "gauss"))].append(t)
        by[2][(r["family"], r["m"], r["skip"], r["norm"], r["act"] in GATED)].append(t)   # same shapes, any activation
        by[3][r["family"]].append(t)

    def est(c):
        ks = [(c["family"], c["L"], c["d"], c["m"], c["skip"], c["norm"], c.get("eps"), c["act"], c.get("init", "gauss")),
              (c["family"], c["L"], c["d"], c["m"], c["skip"], c["norm"], c["act"], c.get("init", "gauss")),
              (c["family"], c["m"], c["skip"], c["norm"], c["act"] in GATED), c["family"]]
        for lvl, k in enumerate(ks):
            if by[lvl].get(k):
                # the same network: its fastest draw (the others may have shared the machine); else the median
                return min(by[lvl][k]) if lvl < 2 else statistics.median(by[lvl][k])
        return 300.0

    total_left = 0.0
    for qf, d in QUEUES:
        q = json.load(open(os.path.join(HERE, qf)))
        spec = os.path.join(HERE, d, "spec")
        left = [c for c in q if not os.path.exists(os.path.join(spec, key(c) + ".npy"))]
        t = sum(est(c) for c in left)
        total_left += t
        print(f"{qf:16s} done {len(q) - len(left):3d}/{len(q)}  left {len(left):3d}  ~{t / 60:5.0f} min alone")
        if left and "--short" not in sys.argv:
            print("   left:", dict(Counter(f"{c['family']} {c['act']}" for c in left)))
    print(f"total left ~{total_left / 3600:.1f} h, run one at a time")


if __name__ == "__main__":
    main()
