"""The eps sweep of the 8-block skipless networks under pre-RMSNorm for ReLU^2 and ReGLU (odd-pairs start), and GELU
(looks-linear start) as a control whose blocks are not homogeneous; eps = 1e-5 comes from queue3. Settings as in
make_queue3.py."""
import json
d = 16
q = []
for act, init, noise, m in (("relu2", "pairs", 0.1, 64), ("reglu", "pairs", 0.1, 42), ("gelu", "ll", 0.3, 64)):
    for eps in (1e-1, 1e-2, 1e-11):
        for seed in (0, 1, 2):
            q.append(dict(arch="mlp", L=8, d=d, rows_factor=1.08, family="L8", m=m, skip="none", norm="rms", eps=eps,
                          act=act, seed=seed, init=init, ll_noise=noise))
json.dump(q, open("queue_eps2.json", "w"), indent=0)
print(len(q), "runs")
