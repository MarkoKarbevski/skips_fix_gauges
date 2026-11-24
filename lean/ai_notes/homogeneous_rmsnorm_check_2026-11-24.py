# Numeric check of Lemma A.3 (ii) of the skips paper: skipless network, pre-RMSNorm with eps > 0,
# blocks positively homogeneous of degree k; change of basis G = exp(tau S) at the hidden state h_l.
# Claim: d/dtau (output) at 0 = c * output with
#   c = -k^(L-l) * (h_l S h_l^T) / (d (r_l^2 + eps)) * prod_{i=l+1..L} eps / (r_i^2 + eps),
# and for the scaling e^tau at h_L (readout unchanged): c = eps / (r_L^2 + eps).
import numpy as np
from scipy.linalg import expm
rng = np.random.default_rng(1)
def N(h, eps): return h / np.sqrt(h @ h / len(h) + eps)
def run(kind, d, qs, eps, l, S, tau, scale_last=None):
    k = {'relu': 1, 'relusq': 2}[kind]
    act = (lambda z: np.maximum(z, 0)) if kind == 'relu' else (lambda z: np.maximum(z, 0)**2)
    G = expm(tau*S)
    hs = [x @ E]
    if l == 0: hs[0] = hs[0] @ G
    for i, (R, W) in enumerate(zip(Rs, Ws)):
        Rm = np.linalg.inv(G) @ R if i == l else R
        Wm = W @ G if i + 1 == l else W
        hs.append(act(N(hs[-1], eps) @ Rm) @ Wm)
    if scale_last is not None: hs[-1] = scale_last*hs[-1]
    return hs, N(hs[-1], eps) @ D
for kind in ['relu', 'relusq']:
    for (d, qs, eps) in [(3, [5, 4], 0.3), (4, [6, 6, 5], 1.1)]:
        L = len(qs); k = {'relu': 1, 'relusq': 2}[kind]
        x = rng.normal(size=d); E = rng.normal(size=(d, d)); D = rng.normal(size=(d, 2))
        Rs = [rng.normal(size=(d, q)) for q in qs]; Ws = [rng.normal(size=(q, d)) for q in qs]
        for l in range(L):
            S = rng.normal(size=(d, d))            # any S: only h S h^T enters
            hs, y = run(kind, d, qs, eps, l, S, 0.0)
            r2 = [h @ h / d for h in hs]
            c = -k**(L - l) * (hs[l] @ S @ hs[l]) / (d*(r2[l] + eps)) * np.prod([eps/(r2[i] + eps) for i in range(l + 1, L + 1)])
            t = 1e-6
            num = (run(kind, d, qs, eps, l, S, t)[1] - run(kind, d, qs, eps, l, S, -t)[1]) / (2*t)
            print(f"{kind} d={d} L={L} eps={eps} l={l}: formula {c:+.8f}, numeric/output {num[0]/y[0]:+.8f} {num[1]/y[1]:+.8f}")
        hs, y = run(kind, d, qs, eps, 99, np.zeros((d, d)), 0.0); r2L = hs[-1] @ hs[-1] / d
        t = 1e-6
        num = (run(kind, d, qs, eps, 99, np.zeros((d, d)), 0.0, np.exp(t))[1] - run(kind, d, qs, eps, 99, np.zeros((d, d)), 0.0, np.exp(-t))[1]) / (2*t)
        print(f"{kind} d={d} L={L} eps={eps} scaling at h_L: formula {eps/(r2L + eps):+.8f}, numeric/output {num[0]/y[0]:+.8f}")
