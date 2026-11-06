"""The small networks of the note's Figures 1 and 4, trained on classification datasets.

Architecture as in experiments.ipynb, section 10: an embedding R^p -> R^d, L MLP blocks of width m and a readout
R^d -> R^q, without biases; identity skips or none; no normalization, or pre-RMSNorm before every block and the readout,
N(h) = h / sqrt(mean(h^2) + eps), with the skips carrying h itself. Here p is the number of features and q the number of
classes, and the readout gives the logits. Shared by train.ipynb, which trains and stores the networks, and
analyze.ipynb, which loads them and computes the Jacobians of the parameter-to-output map.
"""
import gzip
import io
import math
import time
import urllib.request
from pathlib import Path

import numpy as np
import torch
import torch.nn.functional as F

HERE = Path(__file__).resolve().parent
DATA, RUNS, RESULTS = HERE / "data", HERE / "runs", HERE / "results"
d, m, L = 4, 8, 3
ACTS = {"tanh": (False, torch.tanh, 0), "GELU": (False, F.gelu, 0),
        "ReGLU": (True, torch.relu, 2), "SwiGLU": (True, F.silu, 1)}     # gated?, activation, rescalings per unit
PMLB = "https://media.githubusercontent.com/media/EpistasisLab/pmlb/master/datasets/{0}/{0}.tsv.gz"


# ----------------------------------------------------------------------------------------------------------- datasets
def arrays(name):
    """Features and integer labels 0, ..., q-1: a scikit-learn generator, or a dataset of the Penn Machine Learning
    Benchmarks (PMLB), downloaded once into data/."""
    if name == "clusters":      # 5 classes, each a union of 3 Gaussian clusters at vertices of a hypercube in R^8
        from sklearn.datasets import make_classification
        X, y = make_classification(n_samples=3000, n_features=8, n_informative=8, n_redundant=0, n_classes=5,
                                   n_clusters_per_class=3, class_sep=1.5, random_state=0)
    elif name == "hypercube":   # 4 classes, each two Gaussian clusters at vertices of a 4-cube, plus 2 noise features
        from sklearn.datasets import make_classification
        X, y = make_classification(n_samples=3000, n_features=6, n_informative=4, n_redundant=0, n_classes=4,
                                   n_clusters_per_class=2, class_sep=2.0, random_state=1)
    else:
        path = DATA / f"{name}.tsv.gz"
        if not path.exists():
            DATA.mkdir(exist_ok=True)
            urllib.request.urlretrieve(PMLB.format(name), path)
        raw = gzip.decompress(path.read_bytes()).decode()
        arr = np.loadtxt(io.StringIO(raw), delimiter="\t", skiprows=1)
        X, y = arr[:, :-1], arr[:, -1]
    return np.asarray(X, dtype=np.float64), np.unique(y, return_inverse=True)[1]


def load(name, seed=0):
    """Stratified 60/20/20 split into train, validation and test; features constant on the training set dropped;
    features standardized with the mean and standard deviation of the training set."""
    X, y = arrays(name)
    rng = np.random.default_rng(seed)
    parts = {"train": [], "val": [], "test": []}
    for c in np.unique(y):
        idx = rng.permutation(np.flatnonzero(y == c))
        a, b = int(round(0.6 * len(idx))), int(round(0.8 * len(idx)))
        parts["train"] += idx[:a].tolist(); parts["val"] += idx[a:b].tolist(); parts["test"] += idx[b:].tolist()
    parts = {k: np.array(sorted(v)) for k, v in parts.items()}
    X = X[:, X[parts["train"]].std(0) > 0]
    mu, sd = X[parts["train"]].mean(0), X[parts["train"]].std(0)
    X = (X - mu) / sd
    return {k: (X[i], y[i]) for k, i in parts.items()}


def linear_baseline(ds):
    """Multinomial logistic regression with an intercept and L2 penalty, C chosen on the validation set from 1e-3 to
    1e3, refit on train + validation; returns the chosen C and the validation and test accuracies."""
    from sklearn.linear_model import LogisticRegression
    (Xtr, ytr), (Xva, yva), (Xte, yte) = ds["train"], ds["val"], ds["test"]
    scores = {C: LogisticRegression(C=C, max_iter=10000).fit(Xtr, ytr).score(Xva, yva) for C in 10.0 ** np.arange(-3, 4)}
    C = max(scores, key=scores.get)
    clf = LogisticRegression(C=C, max_iter=10000).fit(np.vstack([Xtr, Xva]), np.concatenate([ytr, yva]))
    return {"C": float(C), "val_acc": float(scores[C]), "test_acc": float(clf.score(Xte, yte))}


# -------------------------------------------------------------------------------------------------------------- model
def shapes(act, p, q, widths):
    """Shapes of the weight matrices: embedding, then per block the read (and gate) and the write, then the readout."""
    sh = [(d, p)]
    for w in widths:
        sh += [(w, d), (w, d), (d, w)] if ACTS[act][0] else [(w, d), (d, w)]
    return sh + [(q, d)]


def init(sh, gen):
    """N(0, 1/fan-in), as the generic draws of the note's figures."""
    return torch.cat([torch.randn(a * b, generator=gen, dtype=torch.float64) / b ** 0.5 for a, b in sh])


def forward(theta, X, act, skip, eps, sh):
    """Logits of the network with flat parameters theta on the rows of X; eps is None without normalization."""
    gated, g, _ = ACTS[act]
    ps, i = [], 0
    for a, b in sh:
        ps.append(theta[i:i + a * b].view(a, b)); i += a * b
    N = (lambda h: h) if eps is None else (lambda h: h / torch.sqrt((h * h).mean(-1, keepdim=True) + eps))
    k = 3 if gated else 2
    h = X @ ps[0].T
    for l in range((len(ps) - 2) // k):
        w = ps[1 + k * l:1 + k * (l + 1)]
        z = N(h)
        out = (g(z @ w[0].T) * (z @ w[1].T)) @ w[2].T if gated else g(z @ w[0].T) @ w[1].T
        h = h + out if skip else out
    return N(h) @ ps[-1].T


def group_dim(eps):
    """Dimension of the changes of basis at a hidden state: GL(d) without normalization, O(d) under RMSNorm."""
    return d * d if eps is None else d * (d - 1) // 2


def extra_units(act, eps):
    """Hidden units added to each block of the skipless network: the fewest whole units that add at least L g
    parameters, spread as evenly as possible (as in the note's Figure 4)."""
    per_unit = (3 if ACTS[act][0] else 2) * d
    k = -(-L * group_dim(eps) // per_unit)
    return [k // L + (1 if i < k % L else 0) for i in range(L)]


def widths_of(kind, act, eps):
    return [m + e for e in extra_units(act, eps)] if kind == "wide" else [m] * L


def count(kind, act, eps, P, widths):
    """Predicted functional dimension: P - g - s with skips, P - (L+1) g - s without, where s counts the rescalings of
    hidden units (none for tanh and GELU, one per unit for SwiGLU, two for ReGLU)."""
    g, s = group_dim(eps), ACTS[act][2] * sum(widths)
    return P - g - s if kind == "skip" else P - (len(widths) + 1) * g - s


# ----------------------------------------------------------------------------------------------------------- training
def train(ds, act, skip, eps, widths, seed, lr, wd=1e-4, batch=128, plateau_steps=600, max_steps=40000, cuts=5,
          clip=1.0):
    """AdamW on minibatches of 128, gradients clipped to norm `clip`, with a linear warmup over the first epochs (at
    most 500 steps). The learning rate is cut by a factor 0.3 whenever the validation loss has not improved by 0.01
    percent for about plateau_steps steps; training stops at the next plateau after `cuts` cuts, when the rate is
    0.3^cuts of its start, or after max_steps steps. Returns the parameters with the lowest validation loss, in
    float64, with the accuracies and the curves."""
    torch.manual_seed(seed)
    (Xtr, ytr), (Xva, yva), (Xte, yte) = ds["train"], ds["val"], ds["test"]
    p, q = Xtr.shape[1], int(max(ytr.max(), yva.max(), yte.max())) + 1
    sh = shapes(act, p, q, widths)
    theta = torch.nn.Parameter(init(sh, torch.Generator().manual_seed(1000 + seed)).float())
    Xtr_t, ytr_t = torch.tensor(Xtr, dtype=torch.float32), torch.tensor(ytr)
    Xva_t, yva_t = torch.tensor(Xva, dtype=torch.float32), torch.tensor(yva)
    opt = torch.optim.AdamW([theta], lr=lr, weight_decay=wd)
    n = len(Xtr_t)
    spe = math.ceil(n / batch)                                   # steps per epoch
    patience = max(5, math.ceil(plateau_steps / spe))            # epochs without improvement before a cut
    warm = max(1, min(5 * spe, 500))
    best, best_state, bad, ncut, step, curve, stop = float("inf"), None, 0, 0, 0, [], "max_steps"
    t0 = time.time()
    while step < max_steps:
        perm, tl = torch.randperm(n), 0.0
        for j in range(spe):
            for gr in opt.param_groups:
                gr["lr"] = lr * 0.3 ** ncut * min(1.0, (step + 1) / warm)
            idx = perm[j * batch:(j + 1) * batch]
            loss = F.cross_entropy(forward(theta, Xtr_t[idx], act, skip, eps, sh), ytr_t[idx])
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_([theta], clip)
            opt.step()
            tl += loss.item() * len(idx)
            step += 1
        with torch.no_grad():
            vl = F.cross_entropy(forward(theta, Xva_t, act, skip, eps, sh), yva_t).item()
        curve.append((step, tl / n, vl))
        if not math.isfinite(vl):
            stop = "diverged"
            break
        if best_state is None or vl < best - 1e-4 * abs(best):
            best, best_state, bad = vl, theta.detach().clone(), 0
        else:
            bad += 1
            if bad >= patience:
                ncut, bad = ncut + 1, 0
                if ncut > cuts:
                    stop = "converged"
                    break
    th = (best_state if best_state is not None else theta.detach()).double()

    def acc(X, y):
        with torch.no_grad():
            return float((forward(th, torch.tensor(X), act, skip, eps, sh).argmax(1).numpy() == y).mean())

    return {"theta": th, "shapes": sh, "steps": step, "seconds": time.time() - t0, "val_loss": best, "stop": stop,
            "curve": torch.tensor(curve), "train_acc": acc(Xtr, ytr), "val_acc": acc(Xva, yva),
            "test_acc": acc(Xte, yte)}


def run_name(dataset, act, eps, kind, lr, seed):
    norm = "none" if eps is None else f"rms{eps:.0e}"
    return f"{dataset}/{act}_{norm}_{kind}_lr{lr:.0e}_s{seed}.pt"


def train_and_store(job):
    """Worker: train one network and store it under runs/; returns its summary without the parameters. Skips runs that
    are stored already, so an interrupted grid resumes where it stopped."""
    torch.set_num_threads(1)
    dataset, act, eps, kind, lr, seed = job
    path = RUNS / run_name(*job)
    if path.exists():
        rec = torch.load(path, weights_only=True)
    else:
        ds = load(dataset)
        widths = widths_of(kind, act, eps)
        r = train(ds, act, kind == "skip", eps, widths, seed, lr)
        rec = {"dataset": dataset, "act": act, "eps": eps, "kind": kind, "lr": lr, "seed": seed, "widths": widths,
               **r}
        path.parent.mkdir(parents=True, exist_ok=True)
        torch.save(rec, path)
    return {k: v for k, v in rec.items() if k not in ("theta", "curve", "shapes")}


# ----------------------------------------------------------------------------------------------------------- analysis
def spectrum(theta, X, act, skip, eps, sh):
    """Singular values, divided by the largest, of the exact float64 Jacobian of theta -> logits on the inputs X; the
    rank read at the largest gap, the largest ratio of consecutive singular values; and that ratio."""
    from torch.func import jacfwd
    X = torch.as_tensor(X, dtype=torch.float64)
    J = jacfwd(lambda t: forward(t, X, act, skip, eps, sh).reshape(-1))(theta)
    s = torch.linalg.svdvals(J).numpy()
    s = s / s[0]
    ls = np.log10(np.maximum(s, 1e-300))
    r = int(np.argmax(ls[:-1] - ls[1:])) + 1
    return s, r, float(s[r - 1] / s[r])
