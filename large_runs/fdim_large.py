"""Functional dimension of deeper and wider MLP networks, with and without skips.

Networks (row vectors, as in the note): h_0 = x E, h_l = h_{l-1} S_l + act(N(h_{l-1}) W_up^l) W_dn^l, y = N(h_L) D,
with S_l = 0 (no skip), I (identity skip), a full learned matrix A_l, or a learned upper-triangular T_l, and N the
identity or RMSNorm h / sqrt(mean(h^2) + eps). No biases.

The functional dimension at random parameters is read as the rank of the exact (autodiff, float64) Jacobian of the
parameter-to-output map on a batch of random inputs, at the largest gap of its singular values, and compared with the
symmetry count of the note (GELU and tanh blocks have no symmetries inside, s = 0):
                 no normalization                    pre-RMSNorm, eps > 0  (o = d(d-1)/2)
  no skip        P - (L+1) d^2                       P - (L+1) o
  identity       P - d^2                             P - o
  full learned   P - (L+1) d^2  (= identity)         P - (L+1) o  (= identity + L d(d+1)/2)
  triangular     P - d^2 - L d(d+1)/2 (= identity)   P - o        (= full learned)
where P counts the parameters of each network, the learned skips included.
"""
import argparse, json, math, os, resource, sys, time

import numpy as np
import scipy.linalg as sla
import torch
import torch.nn.functional as F
from torch.func import jacrev, vmap

from svd_inplace import svdvals_inplace

torch.set_default_dtype(torch.float64)
ACTS = {"gelu": F.gelu, "tanh": torch.tanh, "relu": torch.relu, "relu2": lambda z: torch.relu(z) ** 2,
        "reglu": torch.relu, "swiglu": F.silu, "geglu": F.gelu}     # for the gated blocks: the gate function
GATED = {"reglu", "swiglu", "geglu"}
# symmetries inside a block, per hidden unit: positive rescalings for the homogeneous activations, the value of a
# gated unit, and for ReGLU its gate as well
S_PER_UNIT = {"gelu": 0, "tanh": 0, "relu": 1, "relu2": 1, "reglu": 2, "swiglu": 1, "geglu": 1}
# tanh(z) - tanh(-z) = 2 tanh(z) is linear only near 0: the looks-linear start reads tanh pairs at a smaller scale
TANH_LL_SCALE = 0.4


def predicted_rank(P, d, L, skip, norm, s=0):
    g = d * d if norm is None else d * (d - 1) // 2
    return {"none": P - (L + 1) * g, "id": P - g, "full": P - (L + 1) * g,
            "tri": P - g - (L * d * (d + 1) // 2 if norm is None else 0)}[skip] - s


def build(d, m, L, p, q, skip, norm, act, seed, eps, skip_scale=0.2, branch_scale=1.0, init="gauss", ll_noise=0.3):
    """Random parameters as one flat vector, and the network as a function of (theta, x) for a single input x.

    init = "gauss": every read and write has independent N(0, 1/fan_in) entries (writes times branch_scale).
    init = "ll": looks-linear start (Balduzzi et al., 2017) for GELU, ReLU and tanh blocks. The m hidden units come in
    pairs with opposite reads and writes, and sigma(z) - sigma(-z) = z for GELU and ReLU, so the block computes
    h Q Q^T = h exactly (for tanh, 2 tanh(z) replaces z, and the block is the identity up to cubic terms); then
    every read and write gets ll_noise times N(0, 1/fan_in) noise, which makes the point generic. Each block then
    starts near the identity, as a residual block does, and the products of block Jacobians stay near isometries.
    """
    if init == "ll" and (act not in ("gelu", "relu", "tanh") or m % 2 or m // 2 < d):
        raise ValueError("the looks-linear start needs GELU, ReLU or tanh blocks with an even width m >= 2 d")
    if init == "pairs" and (act not in ("relu2", "reglu", "swiglu", "geglu") or m % 2):
        raise ValueError("the odd-pairs start is for ReLU^2 and gated blocks of even width m")
    kappa = 2.0 if act == "tanh" else 1.0     # slope at 0 of sigma(z) - sigma(-z)
    g = torch.Generator().manual_seed(seed)
    qcache = {}
    iu = torch.triu_indices(d, d)
    ntri = iu.shape[1]
    blocks = [("E", (p, d), p)]
    for l in range(L):
        if skip == "full":
            blocks.append((f"A{l}", (d, d), None))
        elif skip == "tri":
            blocks.append((f"T{l}", (ntri,), None))
        blocks += [(f"U{l}", (d, 2 * m if act in GATED else m), d), (f"W{l}", (m, d), m)]
    blocks.append(("D", (d, q), d))
    parts, slices, o = [], {}, 0
    eye = torch.eye(d)
    for name, shape, fan_in in blocks:
        n = math.prod(shape)
        if name[0] == "A":      # a generic invertible skip near the identity
            v = (eye + skip_scale / math.sqrt(d) * torch.randn(d, d, generator=g)).reshape(-1)
        elif name[0] == "T":    # its upper-triangular counterpart, packed row by row
            v = (eye + skip_scale / math.sqrt(d) * torch.randn(d, d, generator=g))[iu[0], iu[1]]
        elif init == "suo" and name[0] in "UW":   # uniform orthogonal, scaled to keep norms on average
            a, b = shape
            O = torch.linalg.qr(torch.randn(max(a, b), min(a, b), generator=g))[0]
            O = O.T if a < b else O                    # a x b with orthonormal rows (a < b) or columns
            v = (O * math.sqrt(max(1.0, a / b))).reshape(-1)
        elif init == "pairs" and name[0] in "UW":
            # degree-2 blocks: odd pairs. ReLU^2: units (u, w) and (-u, -w), relu(z)^2 - relu(-z)^2 = z |z|; gated:
            # gates u and -u with value u and write u, (g(z) + g(-z)) z, which is odd. With unit vectors u in many
            # directions a block is about c |h| h, which keeps the directions of the hidden states (no collapse)
            l, k = int(name[1:]), m // 2
            if name[0] == "U":
                u = torch.randn(d, k, generator=g)
                u = u / u.norm(dim=0, keepdim=True)
                qcache[l] = u
                base = torch.cat([u, -u, u, u], 1) if act in GATED else torch.cat([u, -u], 1)
            else:
                u = qcache[l]
                base = (torch.cat([u.T, u.T], 0) if act in GATED else torch.cat([u.T, -u.T], 0)) / math.sqrt(k)
            v = (base + ll_noise * torch.randn(shape, generator=g) / math.sqrt(fan_in)).reshape(-1)
        elif init == "ll" and name[0] in "UW":
            l, k = int(name[1:]), m // 2
            if name[0] == "U":  # reads [a Q, -a Q], Q with orthonormal rows; a gives pre-activations of unit variance
                Q = torch.linalg.qr(torch.randn(k, d, generator=g))[0].T
                c = math.sqrt(k / d) * (TANH_LL_SCALE if act == "tanh" else 1.0)
                qcache[l] = (Q, c)
                base = torch.cat([c * Q, -c * Q], dim=1)
            else:               # writes [Q^T / a; -Q^T / a] / kappa
                Q, c = qcache[l]
                base = torch.cat([Q.T / c, -Q.T / c], dim=0) / kappa
            v = (base + ll_noise * torch.randn(shape, generator=g) / math.sqrt(fan_in)).reshape(-1)
        else:
            v = torch.randn(n, generator=g) / math.sqrt(fan_in)
            if name[0] == "W":  # the writes of the blocks; a scale below 1 keeps a deep residual stream of order one
                v = v * branch_scale
        parts.append(v)
        slices[name] = (o, o + n, shape)
        o += n
    theta = torch.cat(parts)
    a = ACTS[act]
    N = (lambda h: h) if norm is None else (lambda h: h * torch.rsqrt((h * h).mean(-1, keepdim=True) + eps))

    def get(t, name):
        s, e, shape = slices[name]
        return t[s:e].view(shape)

    def f(t, x):
        h = x @ get(t, "E")
        for l in range(L):
            z = N(h) @ get(t, f"U{l}")
            br = (a(z[..., :m]) * z[..., m:] if act in GATED else a(z)) @ get(t, f"W{l}")
            if skip == "none":
                h = br
            elif skip == "id":
                h = h + br
            elif skip == "full":
                h = h @ get(t, f"A{l}") + br
            else:
                T = torch.zeros(d, d, dtype=t.dtype).index_put((iu[0], iu[1]), get(t, f"T{l}"))
                h = h @ T + br
        return N(h) @ get(t, "D")

    return theta, f


def build_tf(d, m, n_layer, p, q, H, T, skip, norm, act, seed, eps, skip_scale=0.2, branch_scale=1.0,
             init="gauss", ll_noise=0.3, qk_scale=1.0):
    """A decoder transformer on sequences x of T tokens (rows): h_0 = x E; in every layer a causal attention block
    with H heads of width d / H (reads W_Q, W_K, W_V, write W_O) and an MLP block (read U, write W), each with its own
    skip (none, identity, full learned or triangular learned) and pre-RMSNorm or none; y = N(h_L) D. No biases, no
    positional embeddings (the causal mask breaks the permutation symmetry). L = 2 n_layer blocks.

    init = "gauss": N(0, 1/fan_in) everywhere, writes times branch_scale.
    init = "ll": a start near the identity for networks without skips: attention with W_Q = W_K = qk_scale times
    orthonormal columns per head (scores qk_scale^2 z P_h z^T / sqrt(d_h), largest on the diagonal), W_V = R and
    W_O = R^T for an orthogonal R; MLP blocks looks-linear (build). Then ll_noise times N(0, 1/fan_in) everywhere.
    """
    dh = d // H
    g = torch.Generator().manual_seed(seed)
    iu = torch.triu_indices(d, d)
    ntri = iu.shape[1]
    kappa = 2.0 if act == "tanh" else 1.0
    blocks = [("E", (p, d), p)]
    for l in range(n_layer):
        for kind in ("a", "f"):                        # attention block, then MLP block
            if skip == "full":
                blocks.append((f"A{kind}{l}", (d, d), None))
            elif skip == "tri":
                blocks.append((f"T{kind}{l}", (ntri,), None))
        blocks += [(f"Q{l}", (d, d), d), (f"K{l}", (d, d), d), (f"V{l}", (d, d), d), (f"O{l}", (d, d), d),
                   (f"U{l}", (d, 2 * m if act in GATED else m), d), (f"W{l}", (m, d), m)]
    blocks.append(("D", (d, q), d))
    parts, slices, o = [], {}, 0
    eye = torch.eye(d)
    cache = {}
    for name, shape, fan_in in blocks:
        n = math.prod(shape)
        tag = name[0]
        if tag == "A":
            v = (eye + skip_scale / math.sqrt(d) * torch.randn(d, d, generator=g)).reshape(-1)
        elif tag == "T":
            v = (eye + skip_scale / math.sqrt(d) * torch.randn(d, d, generator=g))[iu[0], iu[1]]
        elif init == "ll" and tag in "QKVOUW":
            l = int(name[1:])
            if tag == "Q":                             # orthonormal columns, the same for queries and keys
                Bm = torch.linalg.qr(torch.randn(d, d, generator=g))[0]
                cache[("B", l)] = Bm
                base = qk_scale * Bm
            elif tag == "K":
                base = qk_scale * cache[("B", l)]
            elif tag == "V":
                R = torch.linalg.qr(torch.randn(d, d, generator=g))[0]
                cache[("R", l)] = R
                base = R
            elif tag == "O":
                base = cache[("R", l)].T
            elif tag == "U":
                k = m // 2
                Qm = torch.linalg.qr(torch.randn(k, d, generator=g))[0].T
                c = math.sqrt(k / d) * (TANH_LL_SCALE if act == "tanh" else 1.0)
                cache[("U", l)] = (Qm, c)
                base = torch.cat([c * Qm, -c * Qm], dim=1)
            else:
                Qm, c = cache[("U", l)]
                base = torch.cat([Qm.T / c, -Qm.T / c], dim=0) / kappa
            v = (base + ll_noise * torch.randn(shape, generator=g) / math.sqrt(fan_in)).reshape(-1)
        else:
            v = torch.randn(n, generator=g) / math.sqrt(fan_in)
            if tag in "OW":
                v = v * branch_scale
        parts.append(v)
        slices[name] = (o, o + n, shape)
        o += n
    theta = torch.cat(parts)
    a = ACTS[act]
    N = (lambda h: h) if norm is None else (lambda h: h * torch.rsqrt((h * h).mean(-1, keepdim=True) + eps))
    causal = torch.triu(torch.ones(T, T, dtype=torch.bool), 1)

    def get(t, name):
        s, e, shape = slices[name]
        return t[s:e].view(shape)

    def combine(t, h, out, tag):
        if skip == "none":
            return out
        if skip == "id":
            return h + out
        if skip == "full":
            return h @ get(t, "A" + tag) + out
        Tm = torch.zeros(d, d, dtype=t.dtype).index_put((iu[0], iu[1]), get(t, "T" + tag))
        return h @ Tm + out

    def f(t, x):                                       # x: (T, p) -> (T * q,)
        h = x @ get(t, "E")
        for l in range(n_layer):
            z = N(h)
            Qh = (z @ get(t, f"Q{l}")).view(T, H, dh).transpose(0, 1)
            Kh = (z @ get(t, f"K{l}")).view(T, H, dh).transpose(0, 1)
            Vh = (z @ get(t, f"V{l}")).view(T, H, dh).transpose(0, 1)
            S = (Qh @ Kh.transpose(1, 2)) / math.sqrt(dh)
            A = torch.softmax(S.masked_fill(causal, float("-inf")), dim=-1)
            out = (A @ Vh).transpose(0, 1).reshape(T, d) @ get(t, f"O{l}")
            h = combine(t, h, out, f"a{l}")
            z = N(h) @ get(t, f"U{l}")
            out = (a(z[..., :m]) * z[..., m:] if act in GATED else a(z)) @ get(t, f"W{l}")
            h = combine(t, h, out, f"f{l}")
        return (N(h) @ get(t, "D")).reshape(-1)

    return theta, f


FLOOR = 1e-18
MIN_GAP = 1e3              # a rank is read only at a gap of at least this ratio of consecutive singular values


def read_rank(s, pred):
    """Rank at the largest gap of the normalized singular values, and the gap at the predicted cut."""
    s = s / s[0]
    # clamp at the double-precision floor: below it, the drop from rounding noise to exact zeros (dead ReLU units give
    # exactly zero columns) is not a gap of the spectrum
    c = np.maximum(s, FLOOR)
    ls = np.log10(c)
    r = int(np.argmax(ls[:-1] - ls[1:])) + 1
    gap_pred = float(c[pred - 1] / c[pred]) if 0 < pred < len(s) else float("nan")
    return r, float(c[r - 1] / c[r]), gap_pred, float(s[pred - 1]) if 0 < pred <= len(s) else float("nan")


def net_name(cfg):
    norm = cfg["norm"] if cfg["norm"] == "none" else f"{cfg['norm']}{cfg.get('eps', 1e-2):.0e}"
    i = cfg.get("init", "gauss")
    init = ("" if i == "gauss" else f"_ll{cfg.get('ll_noise', 0.3):g}" if i == "ll" else
            f"_pairs{cfg.get('ll_noise', 0.3):g}" if i == "pairs" else f"_{i}")
    arch = f"_H{cfg['H']}_T{cfg['T']}" if cfg.get("arch", "mlp") == "tf" else ""
    return (f"{cfg.get('family', 'x')}_L{cfg['L']}_d{cfg['d']}_m{cfg['m']}{arch}_{norm}_{cfg['skip']}_{cfg['act']}"
            f"{init}")


def key(cfg):
    return net_name(cfg) + f"_s{cfg['seed']}"


def mem_available():
    """MemAvailable of /proc/meminfo, in bytes."""
    with open("/proc/meminfo") as fh:
        for line in fh:
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) * 1024
    return float("inf")


def wait_for_memory(nbytes, margin=1.0e9, poll=60, max_wait=3600):
    """Waits until nbytes + margin of memory are available, so that a run never starts into an out-of-memory kill
    (two Jacobians of the 8-block networks do not fit together); after max_wait seconds it goes ahead anyway."""
    t0 = time.time()
    while mem_available() < nbytes + margin and time.time() - t0 < max_wait:
        print(f"waiting for memory: need {(nbytes + margin) / 2**30:.2f} GB, "
              f"available {mem_available() / 2**30:.2f} GB", file=sys.stderr, flush=True)
        time.sleep(poll)


def append_line(path, line):
    """Appends one line to a text file and syncs it to disk; a line left unfinished by a crash is closed first."""
    with open(path, "ab+") as fh:
        fh.seek(0, os.SEEK_END)
        if fh.tell() > 0:
            fh.seek(-1, os.SEEK_END)
            if fh.read(1) != b"\n":
                fh.write(b"\n")
        fh.write((line + "\n").encode())
        fh.flush()
        os.fsync(fh.fileno())


def save_atomic(path, arr):
    """np.save to a temporary file, then a rename: the file at path is either absent or complete."""
    tmp = path + ".tmp"
    with open(tmp, "wb") as fh:
        np.save(fh, arr)
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)


def run(cfg):
    d, m, L = cfg["d"], cfg["m"], cfg["L"]
    p, q = cfg.get("p", d), cfg.get("q", d)
    skip, norm, act = cfg["skip"], cfg["norm"], cfg["act"]
    eps = cfg.get("eps", 1e-2)
    nrm = None if norm == "none" else norm
    # an input adds at most min(q, d) independent rows (the output is h_L D, with h_L of width d), and the readout
    # d (q - d) more in all. Under RMSNorm the readout sees N(h_L), which passes the radial direction of h_L only
    # through a factor eps / r^2: an input then adds min(q, d) - 1 rows of full size. The batch needs about
    # pred / (rows per input) inputs, with a margin
    per_token = min(q, d) - (0 if norm == "none" else 1)
    if cfg.get("arch", "mlp") == "tf":               # L layers, each an attention block and an MLP block
        H, T = cfg["H"], cfg["T"]
        theta, f = build_tf(d, m, L, p, q, H, T, skip, nrm, act, cfg["seed"], eps,
                            branch_scale=cfg.get("branch_scale", 1.0), init=cfg.get("init", "gauss"),
                            ll_noise=cfg.get("ll_noise", 0.3), qk_scale=cfg.get("qk_scale", 1.0))
        P = theta.numel()
        # inside the blocks: per head an invertible map between queries and keys and one between values and output
        s_in = L * 2 * H * (d // H) ** 2 + L * m * S_PER_UNIT[act]
        pred = predicted_rank(P, d, 2 * L, skip, nrm, s=s_in)
        per_input, out_rows, xshape = T * per_token, T * q, (T, p)
    else:
        theta, f = build(d, m, L, p, q, skip, nrm, act, cfg["seed"], eps,
                         branch_scale=cfg.get("branch_scale", 1.0), init=cfg.get("init", "gauss"),
                         ll_noise=cfg.get("ll_noise", 0.3))
        P = theta.numel()
        pred = predicted_rank(P, d, L, skip, nrm, s=L * m * S_PER_UNIT[act])
        per_input, out_rows, xshape = per_token, q, (p,)
    B = math.ceil(max(cfg.get("rows_factor", 1.15) * pred, pred + 128) / per_input)
    rows = B * out_rows
    gx = torch.Generator().manual_seed(10_000 + cfg["seed"])
    X = torch.randn(B, *xshape, generator=gx)
    wait_for_memory(rows * P * 8)
    J = torch.empty(rows, P)
    jac = vmap(jacrev(f), in_dims=(None, 0))
    chunk = max(1, min(B, int(cfg.get("chunk_bytes", 2.0e8) // (out_rows * P * 8))))
    t0 = time.perf_counter()
    for b0 in range(0, B, chunk):
        blk = jac(theta, X[b0:b0 + chunk])            # (chunk, out_rows, P)
        J[b0 * out_rows:(b0 + blk.shape[0]) * out_rows] = blk.reshape(-1, P)
        del blk
    if cfg.get("colscale", False):                    # unit columns: the rank is unchanged, the conditioning better
        J /= torch.linalg.vector_norm(J, dim=0).clamp_min(1e-300)
    t_jac = time.perf_counter() - t0
    # NaN and overflow bookkeeping: non-finite entries of J, the largest finite entry of J and of the outputs
    n_nonfinite, max_abs_J = 0, 0.0
    for i in range(0, rows, 512):                     # in row blocks: full-size temporaries would triple the memory
        blk = J[i:i + 512]
        fin = torch.isfinite(blk)
        n_nonfinite += int((~fin).sum())
        if fin.any():
            max_abs_J = max(max_abs_J, float(blk[fin].abs().max()))
        del blk, fin
    finite = n_nonfinite == 0
    with torch.no_grad():
        Y = vmap(f, in_dims=(None, 0))(theta, X[:min(B, 256)])
    n_nonfinite_out = int((~torch.isfinite(Y)).sum())
    max_abs_out = float(Y.abs().masked_fill(~torch.isfinite(Y), 0).max())
    del Y
    t0 = time.perf_counter()
    if finite:
        s = svdvals_inplace(J)                         # MKL dgesdd in place: one copy of J in memory, not two
    else:                                              # the signal overflowed (deep blocks of degree 2): no spectrum
        s = np.full(min(rows, P), np.nan)
    del J
    t_svd = time.perf_counter() - t0
    r, gap, gap_pred, s_pred = read_rank(s, pred) if finite else (-1, float("nan"), float("nan"), float("nan"))
    resolved = bool(finite and gap >= MIN_GAP)       # below this the spectrum has no clear gap: no rank is read
    out = dict(cfg, p=p, q=q, P=P, rows=rows, B=B, pred=pred, rank=r, match=(r == pred), gap=gap,
               gap_at_pred=gap_pred, s_at_pred=s_pred, t_jac=round(t_jac, 2), t_svd=round(t_svd, 2),
               maxrss_gb=round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2**20, 3),
               J_gb=round(rows * P * 8 / 2**30, 3), finite=finite, n_nonfinite=n_nonfinite,
               max_abs_J=max_abs_J, n_nonfinite_out=n_nonfinite_out, max_abs_out=max_abs_out,
               spectrum_nan=bool(np.isnan(s).any()), resolved=resolved)
    return out, (np.log10(np.maximum(s / s[0], 1e-300)) if finite else s).astype(np.float32)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", required=True, help="JSON object or list of objects, or @file")
    ap.add_argument("--out", default=None, help="directory for results.jsonl and the spectra (resumable)")
    a = ap.parse_args()
    text = open(a.config[1:]).read() if a.config.startswith("@") else a.config
    cfgs = json.loads(text)
    cfgs = cfgs if isinstance(cfgs, list) else [cfgs]
    if a.out:
        os.makedirs(os.path.join(a.out, "spec"), exist_ok=True)
    # Resumable: a run is done when its spectrum file exists. The result line is written first and the spectrum last,
    # each synced to disk, the spectrum by a rename: a crash at any point leaves the run either done or to be redone
    # (then its result line appears twice, and aggregate.py keeps the last one)
    for cfg in cfgs:
        if a.out and os.path.exists(os.path.join(a.out, "spec", key(cfg) + ".npy")):
            continue
        res, logs = run(cfg)
        line = json.dumps(res)
        print(line, flush=True)
        if a.out:
            append_line(os.path.join(a.out, "results.jsonl"), line)
            save_atomic(os.path.join(a.out, "spec", key(cfg) + ".npy"), logs)
