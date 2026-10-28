# Functional dimension of larger networks

The figures are in `paper docs/figs/large/`: `spectra_depth_<activation>.pdf` (2, 4 and 8 MLP blocks of width 16 and
transformers of 8 blocks, without normalization and with pre-RMSNorm), `spectra_deep_<activation>.pdf` (64 blocks of
width 4), `spectra_eps.pdf` (skipless ReLU networks under RMSNorm as eps goes to 0), `spectra_eps8.pdf` (the same at 8 blocks for ReLU, ReLU^2, ReGLU and, as a control, GELU) and `almost_sym.pdf` (Lemma A.2:
the directions that are symmetries only at eps = 0, against eps).

## Contents

- `fdim_large.py`, `svd_inplace.py`: the rank of the exact Jacobian of one network (below).
- `make_queue3.py`, `queue3.json`, `make_queue4.py`, `queue4.json`, `queue_eps.json`, `make_queue_eps2.py`,
  `queue_eps2.json`: the networks that were run (`queue4`: depths 2 and 4; `queue_eps2`: the eps sweep of ReLU^2, ReGLU
  and GELU at 8 blocks); `progress.py` reports a run directory.
- `results_v3.jsonl`, `results_v4.jsonl`, `results_eps.jsonl`, `results_eps2.jsonl`: one line per network and draw (rank, predicted rank,
  gap, timings).
- `aggregate.py`, `plot_v4.py`, `plot_eps.py`, `plot_eps2.py`: spectra to one `.npz`, and the figures from it; `plot_v4.py --families
  L2,L4,L8,tf` draws the depth figures and `--families deep` the 64-block ones. The spectra themselves and the
  aggregated files (`spectra_v4.npz` of `runs/v3` and `runs/v4`, 50 MB; `spectra_eps.npz`, 31 MB) are not in the
  repository; `python3 fdim_large.py --config @queue4.json --out runs/v4` recomputes them (resumable).
- `almost_sym.py`, `formula_curves.py`, `plot_almost_sym.py`, with `almost_sym.jsonl` and `formula_curves.json`: for
  8 skipless blocks under pre-RMSNorm, the largest singular value of the Jacobian on the directions e^{tS} (S symmetric)
  at every hidden state, computed in double precision and from the formula of Lemma A.2, for eps from 1e-1 to 1e-12.
- `check_*.py`: the one-block checks of Theorem C.1 parts (b)-(d) at d_model = 4, width 8: learned skips over identity
  skips at eps = 1e-2 and 1e-12 (`check_oneblock_learned.py`, `check_part_c.py`), SwiGLU and GeGLU without
  normalization (`check_glu_parta.py`), identity skips at eps = 1e-12 (`check_eps0_identity.py`), and three blocks at
  eps = 1e-12 (`check_eps0_learned.py`).

`fdim_large.py` computes, at random parameters, the rank of the exact float64 Jacobian of the parameter-to-output
map of a network on a batch of random inputs, reads it at the largest gap of the singular values, and compares it
with the symmetry count of the note. `aggregate.py` collects the spectra into one `.npz`; `plot_v4.py` draws a figure
from that file alone, so the style can change without rerunning anything. The queues are `queue3.json`
(`make_queue3.py 64 4`) and `queue4.json`, run into `runs/v3/` and `runs/v4/` (resumable: finished networks are
skipped).

## Networks

Row vectors, as in the note, no biases. MLP networks: `h_0 = x E`, `h_l = h_{l-1} S_l + f(N(h_{l-1}) W_up^l) W_dn^l`,
`y = N(h_L) D`. Transformers: every layer is a causal attention block (H heads of width d/H; reads W_Q, W_K, W_V,
write W_O; no positional embeddings) followed by an MLP block, each with its own skip; tokens are rows of
`x` (T x d_model). `S_l` is 0 (no skip), `I`, a full learned matrix (started at `I + 0.2 G / sqrt(d)`) or a learned
upper-triangular one. `N` is the identity or RMSNorm with `eps = 1e-5`.

Hidden widths as in practice: `m = 4 d_model` for GELU, ReLU, ReLU^2 and tanh (nanoGPT), and
`m = int(2/3 * 4 d_model)` for SwiGLU, GeGLU and ReGLU (Llama, without its rounding to a multiple of 256), whose
read `W_up` has `2m` columns (gates and values).

| family | blocks L | d_model | m (gated) | activations |
|---|---|---|---|---|
| `deep` | 64 MLP blocks | 4 | 16 (10) | all seven |
| `L2`, `L4`, `L8` | 2, 4 and 8 MLP blocks | 16 | 64 (42) | all seven |
| `tf` | 4 layers = 8 blocks, 4 heads, 8 tokens | 16 | 64 (42) | GELU (nanoGPT), SwiGLU (Llama) |

Three draws of each network (seeds 0, 1, 2).

## Starts

Rank is a generic property: almost every parameter point gives the same rank, so each network is measured at a
random point where double precision can resolve it.
- Residual networks: Gaussian `N(0, 1/fan_in)` weights, writes times `1/sqrt(L)`, or `1/L` for blocks of degree 2
  (ReLU^2 and the gated blocks) without normalization, whose residual stream otherwise overflows.
- MLP networks without skips, GELU, ReLU and tanh: looks-linear start (Balduzzi et al., 2017). Hidden units come in
  pairs with opposite reads and writes, and `sigma(z) - sigma(-z) = z` (GELU, ReLU), so each block starts at the
  identity; noise of 0.3 times the Gaussian scale then makes the point generic. tanh pairs read at 0.4 times the
  scale, where `2 tanh(z)` is nearly linear. Other activations have no such pairing (every unit vanishes to second
  order at 0) and start Gaussian with the usual writes. GELU networks without skips are also run from the Gaussian
  start, for comparison.
- Transformers without skips: Gaussian start.

## Predicted ranks

`s` counts the symmetries inside the blocks: a positive rescaling per hidden unit for ReLU and ReLU^2, the value of
every gated unit for SwiGLU and GeGLU, its gate as well for ReGLU, and in every attention block an invertible map per
head between queries and keys and one between values and outputs (`2 H (d/H)^2`). With `L` blocks, every entry is
lowered by `s`:

| skip | no normalization | pre-RMSNorm, eps > 0 (o = d(d-1)/2) |
|---|---|---|
| none | P - (L+1) d^2 | P - (L+1) o |
| identity | P - d^2 | P - o |
| full learned | P - (L+1) d^2, the identity value | P - (L+1) o, the identity value + L d(d+1)/2 |
| triangular | P - d^2 - L d(d+1)/2, the identity value | P - o, the full learned value |

## Batch size

One input gives at most `min(q, d_model)` independent rows (a transformer input, `T` times as many). Under RMSNorm the
readout sees `N(h_L)`, which passes the radial direction of `h_L` only through a factor `eps / r^2`, so an input gives
`min(q, d_model) - 1` rows of full size; the batch is sized for that. (Earlier runs used `min(q, d_model)` under RMSNorm
too, which left their batches short and their gaps thin.)

## Reading the rank, NaNs

The rank is read at the largest gap of `log10(s_i / s_1)`, clamped at `1e-18`. Every run records the number of
non-finite entries of the Jacobian (`n_nonfinite`) and of the outputs (`n_nonfinite_out`), the largest finite entries
(`max_abs_J`, `max_abs_out`), and `finite`; a run whose Jacobian is not finite gets rank -1 and no spectrum, and
`aggregate.py` reports it as NON-FINITE in k/n draws.

## The file `spectra_v4.npz`

For every network `<net>` (`fdim_large.net_name`):
- `<net>_median`, `<net>_min`, `<net>_max`: log10 of `s_i / s_1` at every index, median and range over the draws
- `<net>_draws`: the same for every draw (one row per draw)
- `<net>_ranks`, `<net>_gaps`: rank read at the largest gap, and the gap, in every draw
- `<net>_info`: `[P, predicted rank, rows of the Jacobian, inputs]`
- `meta_json`: the settings, ranks, matches, NaN counts and timings of every network, as JSON
