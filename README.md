# Skip Connections are Gauge Fixes repo

Code and data for the note **A Note on Residual Networks: Skip Connections are Gauge Fixes** or its earlier version **A Note on Residual Networks: Skip Connections Collapse O(Ld^2) Gauge Degrees of Freedom**

The note shows that a skip connection is a gauge fix. Give each block of a network `d_model` identity units, read and written by trainable matrices. Spending the changes of basis at the linear junctions between blocks turns them into identity skips. A residual network keeps a single change of basis for all its hidden states, while the skipless network with the same parameters keeps one per hidden state. The skips of `L` blocks therefore remove `L d_model²` dimensions of symmetry, and `L d_model (d_model − 1) / 2` under RMSNorm.

The notebook `experiments.ipynb` reproduces every computed number, table and figure of the note, in its order and numbering. Each section says what it reproduces and runs on its own after the setup cell. The notebook is saved with its outputs, so you can read the results without running it.

## Contents

    experiments.ipynb   the notebook, with its outputs
    pyproject.toml      the dependencies, pinned in uv.lock
    uv.lock             the locked environment
    .python-version     Python 3.11
    requirements.txt    the same pinned versions, for pip
    data/               saved results from which the notebook draws Figure 2 and Table 7

## Running it

Everything runs on a CPU, in double precision, with Python 3.11 and the versions pinned in `uv.lock`: NumPy 2.4.4, SciPy 1.17.1, Matplotlib 3.10.9 and PyTorch 2.14.0 (CPU build on Linux and Windows; the standard build on macOS 14 or later with Apple silicon).

With [uv](https://docs.astral.sh/uv/):

    uv sync
    uv run jupyter lab experiments.ipynb

To run every cell without opening the notebook:

    uv run jupyter nbconvert --to notebook --execute --inplace experiments.ipynb

With pip:

    python3.11 -m venv .venv
    source .venv/bin/activate        # Windows: .venv\Scripts\activate
    pip install -r requirements.txt
    jupyter lab experiments.ipynb

From the saved data, the whole notebook runs in about 7 minutes on two CPU cores. Rerunning the two long experiments as well takes about 60 minutes.

## Saved data

The two long experiments save what their figure and table need in `data/`:

- `spectra.npz`, for Figure 2: for every activation, with and without skips, without normalization and under pre-RMSNorm, the base-10 logarithms of the median, smallest and largest singular value at every index over 20 draws, in single precision, and the rank and gap of every draw.
- `nanogpt.json`, for Table 7: for every nanoGPT network (normalization, number of layers, draw, with or without skips), the number of parameters, the rank of the Jacobian and the gap at which it is read, and, for one and two layers, the rank of the constructed symmetry directions and their largest residual.

With `RECOMPUTE = False`, the default in the setup cell, Sections 10 and 13 draw Figure 2 and Table 7 from these files in seconds. With `RECOMPUTE = True`, or when a file is missing, they rerun the experiments and save the files again. Figure 2 is written to `figs/spectra.pdf`.

## Notebook sections

| Section | Reproduces | Time |
|---|---|---|
| 1. The gauge fix, the counts and RMSNorm | Theorems 2 and 5, Corollary 3, Proposition 6, Lemmas 8 and 9, Tables 2 and 6 | 1 min |
| 2. The last row of Table 2 | Table 2 | 23 s |
| 3. A dominant block, and learned, tied and low-rank skips | Sections 3.2, 4 and 5 | under 1 s |
| 4. The redundancy of low-rank skips | Section 4, Appendix E | 36 s |
| 5. DyT reads | Section 4, Appendix E | 9 s |
| 6. Exact reductions after training | Section 5, Theorem 5, Propositions 6 and 12, Lemma 10, Remark 11 | under 1 s |
| 7. The symmetry group of a transformer is not a product | Section 5.2, Appendix C, Table 3 | under 1 s |
| 8. Counts at model scale | Tables 4 and 5 | under 1 s |
| 9. One block | Section 6.1, Theorem 13, Appendix B | 44 s |
| 10. Figure 2 | Section 6.2, Figure 2 | 15 min, or under 1 s from `data/` |
| 11. Exact Jacobians | Table 6, Appendix E | 4 min |
| 12. Certificates modulo a prime | Table 6 | 19 s |
| 13. nanoGPT | Section 6.2, Table 7, Appendix E | 38 min, or under 1 s from `data/` |
| 14. Skipless networks as limits of residual networks | Section 6.3, Proposition 7 | under 1 s |

Wall-clock times are for two CPU cores, with the experiments rerun in Sections 10 and 13.

## Citation

    @misc{karbevski2026skip,
      title  = {A Note on Residual Networks: Skip Connections are Gauge Fixes},
      author = {Karbevski, Marko},
      year   = {2026}
    }

Add the arXiv identifier once the preprint is posted.
