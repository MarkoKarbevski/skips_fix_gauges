# Skip Connections are Gauge Fixes: repository

Code and data for the note **A Note on Residual Networks: Skip Connections are Gauge Fixes** and its earlier version **A Note on Residual Networks: Skip Connections Collapse O(Ld^2) Gauge Degrees of Freedom**.

The note shows that a skip connection is a gauge fix. Give each block of a network `d_model` identity units, read and written by trainable matrices. Without normalization, spending the changes of basis at the linear junctions between blocks turns them into identity skips. A residual network keeps a single change of basis for all its hidden states, while the skipless network with the same parameters keeps one per hidden state. The skips of `L` blocks therefore remove `L d_model²` dimensions of symmetry, and `L d_model (d_model − 1) / 2` under RMSNorm.

The notebook `experiments.ipynb` reproduces every computed number, table and figure of the note, in its order and numbering. Each section says what it reproduces and runs on its own after the setup cell. The notebook is saved with its outputs, so you can read the results without running it.

The note itself is `skip-connections-gauge-fixes-.pdf`, and its LaTeX source is in `paper docs/` (`new_main.tex`, `refs.bib` and `figs/`).

## Contents

    experiments.ipynb   the notebook, with its outputs
    pyproject.toml      the dependencies, pinned in uv.lock
    uv.lock             the locked environment
    .python-version     Python 3.11
    requirements.txt    the same pinned versions, for pip
    data/               saved results from which the notebook draws Figure 2 and Table 6
    novelty_checks/     four AI models asked on 2026-11-05 for all the reasons skip connections help, dated and hashed

## Running it

Everything runs on a CPU, in double precision, with Python 3.11 and the versions pinned in `uv.lock`: NumPy 2.4.4, SciPy 1.17.1, Matplotlib 3.10.9, python-flint 0.9.0 and PyTorch 2.14.0 (CPU build on Linux and Windows; the standard build on macOS 14 or later with Apple silicon).

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

From the saved data, the whole notebook runs in about 14 minutes on two CPU cores. Rerunning the two long experiments as well takes about 80 minutes.

## Saved data

The two long experiments save what their figure and table need in `data/`:

- `spectra.npz`, for Figure 2: for every activation, with and without skips and without skips with hidden units added, without normalization and under pre-RMSNorm with ε = 10⁻⁵ (the figure of the note) and ε = 10⁻², the base-10 logarithms of the median, smallest and largest singular value at every index over 20 draws, in single precision, and the rank and gap of every draw; and the ranks and gaps of the further checks of Section 10, such as the ReGLU networks with ε = 10⁻¹².
- `nanogpt.json`, for Table 6: for every nanoGPT network (normalization, number of layers, draw, with or without skips), the number of parameters, the rank of the Jacobian and the gap at which it is read, and, for one and two layers, the rank of the constructed symmetry directions and their largest residual.

With `RECOMPUTE = False`, the default in the setup cell, Sections 10 and 13 draw Figure 2 and Table 6 from these files in seconds, computing only what a file lacks. With `RECOMPUTE = True`, or when a file is missing, they rerun the experiments and save the files again. Figure 2 is written to `figs/spectra.pdf`, and the same figure with ε = 10⁻² to `figs/spectra_eps1e-2.pdf`.

## Notebook sections

| Section | Reproduces | Time |
|---|---|---|
| 1. The gauge fix, the counts and RMSNorm | Theorems 2 and 5, Corollary 3, Proposition 6, Lemmas 8 and 9, Tables 2 and 5 | 1 min |
| 2. The last row of Table 2 | Table 2 | 23 s |
| 3. A dominant block, and learned, tied and low-rank skips | Sections 3.2, 4 and 5 | under 1 s |
| 4. The redundancy of low-rank skips | Section 4, Appendix E | 36 s |
| 5. DyT reads | Section 4, Appendix E | 9 s |
| 6. Exact reductions after training | Section 5, Theorem 5, Propositions 6 and 12, Lemma 10, Remark 11 | under 1 s |
| 7. The symmetry group of a transformer is not a product | Section 5.2, Appendix C, Table 3 | under 1 s |
| 8. Counts at model scale | Table 4, Section 5.1, Appendix D | under 1 s |
| 9. One block | Section 6.1, Theorem 13, Appendix B | 44 s |
| 10. Figure 2 | Section 6.2, Figure 2, Appendix E | 28 min, or a few seconds from `data/` |
| 11. Exact Jacobians | Table 5, Appendix E | 4 min |
| 12. Certificates modulo a prime | Table 5 | 19 s |
| 13. nanoGPT | Section 6.2, Table 6, Appendix E | 38 min, or under 1 s from `data/` |
| 14. Skipless networks as limits of residual networks | Section 6.3, Proposition 7 | under 1 s |
| 15. ReLU draws above the count | the ReLU draws above the count, in the numerical checks | 2 min |
| 16. Certificates at depth | the certificates at L = 8 in the table of checks | 5 min |
| 17. Homogeneous blocks under RMSNorm | the checks of the lemma on homogeneous blocks under RMSNorm | 2 s |

Wall-clock times are for two CPU cores, with the experiments rerun in Sections 10 and 13.

## Trained networks

The folder `trained/` trains the small networks of Figures 1 and 4 of the note on four small classification datasets and computes the rank of their Jacobian at the trained weights.

    trained/small_nets.py   networks, datasets, training and Jacobians, shared by the two notebooks
    trained/train.ipynb     trains and stores the networks, with its outputs
    trained/analyze.ipynb   loads them and computes the Jacobians, with its outputs
    trained/runs/           the 768 stored networks: parameters in float64, curves and accuracies
    trained/results/        linear baselines, training summary, ranks, spectra and figures

The networks are those of the figures: an embedding R^p → R^4, three MLP blocks of width 8 and a readout R^4 → R^q, without biases; tanh, GELU, ReGLU or SwiGLU blocks; no normalization or pre-RMSNorm with ε = 10⁻⁵; with skips, without, and without skips with hidden units added. Two datasets come from scikit-learn's generators (`hypercube`, `clusters`) and two from PMLB (`satimage`, `segmentation`, downloaded into `trained/data/` on first use). The learning rate is chosen on the validation loss of seed 0, five seeds are trained to convergence, and a network counts as trained when it beats tuned logistic regression on the test set: 436 of 480 do.

At the trained weights the rank equals the symmetry count in 398 of the 436 trained networks, on inputs of the dataset and on Gaussian inputs alike, and the skips add exactly L d² = 48 without normalization and L d(d−1)/2 = 18 under RMSNorm. Of the 38 exceptions, 36 are skipless ReGLU networks under RMSNorm, the exception of Figure 4 at random weights too; one GELU network with skips on `clusters` is 8 below the count and one tanh network with skips under RMSNorm on `satimage` is 1 below.

    uv run jupyter nbconvert --to notebook --execute --inplace trained/train.ipynb      # 36 min; stored networks are loaded
    uv run jupyter nbconvert --to notebook --execute --inplace trained/analyze.ipynb    # 2 min

## Citation

    @misc{karbevski2026skip,
      title  = {A Note on Residual Networks: Skip Connections are Gauge Fixes},
      author = {Karbevski, Marko},
      year   = {2026}
    }

Add the arXiv identifier once the preprint is posted.

## License

Apache License 2.0; see `LICENSE`.
