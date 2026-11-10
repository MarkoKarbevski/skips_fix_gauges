# Skip connections: two papers, with code and data

This repository holds two companion papers on what a skip connection changes, the code that reproduces their numbers, and the data that the code saves.

| Paper | Authors | Folder |
|---|---|---|
| **Can an MLP Absorb Its Skip Connection Exactly?** | Antonij Mijoski, Marko Karbevski | `paper docs/new_paper_absorb_skip/` |
| **Skip Connections Unlock d_model² Parameters per Layer** | Marko Karbevski, Antonij Mijoski | `paper docs/new_paper_skips_unlock_d2_params/` |

Each folder holds the PDF, its LaTeX source and `refs.bib`; the second also holds `figs/`.

**Can an MLP Absorb Its Skip Connection Exactly?** A block absorbs its skip if the block with its skip computes the same function as a skipless block of the same kind that is at least as wide. For blocks without biases, the answer depends on the activation. Almost every ReLU or GELU block at least as wide as the model dimension `d_model` absorbs its skip with exactly `d_model` more hidden units. Squared-ReLU, gated (ReGLU, SwiGLU, GeGLU), tanh and attention blocks never do, however wide. Without normalization, no residual squared-ReLU, gated or tanh network equals a skipless one, and under RMSNorm almost no residual network does. Yet without normalization every skipless network is a limit of residual ones. The paper is theory; its one numerical check is Section 14 of the notebook.

**Skip Connections Unlock d_model² Parameters per Layer.** Residual and skipless networks with the same blocks have the same parameters. Without skips, every hidden state has a free basis: the next block undoes any change of basis, so fixing the basis removes `d_model²` parameters without changing the function, or `d_model (d_model − 1) / 2` under RMSNorm. A skip adds the old hidden state to the new one, which ties these bases into one. With skips, these parameters move the function. For continuous inputs, the skips raise the functional dimension by at least this much at any depth, for attention, tanh, GELU, SwiGLU and GeGLU networks. Without normalization the gain is exactly `d_model²` per block for one block, tanh networks, and GELU networks at least `2 d_model` wide. The notebook and the folders `data/` and `trained/` reproduce the numbers, tables and figures of this paper.

Both papers grew out of a longer note, *A Note on Residual Networks: Skip Connections Unlock d_model² Parameters per Layer* (65 pages; earlier titles *Skip Connections are Gauge Fixes* and *Skip Connections Collapse O(L d²) Gauge Degrees of Freedom*). It is kept as `skip-connections-gauge-fixes-.pdf`, with its source `paper docs/new_main.tex`. The proofs of the two papers were ported from it and revised since; where they differ, the papers are current.

## Contents

    paper docs/new_paper_absorb_skip/             the first paper
    paper docs/new_paper_skips_unlock_d2_params/  the second paper
    paper docs/tools/                             build script and define-before-use check for the two papers
    paper docs/new_main.tex, main.tex             the longer note and an older version of it
    paper docs/refs.bib, paper docs/figs/         bibliography and figures of the longer note
    skip-connections-gauge-fixes-.pdf             the longer note
    experiments.ipynb   the notebook, with its outputs
    data/               saved results of the notebook's two long experiments
    trained/            small networks trained on four datasets, and the ranks of their Jacobians
    large_runs/         ranks for larger networks, with its own README
    novelty_checks/     four AI models asked on 2026-11-05 for all the reasons skip connections help, dated and hashed
    pyproject.toml      the dependencies, pinned in uv.lock
    uv.lock             the locked environment
    .python-version     Python 3.11
    requirements.txt    the same pinned versions, for pip

## Building the papers

    bash "paper docs/tools/build.sh" all      # or A for the first paper, B for the second

This needs `latexmk` with pdfLaTeX, `pdfinfo` and Python 3. The script compiles a paper, copies the PDF next to its source, and checks that the main text defines every term and symbol before using it. It exits with status 1 if LaTeX fails, a reference is undefined, or the check finds a use before its definition. `PAPER_BUILD_DIR` sets where LaTeX writes its build files (default `/tmp/paper_build`).

The check is `check_flow.py`. It splits the main text into reading units and looks for the terms and symbols listed in `glossary_A.py` and `glossary_B.py`. A term that readers know may be accepted, with a reason, in `flow_allow_A.txt` or `flow_allow_B.txt`. The check also writes the flow graph of each paper next to it (`*_flow.md`): what each unit defines and what it uses first.

Two more tools sit in the same folder. `make_chunks.py` writes one file per reading unit, for a review that reads the text strictly in order. `pre-commit` is a Git hook that runs the check on a staged paper; install it with `cp "paper docs/tools/pre-commit" .git/hooks/pre-commit`.

## Running the notebook

`experiments.ipynb` reproduces the computed numbers, tables and figures of the second paper. Each section says what it reproduces and runs on its own after the setup cell. The notebook is saved with its outputs, so the results can be read without running it.

The notebook was written for the longer note, and its headings and comments still use that note's numbering. The table of sections below gives the numbering of the second paper; the same table is in its Appendix E.

Everything runs on a CPU, in double precision, with Python 3.11 and the versions pinned in `uv.lock`: NumPy 2.4.4, SciPy 1.17.1, Matplotlib 3.10.9, python-flint 0.9.0, scikit-learn 1.9.1 and PyTorch 2.14.0 (CPU build on Linux and Windows; the standard build on macOS 14 or later with Apple silicon).

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

The two long experiments save what their figures and table need in `data/`:

- `spectra.npz`, for Figures 1 and 3 of the second paper: for every activation, with and without skips and without skips with hidden units added, without normalization and under pre-RMSNorm with ε = 10⁻⁵ (the figures of the paper) and ε = 10⁻², the base-10 logarithms of the median, smallest and largest singular value at every index over 20 draws, in single precision, and the rank and gap of every draw; and the ranks and gaps of the further checks of Section 10, such as the ReGLU networks with ε = 10⁻¹².
- `nanogpt.json`, for Table 7: for every nanoGPT network (normalization, number of layers, draw, with or without skips), the number of parameters, the rank of the Jacobian and the gap at which it is read, and, for one and two layers, the rank of the constructed symmetry directions and their largest residual.

With `RECOMPUTE = False`, the default in the setup cell, Sections 10 and 13 draw the figures and the table from these files in seconds, computing only what a file lacks. With `RECOMPUTE = True`, or when a file is missing, they rerun the experiments and save the files again.

Run from the repository root, Section 10 writes Figure 3 to `figs/spectra.pdf`, the same figure with ε = 10⁻² to `figs/spectra_eps1e-2.pdf`, and Figure 1 to `figs/spectra_gelu.pdf`. The copies that the paper includes are in `paper docs/new_paper_skips_unlock_d2_params/figs/`.

## Notebook sections

The first column gives each heading as it stands in the notebook, in the numbering of the longer note. The second column uses the numbering of the second paper.

| Section of the notebook | Reproduces, in the second paper | Time |
|---|---|---|
| 1. The gauge fix, the counts and RMSNorm | exactness checks of Theorems A.5 and A.10 and Proposition A.9; finite-difference rows of Table 6; exact ReLU and degree-two Jacobians | 1 min |
| 2. The last row of Table 2 | the last row of Table 3 | 23 s |
| 3. A dominant block, and learned, tied and low-rank skips | the checks of Sections 3, 3.3 and 3.4 | under 1 s |
| 4. The redundancy of low-rank skips | the low-rank skips of Section 3.4 | 36 s |
| 5. DyT reads | the DyT networks | 9 s |
| 6. Exact reductions after training | the reductions of Section 3.1 and Proposition A.12 | under 1 s |
| 7. The symmetry group of a transformer is not a product | Table 4 | under 1 s |
| 8. Counts at model scale | Table 5 | under 1 s |
| 9. One block | Theorem B.1, for MLP and attention blocks | 44 s |
| 10. Figure 2: deeper networks | Figures 1 and 3 and the checks of their networks | 28 min, or a few seconds from `data/` |
| 11. Exact Jacobians for Table 5 | the rows at d_model = 16, the transformers and the embedding table of Table 6 | 4 min |
| 12. Certificates modulo a prime | the certificates at L = 3 in Table 6 | 19 s |
| 13. nanoGPT | Table 7 and the constructed symmetries | 38 min, or under 1 s from `data/` |
| 14. Skipless networks as limits of residual networks | the limits of the first paper (its Proposition 5.1) | under 1 s |
| 15. ReLU draws above the count | the ReLU draws above the count in Appendix E | 2 min |
| 16. Certificates at depth | the certificates at L = 8 in Table 6 | 5 min |
| 17. Homogeneous blocks under RMSNorm | the checks of Lemma A.3 | 2 s |

Wall-clock times are for two CPU cores, with the experiments rerun in Sections 10 and 13.

## Trained networks

The folder `trained/` trains the small networks of Figure 3 of the second paper on four small classification datasets and computes the rank of their Jacobian at the trained weights. Figure 4 of that paper shows the GELU networks.

    trained/small_nets.py   networks, datasets, training and Jacobians, shared by the two notebooks
    trained/train.ipynb     trains and stores the networks, with its outputs
    trained/analyze.ipynb   loads them and computes the Jacobians, with its outputs
    trained/runs/           the 768 stored networks: parameters in float64, curves and accuracies
    trained/results/        linear baselines, training summary, ranks, spectra and figures

The networks are those of the figure: an embedding R^p → R^4, three MLP blocks of width 8 and a readout R^4 → R^q, without biases; tanh, GELU, ReGLU or SwiGLU blocks; no normalization or pre-RMSNorm with ε = 10⁻⁵; with skips, without, and without skips with hidden units added. Two datasets come from scikit-learn's generators (`hypercube`, `clusters`) and two from PMLB (`satimage`, `segmentation`, downloaded into `trained/data/` on first use). The learning rate is chosen on the validation loss of seed 0, five seeds are trained to convergence, and a network counts as trained when it beats tuned logistic regression on the test set: 436 of 480 do.

At the trained weights the rank equals the symmetry count in 398 of the 436 trained networks, on inputs of the dataset and on Gaussian inputs alike, and the skips add exactly L d² = 48 without normalization and L d(d−1)/2 = 18 under RMSNorm. Of the 38 exceptions, 36 are skipless ReGLU networks under RMSNorm, which are the exception at random weights too (Section 4.5 of the paper). One GELU network with skips on `clusters` is 8 below the count, and one tanh network with skips under RMSNorm on `satimage` is 1 below.

    uv run jupyter nbconvert --to notebook --execute --inplace trained/train.ipynb      # 36 min; stored networks are loaded
    uv run jupyter nbconvert --to notebook --execute --inplace trained/analyze.ipynb    # 2 min

## Larger networks

The folder `large_runs/` computes the rank of the exact Jacobian for larger networks: 2, 4, 8 and 64 MLP blocks, and transformers of 8 blocks, without normalization and with pre-RMSNorm. Its own README describes the networks, the runs and the scripts. The figures are in `paper docs/figs/large/`; they are not part of the two papers.

## Citation

    @unpublished{mijoski2026worth,
      title  = {Can an {MLP} Absorb Its Skip Connection Exactly?},
      author = {Mijoski, Antonij and Karbevski, Marko},
      year   = {2026}
    }

    @unpublished{karbevski2026unlock,
      title  = {Skip Connections Unlock $d_{\mathrm{model}}^2$ Parameters per Layer},
      author = {Karbevski, Marko and Mijoski, Antonij},
      year   = {2026}
    }

Add the arXiv identifiers once the preprints are posted.

## License

Apache License 2.0; see `LICENSE`.
