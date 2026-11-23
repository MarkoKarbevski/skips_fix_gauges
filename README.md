# Skip connections: three papers, with code and data

This repository holds three companion papers on what a skip connection changes, the code that reproduces their numbers, and the data that the code saves.

| Paper | Authors | Main result | Folder |
|---|---|---|---|
| **Can an MLP Absorb Its Skip Connection Exactly?**<br>Nominated for an oral in the extended abstract track at NeurReps. | Antonij Mijoski, Marko Karbevski | Almost every ReLU or GELU block absorbs its skip with exactly `d_model` more hidden units; squared-ReLU, gated, tanh and attention blocks never do. | `paper docs/new_paper_absorb_skip/` |
| **On the Functional Dimension of a Family of Analytic Neural Networks** | Marko Karbevski | Without skips, `d_model²` parameters per layer can be removed without changing the function, or about `d_model² / 2` under pre-RMSNorm, for layers of any kind, attention included. For tanh, SwiGLU and GeGLU layers and GELU layers under pre-RMSNorm at any depth, and for one attention block, this and the symmetries inside the layers are the only redundancy. | `paper docs/new_paper_functional_dimension/` |
| **Skip Connections Unlock at Least d_model² Parameters per Layer** | Marko Karbevski, Antonij Mijoski | A residual network of attention, tanh, GELU, SwiGLU or GeGLU layers keeps one change of basis where a skipless one has one per hidden state, so skips unlock at least `d_model²` functional dimensions per layer, or about `d_model² / 2` under pre-RMSNorm. | `paper docs/new_paper_skips_gain/` |

Each folder holds the PDF, its LaTeX source and `refs.bib`; the third also holds `figs/`.

**Can an MLP Absorb Its Skip Connection Exactly?** A block absorbs its skip if the block with its skip computes the same function as a skipless block of the same kind that is at least as wide. For blocks without biases, the answer depends on the activation. Almost every ReLU or GELU block at least as wide as the model dimension `d_model` absorbs its skip with exactly `d_model` more hidden units. Squared-ReLU, gated (ReGLU, SwiGLU, GeGLU), tanh and attention blocks never do, however wide. Without normalization, no residual squared-ReLU, gated or tanh network equals a skipless one, and under RMSNorm almost no residual network does. Yet without normalization every skipless network is a limit of residual ones. The paper is theory; its one numerical check is Section 14 of the notebook.

**On the Functional Dimension of a Family of Analytic Neural Networks.** The functional dimension of a network is the number of independent directions in which its parameters change the function that it computes. The paper studies deep networks in which every layer has input weights, a fixed nonlinear map and output weights, as the layers of a transformer have. Between two such layers, the output weights of the first can be multiplied by an invertible matrix and the input weights of the second by its inverse. With this symmetry, `d_model²` parameters per layer are removed without changing the function, or about `d_model² / 2` under pre-RMSNorm. For tanh, SwiGLU and GeGLU layers, and for GELU layers under pre-RMSNorm, the paper proves that nothing more can be removed, at any depth. The folder `functional_dimension/` holds the two scripts that compute its numbers.

**Skip Connections Unlock at Least d_model² Parameters per Layer.** The paper computes the functional dimension of networks with skip connections. In a residual transformer of any depth with analytic layers such as attention, GELU or SwiGLU, the only redundancy consists of the symmetries inside the layers and a single change of basis of the whole network. A network without skip connections has such a change of basis at every hidden state, hence one more per layer. So skip connections unlock at least `d_model²` functional dimensions per layer, or about `d_model² / 2` under pre-RMSNorm, and exactly this many where the count without skip connections is known to be exact, as for tanh, SwiGLU and GeGLU layers. The notebook and the folders `data/` and `trained/` reproduce the numbers, tables and figures of this paper.

## Earlier versions

The folder `paper docs/archive/` holds the texts from which the three papers were cut: a merged paper, *Skip Connections Unlock d_model² Parameters per Layer* (`new_paper_skips_unlock_d2_params/`), two intermediate cuts of it (`new_paper_skips_at_least/`, `new_paper_skips_exactly/`), and a longer note, *A Note on Residual Networks: Skip Connections Unlock d_model² Parameters per Layer* (65 pages; earlier titles *Skip Connections are Gauge Fixes* and *Skip Connections Collapse O(L d²) Gauge Degrees of Freedom*), kept as `skip-connections-gauge-fixes-.pdf` with its source `paper docs/archive/new_main.tex`. The proofs of the three papers were ported from these texts and revised since; where they differ, the three papers are current.

## Contents

    paper docs/new_paper_absorb_skip/             the first paper
    paper docs/new_paper_functional_dimension/    the second paper
    paper docs/new_paper_skips_gain/              the third paper
    paper docs/tools/                             build script and define-before-use check for the papers
    paper docs/archive/                           the earlier versions, with the bibliography and figures of the longer note
    skip-connections-gauge-fixes-.pdf             the longer note
    functional_dimension/   the two scripts of the second paper
    lean/                   a Lean 4 formalization of statements of the second and third papers, in progress, with its own README
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

    bash "paper docs/tools/build.sh" all      # or one letter: A, E or F

The letters are A for the first paper, E for the second and F for the third; B, C and D build the three papers in `paper docs/archive/`. This needs `latexmk` with pdfLaTeX, `pdfinfo` and Python 3. The script compiles a paper, copies the PDF next to its source, and checks that the main text defines every term and symbol before using it. It exits with status 1 if LaTeX fails, a reference is undefined, or the check finds a use before its definition. `PAPER_BUILD_DIR` sets where LaTeX writes its build files (default `/tmp/paper_build`).

The check is `check_flow.py`. It splits the main text into reading units and looks for the terms and symbols listed in the glossary of the paper (`glossary_A.py` to `glossary_F.py`). A term that readers know may be accepted, with a reason, in `flow_allow_A.txt` to `flow_allow_F.txt`. The check also writes the flow graph of each paper next to it (`*_flow.md`): what each unit defines and what it uses first.

Two more tools sit in the same folder. `make_chunks.py` writes one file per reading unit, for a review that reads the text strictly in order. `pre-commit` is a Git hook that runs the check on a staged paper; install it with `cp "paper docs/tools/pre-commit" .git/hooks/pre-commit`.

## Scripts of the second paper

    python3 functional_dimension/ranks.py             # about 30 seconds
    python3 functional_dimension/global_rotation.py   # a few seconds

`ranks.py` computes the table of Appendix F of the second paper: the rank of the Jacobian of 106 networks without skip connections (tanh, GELU, SwiGLU and GeGLU blocks, without normalization and under pre-RMSNorm with ε = 0.1 and ε = 0, and attention blocks of one to three layers), against the bound of the paper. It prints, for every network, the bound, the rank and the gap of the spectrum at the rank, and then the 15 rows of the table. `global_rotation.py` computes the numbers of Appendix G: in a pre-LayerNorm transformer of three layers, one rotation of the whole stream changes the outputs by about 10⁻¹⁴, and by about 19 when one layer is left out. Both run on a CPU in double precision, in the environment of the notebook below (PyTorch, NumPy and SciPy).

## Running the notebook

`experiments.ipynb` reproduces the computed numbers, tables and figures of the third paper. Each section says what it reproduces and runs on its own after the setup cell. The notebook is saved with its outputs, so the results can be read without running it.

The notebook was written for the longer note, and its headings and comments still use that note's numbering. The table of sections below gives the numbering of the third paper; the same table is in its Appendix E.

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

- `spectra.npz`, for Figures 1 and 4 of the third paper: for every activation, with and without skips and without skips with hidden units added, without normalization and under pre-RMSNorm with ε = 10⁻⁵ (the figures of the paper) and ε = 10⁻², the base-10 logarithms of the median, smallest and largest singular value at every index over 20 draws, in single precision, and the rank and gap of every draw; and the ranks and gaps of the further checks of Section 10, such as the ReGLU networks with ε = 10⁻¹².
- `nanogpt.json`, for Table 7: for every nanoGPT network (normalization, number of layers, draw, with or without skips), the number of parameters, the rank of the Jacobian and the gap at which it is read, and, for one and two layers, the rank of the constructed symmetry directions and their largest residual.

With `RECOMPUTE = False`, the default in the setup cell, Sections 10 and 13 draw the figures and the table from these files in seconds, computing only what a file lacks. With `RECOMPUTE = True`, or when a file is missing, they rerun the experiments and save the files again.

Run from the repository root, Section 10 writes Figure 4 to `figs/spectra.pdf`, the same figure with ε = 10⁻² to `figs/spectra_eps1e-2.pdf`, and Figure 1 to `figs/spectra_gelu.pdf`. The copies that the paper includes are in `paper docs/new_paper_skips_gain/figs/`.

## Notebook sections

The first column gives each heading as it stands in the notebook, in the numbering of the longer note. The second column uses the numbering of the third paper.

| Section of the notebook | Reproduces, in the third paper | Time |
|---|---|---|
| 1. The gauge fix, the counts and RMSNorm | exactness checks of Theorems A.5 and A.12 and Proposition A.9; finite-difference rows of Table 6; exact ReLU and degree-two Jacobians | 1 min |
| 2. The last row of Table 2 | the last row of Table 2 | 23 s |
| 3. A dominant block, and learned, tied and low-rank skips | the checks of Sections 3, 3.3 and 3.4 | under 1 s |
| 4. The redundancy of low-rank skips | the low-rank skips of Section 3.4 | 36 s |
| 5. DyT reads | the DyT networks | 9 s |
| 6. Exact reductions after training | the reductions of Propositions A.9 and A.15 | under 1 s |
| 7. The symmetry group of a transformer is not a product | Table 3 | under 1 s |
| 8. Counts at model scale | Table 4 | under 1 s |
| 9. One block | Theorem B.1, for MLP and attention blocks | 44 s |
| 10. Figure 2: deeper networks | Figures 1 and 4 and the checks of their networks | 28 min, or a few seconds from `data/` |
| 11. Exact Jacobians for Table 5 | the rows at d_model = 16, the transformers and the embedding table of Table 6 | 4 min |
| 12. Certificates modulo a prime | the certificates at L = 3 in Table 6 | 19 s |
| 13. nanoGPT | Table 7 and the constructed symmetries | 38 min, or under 1 s from `data/` |
| 14. Skipless networks as limits of residual networks | the limits of the first paper (its Proposition 5.1) | under 1 s |
| 15. ReLU draws above the count | the ReLU draws above the count in Appendix E | 2 min |
| 16. Certificates at depth | the certificates at L = 8 in Table 6 | 5 min |
| 17. Homogeneous blocks under RMSNorm | the checks of Lemma A.3 | 2 s |

Wall-clock times are for two CPU cores, with the experiments rerun in Sections 10 and 13.

## Trained networks

The folder `trained/` trains the small networks of Figure 4 of the third paper on four small classification datasets and computes the rank of their Jacobian at the trained weights. Figure 5 of that paper shows the GELU networks.

    trained/small_nets.py   networks, datasets, training and Jacobians, shared by the two notebooks
    trained/train.ipynb     trains and stores the networks, with its outputs
    trained/analyze.ipynb   loads them and computes the Jacobians, with its outputs
    trained/runs/           the 768 stored networks: parameters in float64, curves and accuracies
    trained/results/        linear baselines, training summary, ranks, spectra and figures

The networks are those of the figure: an embedding R^p → R^4, three MLP blocks of width 8 and a readout R^4 → R^q, without biases; tanh, GELU, ReGLU or SwiGLU blocks; no normalization or pre-RMSNorm with ε = 10⁻⁵; with skips, without, and without skips with hidden units added. Two datasets come from scikit-learn's generators (`hypercube`, `clusters`) and two from PMLB (`satimage`, `segmentation`, downloaded into `trained/data/` on first use). The learning rate is chosen on the validation loss of seed 0, five seeds are trained to convergence, and a network counts as trained when it beats tuned logistic regression on the test set: 436 of 480 do.

At the trained weights the rank equals the symmetry count in 398 of the 436 trained networks, on inputs of the dataset and on Gaussian inputs alike, and the skips add exactly L d² = 48 without normalization and L d(d−1)/2 = 18 under RMSNorm. Of the 38 exceptions, 36 are skipless ReGLU networks under RMSNorm, which are the exception at random weights too (Appendix E of the paper). One GELU network with skips on `clusters` is 8 below the count, and one tanh network with skips under RMSNorm on `satimage` is 1 below.

    uv run jupyter nbconvert --to notebook --execute --inplace trained/train.ipynb      # 36 min; stored networks are loaded
    uv run jupyter nbconvert --to notebook --execute --inplace trained/analyze.ipynb    # 2 min

## Larger networks

The folder `large_runs/` computes the rank of the exact Jacobian for larger networks: 2, 4, 8 and 64 MLP blocks, and transformers of 8 blocks, without normalization and with pre-RMSNorm. Its own README describes the networks, the runs and the scripts. The figures are in `paper docs/archive/figs/large/`; they are not part of the three papers.

## Citation

    @unpublished{mijoski2026worth,
      title  = {Can an {MLP} Absorb Its Skip Connection Exactly?},
      author = {Mijoski, Antonij and Karbevski, Marko},
      year   = {2026}
    }

    @unpublished{karbevski2026dimension,
      title  = {On the Functional Dimension of a Family of Analytic Neural Networks},
      author = {Karbevski, Marko},
      year   = {2026}
    }

    @unpublished{karbevski2026unlock,
      title  = {Skip Connections Unlock at Least $d_{\mathrm{model}}^2$ Parameters per Layer},
      author = {Karbevski, Marko and Mijoski, Antonij},
      year   = {2026}
    }

Add the arXiv identifiers once the preprints are posted.

## License

Apache License 2.0; see `LICENSE`.
