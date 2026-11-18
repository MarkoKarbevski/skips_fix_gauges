# Variants of Figure 2

Standalone TikZ; build any of them with `pdflatex <name>.tex`. Figure 2 is `grid_core.tex` with `tags_paper.tex`.

- `grid_paper`: Figure 2 as in the paper. Each cell lists its own evidence, proven or simulated.
- `grid_new`: the same, with the runs of 8 and 64 blocks and the check at eps = 1e-12.
- `tree_A_tree`, `tree_B_dag`: identity skips as a tree and as a graph with one shared end; structure only.
- `tree_C_learned`: learned linear skips over identity skips, with their evidence.
