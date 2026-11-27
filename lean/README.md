# Lean 4 formalization

A formalization, in Lean 4 with Mathlib, of the three papers of this repository: "Can an MLP Absorb
Its Skip Connection Exactly?" (the absorb paper), "On the Functional Dimension of a Family of
Analytic Neural Networks" (the dimension paper) and "Skip Connections Unlock at Least d_model²
Parameters per Layer" (the skips paper).

## Status

The three papers have 99 numbered theorems, propositions, lemmas and corollaries: 30 in the absorb
paper, 34 in the dimension paper and 35 in the skips paper. Of these, 96 are stated and proved here,
the main theorems included. The other three are Lemmas A.21, A.23 and A.24 of the skips paper, on
definable sets: no o-minimal structure is defined in Lean, and the one consequence of these lemmas
that the theorems use is taken as a hypothesis.

Three results from the literature are taken as hypotheses and are not proved here:

| Result | File | Used for |
|---|---|---|
| Sard's theorem | `Literature/Sard.lean` | skips paper: Lemma A.26, Theorem A.28 (ii) to (iv) and Theorem 4.11; absorb paper: Proposition 4.7 |
| The closure of a definable set of measure zero has measure zero | `Literature/OMinimal.lean` | skips paper: "not a pointwise limit" in Theorem A.28 (iv) and Theorem 4.11 |
| Invariance of domain | `Literature/InvarianceOfDomain.lean` | skips paper: Proposition A.32; absorb paper: Proposition 4.6 |

Each is a named proposition, and the theorems that use it take it as a hypothesis. None is declared
as an axiom, so the axiom check below stays at the three standard axioms.

A statement counts as proved when `lake build` passes with no `sorry` in its file and the axiom
check shows the three standard axioms for it. The Lean statements were compared with the papers,
statement by statement, by readers who did not write them. A proof of a Lean statement that differs
from the paper's says nothing about the paper, so [`STATEMENTS.md`](STATEMENTS.md) puts each
statement of the papers beside its Lean statement and lists where the two differ on purpose.

## Layout

- [`STATEMENTS.md`](STATEMENTS.md): the index. Each statement of the papers beside its Lean
  statement, with its file; the definitions; the three results assumed from the literature.
- `SkipsLean/`: the library, 425 files. Tokens are rows and weights multiply on the right, as in
  the papers. One definition of a network serves the three papers: the hidden states are
  `h_ℓ = h_{ℓ-1} M_ℓ + f_ℓ(χ(h_{ℓ-1}) W_read^ℓ) W_write^ℓ`, with `M = 0` without skip connections,
  `M = 1` with identity skips, and a general `M` for learned skips.
- `checks/Axioms.lean`: prints the axioms behind 2288 declarations of the library.
- `ai_notes/`: technical notes of the formalization, with their own README: the status of every
  numbered statement, the reports of the readers, and numeric checks of statements.

| Folder of `SkipsLean/` | Files | Content |
|---|---|---|
| `Basic/` | 5 | RMSNorm and LayerNorm on rows: RMSNorm commutes with orthogonal matrices and with no other invertible matrix (for `ε = 0`, with their positive multiples); the computations that reduce LayerNorm to RMSNorm |
| `Network/` | 10 | blocks, networks, hidden states and the function of a network; MLP, gated and attention blocks; networks of attention blocks and MLP blocks; biases; pre-LayerNorm networks; the blocks are real-analytic |
| `Activations/` | 13 | GELU, SiLU, ReLU and its square: analyticity, and GELU and SiLU far from zero through the Mills ratio, at real and complex arguments |
| `Generic/` | 12 | tools for statements at almost all parameters: zero sets of analytic functions, holomorphic extension, level sets, the dimensions of the groups of changes of basis |
| `Symmetry/` | 46 | changes of basis at the hidden states and the exact reduction; under pre-RMSNorm only orthogonal changes of basis pass; the symmetries inside the blocks, also with biases; permutations and sign flips; the groups that these generate, and where they act locally freely |
| `Dimension/` | 52 | the parameters as a vector space; functional dimension; the upper bounds from the symmetries; the equality condition and local identifiability; rank criteria |
| `OneBlock/` | 97 | the one-block theorems: tanh, GELU, ReLU, ReLU², gated and attention blocks, without skip connections, with identity skips and with full or upper triangular learned skips, without normalization and under pre-RMSNorm |
| `Depth/` | 72 | networks without skip connections at any depth (Theorem 5.2 of the dimension paper): tanh, GELU and gated blocks; inactive hidden units, where the count fails |
| `Residual/` | 82 | learned skips reduce to identity skips; the one change of basis of a residual network; residual networks at any depth, with small writes; the gain of the skip connections; residual and skipless networks compute different functions; folding and dead units of ReLU blocks |
| `Absorb/` | 32 | the absorb paper: blocks that absorb their skip connection and blocks that never do, networks, RMSNorm, attention, limits, biases |
| `Literature/` | 3 | the three results assumed from the literature |

## Building

Install [elan](https://github.com/leanprover/elan), then in this folder:

```
lake exe cache get    # downloads the compiled Mathlib
lake build            # must finish with no `sorry` warning
lake env lean checks/Axioms.lean
```

The last command prints the axioms behind 2288 declarations. Each line must show only `propext`,
`Classical.choice` and `Quot.sound`; a `sorryAx` would mean a proof that is not finished. Lean and
Mathlib are pinned to `v4.36.0` (`lean-toolchain`, `lakefile.toml`).
