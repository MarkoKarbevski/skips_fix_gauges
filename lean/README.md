# Lean 4 formalization

A formalization, in Lean 4 with Mathlib, of statements of two of the papers of this repository:
"On the Functional Dimension of a Family of Analytic Neural Networks" and "Skip Connections Unlock
at Least d_model² Parameters per Layer". It is work in progress.

- [`STATEMENTS.md`](STATEMENTS.md) puts each statement of the papers beside its Lean statement,
  with its status, and lists where the Lean statement differs from the paper's on purpose.
- `SkipsLean/` holds the code. Tokens are rows and weights multiply on the right, as in the papers.
  One definition of a network serves both papers: the hidden states are
  `h_ℓ = h_{ℓ-1} S_ℓ + f_ℓ(χ(h_{ℓ-1}) W_read^ℓ) W_write^ℓ`, with `S = 0` without skip connections,
  `S = 1` with identity skips, and a general `S` for learned skips.

| File | Content |
|---|---|
| `Basic/RMSNorm.lean` | RMSNorm on rows; it commutes with orthogonal matrices |
| `Basic/RMSNormConverse.lean` | only orthogonal matrices (for `ε = 0`, their positive multiples) pass through RMSNorm |
| `Basic/LayerNorm.lean` | the computations that reduce LayerNorm to RMSNorm |
| `Network/Defs.lean` | blocks, networks, hidden states, the function of a network |
| `Symmetry/ChangeOfBasis.lean` | changes of basis at the hidden states preserve the function |
| `Symmetry/Normalized.lean` | the same under pre-RMSNorm |
| `Symmetry/Reduction.lean` | the exact reduction: a `d × d` submatrix per hidden state becomes the identity, or upper triangular under pre-RMSNorm |
| `Residual/LearnedSkips.lean` | invertible learned skips reduce to identity skips; the one change of basis of a residual network |
| `Network/Blocks.lean` | MLP networks with a given activation |
| `Dimension/Space.lean` | the parameters as a finite-dimensional normed vector space |
| `Dimension/Functional.lean` | functional dimension, redundancy, flat directions; `fd(θ) = P − dim K(θ)` |
| `Dimension/UpperBound.lean` | the upper bound from the changes of basis: `fd ≤ P − (L+1)d²` without skip connections, `fd ≤ P − d²` with identity skips |
| `Dimension/UpperBoundRMSNorm.lean` | the same under pre-RMSNorm: `P − (L+1)d(d−1)/2` and `P − d(d−1)/2` |
| `Generic/AnalyticZeroSet.lean` | a real-analytic function that is not identically zero vanishes on a set of measure zero |
| `Generic/Params.lean` | statements at generic parameters: invertible submatrices, full ranks, the upper bounds for almost all parameters |
| `OneBlock/Factorization.lean` | the directions that keep `E W_read` and `W_write D` are those of two changes of basis |
| `OneBlock/UnitsTanh.lean` | a flat direction of tanh hidden units vanishes |
| `OneBlock/Tanh.lean` | one tanh block: the functional dimension is `P − 2d²` at generic parameters |

## Building

Install [elan](https://github.com/leanprover/elan), then in this folder:

```
lake exe cache get    # downloads the compiled Mathlib
lake build            # must finish with no `sorry` warning
lake env lean checks/Axioms.lean
```

The last command prints the axioms behind every theorem. Each line must show only `propext`,
`Classical.choice` and `Quot.sound`; a `sorryAx` would mean an open proof. Lean and Mathlib are
pinned to `v4.36.0` (`lean-toolchain`, `lakefile.toml`).
