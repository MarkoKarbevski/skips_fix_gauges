# Statements: the papers beside the Lean code

For the authors. Each row puts a statement of a paper beside its Lean statement. "D" is "On the
Functional Dimension of a Family of Analytic Neural Networks" and "S" is "Skip Connections Unlock
at Least d_model² Parameters per Layer" (numbers of the PDFs of 22 November 2026). A row is
"proved" only when `lake build` passes with no `sorry` in the file and `#print axioms` shows the
three standard axioms. Please check the middle column against the paper: a proof of a statement
that differs from the paper's says nothing about the paper.

Conventions, as in the paper: tokens are rows, weights multiply on the right (`x * E`).

## Definitions

| Paper | Lean | File |
|---|---|---|
| Hidden state `h ∈ ℝ^{T×d_model}` | `Matrix T d ℝ` (`T`, `d` finite index types) | |
| RMSNorm `N_ε` on a row, on a hidden state (Section 2) | `Skips.rmsRow ε v`, `Skips.rmsNorm ε h` | `Basic/RMSNorm.lean` |
| The fixed part of a network: widths, the maps `f_ℓ`, the map `χ` | `Skips.Arch T d L` | `Network/Defs.lean` |
| Parameters `θ = (E, W_read^ℓ, W_write^ℓ, D)` | `Skips.Params A dIn dOut` | `Network/Defs.lean` |
| Hidden states, eq. (2): `h_0 = xE`, `h_ℓ = g_ℓ(χ(h_{ℓ-1}))` | `Skips.hidden A M θ x ℓ`, with `M = 0` | `Network/Defs.lean` |
| The function `F_θ`, eq. (2): `y = χ(h_L) D` | `Skips.eval A M θ x`, with `M = 0` | `Network/Defs.lean` |
| Definition 3.1 (change of basis), at all hidden states | `Skips.Params.cob θ G K` | `Symmetry/ChangeOfBasis.lean` |

Differences from the paper, on purpose:
1. `hidden` and `eval` take stream matrices `M ℓ`: `h_ℓ = h_{ℓ-1} M_ℓ + g_ℓ(χ(h_{ℓ-1}))`. The paper's
   networks are `M = 0`. `M = 1` is a residual network (the other two papers).
2. For `ε = 0` the paper defines a network only where no row of a hidden state vanishes. In Lean
   `rmsRow 0 0 = 0`. Statements for `ε = 0` that need a nonzero row will say so.
3. The maps `f_ℓ` are arbitrary in the definitions. The kinds of block (tanh, GELU, gated,
   attention) enter as choices of `f_ℓ` in later files.

## Results

Status: *defined* (a definition), *in work* (statement compiles, proof not finished), *proved*
(compiled, no `sorry`, standard axioms only). The branch `main` holds only what is proved; statements
in work are on the branch `lean-wip`. On 23 November 2026 every statement listed here is proved.

### Dimension paper

| Paper | Lean statement | File | Status |
|---|---|---|---|
| D Lemma A.1, "⇐": `N_ε(hQ) = N_ε(h)Q` for orthogonal `Q` | `rmsNorm_mul_orthogonal` | `Basic/RMSNorm.lean` | proved |
| D Lemma A.1, "⇐" for `ε = 0`: `N_0(h·cQ) = N_0(h)Q`, `c > 0` | `rmsNorm_zero_mul_smul_orthogonal` | `Basic/RMSNorm.lean` | proved |
| D Proposition 3.2, general form (also S eq. (6)) | `eval_cob` | `Symmetry/ChangeOfBasis.lean` | proved |
| D Proposition 3.2, without normalization | `eval_cob_skipless` | `Symmetry/ChangeOfBasis.lean` | proved |
| D Proposition 3.2, under pre-RMSNorm | `eval_cob_rmsNorm` | `Symmetry/Normalized.lean` | proved |
| D Proposition 3.2, `ε = 0`, `G_ℓ = c_ℓ Q_ℓ` | `eval_cob_rmsNorm_zero` | `Symmetry/Normalized.lean` | proved |
| D Proposition 3.3 (i), all hidden states at once | `exists_cob_reads_eq_one` | `Symmetry/Reduction.lean` | proved |
| D rows of a write (after Proposition 3.3, Example A.2) | `exists_cob_writes_eq_one` | `Symmetry/Reduction.lean` | proved |
| QR in the form `Qᵀ W` upper triangular (used by 3.3 (ii)) | `exists_orthogonal_transpose_mul_upperTriangular` | `Symmetry/Reduction.lean` | proved |
| D Proposition 3.3 (ii), all hidden states at once | `exists_cob_reads_upperTriangular` | `Symmetry/Reduction.lean` | proved |
| the count `d(d−1)/2` of entries below the diagonal | `card_below_diagonal` | `Symmetry/Reduction.lean` | proved |
| D Appendix A.3: `25·767·766/2 = 7,344,025` | `vitB_count` | `Symmetry/Reduction.lean` | proved |
| D Lemma A.1, "⇒", `ε > 0`: `N_ε(vG) = N_ε(v)M` for all `v ≠ 0` gives `G` orthogonal and `M = G` | `orthogonal_of_rmsRow_vecMul` | `Basic/RMSNormConverse.lean` | proved |
| D Lemma A.1, "⇒", `ε = 0`: then `M` is orthogonal and `G = cM`, `c > 0` | `conformal_of_rmsRow_zero_vecMul` | `Basic/RMSNormConverse.lean` | proved |
| D Proposition A.3 (i), its two facts: `Z² = Z`, rows `vZ` have mean zero | `centering_mul_centering`, `sum_vecMul_centering`, `vecMul_centering_of_sum_eq_zero` | `Basic/LayerNorm.lean` | proved |
| D Proposition A.3 (ii), the identity `N_ε(yŪᵀ) = sqrt(d/(d−1)) N'(y)Ūᵀ` (stated for any number `m` of orthonormal columns) | `rmsRow_vecMul_transpose_of_orthonormal` | `Basic/LayerNorm.lean` | proved |
| D parameters `θ ∈ ℝ^P` as a vector space; `P` is its dimension | `Params` with `AddCommGroup`, `Module ℝ`, a norm; `Module.finrank ℝ (Params A dIn dOut)` | `Dimension/Space.lean` | defined |
| D Definition 4.1: outputs on a batch, rank of the Jacobian, functional dimension, redundancy | `evalBatch`, `jacobianRank`, `funDim`, `redundancy` | `Dimension/Functional.lean` | defined |
| D Appendix C: flat directions `K(θ)` | `flat` | `Dimension/Functional.lean` | defined |
| differentiable `f_ℓ` and `χ` give `θ ↦ F_θ(x)` differentiable | `differentiable_eval` | `Dimension/Functional.lean` | proved |
| the maximum of Definition 4.1 is attained on a finite batch | `exists_jacobianRank_eq_funDim`, `jacobianRank_le_funDim`, `jacobianRank_le_finrank` | `Dimension/Functional.lean` | proved |
| D Appendix C: `fd(θ) = P − dim K(θ)` | `funDim_add_finrank_flat` | `Dimension/Functional.lean` | proved |
| D Section 4: a direction in which a symmetry moves `θ` is flat | `mem_flat_of_hasDerivAt`, `funDim_add_finrank_le_of_le_flat` | `Dimension/Functional.lean` | proved |
| the direction `(E X_0, −X_{ℓ−1} W_read^ℓ, W_write^ℓ X_ℓ, −X_L D)` of the changes of basis | `cobDir` | `Dimension/UpperBound.lean` | defined |
| D Lemma B.1, for the changes of basis: `E` and the writes of rank `d` ⇒ the direction determines `X` | `cobDir_injective` | `Dimension/UpperBound.lean` | proved |
| D Theorem 4.3, without normalization, changes of basis only: `fd ≤ P − (L+1)d²` | `cobDir_mem_flat_skipless`, `funDim_add_le_skipless` | `Dimension/UpperBound.lean` | proved |
| D Theorem 4.3, under pre-RMSNorm (`ε > 0`), changes of basis only: `fd ≤ P − (L+1)d(d−1)/2` | `differentiable_rmsNorm`, `cobDir_mem_flat_skipless_rmsNorm`, `finrank_antisymmetric`, `funDim_add_le_skipless_rmsNorm` | `Dimension/UpperBoundRMSNorm.lean` | proved |
| a real-analytic function that is not identically zero vanishes on a set of measure zero (not in Mathlib at this version) | `volume_zeroSet_of_analytic_pi`, `measure_zeroSet_of_analytic` | `Generic/AnalyticZeroSet.lean` | proved |
| D Proposition 3.3, last sentence: at generic parameters any `d` columns of a read or of `D`, and any `d` rows of `E` or of a write, form an invertible matrix | `ae_isUnit_det_submatrix` | `Generic/Params.lean` | proved |
| at generic parameters `E` and the writes have rank `d` (`d_in ≥ d`, at least `d` rows in each write) | `ae_rank_E_write` | `Generic/Params.lean` | proved |
| D Theorem 4.3 at generic parameters, changes of basis only, without normalization and under pre-RMSNorm | `ae_funDim_add_le_skipless`, `ae_funDim_add_le_skipless_rmsNorm` | `Generic/Params.lean` | proved |
| D Lemma C.3 for tanh, with the linear term, the constant and the biases | `tanh_units_flat_eq_zero` | `OneBlock/UnitsTanh.lean` | proved |
| an MLP network with activation `σ` (Section 2, "Blocks") | `Arch.mlp σ χ hid` | `Network/Blocks.lean` | defined |
| D Lemma C.2: the directions that keep `C = E W_read` and `A = W_write D` are those of two changes of basis | `keeps_products_iff_mem_range_cobDir` | `OneBlock/Factorization.lean` | proved |
| the conditions of the proof of Theorem C.1 (ranks `d`; rows of `A` nonzero; columns of `C` nonzero and pairwise non-collinear) | `OneBlockGeneric` | `OneBlock/Tanh.lean` | defined |
| D Theorem 5.1 / C.1 for a tanh block, under these conditions: `fd = P − 2d²` | `flat_le_range_cobDir_tanh`, `funDim_tanh_oneBlock` | `OneBlock/Tanh.lean` | proved |
| D Theorem 5.1 / C.1 for a tanh block at generic parameters (`d_in, d_out, d_hidden ≥ d ≥ 2`) | `ae_oneBlockGeneric`, `ae_funDim_tanh_oneBlock` | `OneBlock/Tanh.lean` | proved |

Notes for the authors on these statements:
- Proposition 3.3 is stated in the paper for one hidden state, with the remark that the reductions
  at all hidden states can be made together. The Lean statements are the simultaneous form.
- `exists_cob_reads_upperTriangular` does not assume that the chosen columns are invertible: a QR
  factorization exists for every square matrix. The paper assumes it.
- "At generic parameters" is written `∀ᵐ θ ∂μ` for an arbitrary additive Haar measure `μ` on the
  parameter space: a Lebesgue measure of that space, without a choice of coordinates. Any two
  differ by a positive constant, so they have the same sets of measure zero.
- Theorem 4.3 is stated under the conditions that its proof uses (`E` and every write have rank
  `d`, the maps `f_ℓ` are differentiable) and not yet "at generic parameters". It counts the
  changes of basis only, without the number `s` of the symmetries inside the blocks, which depend
  on the kind of block. For tanh and GELU blocks, where `s = 0`, this is the bound of the paper.
- The Jacobian needs a norm on the parameters and on the outputs. Matrices carry the elementwise
  norm; on finite-dimensional spaces the derivative does not depend on the norm. The derivative of
  a map that is not differentiable is `0` in Mathlib, so the statements on the functional
  dimension assume that `θ ↦ F_θ(x)` is differentiable at `θ`.
- Proposition A.3 is not stated for whole networks: it needs gains and biases, which the network
  definition does not have yet. Only the computations of its proof are stated.
- "At generic parameters every hidden state has such columns" and "removes `(L+1) dim G`
  parameters" are not stated yet (they belong to the step on generic parameters).

### Skips paper

| Paper | Lean statement | File | Status |
|---|---|---|---|
| S eq. (7): `Λ_ℓ = A_{ℓ+1}⋯A_L`, `A_ℓ Λ_ℓ = Λ_{ℓ-1}` | `skipProd`, `skipProd_last`, `skipProd_castSucc` | `Residual/LearnedSkips.lean` | proved |
| S Theorem 3.2 (i) | `eval_learned_eq_residual`, `cob_skipProd_D` | `Residual/LearnedSkips.lean` | proved |
| S Theorem 3.2 (ii), first sentence (orthogonal skips) | `eval_learned_eq_residual_rmsNorm` | `Residual/LearnedSkips.lean` | proved |
| S Theorem 3.3 (i), "if", without normalization | `eval_cob_residual` | `Symmetry/ChangeOfBasis.lean` | proved |
| S Theorem 3.3 (i), "if", under pre-RMSNorm | `eval_cob_residual_rmsNorm` | `Residual/LearnedSkips.lean` | proved |
| S Theorem 3.3 (iii), without normalization | `exists_cob_residual_read_eq_one`, `exists_cob_residual_D_eq_one` | `Residual/LearnedSkips.lean` | proved |
| S Theorem 3.3 (iii), under pre-RMSNorm, read of a block | `exists_cob_residual_read_upperTriangular` | `Residual/LearnedSkips.lean` | proved |
| S the upper bound for residual networks, changes of basis only: `fd ≤ P − d²` | `cobDir_const_mem_flat_residual`, `funDim_add_le_residual` | `Dimension/UpperBound.lean` | proved |
| S the same under pre-RMSNorm (`ε > 0`): `fd ≤ P − d(d−1)/2` | `funDim_add_le_residual_rmsNorm` | `Dimension/UpperBoundRMSNorm.lean` | proved |
| S the upper bounds for residual networks at generic parameters | `ae_funDim_add_le_residual`, `ae_funDim_add_le_residual_rmsNorm` | `Generic/Params.lean` | proved |

Not stated yet from Section 3 of the skips paper: Theorem 3.2 (ii), second sentence (invertible
skips made upper triangular under pre-RMSNorm); Theorem 3.3 (i), "only if"; Theorem 3.3 (ii), the
dimensions of the groups.
