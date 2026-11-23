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

Status: *open* (statement compiles, proof not written), *in work*, *proved* (compiled, no `sorry`,
standard axioms only).

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

Notes for the authors on these statements:
- Proposition 3.3 is stated in the paper for one hidden state, with the remark that the reductions
  at all hidden states can be made together. The Lean statements are the simultaneous form.
- `exists_cob_reads_upperTriangular` does not assume that the chosen columns are invertible: a QR
  factorization exists for every square matrix. The paper assumes it.
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

Not stated yet from Section 3 of the skips paper: Theorem 3.2 (ii), second sentence (invertible
skips made upper triangular under pre-RMSNorm); Theorem 3.3 (i), "only if"; Theorem 3.3 (ii), the
dimensions of the groups.
