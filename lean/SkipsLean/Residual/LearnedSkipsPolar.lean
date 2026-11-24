import SkipsLean.Residual.OneChangeOfBasis
import Mathlib.Analysis.Matrix.Order

/-!
# Triangular or symmetric skips under pre-RMSNorm

Paper (skips paper), Theorem A.12 (i): "Triangular or symmetric skips. Let `Q_0 = I`, and for
`ℓ = 1, …, L` let `Q_{ℓ−1}ᵀ A_ℓ = R_ℓ Q_ℓᵀ` be an RQ factorization, with `R_ℓ` upper triangular
with positive diagonal and `Q_ℓ` orthogonal. The network with the skips `R_ℓ`, the reads
`Q_{ℓ−1}ᵀ W_read^ℓ`, the writes `W_write^ℓ Q_ℓ` and the readout `Q_Lᵀ D` computes the same
function. So does the network built in the same way from the polar decompositions
`Q_{ℓ−1}ᵀ A_ℓ = S_ℓ Q_ℓᵀ`, with `S_ℓ` symmetric positive definite in place of `R_ℓ`."

The theorem is about "pre-RMSNorm networks with `ε ≥ 0`, and the network with learned skips of (2)
with `χ = N_ε`, whose skips `A_ℓ` are invertible in (i) and (ii)".

Its proof: "With `Q_0 = I` and the `Q_ℓ` of the statement, the skip `A_ℓ` becomes
`Q_{ℓ−1}ᵀ A_ℓ Q_ℓ = R_ℓ`; the RQ factorization of the invertible matrix `Q_{ℓ−1}ᵀ A_ℓ` exists, and
is unique. The same computation with the polar decompositions gives `Q_{ℓ−1}ᵀ A_ℓ Q_ℓ = S_ℓ`:
every invertible matrix `X` is `X = S Qᵀ` with `S = (X Xᵀ)^{1/2}` symmetric positive definite and
`Qᵀ = S⁻¹ X` orthogonal, uniquely. The readout absorbs the last factor, `D ↦ Q_Lᵀ D`."

Here:

* the two factorizations of one invertible matrix, with their uniqueness;
* the two networks. The skips after the change are `cobSkip S Q ℓ = Q_{ℓ−1}⁻¹ A_ℓ Q_ℓ`
  (`Symmetry/ChangeOfBasis.lean`), and the parameters are `θ.cob Q Q`: the embedding `E Q_0`, the
  reads `Q_{ℓ−1}⁻¹ W_read^ℓ`, the writes `W_write^ℓ Q_ℓ`, the readout `Q_L⁻¹ D`; for an orthogonal
  `Q` the inverse is the transpose. The statement holds for every real `ε` (`rmsNorm ε` is a total
  function).

`Matrix.PosDef` is Mathlib's notion: Hermitian (for real matrices: symmetric) with
`0 < x ⬝ᵥ (M *ᵥ x)` for every `x ≠ 0`. `BlockTriangular id` is "upper triangular" (entries below
the diagonal vanish), as in `exists_cob_learned_upperTriangular` of
`Residual/OneChangeOfBasis.lean`, which is the first network below without "positive diagonal" and
for skips that need not be invertible.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn]
variable {A : Arch T d L}

/-! ### One invertible matrix -/

/-- **The polar decomposition** ("every invertible matrix `X` is `X = S Qᵀ` with
`S = (X Xᵀ)^{1/2}` symmetric positive definite and `Qᵀ = S⁻¹ X` orthogonal"). -/
theorem exists_posDef_mul_orthogonal_transpose (X : Matrix d d ℝ) (hX : IsUnit X.det) :
    ∃ S Q : Matrix d d ℝ, S.PosDef ∧ Q ∈ Matrix.orthogonalGroup d ℝ ∧ X = S * Qᵀ := by
  sorry

/-- **The polar decomposition is unique** ("uniquely"). -/
theorem posDef_mul_orthogonal_transpose_unique {S S' Q Q' : Matrix d d ℝ} (hS : S.PosDef)
    (hS' : S'.PosDef) (hQ : Q ∈ Matrix.orthogonalGroup d ℝ)
    (hQ' : Q' ∈ Matrix.orthogonalGroup d ℝ) (h : S * Qᵀ = S' * Q'ᵀ) : S = S' ∧ Q = Q' := by
  sorry

/-- **The RQ factorization with positive diagonal** of an invertible matrix ("the RQ
factorization of the invertible matrix `Q_{ℓ−1}ᵀ A_ℓ` exists"): `X = R Qᵀ` with `R` upper
triangular with positive diagonal and `Q` orthogonal. -/
theorem exists_upperTriangular_pos_mul_orthogonal_transpose [LinearOrder d] (X : Matrix d d ℝ)
    (hX : IsUnit X.det) :
    ∃ R Q : Matrix d d ℝ, R.BlockTriangular id ∧ (∀ i, 0 < R i i) ∧
      Q ∈ Matrix.orthogonalGroup d ℝ ∧ X = R * Qᵀ := by
  sorry

/-- **The RQ factorization with positive diagonal is unique** ("and is unique"). -/
theorem upperTriangular_pos_mul_orthogonal_transpose_unique [LinearOrder d]
    {R R' Q Q' : Matrix d d ℝ} (hR : R.BlockTriangular id) (hRp : ∀ i, 0 < R i i)
    (hR' : R'.BlockTriangular id) (hRp' : ∀ i, 0 < R' i i)
    (hQ : Q ∈ Matrix.orthogonalGroup d ℝ) (hQ' : Q' ∈ Matrix.orthogonalGroup d ℝ)
    (h : R * Qᵀ = R' * Q'ᵀ) : R = R' ∧ Q = Q' := by
  sorry

/-! ### The two networks -/

/-- **Theorem A.12 (i), triangular skips.** Under pre-RMSNorm, for invertible learned skips `A_ℓ`
(the stream matrices `S ℓ`), there are orthogonal `Q_0 = I, Q_1, …, Q_L` such that every
`R_ℓ = Q_{ℓ−1}ᵀ A_ℓ Q_ℓ` is upper triangular with positive diagonal, and the network with the skips
`R_ℓ`, the reads `Q_{ℓ−1}ᵀ W_read^ℓ`, the writes `W_write^ℓ Q_ℓ` and the readout `Q_Lᵀ D` computes
the same function. -/
theorem exists_cob_learned_upperTriangular_pos [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (S : Fin L → Matrix d d ℝ) (hS : ∀ ℓ, IsUnit (S ℓ).det) (θ : Params A dIn dOut) :
    ∃ Q : Fin (L + 1) → GL d ℝ, Q 0 = 1 ∧
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
      (∀ ℓ, (cobSkip S Q ℓ).BlockTriangular id ∧ ∀ i, 0 < cobSkip S Q ℓ i i) ∧
      ∀ x : Matrix T dIn ℝ, eval A (cobSkip S Q) (θ.cob Q Q) x = eval A S θ x := by
  sorry

/-- **Theorem A.12 (i), symmetric skips.** Under pre-RMSNorm, for invertible learned skips `A_ℓ`
(the stream matrices `S ℓ`), there are orthogonal `Q_0 = I, Q_1, …, Q_L` such that every
`S_ℓ = Q_{ℓ−1}ᵀ A_ℓ Q_ℓ` is symmetric positive definite, and the network with the skips `S_ℓ`, the
reads `Q_{ℓ−1}ᵀ W_read^ℓ`, the writes `W_write^ℓ Q_ℓ` and the readout `Q_Lᵀ D` computes the same
function. -/
theorem exists_cob_learned_posDef (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (S : Fin L → Matrix d d ℝ) (hS : ∀ ℓ, IsUnit (S ℓ).det) (θ : Params A dIn dOut) :
    ∃ Q : Fin (L + 1) → GL d ℝ, Q 0 = 1 ∧
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
      (∀ ℓ, (cobSkip S Q ℓ).PosDef) ∧
      ∀ x : Matrix T dIn ℝ, eval A (cobSkip S Q) (θ.cob Q Q) x = eval A S θ x := by
  sorry

end Skips
