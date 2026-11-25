import SkipsLean.Dimension.Space
import SkipsLean.Symmetry.Reduction

/-!
# Exact reduction: the count of the removed parameters

Paper (skips paper), Proposition A.9 (i): "[…] turns `W_1` into the identity for `G = W_1` if
`W_1` is part of a read, and for `G = W_1^{-1}` if it is part of a write. Under RMSNorm with
`ε > 0`, `G = Q` from a QR factorization `W_1 = Q T`, or `W_1^⊤ = Q T` for a write, turns `W_1`
into a triangular matrix. Done at every hidden state, this removes `d_model²`, respectively
`d_model (d_model − 1)/2`, parameters per hidden state without changing the function." Its
proof: "The identity fixes all `d_model²` entries of `W_1`, and the triangular form fixes the
`d_model (d_model − 1)/2` entries on one side of its diagonal."

The reductions themselves ("without changing the function") are `exists_cob_reads_eq_one`,
`exists_cob_writes_eq_one`, `exists_cob_reads_upperTriangular` (`Symmetry/Reduction.lean`),
`exists_cob_writes_lowerTriangular` (`Residual/ExactReductionWrites.lean`) and, for networks of
mixed blocks, `Residual/ExactReductionMixed.lean`. Here the count, for any architecture (so also
for `A.mixed`), with one chosen submatrix per hidden state, `L + 1` of them:

* the parameters in which the chosen columns of every read and of the readout are the identity
  form an affine space; its directions, the parameters in which these columns are `0`, have
  dimension `P − (L + 1) d²` (`finrank_span_reads_eq_zero`); the same for the chosen rows of the
  embedding and of every write (`finrank_span_writes_eq_zero`);
* the parameters in which the chosen columns are upper triangular have dimension
  `P − (L + 1) d(d − 1)/2` (`finrank_span_reads_upperTriangular`); the same for the chosen rows
  with lower triangular matrices (`finrank_span_writes_lowerTriangular`).

The chosen columns (rows) are pairwise different: columns that form an invertible matrix are.
Each set is a subspace, and the statements are for its span, as in
`OneBlock/KeepsProductsBiases.lean`.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]
variable {A : Arch T d L}

/-- **Proposition A.9 (i), "this removes `d_model²` […] parameters per hidden state", reads:**
the parameters whose chosen columns of every read and of the readout vanish (the directions of
the family in which these `L + 1` submatrices are the identity) have dimension
`P − (L + 1) d²`. -/
theorem finrank_span_reads_eq_zero (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut)
    (hc : ∀ ℓ, Function.Injective (c ℓ)) (hcD : Function.Injective cD) :
    Module.finrank ℝ (Submodule.span ℝ {η : Params A dIn dOut |
        (∀ ℓ, (η.read ℓ).submatrix id (c ℓ) = 0) ∧ η.D.submatrix id cD = 0})
      + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **Proposition A.9 (i), "this removes `d_model²` […] parameters per hidden state", writes:**
the parameters whose chosen rows of the embedding and of every write vanish have dimension
`P − (L + 1) d²`. -/
theorem finrank_span_writes_eq_zero (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ)
    (hρE : Function.Injective ρE) (hρ : ∀ ℓ, Function.Injective (ρ ℓ)) :
    Module.finrank ℝ (Submodule.span ℝ {η : Params A dIn dOut |
        η.E.submatrix ρE id = 0 ∧ ∀ ℓ, (η.write ℓ).submatrix (ρ ℓ) id = 0})
      + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **Proposition A.9 (i), "respectively `d_model (d_model − 1)/2`, parameters per hidden
state", reads:** the parameters whose chosen columns of every read and of the readout form upper
triangular matrices have dimension `P − (L + 1) d(d − 1)/2`. -/
theorem finrank_span_reads_upperTriangular [LinearOrder d] (c : ∀ ℓ : Fin L, d → A.r ℓ)
    (cD : d → dOut) (hc : ∀ ℓ, Function.Injective (c ℓ)) (hcD : Function.Injective cD) :
    Module.finrank ℝ (Submodule.span ℝ {θ : Params A dIn dOut |
        (∀ ℓ, ((θ.read ℓ).submatrix id (c ℓ)).BlockTriangular id)
          ∧ (θ.D.submatrix id cD).BlockTriangular id})
      + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **Proposition A.9 (i), "respectively `d_model (d_model − 1)/2`, parameters per hidden
state", writes:** the parameters whose chosen rows of the embedding and of every write form lower
triangular matrices have dimension `P − (L + 1) d(d − 1)/2`. -/
theorem finrank_span_writes_lowerTriangular [LinearOrder d] (ρE : d → dIn)
    (ρ : ∀ ℓ : Fin L, d → A.w ℓ) (hρE : Function.Injective ρE)
    (hρ : ∀ ℓ, Function.Injective (ρ ℓ)) :
    Module.finrank ℝ (Submodule.span ℝ {θ : Params A dIn dOut |
        ((θ.E.submatrix ρE id)ᵀ).BlockTriangular id
          ∧ ∀ ℓ, (((θ.write ℓ).submatrix (ρ ℓ) id)ᵀ).BlockTriangular id})
      + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end Skips
