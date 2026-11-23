import SkipsLean.Residual.LearnedSkips
import SkipsLean.Basic.RMSNormConverse

/-!
# Identity skips leave one change of basis; learned skips under pre-RMSNorm

Paper: "Skip Connections Unlock at Least d_model² Parameters per Layer", Section 3.

* Theorem 3.3 (i), "only if" (Theorem A.5 (iii) in the appendix): if the changes of basis
  `G_0, …, G_L` at the hidden states preserve the function of every residual network, that is, for
  all values of the parameters, then `G_0 = G_1 = ⋯ = G_L`, and under pre-RMSNorm this matrix is
  orthogonal. The paper assumes that every block is nonzero for some value of its parameters.
  The proof sets all writes but one to zero: the output then compares the bases on the two sides
  of that block.
* Theorem 3.2 (ii), second sentence: under pre-RMSNorm, orthogonal changes of basis
  `Q_1, …, Q_L`, with `Q_0 = I`, turn every learned skip `A_ℓ` into an upper triangular matrix
  `Q_{ℓ-1}ᵀ A_ℓ Q_ℓ` and preserve the function. (The paper assumes the `A_ℓ` invertible; the
  factorization exists for every square matrix.)

"Every residual network" is: every value `θ` of the parameters of a fixed architecture `A`, with
the stream matrices `1` (identity skips).
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn]
variable {A : Arch T d L}

/-- **Theorem 3.3 (i), "only if", without normalization.** If every block is nonzero for some
value of its parameters, and the changes of basis `G_0, …, G_L` preserve the function of the
residual network for all values of the parameters, then all `G_ℓ` are equal. -/
theorem cob_eq_of_eval_cob_residual [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hA : A.χ = id)
    (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ),
      A.f ℓ (x * E * W) ≠ 0)
    (G : Fin (L + 1) → GL d ℝ)
    (h : ∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ),
      eval A 1 (θ.cob G G) x = eval A 1 θ x) :
    ∀ ℓ, G ℓ = G 0 := by
  sorry

/-- **Theorem 3.3 (i), without normalization:** the changes of basis `G_0, …, G_L` preserve the
function of every residual network if and only if they are all equal. -/
theorem eval_cob_residual_iff [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hA : A.χ = id)
    (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ),
      A.f ℓ (x * E * W) ≠ 0)
    (G : Fin (L + 1) → GL d ℝ) :
    (∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ), eval A 1 (θ.cob G G) x = eval A 1 θ x)
      ↔ ∀ ℓ, G ℓ = G 0 := by
  sorry

/-- **Theorem 3.3 (i), "only if", under pre-RMSNorm (`ε > 0`).** If every block is nonzero for
some value of its parameters, and the changes of basis `G_0, …, G_L` preserve the function of the
residual network for all values of the parameters, then all `G_ℓ` are equal and orthogonal. -/
theorem cob_eq_orthogonal_of_eval_cob_residual_rmsNorm [Nonempty T] [Nonempty dIn]
    [Nonempty dOut] {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ),
      A.f ℓ (rmsNorm ε (x * E) * W) ≠ 0)
    (G : Fin (L + 1) → GL d ℝ)
    (h : ∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ),
      eval A 1 (θ.cob G G) x = eval A 1 θ x) :
    (∀ ℓ, G ℓ = G 0) ∧ (G 0 : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  sorry

/-- **Theorem 3.3 (i), under pre-RMSNorm (`ε > 0`):** the changes of basis `G_0, …, G_L` preserve
the function of every residual network if and only if they are all equal and orthogonal. -/
theorem eval_cob_residual_rmsNorm_iff [Nonempty T] [Nonempty dIn] [Nonempty dOut] {ε : ℝ}
    (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ),
      A.f ℓ (rmsNorm ε (x * E) * W) ≠ 0)
    (G : Fin (L + 1) → GL d ℝ) :
    (∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ), eval A 1 (θ.cob G G) x = eval A 1 θ x)
      ↔ (∀ ℓ, G ℓ = G 0) ∧ (G 0 : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  sorry

/-- A square real matrix times a suitable orthogonal matrix is upper triangular (the RQ
factorization `M = R Qᵀ`). -/
theorem exists_orthogonal_mul_upperTriangular [LinearOrder d] (M : Matrix d d ℝ) :
    ∃ Q : Matrix d d ℝ, Q ∈ Matrix.orthogonalGroup d ℝ ∧ (M * Q).BlockTriangular id := by
  sorry

/-- **Theorem 3.2 (ii), second sentence.** Under pre-RMSNorm, for learned skips `A_ℓ` (the stream
matrices `S ℓ`), there are orthogonal `Q_0 = I, Q_1, …, Q_L` such that every
`Q_{ℓ-1}ᵀ A_ℓ Q_ℓ` is upper triangular, and the network with these skips, the reads
`Q_{ℓ-1}ᵀ W_read^ℓ`, the writes `W_write^ℓ Q_ℓ` and the readout `Q_Lᵀ D` computes the same
function. -/
theorem exists_cob_learned_upperTriangular [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut) :
    ∃ Q : Fin (L + 1) → GL d ℝ, Q 0 = 1 ∧
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
      (∀ ℓ, (cobSkip S Q ℓ).BlockTriangular id) ∧
      ∀ x : Matrix T dIn ℝ, eval A (cobSkip S Q) (θ.cob Q Q) x = eval A S θ x := by
  sorry

end Skips
