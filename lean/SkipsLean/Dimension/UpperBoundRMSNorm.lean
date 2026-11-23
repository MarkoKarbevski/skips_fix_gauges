import SkipsLean.Dimension.UpperBound

/-!
# The upper bound from the changes of basis, under pre-RMSNorm

Papers: dimension paper, Theorem 4.3 under pre-RMSNorm with `ε > 0`, for the changes of basis at
the hidden states; skips paper, the bound for residual networks under pre-RMSNorm.

Under pre-RMSNorm the changes of basis are orthogonal, and their directions `cobDir θ X` have
antisymmetric `X_ℓ`. The antisymmetric matrices form a space of dimension `d (d - 1) / 2`, so the
functional dimension is at most `P - (L + 1) d (d - 1) / 2` without skip connections, and at most
`P - d (d - 1) / 2` in a residual network.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {A : Arch T d L}
variable (θ : Params A dIn dOut)

/-- RMSNorm with `ε > 0` is differentiable. -/
theorem differentiable_rmsNorm {ε : ℝ} (hε : 0 < ε) :
    Differentiable ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) := by
  sorry

/-- Under pre-RMSNorm with `ε > 0` and without skip connections, the directions `cobDir θ X` with
antisymmetric `X_ℓ` are flat. -/
theorem cobDir_mem_flat_skipless_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (X : Fin (L + 1) → Matrix d d ℝ)
    (hX : ∀ ℓ, (X ℓ)ᵀ = -X ℓ) :
    cobDir θ X ∈ flat A 0 θ := by
  sorry

/-- The antisymmetric `d × d` matrices, as a subspace of all matrices. -/
def antisymmetric (d : Type*) [Fintype d] : Submodule ℝ (Matrix d d ℝ) where
  carrier := {X | Xᵀ = -X}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_ofPred_eq] at hX hY ⊢
    rw [Matrix.transpose_add, hX, hY, neg_add]
  zero_mem' := by simp
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_ofPred_eq] at hX ⊢
    rw [Matrix.transpose_smul, hX, smul_neg]

/-- The antisymmetric `d × d` matrices form a space of dimension `d (d - 1) / 2`. -/
theorem finrank_antisymmetric :
    Module.finrank ℝ (antisymmetric d) = Fintype.card d * (Fintype.card d - 1) / 2 := by
  sorry

/-- **Theorem 4.3, under pre-RMSNorm, for the changes of basis.** If `E` and every write have
rank `d`, the functional dimension of a network without skip connections is at most
`P - (L + 1) d (d - 1) / 2`. -/
theorem funDim_add_le_skipless_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **Skips paper, the upper bound for residual networks under pre-RMSNorm, for the one change of
basis.** If `E` has rank `d`, the functional dimension of a residual network is at most
`P - d (d - 1) / 2`. -/
theorem funDim_add_le_residual_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end Skips
