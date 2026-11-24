import SkipsLean.OneBlock.LearnedSkip

/-!
# One block with a full learned skip under pre-RMSNorm: the upper bound

Paper (skips paper): Theorem B.1 (iii), Step 5 of its proof: "The directions `η^rot` are
independent of `K_B` and of each other, since `η_E = E X_a` and `η_D = −Y D` determine `X_a` and
`Y`. For a full `A` they have dimension `d_model (d_model − 1)`." The definitions are in
`OneBlock/LearnedSkip.lean`. The rotations of `h_0` and `h_1` by `e^{τ X_0}`, `e^{τ X_1}` with
antisymmetric `X_0`, `X_1` preserve the function when the skip moves as `A ↦ G_0⁻¹ A G_1`
(`eval_cob`, `Symmetry/ChangeOfBasis.lean`, with `rmsNorm_mul_orthogonal`); their directions and
the directions of the symmetries inside the block are flat and independent, which bounds the
functional dimension.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The upper bound for one block with a full learned skip under pre-RMSNorm (`ε > 0`):** if `E`
and `D` have rank `d` and `U` is a space spanned by directions of symmetries inside the block,
then `fd + d (d − 1) + dim U ≤ P + d²`, where `P` counts the weights without the skip: the
orthogonal changes of basis at `h_0` and at `h_1` act independently, with `A ↦ G_0⁻¹ A G_1`. -/
theorem funDimLearned_add_le_rmsNorm {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
    (hE : p.1.E.rank = Fintype.card d) (hD : p.1.D.rank = Fintype.card d)
    (U : Submodule ℝ (Params A dIn dOut))
    (hU : U ≤ Submodule.span ℝ {η | InsideBlocks A p.1 η}) :
    funDimLearned A p + (Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ U)
      ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
  sorry

end Skips
