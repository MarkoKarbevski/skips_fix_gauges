import SkipsLean.OneBlock.LearnedSkipBound

/-!
# The network whose skips are parameters, without a hypothesis of differentiability

Paper (skips paper): Appendix B, "Notation and flat directions": "For the ReLU-type activations,
`F(θ, x)` is differentiable in `θ` at the inputs `x` at which no hidden unit sits at its kink, which
form an open set of full measure, and 'every input' means every such input." Theorem B.1 (iii) is
stated for ReLU, ReLU² and ReGLU blocks as well: "Let the network be pre-RMSNorm without biases,
with a learned skip `A`, full or upper triangular. For generic parameters and `ε > 0`, its
functional dimension exceeds that of the residual network of part (ii) by exactly
`d_model (d_model + 1)/2`".

`OneBlock/LearnedSkip.lean` and `OneBlock/LearnedSkipBound.lean` state the rank–nullity identity and
the upper bound for differentiable blocks. Here they are stated with no hypothesis on the blocks,
as `Dimension/Functional.lean` does for the networks with fixed skips (`flatOn`, `flat_le_flatOn`,
`funDim_add_finrank_flat'`, `exists_jacobianRank_add_finrank_flatOn`): Mathlib's derivative of a map
at a point where it is not differentiable is `0`, so an input at which `(θ, v) ↦ F_{θ,v}(x)` is not
differentiable puts no condition on the flat directions, and a batch that contains such an input
has a Jacobian of rank `0`.

* `flatSkipsOn A ι p U`: the directions `(η, a)` that are flat at every input of a set `U`.
* `funDimSkips_add_finrank_flatSkips'`: `fd + dim (flat directions) = number of parameters`.
* `exists_jacobianRankSkips_add_finrank_flatSkipsOn`: on a set `U` of inputs at which the output
  is differentiable in `(θ, v)`, a finite batch of inputs of `U` has the rank
  `(number of parameters) − dim (directions flat on U)`.
* `funDimLearned_add_le_rmsNorm'`: the upper bound of `OneBlock/LearnedSkipBound.lean` for one
  block with a full learned skip, for any block.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The directions `(η, a)` of the weights and the skips that are flat at every input of a set
`U`: the derivative of `(θ, v) ↦ F_{θ,v}(x)` at `p` vanishes along them for every `x ∈ U`. -/
noncomputable def flatSkipsOn (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V) (U : Set (Matrix T dIn ℝ)) :
    Submodule ℝ (Params A dIn dOut × V) :=
  ⨅ x ∈ U,
    LinearMap.ker (fderiv ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p).toLinearMap

/-- A flat direction is flat at every input of `U`. -/
theorem flatSkips_le_flatSkipsOn (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V) (U : Set (Matrix T dIn ℝ)) :
    flatSkips A ι p ≤ flatSkipsOn A ι p U := by
  sorry

/-- `fd = (number of parameters) − dim K`, for the network whose skips are parameters, with no
hypothesis of differentiability. -/
theorem funDimSkips_add_finrank_flatSkips' [FiniteDimensional ℝ V] (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V) :
    funDimSkips A ι p + Module.finrank ℝ (flatSkips A ι p)
      = Module.finrank ℝ (Params A dIn dOut × V) := by
  sorry

/-- On a set `U` of inputs at which `(θ, v) ↦ F_{θ,v}(x)` is differentiable at `p`, some finite
batch of inputs of `U` has a Jacobian of rank `(number of parameters) − dim K_U(p)`, where `K_U(p)`
are the directions that are flat at every input of `U`. -/
theorem exists_jacobianRankSkips_add_finrank_flatSkipsOn [FiniteDimensional ℝ V] (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V) (U : Set (Matrix T dIn ℝ))
    (hU : ∀ x ∈ U,
      DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      jacobianRankSkips A ι X p + Module.finrank ℝ (flatSkipsOn A ι p U)
        = Module.finrank ℝ (Params A dIn dOut × V) := by
  sorry

/-- **The upper bound for one block with a full learned skip under pre-RMSNorm, for any block:**
if `E` and `D` have rank `d` and `U` is a space spanned by directions of symmetries inside the
block, then `fd + d (d − 1) + dim U ≤ P + d²`, where `P` counts the weights without the skip. This
is `funDimLearned_add_le_rmsNorm` without the hypothesis that the block is differentiable. It is
stated for every real `ε`; for `ε = 0` the map `rmsNorm 0` is Lean's total function, the changes of
basis used are the orthogonal ones, and the paper's bound for `ε = 0` (with the scalings) is not
stated here. -/
theorem funDimLearned_add_le_rmsNorm' {A : Arch T d 1} (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
    (hE : p.1.E.rank = Fintype.card d) (hD : p.1.D.rank = Fintype.card d)
    (U : Submodule ℝ (Params A dIn dOut))
    (hU : U ≤ Submodule.span ℝ {η | InsideBlocks A p.1 η}) :
    funDimLearned A p + (Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ U)
      ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
  sorry

end Skips
