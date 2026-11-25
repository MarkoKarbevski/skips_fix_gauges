import SkipsLean.Dimension.FunctionalBiasesKinks

/-!
# Directions with biases that are flat on a set of inputs

Paper (skips paper), Appendix B, "Notation and flat directions": "For the ReLU-type activations,
`F(θ, x)` is differentiable in `θ` at the inputs `x` at which no hidden unit sits at its kink,
which form an open set of full measure, and "every input" means every such input."

For networks with biases (`Network/Biases.lean`), the twins of `flatOn`, `flat_le_flatOn` and
`exists_jacobianRank_add_finrank_flatOn` of `Dimension/Functional.lean`:

* `flatOnB A S p U`: the directions of weights and biases that are flat at every input of `U`;
* `flatB_le_flatOnB`: a flat direction is flat at every input of `U`;
* `exists_jacobianRankB_add_finrank_flatOnB`: if the output at every input of `U` is
  differentiable in `(θ, b)` at `p`, some finite batch of inputs of `U` has a Jacobian of rank
  `P − dim K_U(θ, b)`. With `U` the inputs at which no hidden unit sits at its kink, this is the
  rank on the paper's inputs.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut]

/-- The directions of weights and biases that are flat at every input of a set `U`. -/
noncomputable def flatOnB (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (p : ParamsB A dIn dOut)
    (U : Set (Matrix T dIn ℝ)) : Submodule ℝ (ParamsB A dIn dOut) :=
  ⨅ x ∈ U,
    LinearMap.ker (fderiv ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p).toLinearMap

variable {A : Arch T d L} {S : Fin L → Matrix d d ℝ} (p : ParamsB A dIn dOut)

omit [Fintype T] in
/-- A flat direction is flat at every input of `U`. -/
theorem flatB_le_flatOnB (U : Set (Matrix T dIn ℝ)) : flatB A S p ≤ flatOnB A S p U := by
  -- an infimum over every input lies below the infimum over the inputs of `U`
  intro η hη
  rw [flatB, Submodule.mem_iInf] at hη
  rw [flatOnB, Submodule.mem_iInf]
  intro x
  rw [Submodule.mem_iInf]
  intro _
  exact hη x

/-- On a set `U` of inputs at which `(θ, b) ↦ F_{θ,b}(x)` is differentiable at `p`, some finite
batch of inputs of `U` has a Jacobian of rank `P − dim K_U(θ, b)`, where `K_U(θ, b)` are the
directions that are flat at every input of `U`. -/
theorem exists_jacobianRankB_add_finrank_flatOnB (U : Set (Matrix T dIn ℝ))
    (hU : ∀ x ∈ U,
      DifferentiableAt ℝ (fun q : ParamsB A dIn dOut => evalB A S q.1 q.2 x) p) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      jacobianRankB A S X p + Module.finrank ℝ (flatOnB A S p U)
        = Module.finrank ℝ (ParamsB A dIn dOut) := by
  sorry

end Skips
