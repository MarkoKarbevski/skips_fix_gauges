import SkipsLean.Dimension.FunctionalBiases

/-!
# The functional dimension with biases, without a hypothesis of differentiability

Paper (skips paper), Appendix B, "Notation and flat directions": "For the ReLU-type activations,
`F(θ, x)` is differentiable in `θ` at the inputs `x` at which no hidden unit sits at its kink,
which form an open set of full measure, and "every input" means every such input." With biases
the kinks lie on hyperplanes that need not pass through the origin; at an input on one of them
the output need not be differentiable in the parameters.

`Dimension/FunctionalBiases.lean` has the general statements for networks with biases under the
hypothesis that the output at every input is differentiable in `(θ, b)` at the point. Here are
the forms without that hypothesis, the twins of `mem_flat_of_hasDerivAt'`,
`funDim_add_finrank_flat'` and `funDim_add_finrank_le_of_le_flat'` of `Dimension/Functional.lean`.
In Lean the derivative of a map at a point where it is not differentiable is `0`; so an input at
which the output is not differentiable in `(θ, b)` puts no condition on a flat direction, and a
batch that contains such an input has a Jacobian of rank `0`. With this convention:

* `mem_flatB_of_hasDerivAt'`: the velocity of a curve of parameters along which the function does
  not change is flat;
* `funDimB_add_finrank_flatB'`: `fd = P − dim K(θ, b)`;
* `funDimB_add_finrank_le_of_le_flatB'`: a space of flat directions bounds the functional
  dimension.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut]
variable {A : Arch T d L} {S : Fin L → Matrix d d ℝ} (p : ParamsB A dIn dOut)

/-- **A direction of a symmetry is flat, with biases, without a hypothesis of
differentiability.** If a curve `γ` of parameters passes through `(θ, b)` with velocity `η` and
the function of the network is the same along it, then `η` is flat at `(θ, b)`. -/
theorem mem_flatB_of_hasDerivAt'
    (γ : ℝ → ParamsB A dIn dOut) (η : ParamsB A dIn dOut) (hγ : HasDerivAt γ η 0)
    (hγ0 : γ 0 = p)
    (hconst : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ x : Matrix T dIn ℝ,
      evalB A S (γ τ).1 (γ τ).2 x = evalB A S p.1 p.2 x) :
    η ∈ flatB A S p := by
  sorry

/-- **The functional dimension with biases is `P − dim K(θ, b)`, without a hypothesis of
differentiability** (with Lean's convention that the derivative is `0` where it does not
exist). -/
theorem funDimB_add_finrank_flatB' :
    funDimB A S p + Module.finrank ℝ (flatB A S p) = Module.finrank ℝ (ParamsB A dIn dOut) := by
  sorry

/-- **A space of flat directions bounds the functional dimension with biases,** without a
hypothesis of differentiability: `fd + dim V ≤ P`. -/
theorem funDimB_add_finrank_le_of_le_flatB' (V : Submodule ℝ (ParamsB A dIn dOut))
    (hV : V ≤ flatB A S p) :
    funDimB A S p + Module.finrank ℝ V ≤ Module.finrank ℝ (ParamsB A dIn dOut) := by
  -- `fd + dim K = P` and `dim V ≤ dim K`
  have h := funDimB_add_finrank_flatB' (S := S) p
  have hV' := Submodule.finrank_mono hV
  omega

end Skips
