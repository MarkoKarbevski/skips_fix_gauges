import SkipsLean.Residual.SmallParameter

/-!
# The rank of a Jacobian along a small parameter, for a map that is smooth near one point

Paper (skips paper): proof of Lemma A.30 (ReLU-type blocks with small writes): "We follow the
proof of Lemma A.27 […]. With the writes `τ V_ℓ`, the pre-activations of block `ℓ` are
`h_{ℓ−1} W_read^ℓ` with `h_{ℓ−1} = x E + O(τ)`. So for `|τ|` below some `τ_0 > 0`, which depends
on the parameters and on the batch, every pre-activation on the batch has the sign of its limit.
The outputs on the batch are then polynomial in the parameters and in `τ`, the Jacobian on the
batch, with its read columns divided by `τ`, tends to `J_0`, and by lower semicontinuity it has
rank at least `P − d_model² − s` for all small `τ ≠ 0`."

So the step "The rank" of Lemma A.27 (`Residual/SmallParameter.lean`,
`eventually_finrank_le_of_small_parameter`) is used for a map `G τ θ` that is twice continuously
differentiable only near `(0, θ)`. This file states that form. The hypotheses and the conclusion
are those of `eventually_finrank_le_of_small_parameter`; they involve `G` only near `(0, θ)`.
-/

namespace Skips

open Filter Topology

variable {P Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- **Proof of Lemma A.27, "The rank", as the proof of Lemma A.30 uses it:** the statement of
`eventually_finrank_le_of_small_parameter` for a map `G` that is twice continuously differentiable
on a neighborhood `U` of `(0, θ)`. -/
theorem eventually_finrank_le_of_small_parameter_of_contDiffOn (G : ℝ → P → Y) (θ : P)
    (U : Set (ℝ × P)) (hU : U ∈ 𝓝 ((0 : ℝ), θ))
    (hG : ContDiffOn ℝ 2 (fun p : ℝ × P => G p.1 p.2) U) (π : P →L[ℝ] P)
    (h0 : ∀ η, fderiv ℝ (G 0) θ (π η) = 0) (V : Submodule ℝ P)
    (hV : ∀ η, fderiv ℝ (G 0) θ (η - π η)
        + fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ (π η) = 0 → η ∈ V) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      Module.finrank ℝ P
        ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ (G τ) θ).toLinearMap)
          + Module.finrank ℝ V := by
  sorry

end Skips
