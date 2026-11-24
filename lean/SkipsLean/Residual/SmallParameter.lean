import SkipsLean.Imports

/-!
# The rank of a Jacobian along a small parameter

Paper (skips paper): proof of Lemma A.27, its first paragraph and its last paragraph ("The
rank"). There `J_τ` is the Jacobian of the outputs at the parameters `θ_τ`, `S_τ` divides some
coordinates of a direction by `τ`, `rank J_τ = rank (J_τ S_τ)` for `τ ≠ 0`, the limit
`J_0 = lim_{τ → 0} J_τ S_τ` exists, and, the rank being lower semicontinuous,
`rank J_τ ≥ rank J_0` for all small `τ ≠ 0`.

This file states that step without networks, for a map `G τ θ` of a real number `τ` and of
parameters `θ` that is twice continuously differentiable in `(τ, θ)`. The coordinates that `S_τ`
divides by `τ` are given by a continuous linear map `π` on the parameters (`π η` is the part of the
direction `η` that is divided), and the hypothesis is that `G 0` does not move along them at `θ`.
Then, as `τ → 0`,

  `D_θ G(τ, θ) ((η - π η) + τ⁻¹ π η) → D_θ G(0, θ) (η - π η) + D_θ (∂_τ G(0, ·))(θ) (π η)`,

since the second derivative of `G` is symmetric. The right-hand side is `J_0 η`.

In the paper `G τ θ` is the batch of outputs at `θ_τ`; the derivative of `θ ↦ θ_τ` is invertible for
`τ ≠ 0`, so the rank of `D_θ G(τ, θ)` is the rank of `J_τ`. Here only "the rank of a composition is
at most the rank of the outer map" is used, which needs no inverse.
-/

namespace Skips

open Filter Topology

variable {P Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- **Proof of Lemma A.27 of the skips paper, "`J_τ S_τ → J_0`" and "the rank is lower
semicontinuous", without networks.** Let `G τ θ` be twice continuously differentiable in `(τ, θ)`,
and let `G 0` have derivative zero at `θ` along every direction `π η`. Then for all small `τ ≠ 0`
the rank of `D_θ G(τ, θ)` is at least the rank of the limit
`J_0 η = D_θ G(0, θ) (η - π η) + D_θ (∂_τ G(0, ·))(θ) (π η)`. -/
theorem eventually_finrank_range_le_of_small_parameter (G : ℝ → P → Y)
    (hG : ContDiff ℝ 2 (fun p : ℝ × P => G p.1 p.2)) (π : P →L[ℝ] P) (θ : P)
    (h0 : ∀ η, fderiv ℝ (G 0) θ (π η) = 0) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      Module.finrank ℝ (LinearMap.range
          ((fderiv ℝ (G 0) θ).comp (ContinuousLinearMap.id ℝ P - π)
            + (fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ).comp π).toLinearMap)
        ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ (G τ) θ).toLinearMap) := by
  sorry

/-- **The same step in the form used for Lemma A.27,** by the kernel of the limit: if every
direction `η` with `J_0 η = 0` lies in a subspace `V`, then for all small `τ ≠ 0` the rank of
`D_θ G(τ, θ)` is at least `dim P - dim V`. -/
theorem eventually_finrank_le_of_small_parameter (G : ℝ → P → Y)
    (hG : ContDiff ℝ 2 (fun p : ℝ × P => G p.1 p.2)) (π : P →L[ℝ] P) (θ : P)
    (h0 : ∀ η, fderiv ℝ (G 0) θ (π η) = 0) (V : Submodule ℝ P)
    (hV : ∀ η, fderiv ℝ (G 0) θ (η - π η)
        + fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ (π η) = 0 → η ∈ V) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      Module.finrank ℝ P
        ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ (G τ) θ).toLinearMap)
          + Module.finrank ℝ V := by
  sorry

end Skips
