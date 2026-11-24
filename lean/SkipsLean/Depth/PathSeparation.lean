import SkipsLean.Depth.RaySeparation

/-!
# Separation on the path

Paper (dimension paper): Lemma D.16 (Separation on the path), Appendix D.6 (the case `ε = 0`).
"Let `u_1, …, u_q > 0` be linearly independent over `ℚ`, let `u'_1, …, u'_q` be real, and for
`t ≥ 1` let

  `ζ_j(t) = exp(−(t + t⁻¹) u_j − i (t − t⁻¹) u'_j)`.

Let `ρ₀ > max_j e^{−2 u_j}`, and let `𝒯_{−K}, …, 𝒯_K` be holomorphic maps from the polydisc
`{ζ ∈ ℂ^q : |ζ_j| < ρ₀}` to `ℂ^{1 × d_out}`. If `∑_{i=−K}^{K} t^i 𝒯_i(ζ_1(t), …, ζ_q(t)) = 0` for all
`t ≥ 1`, then `𝒯_i = 0` for every `i`."

"This is the proof of Lemma D.1, with a phase and with negative powers": in the expansion
`𝒯_i(ζ) = ∑_α b_{i,α} ζ^α` the monomial `ζ(t)^α` has the absolute value `e^{−(t + t⁻¹) μ_α}`,
`μ_α = ∑_j α_j u_j`; these rates are pairwise different, and finitely many lie below any bound.

As for Lemma D.1 (`Depth/RaySeparation.lean`), the middle step is stated on its own, for maps that
are analytic at `0` and an identity for all large `t`, with nonnegative powers of `t` (negative
powers are removed by multiplying with `t^K`). Holomorphic maps of several variables are
`AnalyticOnNhd ℂ` here.
-/

namespace Skips

open Filter Topology

/-- **The middle step of the proof of Lemma D.16.** Let the rates `u_j > 0` be linearly independent
over `ℚ`, let `u'_j` be real, and let `G_0, …, G_K` be analytic near `0 ∈ ℂ^q`. If
`∑_i t^i G_i(ζ_1(t), …, ζ_q(t)) = 0` for all large real `t`, with
`ζ_j(t) = exp(−(t + t⁻¹) u_j − i (t − t⁻¹) u'_j)`, then every `G_i` vanishes near `0`. -/
theorem eventually_eq_zero_of_sum_pow_mul_exp_path {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (hpos : ∀ j, 0 < u j) (hu : LinearIndependent ℚ u) (u' : ι → ℝ)
    (K : ℕ) (G : Fin (K + 1) → (ι → ℂ) → ℂ) (hG : ∀ i, AnalyticAt ℂ (G i) 0)
    (h : ∀ᶠ t : ℝ in atTop,
      ∑ i : Fin (K + 1), (t : ℂ) ^ (i : ℕ) * G i (fun j =>
        Complex.exp (-(((t + t⁻¹) * u j : ℝ) : ℂ) - Complex.I * (((t - t⁻¹) * u' j : ℝ) : ℂ)))
        = 0) :
    ∀ i, ∀ᶠ ζ in 𝓝 (0 : ι → ℂ), G i ζ = 0 := by
  sorry

/-- **Lemma D.16 of the dimension paper (Separation on the path).** Let `u_1, …, u_q > 0` be
linearly independent over `ℚ`, let `u'_j` be real, let `ρ₀ > e^{−2 u_j}` for every `j`, and let
`𝒯_{−K}, …, 𝒯_K` be holomorphic on the polydisc `{|ζ_j| < ρ₀}` with values in a complex normed
space. If `∑_{i=−K}^{K} t^i 𝒯_i(ζ_1(t), …, ζ_q(t)) = 0` for all real `t ≥ 1`, then every `𝒯_i`
vanishes on the polydisc. (The map `𝒯_i` of the paper is `𝒯 ⟨i + K, _⟩` here.) -/
theorem path_separation {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (u : ι → ℝ) (hpos : ∀ j, 0 < u j) (hu : LinearIndependent ℚ u)
    (u' : ι → ℝ) (ρ₀ : ℝ) (hρ : ∀ j, Real.exp (-(2 * u j)) < ρ₀) (K : ℕ)
    (𝒯 : Fin (2 * K + 1) → (ι → ℂ) → F)
    (h𝒯 : ∀ i, AnalyticOnNhd ℂ (𝒯 i) {ζ : ι → ℂ | ∀ j, ‖ζ j‖ < ρ₀})
    (h : ∀ t : ℝ, 1 ≤ t →
      ∑ i : Fin (2 * K + 1), (t : ℂ) ^ (((i : ℕ) : ℤ) - (K : ℤ)) • 𝒯 i (fun j =>
        Complex.exp (-(((t + t⁻¹) * u j : ℝ) : ℂ) - Complex.I * (((t - t⁻¹) * u' j : ℝ) : ℂ)))
        = 0) :
    ∀ i, ∀ ζ : ι → ℂ, (∀ j, ‖ζ j‖ < ρ₀) → 𝒯 i ζ = 0 := by
  sorry

end Skips
