import Mathlib

/-!
# Separation on a ray

Paper (dimension paper): Lemma D.1 (`lem:raysep`), "Separation on a ray", stated in Appendix D.1 and
proved in Appendix D.4.

Let `u_1, …, u_q` be real numbers that are linearly independent over `ℚ`, and let `𝒯_0, …, 𝒯_K` be
real-analytic maps on `ℝ^q`. If

  `∑_{i=0}^{K} t^i 𝒯_i(tanh(t u_1), …, tanh(t u_q)) = 0`   for all `t > 0`,

then every `𝒯_i` vanishes on `ℝ^q`. Along the ray the outputs `tanh(t u_j)` of the hidden units
become free variables.

The proof of the paper writes `tanh(t u_j) = s_j (1 - ζ_j) / (1 + ζ_j)` with `s_j` the sign of `u_j`
and `ζ_j = exp(-2 |u_j| t)`, expands every `𝒯_i` in powers of `ζ_1, …, ζ_q`, and uses that the
monomials `ζ^α` decay at the pairwise different rates `2 ∑_j α_j |u_j|`. Its middle step is stated
here on its own (`eventually_eq_zero_of_sum_pow_mul_exp_ray`): it does not mention `tanh`.
-/

namespace Skips

open Filter Topology
open scoped Matrix.Norms.Elementwise

/-- **The middle step of the proof of Lemma D.1.** Let the rates `λ_j > 0` be linearly independent
over `ℚ`, and let `G_0, …, G_K` be real-analytic near `0 ∈ ℝ^q`. If
`∑_i t^i G_i(exp(-λ_1 t), …, exp(-λ_q t)) = 0` for all large `t`, then every `G_i` vanishes near
`0`. (In the expansion `G_i(ζ) = ∑_α b_{i,α} ζ^α` the monomial `ζ^α` decays at the rate
`∑_j α_j λ_j`; these rates are pairwise different, and finitely many lie below any bound.) -/
theorem eventually_eq_zero_of_sum_pow_mul_exp_ray {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (hpos : ∀ j, 0 < lam j) (hlam : LinearIndependent ℚ lam)
    (K : ℕ) (G : Fin (K + 1) → (ι → ℝ) → ℝ) (hG : ∀ i, AnalyticAt ℝ (G i) 0)
    (h : ∀ᶠ t : ℝ in atTop,
      ∑ i : Fin (K + 1), t ^ (i : ℕ) * G i (fun j => Real.exp (-(lam j * t))) = 0) :
    ∀ i, ∀ᶠ ζ in 𝓝 (0 : ι → ℝ), G i ζ = 0 := by
  sorry

/-- **Lemma D.1 (separation on a ray).** Let `u_1, …, u_q` be real numbers that are linearly
independent over `ℚ`, and let `𝒯_0, …, 𝒯_K` be real-analytic maps from `ℝ^q` to a normed space. If
`∑_i t^i 𝒯_i(tanh(t u_1), …, tanh(t u_q)) = 0` for all `t > 0`, then every `𝒯_i` vanishes on
`ℝ^q`. -/
theorem tanh_ray_separation {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (u : ι → ℝ) (hu : LinearIndependent ℚ u) (K : ℕ)
    (𝒯 : Fin (K + 1) → (ι → ℝ) → F) (h𝒯 : ∀ i, AnalyticOnNhd ℝ (𝒯 i) Set.univ)
    (h : ∀ t : ℝ, 0 < t →
      ∑ i : Fin (K + 1), t ^ (i : ℕ) • 𝒯 i (fun j => Real.tanh (t * u j)) = 0) :
    ∀ i w, 𝒯 i w = 0 := by
  sorry

/-- **Lemma D.1 for the hidden units of several tokens.** The same statement with the numbers
`u` arranged in a matrix `U` (one row per token, one column per hidden unit), for maps `𝒯_i` of
the matrix `tanh(t U)` of the outputs of the hidden units. -/
theorem tanh_ray_separation_matrix {T q : Type*} [Fintype T] [Fintype q] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (U : Matrix T q ℝ)
    (hU : LinearIndependent ℚ (fun p : T × q => U p.1 p.2)) (K : ℕ)
    (𝒯 : Fin (K + 1) → Matrix T q ℝ → F) (h𝒯 : ∀ i, AnalyticOnNhd ℝ (𝒯 i) Set.univ)
    (h : ∀ t : ℝ, 0 < t →
      ∑ i : Fin (K + 1), t ^ (i : ℕ) • 𝒯 i ((t • U).map Real.tanh) = 0) :
    ∀ i w, 𝒯 i w = 0 := by
  sorry

end Skips
