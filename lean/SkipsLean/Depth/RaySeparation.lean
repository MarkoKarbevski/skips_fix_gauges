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

/-- `tanh x = (1 - e^{-2x}) / (1 + e^{-2x})`. -/
private lemma tanh_eq_one_sub_div (x : ℝ) :
    Real.tanh x = (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))) := by
  have h1 : Real.exp (-(2 * x)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hp1 : 0 < Real.exp x := Real.exp_pos x
  have hp2 : 0 < Real.exp (-x) := Real.exp_pos _
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, h1,
    div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (Real.exp (-x)) * h2

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
  -- No `u_j` is zero; `σ j = ±1` is the sign of `u_j`, and `s j` its image in `ℝ`.
  have hu0 : ∀ j, u j ≠ 0 := fun j => hu.ne_zero j
  let σ : ι → ℚ := fun j => if 0 < u j then 1 else -1
  let s : ι → ℝ := fun j => (σ j : ℝ)
  have hσ0 : ∀ j, σ j ≠ 0 := fun j => by
    simp only [σ]; split_ifs <;> norm_num
  have hs0 : ∀ j, s j ≠ 0 := fun j => by simp only [s]; exact_mod_cast hσ0 j
  have hsabs : ∀ j, |u j| = s j * u j := fun j => by
    simp only [s, σ]
    split_ifs with hj
    · simp [abs_of_pos hj]
    · have : u j < 0 := lt_of_le_of_ne (not_lt.1 hj) (hu0 j)
      simp [abs_of_neg this]
  have hss : ∀ j, s j * s j = 1 := fun j => by
    simp only [s, σ]; split_ifs <;> norm_num
  -- The rates `λ_j = 2 |u_j|` are positive and linearly independent over `ℚ`.
  let lam : ι → ℝ := fun j => 2 * |u j|
  have hpos : ∀ j, 0 < lam j := fun j => by
    have := abs_pos.2 (hu0 j); simp only [lam]; linarith
  have hlam : LinearIndependent ℚ lam := by
    have := hu.units_smul (fun j => Units.mk0 (2 * σ j) (mul_ne_zero two_ne_zero (hσ0 j)))
    convert this using 1
    funext j
    simp only [lam, Pi.smul_apply', Units.smul_def, Units.val_mk0, Rat.smul_def, hsabs]
    push_cast
    ring
  -- `tanh` is odd: `tanh (x u_j) = s_j tanh (x |u_j|)`.
  have hodd : ∀ x j, Real.tanh (x * u j) = s j * Real.tanh (x * |u j|) := fun x j => by
    simp only [s, σ]
    split_ifs with hj
    · simp [abs_of_pos hj]
    · have : u j < 0 := lt_of_le_of_ne (not_lt.1 hj) (hu0 j)
      rw [abs_of_neg this, mul_neg, Real.tanh_neg]
      push_cast; ring
  have hs2 : ∀ j, s j + s j ≠ 0 := fun j => by
    rw [← two_mul]; exact mul_ne_zero two_ne_zero (hs0 j)
  clear_value s σ
  -- `tanh (t u_j) = s_j (1 - ζ_j) / (1 + ζ_j)` with `ζ_j = exp (-λ_j t)`.
  have htanh : ∀ t j, s j * (1 - Real.exp (-(lam j * t))) / (1 + Real.exp (-(lam j * t))) =
      Real.tanh (t * u j) := fun t j => by
    rw [hodd, mul_div_assoc, show lam j * t = 2 * (t * |u j|) by simp only [lam]; ring,
      ← tanh_eq_one_sub_div]
  -- The map `g : ζ ↦ s (1 - ζ) / (1 + ζ)` (analytic near `0`) and its inverse `ψ` near `s`.
  let g : (ι → ℝ) → (ι → ℝ) := fun ζ j => s j * (1 - ζ j) / (1 + ζ j)
  let ψ : (ι → ℝ) → (ι → ℝ) := fun w j => (s j - w j) / (s j + w j)
  have hg : AnalyticAt ℝ g 0 := by
    refine analyticAt_pi_iff.2 fun j => ?_
    have hp : AnalyticAt ℝ (fun ζ : ι → ℝ => ζ j) 0 :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j).analyticAt 0
    exact (analyticAt_const.mul (analyticAt_const.sub hp)).div (analyticAt_const.add hp)
      (by simp)
  have hψ : ContinuousAt ψ s := by
    refine continuousAt_pi.2 fun j => ?_
    exact (continuousAt_const.sub (continuous_apply j).continuousAt).div
      (continuousAt_const.add (continuous_apply j).continuousAt) (hs2 j)
  have hψs : ψ s = 0 := by funext j; simp [ψ]
  have hgψ : ∀ᶠ w in 𝓝 s, g (ψ w) = w := by
    have : ∀ᶠ w in 𝓝 s, ∀ j, s j + w j ≠ 0 := by
      refine eventually_all.2 fun j => ?_
      exact (continuousAt_const.add (continuous_apply j).continuousAt).eventually_ne (hs2 j)
    filter_upwards [this] with w hw
    funext j
    have h1 : 1 - (s j - w j) / (s j + w j) = 2 * w j / (s j + w j) := by
      field_simp [hw j]; ring
    have h2 : 1 + (s j - w j) / (s j + w j) = 2 * s j / (s j + w j) := by
      field_simp [hw j]; ring
    simp only [g, ψ]
    rw [h1, h2]
    field_simp [hw j, hs0 j]
  -- For each continuous linear functional `φ`, the function `φ ∘ 𝒯_i` vanishes everywhere.
  intro i w
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun φ => ?_
  have hG : ∀ i, AnalyticAt ℝ (fun ζ => φ (𝒯 i (g ζ))) 0 := fun i =>
    (φ.analyticAt _).comp ((h𝒯 i (g 0) trivial).comp hg)
  have hray : ∀ᶠ t : ℝ in atTop, ∑ i : Fin (K + 1), t ^ (i : ℕ) *
      φ (𝒯 i (g (fun j => Real.exp (-(lam j * t))))) = 0 := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    have hgt : g (fun j => Real.exp (-(lam j * t))) = fun j => Real.tanh (t * u j) := by
      funext j; exact htanh t j
    rw [hgt, ← map_zero φ, ← h t ht, map_sum]
    simp only [map_smul, smul_eq_mul]
  have h0 := eventually_eq_zero_of_sum_pow_mul_exp_ray lam hpos hlam K _ hG hray i
  -- Near `s`, `φ (𝒯_i w) = φ (𝒯_i (g (ψ w)))`, and `ψ w` is near `0`.
  have hnear : ∀ᶠ w in 𝓝 s, φ (𝒯 i w) = 0 := by
    have ht := hψ.tendsto
    rw [hψs] at ht
    filter_upwards [ht.eventually h0, hgψ] with w hw1 hw2
    rw [hw2] at hw1
    exact hw1
  -- Identity principle on `ℝ^q`.
  have han : AnalyticOnNhd ℝ (fun w => φ (𝒯 i w)) Set.univ := fun x _ =>
    (φ.analyticAt _).comp (h𝒯 i x trivial)
  exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ s) hnear (Set.mem_univ w)

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
  -- The continuous linear map `v ↦ (a, b) ↦ v (a, b)` from `ℝ^{T × q}` onto the matrices.
  let L : (T × q → ℝ) →ₗ[ℝ] Matrix T q ℝ :=
    { toFun := fun v => Matrix.of fun a b => v (a, b)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e : (T × q → ℝ) →L[ℝ] Matrix T q ℝ := LinearMap.toContinuousLinearMap L
  have he : ∀ v, e v = Matrix.of fun a b => v (a, b) := fun v => rfl
  have key := tanh_ray_separation (fun p : T × q => U p.1 p.2) hU K (fun i v => 𝒯 i (e v))
    (fun i x _ => (h𝒯 i (e x) trivial).comp (e.analyticAt x)) (fun t ht => by
      have hm : e (fun p => Real.tanh (t * U p.1 p.2)) = (t • U).map Real.tanh := by
        ext a b; simp [he]
      simp only [hm]
      exact h t ht)
  intro i w
  exact key i (fun p => w p.1 p.2)

end Skips
