import SkipsLean.Imports

/-!
# The normal distribution function, its tail, and GELU

Papers: GELU is `σ(z) = z Φ(z)`, with `Φ` the standard normal distribution function and `φ = Φ'`
its density (dimension paper, Appendix C, proof of Lemma C.3 for GELU, and Lemma D.8).

`Φ` is defined here as `1/2 + ∫₀^z φ`. The file proves what the proofs of the papers use: `Φ' = φ`,
`Φ(-z) = 1 - Φ(z)`, `0 < Φ < 1`, the limits of `Φ` at `±∞`, and the bounds on the tail

  `φ(z) (1/z - 1/z³) ≤ 1 - Φ(z) ≤ φ(z) / z`   for `z > 0`,

and for GELU its derivative `Φ(z) + z φ(z)` and the identity `σ(z) - σ(-z) = z`.
-/

namespace Skips

open Filter Topology

/-- The standard normal density `φ(z) = e^{-z²/2} / √(2π)`. -/
noncomputable def gaussPdf (z : ℝ) : ℝ := Real.exp (-z ^ 2 / 2) / Real.sqrt (2 * Real.pi)

/-- The standard normal distribution function `Φ(z) = 1/2 + ∫₀^z φ`. -/
noncomputable def gaussCdf (z : ℝ) : ℝ := 1 / 2 + ∫ t in (0 : ℝ)..z, gaussPdf t

/-- GELU: `σ(z) = z Φ(z)`. -/
noncomputable def gelu (z : ℝ) : ℝ := z * gaussCdf z

theorem gaussPdf_pos (z : ℝ) : 0 < gaussPdf z := by
  exact div_pos (Real.exp_pos _) (Real.sqrt_pos.2 (by positivity))

theorem gaussPdf_neg (z : ℝ) : gaussPdf (-z) = gaussPdf z := by
  simp only [gaussPdf, neg_sq]

/-- `φ'(z) = -z φ(z)`. -/
theorem hasDerivAt_gaussPdf (z : ℝ) : HasDerivAt gaussPdf (-z * gaussPdf z) z := by
  -- chain rule for `exp (-z²/2)`, then division by the constant `√(2π)`
  have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-z) z := by
    convert ((hasDerivAt_pow 2 z).neg).div_const 2 using 1
    norm_num
    ring
  unfold gaussPdf
  convert h1.exp.div_const (Real.sqrt (2 * Real.pi)) using 1
  ring

theorem continuous_gaussPdf : Continuous gaussPdf := by
  unfold gaussPdf
  fun_prop

/-- `Φ' = φ`. -/
theorem hasDerivAt_gaussCdf (z : ℝ) : HasDerivAt gaussCdf (gaussPdf z) z := by
  -- fundamental theorem of calculus for the continuous `φ`, plus the constant `1/2`
  have h := intervalIntegral.integral_hasDerivAt_right (continuous_gaussPdf.intervalIntegrable 0 z)
    (continuous_gaussPdf.stronglyMeasurableAtFilter _ _) continuous_gaussPdf.continuousAt
  exact h.const_add (1 / 2)

/-- `Φ(-z) = 1 - Φ(z)`. -/
theorem gaussCdf_neg (z : ℝ) : gaussCdf (-z) = 1 - gaussCdf z := by
  -- `∫₀^{-z} φ = -∫_{-z}^0 φ = -∫₀^z φ(-t) dt = -∫₀^z φ`, by the substitution `t ↦ -t`
  have h : ∫ t in (0 : ℝ)..(-z), gaussPdf t = -∫ t in (0 : ℝ)..z, gaussPdf t := by
    have h1 := intervalIntegral.integral_comp_neg (a := 0) (b := z) gaussPdf
    simp only [gaussPdf_neg, neg_zero] at h1
    rw [intervalIntegral.integral_symm, h1]
  rw [gaussCdf, gaussCdf, h]
  ring

theorem gaussPdf_eq :
    gaussPdf = fun t => Real.exp (-(1 / 2) * t ^ 2) / Real.sqrt (2 * Real.pi) := by
  funext t
  rw [gaussPdf]
  congr 2
  ring

theorem integrable_gaussPdf : MeasureTheory.Integrable gaussPdf := by
  rw [gaussPdf_eq]
  exact (integrable_exp_neg_mul_sq (by norm_num)).div_const _

/-- `∫₀^∞ φ = 1/2`, from `∫₀^∞ e^{-b t²} = √(π/b)/2` with `b = 1/2`. -/
theorem integral_gaussPdf_Ioi : ∫ t in Set.Ioi (0 : ℝ), gaussPdf t = 1 / 2 := by
  rw [gaussPdf_eq, MeasureTheory.integral_div, integral_gaussian_Ioi,
    show Real.pi / (1 / 2) = 2 * Real.pi by ring]
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  field_simp

theorem tendsto_gaussCdf_atTop : Tendsto gaussCdf atTop (𝓝 1) := by
  -- `∫₀^z φ → ∫₀^∞ φ = 1/2`
  have h := MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
    integrable_gaussPdf.integrableOn tendsto_id
  rw [integral_gaussPdf_Ioi] at h
  have h2 : Tendsto gaussCdf atTop (𝓝 (1 / 2 + 1 / 2)) := h.const_add (1 / 2)
  rwa [show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num] at h2

theorem tendsto_gaussCdf_atBot : Tendsto gaussCdf atBot (𝓝 0) := by
  -- `Φ(z) = 1 - Φ(-z)` and `-z → +∞`
  have h := (tendsto_gaussCdf_atTop.comp tendsto_neg_atBot_atTop).const_sub 1
  rw [sub_self] at h
  refine h.congr fun z => ?_
  simp only [Function.comp_apply, gaussCdf_neg, sub_sub_cancel]

/-- `Φ` is strictly increasing, since `Φ' = φ > 0`. -/
theorem strictMono_gaussCdf : StrictMono gaussCdf :=
  strictMono_of_hasDerivAt_pos hasDerivAt_gaussCdf gaussPdf_pos

theorem gaussCdf_pos (z : ℝ) : 0 < gaussCdf z := by
  -- `0 ≤ Φ(z - 1) < Φ(z)`
  exact lt_of_le_of_lt (strictMono_gaussCdf.monotone.le_of_tendsto tendsto_gaussCdf_atBot (z - 1))
    (strictMono_gaussCdf (by linarith))

theorem gaussCdf_lt_one (z : ℝ) : gaussCdf z < 1 := by
  -- `Φ(z) < Φ(z + 1) ≤ 1`
  exact lt_of_lt_of_le (strictMono_gaussCdf (by linarith))
    (strictMono_gaussCdf.monotone.ge_of_tendsto tendsto_gaussCdf_atTop (z + 1))

theorem tendsto_gaussPdf_atTop : Tendsto gaussPdf atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => -y ^ 2 / 2) atTop atBot :=
    (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero)).atBot_div_const (by norm_num)
  have h2 := (Real.tendsto_exp_atBot.comp h1).div_const (Real.sqrt (2 * Real.pi))
  rw [zero_div] at h2
  exact h2

/-- A function antitone on `(0, ∞)` with limit `0` at `+∞` is nonnegative there. -/
private theorem nonneg_of_antitoneOn_of_tendsto {g : ℝ → ℝ} (hg : AntitoneOn g (Set.Ioi 0))
    (hlim : Tendsto g atTop (𝓝 0)) {z : ℝ} (hz : 0 < z) : 0 ≤ g z :=
  le_of_tendsto hlim ((eventually_ge_atTop z).mono fun _y hy =>
    hg (Set.mem_Ioi.2 hz) (Set.mem_Ioi.2 (lt_of_lt_of_le hz hy)) hy)

/-- A function on `(0, ∞)` with a nonpositive derivative is antitone there. -/
private theorem antitoneOn_Ioi_of_hasDerivAt {g g' : ℝ → ℝ}
    (hg : ∀ y, 0 < y → HasDerivAt g (g' y) y) (hg' : ∀ y, 0 < y → g' y ≤ 0) :
    AntitoneOn g (Set.Ioi 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := g') (convex_Ioi 0)
    (fun y hy => (hg y hy).continuousAt.continuousWithinAt) (fun y hy => ?_) (fun y hy => ?_)
  · rw [interior_Ioi] at hy ⊢
    exact (hg y hy).hasDerivWithinAt
  · rw [interior_Ioi] at hy
    exact hg' y hy

/-- The upper bound on the tail: `1 - Φ(z) ≤ φ(z) / z` for `z > 0`. -/
theorem one_sub_gaussCdf_le {z : ℝ} (hz : 0 < z) : 1 - gaussCdf z ≤ gaussPdf z / z := by
  -- `g(y) = φ(y)/y - (1 - Φ(y))` has `g' = -φ/y² ≤ 0` on `(0, ∞)` and `g → 0` at `+∞`, so `g ≥ 0`
  have hd : ∀ y, 0 < y → HasDerivAt (fun y => gaussPdf y / y - (1 - gaussCdf y))
      (-gaussPdf y / y ^ 2) y := by
    intro y hy
    convert ((hasDerivAt_gaussPdf y).div (hasDerivAt_id' y) hy.ne').sub
      ((hasDerivAt_gaussCdf y).const_sub 1) using 1
    field_simp
    ring
  have hanti := antitoneOn_Ioi_of_hasDerivAt hd fun y _ =>
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (gaussPdf_pos y).le) (sq_nonneg y)
  have hlim : Tendsto (fun y => gaussPdf y / y - (1 - gaussCdf y)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y => gaussPdf y / y) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using tendsto_gaussPdf_atTop.mul tendsto_inv_atTop_zero
    have h2 := h1.sub (tendsto_gaussCdf_atTop.const_sub 1)
    rwa [sub_self, sub_zero] at h2
  have := nonneg_of_antitoneOn_of_tendsto hanti hlim hz
  linarith

/-- The lower bound on the tail: `φ(z) (1/z - 1/z³) ≤ 1 - Φ(z)` for `z > 0`. -/
theorem le_one_sub_gaussCdf {z : ℝ} (hz : 0 < z) :
    gaussPdf z * (1 / z - 1 / z ^ 3) ≤ 1 - gaussCdf z := by
  -- `k(y) = (1 - Φ(y)) - φ(y)(1/y - 1/y³)` has `k' = -3φ/y⁴ ≤ 0` on `(0, ∞)` and `k → 0` at `+∞`,
  -- so `k ≥ 0`
  have hd : ∀ y, 0 < y → HasDerivAt (fun y => (1 - gaussCdf y) - gaussPdf y * (1 / y - 1 / y ^ 3))
      (-3 * gaussPdf y / y ^ 4) y := by
    intro y hy
    have h1 := (hasDerivAt_const y (1 : ℝ)).div (hasDerivAt_id' y) hy.ne'
    have h3 := (hasDerivAt_const y (1 : ℝ)).div (hasDerivAt_pow 3 y) (pow_ne_zero 3 hy.ne')
    convert ((hasDerivAt_gaussCdf y).const_sub 1).sub ((hasDerivAt_gaussPdf y).mul (h1.sub h3))
      using 1
    norm_num
    field_simp
    ring
  have hanti := antitoneOn_Ioi_of_hasDerivAt hd fun y _ =>
    div_nonpos_of_nonpos_of_nonneg (by nlinarith [gaussPdf_pos y]) (by positivity)
  have hlim : Tendsto (fun y => (1 - gaussCdf y) - gaussPdf y * (1 / y - 1 / y ^ 3)) atTop
      (𝓝 0) := by
    have hinv : Tendsto (fun y : ℝ => 1 / y - 1 / y ^ 3) atTop (𝓝 0) := by
      have a := tendsto_inv_atTop_zero (𝕜 := ℝ)
      have b := tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (α := ℝ) (n := 3) (by norm_num))
      simpa [one_div] using a.sub b
    have h2 := (tendsto_gaussCdf_atTop.const_sub 1).sub (tendsto_gaussPdf_atTop.mul hinv)
    rwa [sub_self, mul_zero, sub_zero] at h2
  have := nonneg_of_antitoneOn_of_tendsto hanti hlim hz
  linarith

/-- The derivative of GELU, `σ'(z) = Φ(z) + z φ(z)` (`hasDerivAt_gelu`). -/
noncomputable def geluDeriv (z : ℝ) : ℝ := gaussCdf z + z * gaussPdf z

/-- The derivative of GELU: `σ'(z) = Φ(z) + z φ(z)`. -/
theorem hasDerivAt_gelu (z : ℝ) : HasDerivAt gelu (gaussCdf z + z * gaussPdf z) z := by
  -- product rule for `z Φ(z)`
  show HasDerivAt (fun y => y * gaussCdf y) _ z
  convert (hasDerivAt_id' z).mul (hasDerivAt_gaussCdf z) using 1
  ring

/-- `σ(z) - σ(-z) = z` for GELU. -/
theorem gelu_sub_gelu_neg (z : ℝ) : gelu z - gelu (-z) = z := by
  -- `zΦ(z) + z(1 - Φ(z)) = z`
  rw [gelu, gelu, gaussCdf_neg]
  ring

end Skips
