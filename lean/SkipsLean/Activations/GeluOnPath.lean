import SkipsLean.Activations.MillsCExpansion

/-!
# GELU at the input of a hidden unit on the path

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), proof of Lemma D.19, "The path":

"Fix `ξ ∈ P` and a unit row `ξ'` orthogonal to `ξ`, let `n(t)` be the path (41), and
`z_j(t) = n(t) c_j`, `r_j = (ξc_j)² − (ξ'c_j)² > 0`, `δ_j(t) = z_j − σ(z_j)`,
`δ'_j(t) = 1 − σ'(z_j)`. […] For `t ≥ 1`, by (41) and (P2),

  `Re z_j ≥ √d ξc_j > 0`, `|Im z_j| ≤ Re z_j`, `Re z_j² = d (ξc_j)² + (d/4)(t − t⁻¹)² r_j`.   (44)

By Lemma D.8, `δ_j = φ(z_j) z_j mr(z_j)` and `δ'_j = φ(z_j) (mr(z_j) − z_j)`, with
`|mr(z_j)| ≤ 1/Re z_j` and `|z_j| ≤ √2 Re z_j`. So, with a constant `κ`,

  `|δ_j(t)| ≤ e^{−d(ξc_j)²/2} e^{−(d/8)(t−t⁻¹)² r_j}`,
  `|δ'_j(t)| ≤ κ t e^{−(d/8)(t−t⁻¹)² r_j}`.   (45)"

By (41), `z_j(t) = n(t) c_j = ω t + ω̄/t` with the complex number `ω = (√d/2)(ξc_j + i ξ'c_j)`,
for which (P2) says `|Im ω| < Re ω`. In these terms `Re z_j = Re ω (t + 1/t)`,
`Im z_j = Im ω (t − 1/t)`, `d (ξc_j)² = 4 (Re ω)²` and `(d/4) r_j = (Re ω)² − (Im ω)²`. The
statements below are (44) and (45) for the curve `z(t) = ω t + ω̄/t`, with the constant
`κ = 1/(2 Re ω) + 2 Re ω`, and the absolute value of `φ(z(t))`, by which Step 2 of the proof
divides.
-/

namespace Skips

/-- The input of a hidden unit on the path: `z(t) = ω t + ω̄/t`. For the path (41) and a column `c`
of the read, `n(t) c = z(t)` with `ω = (√d/2)(ξc + i ξ'c)`. -/
noncomputable def unitPath (ω : ℂ) (t : ℝ) : ℂ :=
  ω * (t : ℂ) + (starRingEnd ℂ) ω / (t : ℂ)

/-- `z(t) = ω t + ω̄ · (1/t)` with a real factor `1/t`. -/
private theorem unitPath_eq_gop (ω : ℂ) (t : ℝ) :
    unitPath ω t = ω * (t : ℂ) + (starRingEnd ℂ) ω * ((1 / t : ℝ) : ℂ) := by
  simp [unitPath, div_eq_mul_inv]

/-- (44): `Re z(t) = Re ω (t + 1/t)`. -/
theorem unitPath_re (ω : ℂ) {t : ℝ} (ht : 0 < t) : (unitPath ω t).re = ω.re * (t + 1 / t) := by
  rw [unitPath_eq_gop]
  simp [Complex.mul_re]
  ring

/-- (44): `Im z(t) = Im ω (t − 1/t)`. -/
theorem unitPath_im (ω : ℂ) {t : ℝ} (ht : 0 < t) : (unitPath ω t).im = ω.im * (t - 1 / t) := by
  rw [unitPath_eq_gop]
  simp [Complex.mul_im]
  ring

/-- (44): `Re z(t)² = 4 (Re ω)² + ((Re ω)² − (Im ω)²)(t − 1/t)²`. -/
theorem unitPath_sq_re (ω : ℂ) {t : ℝ} (ht : 0 < t) :
    ((unitPath ω t) ^ 2).re = 4 * ω.re ^ 2 + (ω.re ^ 2 - ω.im ^ 2) * (t - 1 / t) ^ 2 := by
  -- `Re z² = (Re z)² − (Im z)²`, and `(t + 1/t)² = (t − 1/t)² + 4`
  have h : t * (1 / t) = 1 := by field_simp
  rw [pow_two, Complex.mul_re, unitPath_re ω ht, unitPath_im ω ht]
  linear_combination (4 * ω.re ^ 2) * h

/-- The absolute value of the normal density on the path:
`|φ(z(t))| = e^{−2(Re ω)²} e^{−((Re ω)² − (Im ω)²)(t − 1/t)²/2} / √(2π)`. -/
theorem norm_gaussPdfC_unitPath (ω : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖gaussPdfC (unitPath ω t)‖
      = Real.exp (-(2 * ω.re ^ 2))
          * Real.exp (-((ω.re ^ 2 - ω.im ^ 2) * (t - 1 / t) ^ 2 / 2))
          / Real.sqrt (2 * Real.pi) := by
  -- `|e^w| = e^{Re w}` with `Re(−z²/2) = −Re z²/2`, and (44) for `Re z²`
  have hsq := unitPath_sq_re ω ht
  unfold gaussPdfC
  rw [norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    ← Real.exp_add]
  congr 2
  simp [hsq]
  ring

/-- On the path for `t ≥ 1`, when `|Im ω| < Re ω`: `Re z ≥ 2 Re ω > 0`, `‖z‖ ≤ √2 Re z`, and
`Re z ≤ 2 Re ω t`. -/
private theorem unitPath_facts_gop {ω : ℂ} (hω : |ω.im| < ω.re) {t : ℝ} (ht : 1 ≤ t) :
    2 * ω.re ≤ (unitPath ω t).re ∧ ‖unitPath ω t‖ ≤ Real.sqrt 2 * (unitPath ω t).re
      ∧ (unitPath ω t).re ≤ 2 * ω.re * t := by
  have ht0 : 0 < t := by linarith
  have ha : 0 < ω.re := lt_of_le_of_lt (abs_nonneg _) hω
  have hit : 1 / t ≤ 1 := by rw [div_le_one ht0]; exact ht
  have hit0 : 0 < 1 / t := by positivity
  -- `t + 1/t ≥ 2`, from `t · (1/t) = 1` and `(t − 1)² ≥ 0`
  have h1 : t * (1 / t) = 1 := by field_simp
  have h2 : 2 ≤ t + 1 / t := by nlinarith [sq_nonneg (t - 1), mul_pos ht0 hit0]
  rw [unitPath_re ω ht0]
  refine ⟨by nlinarith, ?_, by nlinarith⟩
  -- `|Im z| = |Im ω| (t − 1/t) ≤ Re ω (t + 1/t) = Re z`, so `max |Re z| |Im z| = Re z`
  have hre : 0 ≤ ω.re * (t + 1 / t) := by positivity
  have him : |(unitPath ω t).im| ≤ ω.re * (t + 1 / t) := by
    rw [unitPath_im ω ht0, abs_mul, abs_of_nonneg (by linarith : 0 ≤ t - 1 / t)]
    nlinarith [abs_nonneg ω.im]
  calc ‖unitPath ω t‖ ≤ Real.sqrt 2 * max |(unitPath ω t).re| |(unitPath ω t).im| :=
        Complex.norm_le_sqrt_two_mul_max _
    _ = Real.sqrt 2 * (ω.re * (t + 1 / t)) := by
        rw [unitPath_re ω ht0, abs_of_nonneg hre, max_eq_left him]

/-- (45), first bound: for `t ≥ 1`, when `|Im ω| < Re ω`,
`|δ(t)| = |z(t) − σ(z(t))| ≤ e^{−2(Re ω)²} e^{−((Re ω)² − (Im ω)²)(t−1/t)²/2}`. -/
theorem norm_sub_geluC_unitPath_le {ω : ℂ} (hω : |ω.im| < ω.re) {t : ℝ} (ht : 1 ≤ t) :
    ‖unitPath ω t - geluC (unitPath ω t)‖
      ≤ Real.exp (-(2 * ω.re ^ 2))
          * Real.exp (-((ω.re ^ 2 - ω.im ^ 2) * (t - 1 / t) ^ 2 / 2)) := by
  -- `δ = φ(z) z mr(z)` with `‖z‖ ‖mr(z)‖ ≤ √2 Re z / Re z = √2` and `√2 ≤ √(2π)`
  have ht0 : 0 < t := by linarith
  obtain ⟨hre, hz, -⟩ := unitPath_facts_gop hω ht
  have hre0 : 0 < (unitPath ω t).re := by
    nlinarith [lt_of_le_of_lt (abs_nonneg _) hω]
  have hmr := norm_millsRatioC_le hre0
  have hzm : ‖unitPath ω t‖ * ‖millsRatioC (unitPath ω t)‖ ≤ Real.sqrt 2 := by
    calc ‖unitPath ω t‖ * ‖millsRatioC (unitPath ω t)‖
        ≤ (Real.sqrt 2 * (unitPath ω t).re) * (1 / (unitPath ω t).re) :=
          mul_le_mul hz hmr (norm_nonneg _) (by positivity)
      _ = Real.sqrt 2 := by field_simp
  have hs : Real.sqrt 2 ≤ Real.sqrt (2 * Real.pi) :=
    Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
  have hs0 : 0 < Real.sqrt (2 * Real.pi) := by positivity
  set E := Real.exp (-(2 * ω.re ^ 2))
    * Real.exp (-((ω.re ^ 2 - ω.im ^ 2) * (t - 1 / t) ^ 2 / 2)) with hE
  have hE0 : 0 ≤ E := by positivity
  rw [sub_geluC, norm_mul, norm_mul, norm_gaussPdfC_unitPath ω ht0, mul_assoc]
  calc E / Real.sqrt (2 * Real.pi) * (‖unitPath ω t‖ * ‖millsRatioC (unitPath ω t)‖)
      ≤ E / Real.sqrt (2 * Real.pi) * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_left hzm (by positivity)
    _ ≤ E := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hs0]
        exact mul_le_mul_of_nonneg_left hs hE0

/-- (45), second bound: `|δ'(t)| = |1 − σ'(z(t))| ≤ κ t e^{−((Re ω)² − (Im ω)²)(t−1/t)²/2}` for
`t ≥ 1`, with `κ = 1/(2 Re ω) + 2 Re ω`, when `|Im ω| < Re ω`. -/
theorem norm_one_sub_deriv_geluC_unitPath_le {ω : ℂ} (hω : |ω.im| < ω.re) {t : ℝ}
    (ht : 1 ≤ t) :
    ‖1 - deriv geluC (unitPath ω t)‖
      ≤ (1 / (2 * ω.re) + 2 * ω.re) * t
          * Real.exp (-((ω.re ^ 2 - ω.im ^ 2) * (t - 1 / t) ^ 2 / 2)) := by
  -- `δ' = φ(z) (mr(z) − z)` with `‖mr(z)‖ ≤ 1/Re z ≤ 1/(2 Re ω)`,
  -- `‖z‖ ≤ √2 Re z ≤ 2√2 Re ω t`, `e^{−2(Re ω)²} ≤ 1`, `1 ≤ t √(2π)` and `√2 ≤ √(2π)`
  have ht0 : 0 < t := by linarith
  have ha : 0 < ω.re := lt_of_le_of_lt (abs_nonneg _) hω
  obtain ⟨hre, hz, hre2⟩ := unitPath_facts_gop hω ht
  have hre0 : 0 < (unitPath ω t).re := by linarith
  have hmr : ‖millsRatioC (unitPath ω t)‖ ≤ 1 / (2 * ω.re) :=
    (norm_millsRatioC_le hre0).trans (one_div_le_one_div_of_le (by positivity) hre)
  have hz' : ‖unitPath ω t‖ ≤ Real.sqrt 2 * (2 * ω.re * t) :=
    hz.trans (mul_le_mul_of_nonneg_left hre2 (Real.sqrt_nonneg 2))
  have hs : Real.sqrt 2 ≤ Real.sqrt (2 * Real.pi) :=
    Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
  have hs0 : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : 1 ≤ Real.sqrt (2 * Real.pi) := by nlinarith [Real.sqrt_nonneg 2]
  have hts : 1 ≤ t * Real.sqrt (2 * Real.pi) := by nlinarith
  set E := Real.exp (-((ω.re ^ 2 - ω.im ^ 2) * (t - 1 / t) ^ 2 / 2)) with hE
  have hE0 : 0 ≤ E := by positivity
  have hE1 : Real.exp (-(2 * ω.re ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hφ : ‖gaussPdfC (unitPath ω t)‖ ≤ E / Real.sqrt (2 * Real.pi) := by
    rw [norm_gaussPdfC_unitPath ω ht0]
    gcongr
    calc Real.exp (-(2 * ω.re ^ 2)) * E ≤ 1 * E := mul_le_mul_of_nonneg_right hE1 hE0
      _ = E := one_mul E
  have hsum : ‖millsRatioC (unitPath ω t) - unitPath ω t‖
      ≤ 1 / (2 * ω.re) + Real.sqrt 2 * (2 * ω.re * t) :=
    (norm_sub_le _ _).trans (add_le_add hmr hz')
  rw [one_sub_deriv_geluC, norm_mul]
  calc ‖gaussPdfC (unitPath ω t)‖ * ‖millsRatioC (unitPath ω t) - unitPath ω t‖
      ≤ E / Real.sqrt (2 * Real.pi) * (1 / (2 * ω.re) + Real.sqrt 2 * (2 * ω.re * t)) :=
        mul_le_mul hφ hsum (norm_nonneg _) (by positivity)
    _ ≤ (1 / (2 * ω.re) + 2 * ω.re) * t * E := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hs0]
        have hc1 : 0 ≤ E * (1 / (2 * ω.re)) := by positivity
        have hc2 : 0 ≤ E * (2 * ω.re * t) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hts hc1, mul_le_mul_of_nonneg_left hs hc2]


end Skips
