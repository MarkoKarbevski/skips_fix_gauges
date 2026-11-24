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

/-- (45), first bound: for `t ≥ 1`, when `|Im ω| < Re ω`,
`|δ(t)| = |z(t) − σ(z(t))| ≤ e^{−2(Re ω)²} e^{−((Re ω)² − (Im ω)²)(t−1/t)²/2}`. -/
theorem norm_sub_geluC_unitPath_le {ω : ℂ} (hω : |ω.im| < ω.re) {t : ℝ} (ht : 1 ≤ t) :
    ‖unitPath ω t - geluC (unitPath ω t)‖
      ≤ Real.exp (-(2 * ω.re ^ 2))
          * Real.exp (-((ω.re ^ 2 - ω.im ^ 2) * (t - 1 / t) ^ 2 / 2)) := by
  sorry

/-- (45), second bound: `|δ'(t)| = |1 − σ'(z(t))| ≤ κ t e^{−((Re ω)² − (Im ω)²)(t−1/t)²/2}` for
`t ≥ 1`, with `κ = 1/(2 Re ω) + 2 Re ω`, when `|Im ω| < Re ω`. -/
theorem norm_one_sub_deriv_geluC_unitPath_le {ω : ℂ} (hω : |ω.im| < ω.re) {t : ℝ}
    (ht : 1 ≤ t) :
    ‖1 - deriv geluC (unitPath ω t)‖
      ≤ (1 / (2 * ω.re) + 2 * ω.re) * t
          * Real.exp (-((ω.re ^ 2 - ω.im ^ 2) * (t - 1 / t) ^ 2 / 2)) := by
  sorry

end Skips
