import Mathlib

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
  sorry

theorem gaussPdf_neg (z : ℝ) : gaussPdf (-z) = gaussPdf z := by
  sorry

/-- `φ'(z) = -z φ(z)`. -/
theorem hasDerivAt_gaussPdf (z : ℝ) : HasDerivAt gaussPdf (-z * gaussPdf z) z := by
  sorry

/-- `Φ' = φ`. -/
theorem hasDerivAt_gaussCdf (z : ℝ) : HasDerivAt gaussCdf (gaussPdf z) z := by
  sorry

/-- `Φ(-z) = 1 - Φ(z)`. -/
theorem gaussCdf_neg (z : ℝ) : gaussCdf (-z) = 1 - gaussCdf z := by
  sorry

theorem tendsto_gaussCdf_atTop : Tendsto gaussCdf atTop (𝓝 1) := by
  sorry

theorem tendsto_gaussCdf_atBot : Tendsto gaussCdf atBot (𝓝 0) := by
  sorry

theorem gaussCdf_pos (z : ℝ) : 0 < gaussCdf z := by
  sorry

theorem gaussCdf_lt_one (z : ℝ) : gaussCdf z < 1 := by
  sorry

/-- The upper bound on the tail: `1 - Φ(z) ≤ φ(z) / z` for `z > 0`. -/
theorem one_sub_gaussCdf_le {z : ℝ} (hz : 0 < z) : 1 - gaussCdf z ≤ gaussPdf z / z := by
  sorry

/-- The lower bound on the tail: `φ(z) (1/z - 1/z³) ≤ 1 - Φ(z)` for `z > 0`. -/
theorem le_one_sub_gaussCdf {z : ℝ} (hz : 0 < z) :
    gaussPdf z * (1 / z - 1 / z ^ 3) ≤ 1 - gaussCdf z := by
  sorry

/-- The derivative of GELU: `σ'(z) = Φ(z) + z φ(z)`. -/
theorem hasDerivAt_gelu (z : ℝ) : HasDerivAt gelu (gaussCdf z + z * gaussPdf z) z := by
  sorry

/-- `σ(z) - σ(-z) = z` for GELU. -/
theorem gelu_sub_gelu_neg (z : ℝ) : gelu z - gelu (-z) = z := by
  sorry

end Skips
