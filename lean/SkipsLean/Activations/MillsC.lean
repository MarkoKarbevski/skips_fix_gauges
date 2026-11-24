import SkipsLean.Activations.FarFromZero

/-!
# The Mills ratio and GELU at complex arguments

Paper (dimension paper): Appendix D.5, "GELU and the Mills ratio", and Lemma D.8 (i), at complex
`z`. They are used at complex `z` in Appendix D.6 (the case `ε = 0`), Lemma D.19.

"GELU is `σ(z) = (z/2)(1 + erf(z/√2))`, which is entire. For `z ∈ ℂ` let
`φ(z) = e^{−z²/2}/√(2π)`, `mr(z) = √(π/2) e^{z²/2} (1 − erf(z/√2))`, the normal density and the
Mills ratio. Lemma D.8 (The Mills ratio). (i) For all `z ∈ ℂ`: `σ(z) = z − φ(z) z mr(z)` and
`σ'(z) = 1 − φ(z) (mr(z) − z)`." And, in the proof of (ii): "for real `z`,
`mr(z) = e^{z²/2} ∫_z^∞ e^{−y²/2} dy`, and the substitution `y = z + u` gives
`mr(z) = ∫_0^∞ e^{−zu−u²/2} du`. Both sides are entire, so this holds for all `z`."

Mathlib has no error function. So here the Mills ratio at a complex `z` is *defined* by the
integral `∫_0^∞ e^{−zu−u²/2} du` of the proof of Lemma D.8 (ii), and GELU at a complex `z` by the
first formula of Lemma D.8 (i), `z − φ(z) z mr(z)`. The file proves that `mr` and GELU so defined
are entire, that on the real line they are the real Mills ratio `(1 − Φ(z))/φ(z)`
(`Activations/FarFromZero.lean`) and the real GELU `z Φ(z)` (`Activations/Gaussian.lean`), and the
second formula of Lemma D.8 (i). An entire function is determined by its values on the real line,
so `geluC` is the paper's GELU at complex arguments.
-/

namespace Skips

open MeasureTheory

/-- The normal density at a complex `z`: `φ(z) = e^{−z²/2}/√(2π)`. -/
noncomputable def gaussPdfC (z : ℂ) : ℂ :=
  Complex.exp (-z ^ 2 / 2) / ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)

/-- The Mills ratio at a complex `z`, as the integral `mr(z) = ∫_0^∞ e^{−zu−u²/2} du` (proof of
Lemma D.8 (ii)). -/
noncomputable def millsRatioC (z : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2)

/-- GELU at a complex `z`, by the first formula of Lemma D.8 (i): `σ(z) = z − φ(z) z mr(z)`. -/
noncomputable def geluC (z : ℂ) : ℂ := z - gaussPdfC z * z * millsRatioC z

/-- On the real line `φ` is the real normal density. -/
theorem gaussPdfC_ofReal (x : ℝ) : gaussPdfC (x : ℂ) = ((gaussPdf x : ℝ) : ℂ) := by
  sorry

/-- `φ(z) ≠ 0`. -/
theorem gaussPdfC_ne_zero (z : ℂ) : gaussPdfC z ≠ 0 := by
  sorry

/-- The integrand `u ↦ e^{−zu−u²/2}` of the Mills ratio is integrable on `(0, ∞)`, for every
complex `z`. -/
theorem integrableOn_millsRatioC (z : ℂ) :
    IntegrableOn (fun u : ℝ => Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2)) (Set.Ioi 0) := by
  sorry

/-- **The Mills ratio is entire, with `mr'(z) = z mr(z) − 1`.** (The derivative under the integral
is `∫_0^∞ −u e^{−zu−u²/2} du`, and `∫_0^∞ (z + u) e^{−zu−u²/2} du = 1`.) -/
theorem hasDerivAt_millsRatioC (z : ℂ) : HasDerivAt millsRatioC (z * millsRatioC z - 1) z := by
  sorry

/-- **"for real `z`, `mr(z) = e^{z²/2} ∫_z^∞ e^{−y²/2} dy`, and the substitution `y = z + u` gives
`mr(z) = ∫_0^∞ e^{−zu−u²/2} du`":** on the real line the Mills ratio defined by the integral is
the real Mills ratio `(1 − Φ(x))/φ(x)`. -/
theorem millsRatioC_ofReal (x : ℝ) : millsRatioC (x : ℂ) = ((millsRatio x : ℝ) : ℂ) := by
  sorry

/-- On the real line `geluC` is GELU. -/
theorem geluC_ofReal (x : ℝ) : geluC (x : ℂ) = ((gelu x : ℝ) : ℂ) := by
  sorry

/-- **Lemma D.8 (i), second formula, at every complex `z`:** `σ'(z) = 1 − φ(z) (mr(z) − z)`. -/
theorem hasDerivAt_geluC (z : ℂ) :
    HasDerivAt geluC (1 - gaussPdfC z * (millsRatioC z - z)) z := by
  sorry

/-- "GELU […] is entire." -/
theorem differentiable_geluC : Differentiable ℂ geluC := by
  sorry

/-- GELU is holomorphic at every complex `z`. -/
theorem analyticAt_geluC (z : ℂ) : AnalyticAt ℂ geluC z := by
  sorry

/-- The gap `δ(z) = z − σ(z) = φ(z) z mr(z)` of GELU (Lemma D.8 (i), first formula). -/
theorem sub_geluC (z : ℂ) : z - geluC z = gaussPdfC z * z * millsRatioC z := by
  sorry

/-- The gap `δ'(z) = 1 − σ'(z) = φ(z) (mr(z) − z)` of the derivative of GELU (Lemma D.8 (i),
second formula). -/
theorem one_sub_deriv_geluC (z : ℂ) :
    1 - deriv geluC z = gaussPdfC z * (millsRatioC z - z) := by
  sorry

/-- On the real line the complex derivative of `geluC` is the derivative of GELU. -/
theorem deriv_geluC_ofReal (x : ℝ) : deriv geluC (x : ℂ) = ((geluDeriv x : ℝ) : ℂ) := by
  sorry

end Skips
