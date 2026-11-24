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
  rw [gaussPdfC, gaussPdf]
  push_cast
  rfl

/-- `φ(z) ≠ 0`. -/
theorem gaussPdfC_ne_zero (z : ℂ) : gaussPdfC z ≠ 0 := by
  exact div_ne_zero (Complex.exp_ne_zero _)
    (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne')

/-- The Gaussian bound `‖e^{−zu−u²/2}‖ ≤ e^{c²} e^{−u²/4}` for `|Re z| ≤ c`. -/
private theorem norm_exp_le_mc {z : ℂ} {c : ℝ} (hc : |z.re| ≤ c) (u : ℝ) :
    ‖Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2)‖
      ≤ Real.exp (c ^ 2) * Real.exp (-(1 / 4) * u ^ 2) := by
  -- `−Re z · u − u²/2 ≤ (Re z)² − u²/4 ≤ c² − u²/4`, since `(u/2 + Re z)² ≥ 0`
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hre : (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2).re = -(z.re * u) - u ^ 2 / 2 := by
    simp [sq]
  rw [hre]
  have h2 : z.re ^ 2 ≤ c ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  nlinarith [sq_nonneg (u / 2 + z.re)]

/-- The integrand `u ↦ e^{−zu−u²/2}` of the Mills ratio is integrable on `(0, ∞)`, for every
complex `z`. -/
theorem integrableOn_millsRatioC (z : ℂ) :
    IntegrableOn (fun u : ℝ => Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2)) (Set.Ioi 0) := by
  have hg := ((integrable_exp_neg_mul_sq (b := 1 / 4) (by norm_num)).const_mul
    (Real.exp (|z.re| ^ 2))).integrableOn (s := Set.Ioi 0)
  refine hg.mono' (by fun_prop : Continuous _).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by simpa using norm_exp_le_mc le_rfl u

/-- `∂_z e^{−zu−u²/2} = −u e^{−zu−u²/2}`. -/
private theorem hasDerivAt_integrand_mc (u : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (-(w * (u : ℂ)) - (u : ℂ) ^ 2 / 2))
      (-(u : ℂ) * Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2)) z := by
  have h1 : HasDerivAt (fun w : ℂ => -(w * (u : ℂ)) - (u : ℂ) ^ 2 / 2) (-(1 * (u : ℂ))) z :=
    ((hasDerivAt_id' z).mul_const (u : ℂ)).fun_neg.sub_const ((u : ℂ) ^ 2 / 2)
  convert h1.cexp using 1
  ring

/-- The bound `‖−u e^{−zu−u²/2}‖ ≤ e^{c²} |u e^{−u²/4}|` for `|Re z| ≤ c`. -/
private theorem norm_mul_exp_le_mc {z : ℂ} {c : ℝ} (hc : |z.re| ≤ c) (u : ℝ) :
    ‖-(u : ℂ) * Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2)‖
      ≤ Real.exp (c ^ 2) * |u * Real.exp (-(1 / 4) * u ^ 2)| := by
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc |u| * ‖Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2)‖
      ≤ |u| * (Real.exp (c ^ 2) * Real.exp (-(1 / 4) * u ^ 2)) :=
        mul_le_mul_of_nonneg_left (norm_exp_le_mc hc u) (abs_nonneg u)
    _ = Real.exp (c ^ 2) * (|u| * Real.exp (-(1 / 4) * u ^ 2)) := by ring

/-- `u ↦ −u e^{−zu−u²/2}` is integrable on `(0, ∞)`. -/
private theorem integrableOn_neg_mul_mc (z : ℂ) :
    IntegrableOn (fun u : ℝ => -(u : ℂ) * Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2))
      (Set.Ioi 0) := by
  have hg := ((integrable_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num)).abs.const_mul
    (Real.exp (|z.re| ^ 2))).integrableOn (s := Set.Ioi 0)
  exact hg.mono' (by fun_prop : Continuous _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => norm_mul_exp_le_mc le_rfl u)

/-- `u ↦ (−z − u) e^{−zu−u²/2}` is integrable on `(0, ∞)`. -/
private theorem integrableOn_sub_mul_mc (z : ℂ) :
    IntegrableOn
      (fun u : ℝ => (-z - (u : ℂ)) * Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2))
      (Set.Ioi 0) := by
  have h := ((integrableOn_millsRatioC z).const_mul (-z)).add (integrableOn_neg_mul_mc z)
  refine IntegrableOn.congr_fun h (fun u _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  ring

open Filter Topology in
/-- `∫_0^∞ (−z − u) e^{−zu−u²/2} du = −1`: the integrand is the derivative of `e^{−zu−u²/2}`,
which is `1` at `u = 0` and tends to `0` at `+∞`. -/
private theorem integral_deriv_mc (z : ℂ) :
    ∫ u in Set.Ioi (0 : ℝ), (-z - (u : ℂ)) * Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2)
      = -1 := by
  have hd : ∀ u ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun v : ℝ => Complex.exp (-(z * (v : ℂ)) - (v : ℂ) ^ 2 / 2))
        ((-z - (u : ℂ)) * Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2)) u := by
    intro u _
    have h1 : HasDerivAt (fun w : ℂ => -(z * w) - w ^ 2 / 2) (-z - (u : ℂ)) (u : ℂ) := by
      have h := ((hasDerivAt_id' (u : ℂ)).const_mul z).fun_neg.fun_sub
        ((hasDerivAt_pow 2 (u : ℂ)).div_const 2)
      convert h using 1
      push_cast
      ring
    convert h1.comp_ofReal.cexp using 1
    ring
  have h0 : Tendsto (fun v : ℝ => Real.exp (|z.re| ^ 2) * Real.exp (-(1 / 4) * v ^ 2)) atTop
      (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp ((tendsto_pow_atTop (α := ℝ) two_ne_zero
      ).const_mul_atTop_of_neg (by norm_num : -(1 / 4 : ℝ) < 0))).const_mul (Real.exp (|z.re| ^ 2))
    rw [mul_zero] at h
    exact h
  have hlim : Tendsto (fun v : ℝ => Complex.exp (-(z * (v : ℂ)) - (v : ℂ) ^ 2 / 2)) atTop
      (𝓝 0) := squeeze_zero_norm (fun v => norm_exp_le_mc le_rfl v) h0
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_sub_mul_mc z) hlim]
  simp

/-- **The Mills ratio is entire, with `mr'(z) = z mr(z) − 1`.** (The derivative under the integral
is `∫_0^∞ −u e^{−zu−u²/2} du`, and `∫_0^∞ (z + u) e^{−zu−u²/2} du = 1`.) -/
theorem hasDerivAt_millsRatioC (z : ℂ) : HasDerivAt millsRatioC (z * millsRatioC z - 1) z := by
  -- on the ball of radius `1` around `z`, `|Re w| ≤ |Re z| + 1`
  have hball : ∀ w ∈ Metric.ball z 1, |w.re| ≤ |z.re| + 1 := by
    intro w hw
    have h1 : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm _
    have h2 : ‖w - z‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have h3 := abs_sub_abs_le_abs_sub w.re z.re
    rw [Complex.sub_re] at h1
    linarith
  -- differentiation under the integral, dominated by `e^{(|Re z| + 1)²} |u e^{−u²/4}|`
  have hF_meas : ∀ᶠ w in nhds z, AEStronglyMeasurable
      (fun u : ℝ => Complex.exp (-(w * (u : ℂ)) - (u : ℂ) ^ 2 / 2))
      (volume.restrict (Set.Ioi 0)) :=
    Filter.Eventually.of_forall fun w => (by fun_prop : Continuous _).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ => -(u : ℂ) * Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2))
      (volume.restrict (Set.Ioi 0)) :=
    (by fun_prop : Continuous _).aestronglyMeasurable
  have h_bound : ∀ᵐ (u : ℝ) ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ w ∈ Metric.ball z 1,
      ‖-(u : ℂ) * Complex.exp (-(w * (u : ℂ)) - (u : ℂ) ^ 2 / 2)‖
        ≤ Real.exp ((|z.re| + 1) ^ 2) * |u * Real.exp (-(1 / 4) * u ^ 2)| :=
    Filter.Eventually.of_forall fun u w hw => norm_mul_exp_le_mc (hball w hw) u
  have h_int : Integrable (fun u : ℝ => Real.exp ((|z.re| + 1) ^ 2) *
      |u * Real.exp (-(1 / 4) * u ^ 2)|) (volume.restrict (Set.Ioi 0)) :=
    ((integrable_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num)).abs.const_mul _).integrableOn
  have h_diff : ∀ᵐ (u : ℝ) ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ w ∈ Metric.ball z 1,
      HasDerivAt (fun w : ℂ => Complex.exp (-(w * (u : ℂ)) - (u : ℂ) ^ 2 / 2))
        (-(u : ℂ) * Complex.exp (-(w * (u : ℂ)) - (u : ℂ) ^ 2 / 2)) w :=
    Filter.Eventually.of_forall fun u w _ => hasDerivAt_integrand_mc u w
  have key : HasDerivAt millsRatioC
      (∫ u in Set.Ioi (0 : ℝ), -(u : ℂ) * Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2)) z :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z one_pos) hF_meas
      (integrableOn_millsRatioC z) hF'_meas h_bound h_int h_diff).2
  -- the value: `∫ −u e = ∫ (−z − u) e + z ∫ e = −1 + z mr(z)`
  convert key using 1
  have hsplit : (fun u : ℝ => -(u : ℂ) * Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2))
      = fun u : ℝ => (-z - (u : ℂ)) * Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2)
        + z * Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2) := by
    funext u
    ring
  rw [hsplit, integral_add (integrableOn_sub_mul_mc z) ((integrableOn_millsRatioC z).const_mul z),
    integral_deriv_mc, integral_const_mul, millsRatioC]
  ring

open Filter Topology in
/-- `∫_0^∞ φ(x + u) du = 1 − Φ(x)`, by the fundamental theorem of calculus on `(0, ∞)` for
`u ↦ Φ(x + u)`, which tends to `1` at `+∞`. -/
private theorem integral_gaussPdf_add_mc (x : ℝ) :
    ∫ u in Set.Ioi (0 : ℝ), gaussPdf (x + u) = 1 - gaussCdf x := by
  have hd : ∀ u ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun v => gaussCdf (x + v)) (gaussPdf (x + u)) u := by
    intro u _
    have h := (hasDerivAt_gaussCdf (x + u)).comp u ((hasDerivAt_id' u).const_add x)
    rwa [mul_one] at h
  have hint : IntegrableOn (fun u => gaussPdf (x + u)) (Set.Ioi 0) :=
    (integrable_gaussPdf.comp_add_left x).integrableOn
  have hlim : Tendsto (fun v => gaussCdf (x + v)) atTop (𝓝 1) :=
    tendsto_gaussCdf_atTop.comp (tendsto_atTop_add_const_left _ x tendsto_id)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim, add_zero]

/-- `φ(x + u) = φ(x) e^{−xu−u²/2}`. -/
private theorem gaussPdf_add_mc (x u : ℝ) :
    gaussPdf (x + u) = gaussPdf x * Real.exp (-(x * u) - u ^ 2 / 2) := by
  rw [gaussPdf, gaussPdf, div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  ring

/-- **"for real `z`, `mr(z) = e^{z²/2} ∫_z^∞ e^{−y²/2} dy`, and the substitution `y = z + u` gives
`mr(z) = ∫_0^∞ e^{−zu−u²/2} du`":** on the real line the Mills ratio defined by the integral is
the real Mills ratio `(1 − Φ(x))/φ(x)`. -/
theorem millsRatioC_ofReal (x : ℝ) : millsRatioC (x : ℂ) = ((millsRatio x : ℝ) : ℂ) := by
  -- at a real `x` the integrand is real
  have h1 : millsRatioC (x : ℂ)
      = ((∫ u in Set.Ioi (0 : ℝ), Real.exp (-(x * u) - u ^ 2 / 2) : ℝ) : ℂ) := by
    rw [millsRatioC, ← integral_complex_ofReal]
    congr 1
    funext u
    push_cast
    rfl
  -- the substitution `y = x + u`: `φ(x) ∫_0^∞ e^{−xu−u²/2} du = ∫_0^∞ φ(x + u) du = 1 − Φ(x)`
  have h2 : gaussPdf x * ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(x * u) - u ^ 2 / 2)
      = 1 - gaussCdf x := by
    rw [← integral_const_mul, ← integral_gaussPdf_add_mc]
    simp_rw [gaussPdf_add_mc]
  rw [h1, millsRatio, ← h2, mul_div_cancel_left₀ _ (gaussPdf_pos x).ne']

/-- On the real line `geluC` is GELU. -/
theorem geluC_ofReal (x : ℝ) : geluC (x : ℂ) = ((gelu x : ℝ) : ℂ) := by
  rw [geluC, gaussPdfC_ofReal, millsRatioC_ofReal, gelu_eq_sub_millsRatio]
  push_cast
  ring

/-- `φ'(z) = −z φ(z)`. -/
private theorem hasDerivAt_gaussPdfC_mc (z : ℂ) : HasDerivAt gaussPdfC (-z * gaussPdfC z) z := by
  have h1 : HasDerivAt (fun w : ℂ => -w ^ 2 / 2) (-z) z := by
    convert ((hasDerivAt_pow 2 z).fun_neg).div_const 2 using 1
    push_cast
    ring
  have e : -z * gaussPdfC z
      = Complex.exp (-z ^ 2 / 2) * -z / ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) := by
    rw [gaussPdfC]
    ring
  rw [e]
  exact h1.cexp.div_const ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)

/-- **Lemma D.8 (i), second formula, at every complex `z`:** `σ'(z) = 1 − φ(z) (mr(z) − z)`. -/
theorem hasDerivAt_geluC (z : ℂ) :
    HasDerivAt geluC (1 - gaussPdfC z * (millsRatioC z - z)) z := by
  -- product rule for `z − φ(z) z mr(z)`, with `φ' = −z φ` and `mr' = z mr − 1`
  have h := (hasDerivAt_id' z).fun_sub (((hasDerivAt_gaussPdfC_mc z).fun_mul
    (hasDerivAt_id' z)).fun_mul (hasDerivAt_millsRatioC z))
  show HasDerivAt (fun w => w - gaussPdfC w * w * millsRatioC w) _ z
  convert h using 1
  ring

/-- "GELU […] is entire." -/
theorem differentiable_geluC : Differentiable ℂ geluC := by
  exact fun z => (hasDerivAt_geluC z).differentiableAt

/-- GELU is holomorphic at every complex `z`. -/
theorem analyticAt_geluC (z : ℂ) : AnalyticAt ℂ geluC z := by
  exact differentiable_geluC.analyticAt z

/-- The gap `δ(z) = z − σ(z) = φ(z) z mr(z)` of GELU (Lemma D.8 (i), first formula). -/
theorem sub_geluC (z : ℂ) : z - geluC z = gaussPdfC z * z * millsRatioC z := by
  rw [geluC]
  ring

/-- The gap `δ'(z) = 1 − σ'(z) = φ(z) (mr(z) − z)` of the derivative of GELU (Lemma D.8 (i),
second formula). -/
theorem one_sub_deriv_geluC (z : ℂ) :
    1 - deriv geluC z = gaussPdfC z * (millsRatioC z - z) := by
  rw [(hasDerivAt_geluC z).deriv]
  ring

/-- On the real line the complex derivative of `geluC` is the derivative of GELU. -/
theorem deriv_geluC_ofReal (x : ℝ) : deriv geluC (x : ℂ) = ((geluDeriv x : ℝ) : ℂ) := by
  rw [(hasDerivAt_geluC x).deriv, gaussPdfC_ofReal, millsRatioC_ofReal,
    geluDeriv_eq_sub_millsRatio]
  push_cast
  ring

end Skips
