import SkipsLean.Activations.Gaussian
import SkipsLean.OneBlock.UnitsSwiGLU
import SkipsLean.Network.Analytic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv

/-!
# GELU, SiLU and the gated blocks are real-analytic

Papers: Section 1.1 (Results) of the dimension paper says of the tanh, GELU, SwiGLU and GeGLU
blocks: "These four kinds of block are real-analytic"; Appendix D uses that the network after a hidden state is real-analytic in the
hidden state and in the weights (cases (n) and (+)), and Appendix D.7 that the outputs on a batch
are real-analytic in the weights.

Stated here: the standard normal distribution function `Φ` is real-analytic, hence GELU
(`z Φ(z)`); SiLU (`z / (1 + e^{-z})`) is real-analytic; and the map of a gated block,
`(z, w) ↦ σ(z_i) w_i`, is real-analytic if its gate `σ` is.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

/-- The standard normal density is real-analytic. -/
theorem analyticOnNhd_gaussPdf : AnalyticOnNhd ℝ gaussPdf Set.univ := by
  -- `exp` of a polynomial, divided by the constant `√(2π) ≠ 0`
  have h : AnalyticOnNhd ℝ (fun z : ℝ => -z ^ 2 / 2) Set.univ :=
    ((analyticOnNhd_id.pow 2).neg).div analyticOnNhd_const fun _ _ => two_ne_zero
  exact h.rexp.div analyticOnNhd_const fun _ _ => (Real.sqrt_pos.2 (by positivity)).ne'

/-- The complex standard normal density `w ↦ e^{-w²/2} / √(2π)`, an entire function. -/
private noncomputable def cGaussPdf (w : ℂ) : ℂ :=
  Complex.exp (-w ^ 2 / 2) / (Real.sqrt (2 * Real.pi) : ℂ)

private theorem differentiable_cGaussPdf : Differentiable ℂ cGaussPdf := by
  unfold cGaussPdf
  fun_prop

/-- On the real line, `cGaussPdf` is the real density `φ`. -/
private theorem cGaussPdf_ofReal (x : ℝ) : cGaussPdf x = (gaussPdf x : ℂ) := by
  simp only [cGaussPdf, gaussPdf, Complex.ofReal_div, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_pow, Complex.ofReal_ofNat]

/-- The standard normal distribution function `Φ(z) = 1/2 + ∫_0^z φ` is real-analytic. -/
theorem analyticOnNhd_gaussCdf : AnalyticOnNhd ℝ gaussCdf Set.univ := by
  -- the entire function `e^{-w²/2}/√(2π)` has an entire primitive `G` (Morera on `ℂ`)
  obtain ⟨G, hG⟩ := differentiable_cGaussPdf.isExactOn_univ
  have hGd : Differentiable ℂ G := fun w => (hG w (Set.mem_univ w)).differentiableAt
  -- `g x = Re G(x)` is real-analytic on `ℝ`: `G` is complex-analytic, restrict the scalars
  set g : ℝ → ℝ := fun x => (G x).re
  have hg : AnalyticOnNhd ℝ g Set.univ := by
    intro x _
    have h1 : AnalyticAt ℝ G (x : ℂ) := (hGd.analyticAt (x : ℂ)).restrictScalars
    have h2 : AnalyticAt ℝ (fun y : ℝ => G (Complex.ofRealCLM y)) x :=
      h1.comp (Complex.ofRealCLM.analyticAt x)
    exact Complex.reCLM.analyticAt _ |>.comp h2
  -- `g' = φ = Φ'`, so `Φ - g` is constant
  have hgd : ∀ x, HasDerivAt g (gaussPdf x) x := by
    intro x
    have h := (hG x (Set.mem_univ _)).real_of_complex
    rwa [cGaussPdf_ofReal, Complex.ofReal_re] at h
  have hc : ∀ x, gaussCdf x = g x + (gaussCdf 0 - g 0) := by
    have hd : ∀ x, HasDerivAt (fun y => gaussCdf y - g y) 0 x := fun x => by
      have h := (hasDerivAt_gaussCdf x).sub (hgd x)
      rw [sub_self] at h
      exact h
    intro x
    have := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt)
      (fun y => (hd y).deriv) x 0
    linarith
  -- hence `Φ = g + const` is real-analytic
  have heq : gaussCdf = fun x => g x + (gaussCdf 0 - g 0) := funext hc
  rw [heq]
  exact hg.add analyticOnNhd_const

/-- GELU, `z ↦ z Φ(z)`, is real-analytic. -/
theorem analyticOnNhd_gelu : AnalyticOnNhd ℝ gelu Set.univ := by
  -- the product of the identity and `Φ`
  have h : gelu = fun z => z * gaussCdf z := rfl
  rw [h]
  exact analyticOnNhd_id.mul analyticOnNhd_gaussCdf

/-- SiLU, `z ↦ z / (1 + e^{-z})`, is real-analytic. -/
theorem analyticOnNhd_silu : AnalyticOnNhd ℝ silu Set.univ := by
  -- a quotient of analytic functions with the denominator `1 + e^{-z} > 0`
  have h : silu = fun z => z / (1 + Real.exp (-z)) := rfl
  rw [h]
  exact analyticOnNhd_id.div (analyticOnNhd_const.add analyticOnNhd_id.neg.rexp)
    fun z _ => by positivity

variable {T d : Type*} {L : ℕ} [Fintype T] {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ}
  {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- The map of a gated block is real-analytic if its gate is. -/
theorem analyticOnNhd_f_gated (hσ : AnalyticOnNhd ℝ σ Set.univ) (ℓ : Fin L) :
    AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) σ χ hid).f ℓ) Set.univ := by
  -- entrywise: `σ` of one entry times another entry
  show AnalyticOnNhd ℝ (fun M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ => fun t => fun i =>
    σ (M t (Sum.inl i)) * M t (Sum.inr i)) Set.univ
  exact AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun i =>
    (hσ.comp (analyticOnNhd_matrix_entry t (Sum.inl i)) (Set.mapsTo_univ _ _)).mul
      (analyticOnNhd_matrix_entry t (Sum.inr i))

end Skips
