import SkipsLean.Activations.Gaussian
import SkipsLean.OneBlock.UnitsSwiGLU
import SkipsLean.Network.Analytic

/-!
# GELU, SiLU and the gated blocks are real-analytic

Papers: Section 2 (Setup) of the dimension paper names the tanh, GELU, SwiGLU and GeGLU blocks
"analytic blocks"; Appendix D uses that the network after a hidden state is real-analytic in the
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
  sorry

/-- The standard normal distribution function `Φ(z) = 1/2 + ∫_0^z φ` is real-analytic. -/
theorem analyticOnNhd_gaussCdf : AnalyticOnNhd ℝ gaussCdf Set.univ := by
  sorry

/-- GELU, `z ↦ z Φ(z)`, is real-analytic. -/
theorem analyticOnNhd_gelu : AnalyticOnNhd ℝ gelu Set.univ := by
  sorry

/-- SiLU, `z ↦ z / (1 + e^{-z})`, is real-analytic. -/
theorem analyticOnNhd_silu : AnalyticOnNhd ℝ silu Set.univ := by
  sorry

variable {T d : Type*} {L : ℕ} [Fintype T] {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ}
  {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- The map of a gated block is real-analytic if its gate is. -/
theorem analyticOnNhd_f_gated (hσ : AnalyticOnNhd ℝ σ Set.univ) (ℓ : Fin L) :
    AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) σ χ hid).f ℓ) Set.univ := by
  sorry

end Skips
