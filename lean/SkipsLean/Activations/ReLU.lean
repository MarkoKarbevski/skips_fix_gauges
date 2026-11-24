import Mathlib

/-!
# ReLU and its square

Papers: the activations `ReLU(z) = max(z, 0)` and `ReLU²(z) = max(z, 0)²` of the ReLU, ReGLU and
ReLU² blocks (dimension paper, Section 2, "Blocks", and Appendix C). ReLU has a kink at `0`: it is
differentiable at every `z ≠ 0`, with derivative `1[z > 0]`. ReLU² is differentiable everywhere,
with derivative `2 max(z, 0)`.
-/

namespace Skips

/-- ReLU: `σ(z) = max(z, 0)`. -/
noncomputable def relu (z : ℝ) : ℝ := max z 0

/-- The derivative of ReLU away from its kink: `1[z > 0]`. -/
noncomputable def reluDeriv (z : ℝ) : ℝ := if 0 < z then 1 else 0

/-- The square of ReLU: `σ(z) = max(z, 0)²`. -/
noncomputable def reluSq (z : ℝ) : ℝ := (max z 0) ^ 2

/-- The derivative of ReLU²: `2 max(z, 0)`. -/
noncomputable def reluSqDeriv (z : ℝ) : ℝ := 2 * max z 0

/-- ReLU is differentiable away from `0`, with derivative `1[z > 0]`. -/
theorem hasDerivAt_relu {z : ℝ} (hz : z ≠ 0) : HasDerivAt relu (reluDeriv z) z := by
  sorry

/-- ReLU² is differentiable everywhere, with derivative `2 max(z, 0)`. -/
theorem hasDerivAt_reluSq (z : ℝ) : HasDerivAt reluSq (reluSqDeriv z) z := by
  sorry

end Skips
