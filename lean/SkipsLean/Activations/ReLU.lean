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
  rcases hz.lt_or_gt with hneg | hpos
  · -- near `z < 0`, `relu` is the constant `0`
    have hd : reluDeriv z = 0 := by simp only [reluDeriv, not_lt.2 hneg.le, ite_false]
    rw [hd]
    refine (hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_lt_nhds hneg] with y hy
    exact max_eq_right hy.le
  · -- near `z > 0`, `relu` is the identity
    have hd : reluDeriv z = 1 := by simp only [reluDeriv, hpos, ite_true]
    rw [hd]
    refine (hasDerivAt_id z).congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds hpos] with y hy
    exact max_eq_left hy.le

/-- ReLU² is differentiable everywhere, with derivative `2 max(z, 0)`. -/
theorem hasDerivAt_reluSq (z : ℝ) : HasDerivAt reluSq (reluSqDeriv z) z := by
  rcases lt_trichotomy z 0 with hneg | rfl | hpos
  · -- near `z < 0`, `reluSq` is the constant `0`
    have hd : reluSqDeriv z = 0 := by rw [reluSqDeriv, max_eq_right hneg.le, mul_zero]
    rw [hd]
    refine (hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_lt_nhds hneg] with y hy
    show max y 0 ^ 2 = 0
    rw [max_eq_right hy.le]; norm_num
  · -- at `0`: `0 ≤ reluSq h ≤ h²`, which is `o(h)`
    have hd : reluSqDeriv 0 = 0 := by rw [reluSqDeriv, max_self, mul_zero]
    rw [hd, hasDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_pow_id one_lt_two)
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun h => ?_)
    have h0 : reluSq 0 = 0 := by rw [reluSq, max_self]; norm_num
    rw [h0, zero_add, smul_zero, sub_zero, sub_zero, reluSq, one_mul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    rcases le_total 0 h with h1 | h1
    · rw [max_eq_left h1]
    · rw [max_eq_right h1]; exact (zero_pow two_ne_zero).trans_le (sq_nonneg h)
  · -- near `z > 0`, `reluSq` is the square
    refine ((hasDerivAt_pow 2 z).congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [eventually_gt_nhds hpos] with y hy
      show max y 0 ^ 2 = y ^ 2
      rw [max_eq_left hy.le]
    · rw [reluSqDeriv, max_eq_left hpos.le]; norm_num

end Skips
