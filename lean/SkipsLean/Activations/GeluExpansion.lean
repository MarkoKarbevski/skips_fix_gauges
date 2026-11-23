import SkipsLean.Activations.Gaussian

/-!
# GELU far from the origin

Paper (dimension paper): proof of Lemma C.3 for GELU, and Lemma D.8. With `σ(z) = z Φ(z)`, the
bounds `φ(z) (1/z - 1/z³) ≤ 1 - Φ(z) ≤ φ(z)/z` on the tail give, as `|z| → ∞` on either side,

  `σ(z) = max(z, 0) - φ(z) + O(φ(z)/z²)`,
  `σ'(z) = 1[z > 0] + φ(z) (z - 1/z) + O(φ(z)/|z|³)`.

The four statements below are these expansions with explicit two-sided bounds on the remainders.
-/

namespace Skips

/-- For `z > 0`: `0 ≤ σ(z) - z + φ(z) ≤ φ(z)/z²`. -/
theorem gelu_expansion_pos {z : ℝ} (hz : 0 < z) :
    0 ≤ gelu z - z + gaussPdf z ∧ gelu z - z + gaussPdf z ≤ gaussPdf z / z ^ 2 := by
  have h1 := le_one_sub_gaussCdf hz
  have h2 := one_sub_gaussCdf_le hz
  -- `z (1 - Φ(z))` lies between `φ(z) (1 - 1/z²)` and `φ(z)`
  have h3 : z * (1 - gaussCdf z) ≤ gaussPdf z := by
    have := mul_le_mul_of_nonneg_left h2 hz.le
    rwa [mul_div_cancel₀ _ hz.ne'] at this
  have h4 : gaussPdf z - gaussPdf z / z ^ 2 ≤ z * (1 - gaussCdf z) := by
    have := mul_le_mul_of_nonneg_left h1 hz.le
    have e : z * (gaussPdf z * (1 / z - 1 / z ^ 3)) = gaussPdf z - gaussPdf z / z ^ 2 := by
      field_simp
    rwa [e] at this
  have e : gelu z = z - z * (1 - gaussCdf z) := by unfold gelu; ring
  rw [e]
  constructor <;> linarith

/-- For `z < 0`: `0 ≤ σ(z) + φ(z) ≤ φ(z)/z²`. -/
theorem gelu_expansion_neg {z : ℝ} (hz : z < 0) :
    0 ≤ gelu z + gaussPdf z ∧ gelu z + gaussPdf z ≤ gaussPdf z / z ^ 2 := by
  have h := gelu_expansion_pos (neg_pos.2 hz)
  -- `σ(z) = σ(-z) + z` and `φ(-z) = φ(z)`
  have e : gelu (-z) = gelu z - z := by
    have := gelu_sub_gelu_neg z
    linarith
  rw [e, gaussPdf_neg, neg_sq] at h
  constructor <;> [linarith [h.1]; linarith [h.2]]

/-- For `z > 0`: `0 ≤ σ'(z) - 1 - φ(z) (z - 1/z) ≤ φ(z)/z³`. -/
theorem geluDeriv_expansion_pos {z : ℝ} (hz : 0 < z) :
    0 ≤ geluDeriv z - 1 - gaussPdf z * (z - 1 / z) ∧
      geluDeriv z - 1 - gaussPdf z * (z - 1 / z) ≤ gaussPdf z / z ^ 3 := by
  have h1 := le_one_sub_gaussCdf hz
  have h2 := one_sub_gaussCdf_le hz
  have e : geluDeriv z - 1 - gaussPdf z * (z - 1 / z)
      = gaussPdf z / z - (1 - gaussCdf z) := by
    unfold geluDeriv; ring
  have e' : gaussPdf z * (1 / z - 1 / z ^ 3) = gaussPdf z / z - gaussPdf z / z ^ 3 := by ring
  rw [e]
  rw [e'] at h1
  constructor <;> linarith

/-- For `z < 0`: `φ(z)/z³ ≤ σ'(z) - φ(z) (z - 1/z) ≤ 0` (here `z³ < 0`). -/
theorem geluDeriv_expansion_neg {z : ℝ} (hz : z < 0) :
    gaussPdf z / z ^ 3 ≤ geluDeriv z - gaussPdf z * (z - 1 / z) ∧
      geluDeriv z - gaussPdf z * (z - 1 / z) ≤ 0 := by
  have hz' : 0 < -z := neg_pos.2 hz
  have h1 := le_one_sub_gaussCdf hz'
  have h2 := one_sub_gaussCdf_le hz'
  -- `Φ(z) = 1 - Φ(-z)` and `φ(-z) = φ(z)`
  have hΦ : 1 - gaussCdf (-z) = gaussCdf z := by rw [gaussCdf_neg]; ring
  rw [hΦ, gaussPdf_neg] at h1 h2
  have e : geluDeriv z - gaussPdf z * (z - 1 / z) = gaussCdf z + gaussPdf z / z := by
    unfold geluDeriv; ring
  have e1 : gaussPdf z * (1 / -z - 1 / (-z) ^ 3) = -(gaussPdf z / z) + gaussPdf z / z ^ 3 := by
    have : (-z) ^ 3 = -z ^ 3 := by ring
    rw [this]
    field_simp
    ring
  have e2 : gaussPdf z / -z = -(gaussPdf z / z) := by rw [div_neg]
  rw [e]
  rw [e1] at h1
  rw [e2] at h2
  constructor <;> linarith

end Skips
