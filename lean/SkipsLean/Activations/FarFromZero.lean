import SkipsLean.Activations.GeluExpansion
import SkipsLean.OneBlock.UnitsSwiGLU

/-!
# GELU and SiLU far from zero: the small term `δ`

Paper (dimension): Appendix D.5, "GELU and the Mills ratio" and "A gate on a ray".

* The Mills ratio `mr(z) = √(π/2) e^{z²/2} (1 − erf(z/√2))`, which for real `z` is
  `(1 − Φ(z)) / φ(z)`.
* Lemma D.8, for real `z`: "(i) For all `z`: `σ(z) = z − φ(z) z mr(z)` and
  `σ'(z) = 1 − φ(z) (mr(z) − z)`. (ii) For `Re z > 0` and every integer `m ≥ 0`, with `(−1)!! = 1`,
  `|mr(z) − ∑_{l=0}^{m−1} (−1)^l (2l−1)!! / z^{2l+1}| ≤ (2m−1)!! / (Re z)^{2m+1}`." Here `σ` is
  GELU. The paper states the lemma for complex `z`; the cases (n) and (+) use real `z` only.
* "A gate on a ray": "GELU and SiLU both satisfy `σ(z) − σ(−z) = z`, and so `σ'(z) + σ'(−z) = 1`.
  Let `δ(y) = y − σ(y)`, with the derivative `δ'(y) = 1 − σ'(y)`. For every real number `y > 0`,
  `σ(y) = y − δ(y)`, `σ(−y) = −δ(y)`, `σ'(y) = 1 − δ'(y)`, `σ'(−y) = δ'(y)` (24). By Lemma D.8 (i),
  for GELU `δ(y) = φ(y) y mr(y)` and `δ'(y) = φ(y) (mr(y) − y)`, and for SiLU
  `δ(y) = y / (1 + e^y)`, `δ'(y) = (1 + e^y − y e^y) / (1 + e^y)²`. Let `p = 2` for GELU and
  `p = 1` for SiLU. For every real number `y ≥ 2`,
  `(1/6) e^{−y^p/p} ≤ δ(y) ≤ y e^{−y^p/p}`, `|δ'(y)| ≤ 4 y δ(y)` (25). For GELU, Lemma D.8 (ii)
  gives `mr(y) ≤ 1/y` and `|mr(y) − 1/y| ≤ 1/y³`, so `3/4 ≤ y mr(y) ≤ 1` and `|mr(y) − y| ≤ 2y`.
  For SiLU, `(1/2) y e^{−y} ≤ δ(y) ≤ y e^{−y}` and `|δ'(y)| ≤ (2 + y) e^{−y}`."

In Lean `δ` is written out as `y - gelu y` and `y - silu y`, and `δ'` as `1 - geluDeriv y` and
`1 - siluDeriv y` (`hasDerivAt_gelu`, `hasDerivAt_silu` say that these are the derivatives). The
double factorial `(2l − 1)!!` is `(2 * l - 1)‼` with the subtraction of natural numbers, so that
`l = 0` gives `0‼ = 1`, the paper's `(−1)!! = 1`.
-/

namespace Skips

open scoped Nat

/-- The Mills ratio of the standard normal distribution, for real `z`:
`mr(z) = (1 − Φ(z)) / φ(z)`. -/
noncomputable def millsRatio (z : ℝ) : ℝ := (1 - gaussCdf z) / gaussPdf z

/-! ### Lemma D.8, for real `z` -/

/-- **Lemma D.8 (i), first formula:** `GELU(z) = z − φ(z) z mr(z)`. -/
theorem gelu_eq_sub_millsRatio (z : ℝ) : gelu z = z - gaussPdf z * z * millsRatio z := by
  sorry

/-- **Lemma D.8 (i), second formula:** `GELU'(z) = 1 − φ(z) (mr(z) − z)`. -/
theorem geluDeriv_eq_sub_millsRatio (z : ℝ) :
    geluDeriv z = 1 - gaussPdf z * (millsRatio z - z) := by
  sorry

/-- **Lemma D.8 (ii), for real `z > 0`:** the partial sums of
`∑_l (−1)^l (2l−1)!! / z^{2l+1}` approximate the Mills ratio with an error of at most the first
omitted term. -/
theorem abs_millsRatio_sub_sum_le {z : ℝ} (hz : 0 < z) (m : ℕ) :
    |millsRatio z - ∑ l ∈ Finset.range m, (-1 : ℝ) ^ l * ((2 * l - 1)‼ : ℝ) / z ^ (2 * l + 1)|
      ≤ ((2 * m - 1)‼ : ℝ) / z ^ (2 * m + 1) := by
  sorry

/-- `0 < mr(y) ≤ 1/y` for `y > 0` (Lemma D.8 (ii) with `m = 0`). -/
theorem millsRatio_pos_le {y : ℝ} (hy : 0 < y) : 0 < millsRatio y ∧ millsRatio y ≤ 1 / y := by
  sorry

/-- `|mr(y) − 1/y| ≤ 1/y³` for `y > 0` (Lemma D.8 (ii) with `m = 1`). -/
theorem abs_millsRatio_sub_inv_le {y : ℝ} (hy : 0 < y) : |millsRatio y - 1 / y| ≤ 1 / y ^ 3 := by
  sorry

/-- `3/4 ≤ y mr(y) ≤ 1` and `|mr(y) − y| ≤ 2y` for `y ≥ 2`. -/
theorem mul_millsRatio_bounds {y : ℝ} (hy : 2 ≤ y) :
    3 / 4 ≤ y * millsRatio y ∧ y * millsRatio y ≤ 1 ∧ |millsRatio y - y| ≤ 2 * y := by
  sorry

/-! ### Equation (24) -/

/-- (24) for GELU: `σ(−y) = −δ(y)` and `σ'(−y) = δ'(y)`. -/
theorem gelu_neg_eq (y : ℝ) :
    gelu (-y) = -(y - gelu y) ∧ geluDeriv (-y) = 1 - geluDeriv y := by
  sorry

/-- (24) for SiLU: `σ(−y) = −δ(y)` and `σ'(−y) = δ'(y)`. -/
theorem silu_neg_eq (y : ℝ) :
    silu (-y) = -(y - silu y) ∧ siluDeriv (-y) = 1 - siluDeriv y := by
  sorry

/-! ### The small terms `δ` and `δ'` -/

/-- For GELU, `δ(y) = φ(y) y mr(y)` and `δ'(y) = φ(y) (mr(y) − y)`. -/
theorem gelu_gap_eq (y : ℝ) :
    y - gelu y = gaussPdf y * y * millsRatio y ∧
      1 - geluDeriv y = gaussPdf y * (millsRatio y - y) := by
  sorry

/-- For SiLU, `δ(y) = y / (1 + e^y)` and `δ'(y) = (1 + e^y − y e^y) / (1 + e^y)²`. -/
theorem silu_gap_eq (y : ℝ) :
    y - silu y = y / (1 + Real.exp y) ∧
      1 - siluDeriv y = (1 + Real.exp y - y * Real.exp y) / (1 + Real.exp y) ^ 2 := by
  sorry

/-- **Equation (25) for GELU** (`p = 2`): for `y ≥ 2`,
`(1/6) e^{−y²/2} ≤ δ(y) ≤ y e^{−y²/2}` and `|δ'(y)| ≤ 4 y δ(y)`. -/
theorem gelu_gap_bounds {y : ℝ} (hy : 2 ≤ y) :
    1 / 6 * Real.exp (-y ^ 2 / 2) ≤ y - gelu y ∧ y - gelu y ≤ y * Real.exp (-y ^ 2 / 2) ∧
      |1 - geluDeriv y| ≤ 4 * y * (y - gelu y) := by
  sorry

/-- **Equation (25) for SiLU** (`p = 1`): for `y ≥ 2`,
`(1/6) e^{−y} ≤ δ(y) ≤ y e^{−y}` and `|δ'(y)| ≤ 4 y δ(y)`. -/
theorem silu_gap_bounds {y : ℝ} (hy : 2 ≤ y) :
    1 / 6 * Real.exp (-y) ≤ y - silu y ∧ y - silu y ≤ y * Real.exp (-y) ∧
      |1 - siluDeriv y| ≤ 4 * y * (y - silu y) := by
  sorry

/-- For SiLU and `y ≥ 2`: `(1/2) y e^{−y} ≤ δ(y)` and `|δ'(y)| ≤ (2 + y) e^{−y}`. -/
theorem silu_gap_bounds' {y : ℝ} (hy : 2 ≤ y) :
    1 / 2 * y * Real.exp (-y) ≤ y - silu y ∧ |1 - siluDeriv y| ≤ (2 + y) * Real.exp (-y) := by
  sorry

end Skips
