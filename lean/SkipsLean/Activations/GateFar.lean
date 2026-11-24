import SkipsLean.Activations.FarFromZero
import SkipsLean.Activations.Analytic

/-!
# A gate far from zero: what the proofs on rays use of GELU and SiLU

Paper (dimension): Appendix D.5, "A gate on a ray", equations (24) and (25), and the proof of
Lemma D.12, "One small factor".

The proofs on rays use the gate `σ` of a gated block (GELU for GeGLU, SiLU for SwiGLU) only through
a few properties, with `δ(y) = y − σ(y)`, `δ'(y) = 1 − σ'(y)` and `p = 2` for GELU, `p = 1` for
SiLU:

* `σ` is real-analytic with the derivative `σ'`;
* (24): `σ(−y) = −δ(y)` and `σ'(−y) = δ'(y)`;
* (25): for `y ≥ 2`, `e^{−y^p/p}/6 ≤ δ(y) ≤ y e^{−y^p/p}` and `|δ'(y)| ≤ 4 y δ(y)`;
* `y |δ'(y)| / δ(y) → ∞` as `y → ∞`. (For GELU, `δ'(y)/δ(y) = (mr(y) − y)/(y mr(y))` and
  `y mr(y) ≤ 1`; for SiLU, `y δ'(y)/δ(y) = 1 − y + δ(y)`: both are in "One small factor".)

`GateFar σ σ' p` collects them, so that the statements on rays are written once for both gates. It
is not a notion of the paper.
-/

namespace Skips

open Filter Topology

/-- What the proofs on rays use of a gate `σ` with the derivative `σ'` and the exponent `p`:
(24), (25) and `y |δ'(y)| / δ(y) → ∞`, for `δ(y) = y − σ(y)`. -/
structure GateFar (σ σ' : ℝ → ℝ) (p : ℕ) : Prop where
  one_le : 1 ≤ p
  analytic : AnalyticOnNhd ℝ σ Set.univ
  hasDerivAt : ∀ z, HasDerivAt σ (σ' z) z
  /-- equation (24) -/
  neg : ∀ y, σ (-y) = -(y - σ y) ∧ σ' (-y) = 1 - σ' y
  /-- equation (25) -/
  gap : ∀ y, 2 ≤ y →
    1 / 6 * Real.exp (-(y ^ p / (p : ℝ))) ≤ y - σ y ∧
      y - σ y ≤ y * Real.exp (-(y ^ p / (p : ℝ))) ∧ |1 - σ' y| ≤ 4 * y * (y - σ y)
  ratio : Tendsto (fun y : ℝ => y * |1 - σ' y| / (y - σ y)) atTop atTop

/-- For SiLU and `y ≥ 2`: `y |δ'(y)| / δ(y) ≥ y/2 − 1`. With `E = e^y`, `δ = y/(1 + E)` and
`δ' = (1 + E − y E)/(1 + E)²`, so `y |δ'|/δ = |1 + E − y E|/(1 + E) ≥ (y E − 1 − E)/(1 + E)`, and
`(y/2 − 1)(1 + E) ≤ y E − 1 − E` because `E ≥ 1`. -/
private theorem silu_ratio_ge {y : ℝ} (hy : 2 ≤ y) :
    y / 2 + -1 ≤ y * |1 - siluDeriv y| / (y - silu y) := by
  have hy0 : 0 < y := by linarith
  obtain ⟨hδ, hδ'⟩ := silu_gap_eq y
  have hE1 : 1 ≤ Real.exp y := Real.one_le_exp hy0.le
  have hD : 0 < 1 + Real.exp y := by positivity
  have hy' := hy0.ne'
  have hD' := hD.ne'
  rw [hδ, hδ', abs_div, abs_of_pos (pow_pos hD 2)]
  -- `y |N|/(1 + E)² / (y/(1 + E)) = |N|/(1 + E)`
  have e : y * (|1 + Real.exp y - y * Real.exp y| / (1 + Real.exp y) ^ 2) / (y / (1 + Real.exp y))
      = |1 + Real.exp y - y * Real.exp y| / (1 + Real.exp y) := by
    field_simp
  rw [e, le_div_iff₀ hD]
  -- `|N| ≥ −N = y E − 1 − E ≥ (y/2 − 1)(1 + E)`
  have hN := neg_le_abs (1 + Real.exp y - y * Real.exp y)
  nlinarith [mul_nonneg hy0.le (sub_nonneg.2 hE1)]

/-- SiLU, the gate of SwiGLU, with `p = 1`. -/
theorem gateFar_silu : GateFar silu siluDeriv 1 := by
  refine ⟨le_rfl, analyticOnNhd_silu, hasDerivAt_silu, silu_neg_eq, fun y hy => ?_, ?_⟩
  · -- (25), with `e^{−y^1/1} = e^{−y}`
    simp only [pow_one, Nat.cast_one, div_one]
    exact silu_gap_bounds hy
  · -- `y |δ'|/δ ≥ y/2 − 1 → ∞`
    refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (-1)
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)))
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
    exact silu_ratio_ge hy

/-- For GELU and `y ≥ 2`: `y |δ'(y)| / δ(y) ≥ y`. With `δ = φ y mr` and `δ' = φ (mr − y)`,
`y |δ'|/δ = |mr − y|/mr`, and `y mr ≤ 1 ≤ y − mr ≤ |mr − y|` since `mr ≤ 1/y ≤ 1/2`. -/
private theorem gelu_ratio_ge {y : ℝ} (hy : 2 ≤ y) :
    y ≤ y * |1 - geluDeriv y| / (y - gelu y) := by
  have hy0 : 0 < y := by linarith
  obtain ⟨hδ, hδ'⟩ := gelu_gap_eq y
  obtain ⟨hpos, hle⟩ := millsRatio_pos_le hy0
  obtain ⟨-, hu, -⟩ := mul_millsRatio_bounds hy
  have hP := gaussPdf_pos y
  have hinv : 1 / y ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hy0 (by norm_num)]
    linarith
  have hy' := hy0.ne'
  have hP' := hP.ne'
  have hm' := hpos.ne'
  rw [hδ, hδ', abs_mul, abs_of_pos hP]
  -- `y φ |mr − y| / (φ y mr) = |mr − y| / mr`
  have e : y * (gaussPdf y * |millsRatio y - y|) / (gaussPdf y * y * millsRatio y)
      = |millsRatio y - y| / millsRatio y := by
    field_simp
  rw [e, le_div_iff₀ hpos]
  -- `y mr ≤ 1 ≤ y − mr ≤ |mr − y|`
  have hN := neg_le_abs (millsRatio y - y)
  linarith

/-- GELU, the gate of GeGLU, with `p = 2`. -/
theorem gateFar_gelu : GateFar gelu geluDeriv 2 := by
  refine ⟨by norm_num, analyticOnNhd_gelu, hasDerivAt_gelu, gelu_neg_eq, fun y hy => ?_, ?_⟩
  · -- (25), with `e^{−y²/2}`
    have h := gelu_gap_bounds hy
    rw [neg_div] at h
    simp only [Nat.cast_ofNat]
    exact h
  · -- `y |δ'|/δ ≥ y → ∞`
    refine tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
    exact gelu_ratio_ge hy

end Skips
