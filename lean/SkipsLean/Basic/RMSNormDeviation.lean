import SkipsLean.Basic.RMSNorm

/-!
# RMSNorm and a conformal change of basis for `ε > 0`: the deviation

Paper (skips paper), Lemma A.2 (RMSNorm equivariance), (ii): "If `ε > 0` and `G = cQ`, then
`‖N(hG) − N_ε(h)Q‖/‖N(h)‖ = (ε/(2r²)) |1 − c⁻²| + O(ε²)`, where `r² = ‖h‖²/d_model`." Its proof:
"For `G = cQ`, `N_ε(h cQ) = c hQ/√(c²‖h‖²/d_model + ε)` and `N_ε(h)Q = hQ/√(‖h‖²/d_model + ε)`
[…] The expansion of the deviation is the Taylor expansion of `c√(r²+ε)/√(c²r²+ε) − 1` in `ε`."
(The two `N` without a subscript in (ii) are `N_ε`.)

Part (i) is in `Basic/RMSNorm.lean` and `Basic/RMSNormConverse.lean`. Here part (ii), for a row
`v`, `r² = (v ⬝ᵥ v)/d` and an orthogonal `Q`, in three statements:

* the exact relation `N_ε(v (cQ)) = (c√(r²+ε)/√(c²r²+ε)) · N_ε(v) Q`, for every real `c` and
  `ε > 0`;
* the deviation in the Euclidean norm (the square root of the dot product of a row with itself):
  `‖N_ε(v (cQ)) − N_ε(v)Q‖ = |c√(r²+ε)/√(c²r²+ε) − 1| · ‖N_ε(v)‖`;
* the expansion `|c√(r²+ε)/√(c²r²+ε) − 1| = (ε/(2r²)) |1 − c⁻²| + O(ε²)` as `ε → 0` from above,
  for `r² > 0` and `c > 0` (as `ε → 0` from below the two sides differ at first order:
  `ai_notes/rmsnorm_deviation_check_2026-11-25.py`).
-/

namespace Skips

open Matrix Filter Topology

variable {d : Type*} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
/-- Helper: `r² + ε > 0` for `r² = (v ⬝ᵥ v)/d` and `ε > 0` (also for `card d = 0`). -/
private theorem dotProduct_div_card_add_pos_rmd {ε : ℝ} (hε : 0 < ε) (v : d → ℝ) :
    0 < (v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε := by
  have h : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have h' : 0 ≤ (v ⬝ᵥ v) / (Fintype.card d : ℝ) := div_nonneg h (Nat.cast_nonneg _)
  linarith

/-- **Lemma A.2 (ii), the exact relation.** For `ε > 0`, an orthogonal `Q`, a real `c` and a row
`v` with `r² = (v ⬝ᵥ v)/d`: `N_ε(v (cQ)) = (c√(r²+ε)/√(c²r²+ε)) · N_ε(v) Q`. -/
theorem rmsRow_vecMul_smul_orthogonal {ε : ℝ} (hε : 0 < ε) (c : ℝ) {Q : Matrix d d ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup d ℝ) (v : d → ℝ) :
    rmsRow ε (v ᵥ* (c • Q))
      = (c * Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε)
          / Real.sqrt (c ^ 2 * ((v ⬝ᵥ v) / (Fintype.card d : ℝ)) + ε)) • (rmsRow ε v ᵥ* Q) := by
  -- `v (cQ) = c (vQ)`, whose squared norm is `c² ‖v‖²`
  have ha : Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε) ≠ 0 :=
    (Real.sqrt_pos.2 (dotProduct_div_card_add_pos_rmd hε v)).ne'
  have hn : (c • (v ᵥ* Q)) ⬝ᵥ (c • (v ᵥ* Q)) / (Fintype.card d : ℝ) + ε
      = c ^ 2 * ((v ⬝ᵥ v) / (Fintype.card d : ℝ)) + ε := by
    rw [smul_dotProduct, dotProduct_smul, dotProduct_vecMul_orthogonal hQ]
    simp only [smul_eq_mul]
    ring
  unfold rmsRow
  rw [Matrix.vecMul_smul, hn, Matrix.smul_vecMul, smul_smul, smul_smul]
  -- the scalars: `b⁻¹ c = (c a / b) a⁻¹` since `a ≠ 0`
  congr 1
  field_simp

omit [DecidableEq d] in
/-- Helper: `‖k w − w‖ = |k − 1| ‖w‖` for the Euclidean norm `√(w ⬝ᵥ w)`. -/
private theorem sqrt_dotProduct_smul_sub_self_rmd (k : ℝ) (w : d → ℝ) :
    Real.sqrt ((k • w - w) ⬝ᵥ (k • w - w)) = |k - 1| * Real.sqrt (w ⬝ᵥ w) := by
  have h : k • w - w = (k - 1) • w := by rw [sub_smul, one_smul]
  rw [h, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self_eq_abs]

/-- **Lemma A.2 (ii), the deviation in the Euclidean norm.** For `ε > 0`, an orthogonal `Q`, a
real `c` and a row `v` with `r² = (v ⬝ᵥ v)/d`:
`‖N_ε(v (cQ)) − N_ε(v)Q‖ = |c√(r²+ε)/√(c²r²+ε) − 1| · ‖N_ε(v)‖`. -/
theorem sqrt_dotProduct_rmsRow_vecMul_smul_orthogonal_sub {ε : ℝ} (hε : 0 < ε) (c : ℝ)
    {Q : Matrix d d ℝ} (hQ : Q ∈ Matrix.orthogonalGroup d ℝ) (v : d → ℝ) :
    Real.sqrt ((rmsRow ε (v ᵥ* (c • Q)) - rmsRow ε v ᵥ* Q)
        ⬝ᵥ (rmsRow ε (v ᵥ* (c • Q)) - rmsRow ε v ᵥ* Q))
      = |c * Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε)
          / Real.sqrt (c ^ 2 * ((v ⬝ᵥ v) / (Fintype.card d : ℝ)) + ε) - 1|
        * Real.sqrt (rmsRow ε v ⬝ᵥ rmsRow ε v) := by
  -- by the exact relation the difference is `(k − 1) N_ε(v) Q`, and `Q` keeps the norm
  rw [rmsRow_vecMul_smul_orthogonal hε c hQ v, sqrt_dotProduct_smul_sub_self_rmd,
    dotProduct_vecMul_orthogonal hQ]

/-- Helper: the algebra of the expansion. For `0 < s ≤ P, q` with `P² = s² + c²ε`,
`q² = s² + ε` and `ε > 0`: `|P/q − 1 − (c² − 1)ε/(2s²)| ≤ |c² − 1|(3 + c²)/(8s⁴) ε²`. -/
private theorem abs_div_sub_one_sub_le_rmd {P q s c ε : ℝ} (hs : 0 < s) (hε : 0 < ε)
    (hP : s ≤ P) (hq : s ≤ q) (hP2 : P ^ 2 = s ^ 2 + c ^ 2 * ε) (hq2 : q ^ 2 = s ^ 2 + ε) :
    |P / q - 1 - (c ^ 2 - 1) * ε / (2 * s ^ 2)|
      ≤ |c ^ 2 - 1| * (3 + c ^ 2) / (8 * s ^ 4) * ε ^ 2 := by
  have hq0 : 0 < q := hs.trans_le hq
  have hP0 : 0 < P := hs.trans_le hP
  have hD0 : 0 < q * (P + q) := by positivity
  -- `P/q − 1 = (P² − q²)/(q(P + q)) = (c² − 1)ε/(q(P + q))`
  have h1 : P / q - 1 = (c ^ 2 - 1) * ε / (q * (P + q)) := by
    rw [div_sub_one hq0.ne', div_eq_div_iff hq0.ne' hD0.ne']
    linear_combination q * (hP2 - hq2)
  -- `2s² ≤ q(P + q) ≤ 2s² + (3 + c²)ε/2`
  have hD1 : 2 * s ^ 2 ≤ q * (P + q) := by nlinarith [mul_le_mul hq hP hs.le hq0.le]
  have hD2 : q * (P + q) - 2 * s ^ 2 ≤ (3 + c ^ 2) * ε / 2 := by
    nlinarith [two_mul_le_add_sq q P]
  -- the difference is `−(c² − 1)ε (q(P + q) − 2s²)/(2s² q(P + q))`
  have h2 : P / q - 1 - (c ^ 2 - 1) * ε / (2 * s ^ 2)
      = -((c ^ 2 - 1) * ε * ((q * (P + q) - 2 * s ^ 2) / (2 * s ^ 2 * (q * (P + q))))) := by
    rw [h1, div_sub_div _ _ hD0.ne' (by positivity)]
    ring
  have h3 : (q * (P + q) - 2 * s ^ 2) / (2 * s ^ 2 * (q * (P + q)))
      ≤ (3 + c ^ 2) * ε / 2 / (2 * s ^ 2 * (2 * s ^ 2)) :=
    div_le_div₀ (by positivity) hD2 (by positivity)
      (mul_le_mul_of_nonneg_left hD1 (by positivity))
  have h4 : 0 ≤ (q * (P + q) - 2 * s ^ 2) / (2 * s ^ 2 * (q * (P + q))) :=
    div_nonneg (sub_nonneg.2 hD1) (by positivity)
  rw [h2, abs_neg, abs_mul, abs_mul, abs_of_pos hε, abs_of_nonneg h4]
  calc |c ^ 2 - 1| * ε * ((q * (P + q) - 2 * s ^ 2) / (2 * s ^ 2 * (q * (P + q))))
      ≤ |c ^ 2 - 1| * ε * ((3 + c ^ 2) * ε / 2 / (2 * s ^ 2 * (2 * s ^ 2))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = |c ^ 2 - 1| * (3 + c ^ 2) / (8 * s ^ 4) * ε ^ 2 := by
        field_simp
        ring

/-- **Lemma A.2 (ii), the expansion.** For `r² > 0` and `c > 0`, as `ε → 0` from above:
`|c√(r²+ε)/√(c²r²+ε) − 1| = (ε/(2r²)) |1 − c⁻²| + O(ε²)`. -/
theorem abs_rmsNorm_deviation_sub_isBigO {r2 c : ℝ} (hr : 0 < r2) (hc : 0 < c) :
    (fun ε : ℝ => |c * Real.sqrt (r2 + ε) / Real.sqrt (c ^ 2 * r2 + ε) - 1|
        - ε / (2 * r2) * |1 - (c ^ 2)⁻¹|) =O[𝓝[>] 0] fun ε : ℝ => ε ^ 2 := by
  -- `s = c √r²`, the common value of both square roots at `ε = 0`
  have hs : 0 < c * Real.sqrt r2 := mul_pos hc (Real.sqrt_pos.2 hr)
  have hs2 : (c * Real.sqrt r2) ^ 2 = c ^ 2 * r2 := by rw [mul_pow, Real.sq_sqrt hr.le]
  refine Asymptotics.IsBigO.of_bound
    (|c ^ 2 - 1| * (3 + c ^ 2) / (8 * (c * Real.sqrt r2) ^ 4)) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : 0 < ε := hε
  have hP2 : (c * Real.sqrt (r2 + ε)) ^ 2 = (c * Real.sqrt r2) ^ 2 + c ^ 2 * ε := by
    rw [mul_pow, Real.sq_sqrt (by linarith), hs2]
    ring
  have hq2 : Real.sqrt (c ^ 2 * r2 + ε) ^ 2 = (c * Real.sqrt r2) ^ 2 + ε := by
    rw [Real.sq_sqrt (by positivity), hs2]
  have hP : c * Real.sqrt r2 ≤ c * Real.sqrt (r2 + ε) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hc.le
  have hq : c * Real.sqrt r2 ≤ Real.sqrt (c ^ 2 * r2 + ε) := by
    rw [← Real.sqrt_sq hs.le, hs2]
    exact Real.sqrt_le_sqrt (by linarith)
  -- for `ε > 0` the first-order term is the absolute value of `(c² − 1)ε/(2s²)`
  have hL : ε / (2 * r2) * |1 - (c ^ 2)⁻¹|
      = |(c ^ 2 - 1) * ε / (2 * (c * Real.sqrt r2) ^ 2)| := by
    rw [hs2, ← abs_of_pos (show 0 < ε / (2 * r2) by positivity), ← abs_mul]
    congr 1
    field_simp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε), hL]
  -- `||g| − |L|| ≤ |g − L|`
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans (abs_div_sub_one_sub_le_rmd hs hε hP hq hP2 hq2)

end Skips
