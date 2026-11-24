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

/-- `φ(z) mr(z) = 1 − Φ(z)`, since `φ(z) > 0`. -/
private theorem gaussPdf_mul_millsRatio (z : ℝ) : gaussPdf z * millsRatio z = 1 - gaussCdf z := by
  unfold millsRatio
  exact mul_div_cancel₀ _ (gaussPdf_pos z).ne'

/-- **Lemma D.8 (i), first formula:** `GELU(z) = z − φ(z) z mr(z)`. -/
theorem gelu_eq_sub_millsRatio (z : ℝ) : gelu z = z - gaussPdf z * z * millsRatio z := by
  -- `z Φ(z) = z − z (1 − Φ(z))` and `φ(z) mr(z) = 1 − Φ(z)`
  rw [gelu]
  linear_combination z * gaussPdf_mul_millsRatio z

/-- **Lemma D.8 (i), second formula:** `GELU'(z) = 1 − φ(z) (mr(z) − z)`. -/
theorem geluDeriv_eq_sub_millsRatio (z : ℝ) :
    geluDeriv z = 1 - gaussPdf z * (millsRatio z - z) := by
  -- `Φ(z) + z φ(z) = 1 − (1 − Φ(z)) + z φ(z)` and `φ(z) mr(z) = 1 − Φ(z)`
  rw [geluDeriv]
  linear_combination gaussPdf_mul_millsRatio z

open Filter Topology

/-- A function antitone on `(0, ∞)` with limit `0` at `+∞` is nonnegative there (a copy of the
private lemma of `Gaussian.lean`). -/
private theorem nonneg_of_antitoneOn_of_tendsto' {g : ℝ → ℝ} (hg : AntitoneOn g (Set.Ioi 0))
    (hlim : Tendsto g atTop (𝓝 0)) {z : ℝ} (hz : 0 < z) : 0 ≤ g z :=
  le_of_tendsto hlim ((eventually_ge_atTop z).mono fun _y hy =>
    hg (Set.mem_Ioi.2 hz) (Set.mem_Ioi.2 (lt_of_lt_of_le hz hy)) hy)

/-- A function on `(0, ∞)` with a nonpositive derivative is antitone there (a copy of the private
lemma of `Gaussian.lean`). -/
private theorem antitoneOn_Ioi_of_hasDerivAt' {g g' : ℝ → ℝ}
    (hg : ∀ y, 0 < y → HasDerivAt g (g' y) y) (hg' : ∀ y, 0 < y → g' y ≤ 0) :
    AntitoneOn g (Set.Ioi 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := g') (convex_Ioi 0)
    (fun y hy => (hg y hy).continuousAt.continuousWithinAt) (fun y hy => ?_) (fun y hy => ?_)
  · rw [interior_Ioi] at hy ⊢
    exact (hg y hy).hasDerivWithinAt
  · rw [interior_Ioi] at hy
    exact hg' y hy

/-- `(2(m+1) − 1)!! = (2m+1) (2m−1)!!`, also for `m = 0` (where `(2·0 − 1)!! = 0!! = 1`). -/
private theorem doubleFactorial_two_mul_succ_sub_one (m : ℕ) :
    (2 * (m + 1) - 1)‼ = (2 * m + 1) * (2 * m - 1)‼ := by
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
  rcases m with _ | k
  · rfl
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, Nat.doubleFactorial_add_two,
      show 2 * (k + 1) - 1 = 2 * k + 1 by omega]

/-- The signed remainder of the asymptotic series, times `φ`:
`h_m(z) = (−1)^m (1 − Φ(z) − φ(z) S_m(z))`, with `S_m` the partial sum of Lemma D.8 (ii).
It is defined by the recursion `h_0 = 1 − Φ`, `h_{m+1} = −h_m + (2m−1)!! φ(z) / z^{2m+1}`
(`tailRem_eq` relates the two forms). -/
private noncomputable def tailRem : ℕ → ℝ → ℝ
  | 0 => fun z => 1 - gaussCdf z
  | m + 1 => fun z => -tailRem m z + ((2 * m - 1)‼ : ℝ) * gaussPdf z / z ^ (2 * m + 1)

/-- `h_m'(z) = −(2m−1)!! φ(z) / z^{2m}` for `z > 0`. -/
private theorem hasDerivAt_tailRem (m : ℕ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (tailRem m) (-(((2 * m - 1)‼ : ℝ) * gaussPdf z / z ^ (2 * m))) z := by
  induction m with
  | zero =>
    -- `(1 − Φ)' = −φ`
    show HasDerivAt (fun z => 1 - gaussCdf z) _ z
    convert (hasDerivAt_gaussCdf z).const_sub 1 using 1
    simp
  | succ m ih =>
    -- `(c φ / z^{2m+1})' = c (−z φ z^{2m+1} − (2m+1) φ z^{2m}) / z^{4m+2}`, with `φ' = −z φ`
    show HasDerivAt
      (fun z => -tailRem m z + ((2 * m - 1)‼ : ℝ) * gaussPdf z / z ^ (2 * m + 1)) _ z
    have h2 := ((hasDerivAt_gaussPdf z).const_mul ((2 * m - 1)‼ : ℝ)).div
      (hasDerivAt_pow (2 * m + 1) z) (pow_ne_zero _ hz.ne')
    convert ih.neg.add h2 using 1
    rw [doubleFactorial_two_mul_succ_sub_one, Nat.add_sub_cancel]
    have hz' := hz.ne'
    push_cast
    field_simp
    ring

/-- `h_m(z) → 0` as `z → +∞`. -/
private theorem tendsto_tailRem (m : ℕ) : Tendsto (tailRem m) atTop (𝓝 0) := by
  induction m with
  | zero =>
    -- `Φ → 1`
    have h := tendsto_gaussCdf_atTop.const_sub 1
    rw [sub_self] at h
    exact h
  | succ m ih =>
    -- `φ → 0` and `z^{2m+1} → ∞`
    have h1 : Tendsto (fun z => ((2 * m - 1)‼ : ℝ) * gaussPdf z / z ^ (2 * m + 1)) atTop (𝓝 0) :=
      (tendsto_gaussPdf_atTop.const_mul _).div_atTop (tendsto_pow_atTop (by omega))
    have h2 := ih.neg.add h1
    rw [neg_zero, zero_add] at h2
    exact h2

/-- `h_m(z) ≥ 0` for `z > 0`: `h_m` decreases on `(0, ∞)` and tends to `0`. -/
private theorem tailRem_nonneg (m : ℕ) {z : ℝ} (hz : 0 < z) : 0 ≤ tailRem m z := by
  have hanti := antitoneOn_Ioi_of_hasDerivAt'
    (g' := fun y => -(((2 * m - 1)‼ : ℝ) * gaussPdf y / y ^ (2 * m)))
    (fun y hy => hasDerivAt_tailRem m hy) (fun y hy => by
      have := gaussPdf_pos y
      have : 0 < y ^ (2 * m) := pow_pos hy _
      simp only [neg_nonpos]
      positivity)
  exact nonneg_of_antitoneOn_of_tendsto' hanti (tendsto_tailRem m) hz

/-- `h_m(z) = (−1)^m φ(z) (mr(z) − S_m(z))`. -/
private theorem tailRem_eq (m : ℕ) (z : ℝ) :
    tailRem m z = (-1 : ℝ) ^ m * gaussPdf z * (millsRatio z -
      ∑ l ∈ Finset.range m, (-1 : ℝ) ^ l * ((2 * l - 1)‼ : ℝ) / z ^ (2 * l + 1)) := by
  induction m with
  | zero =>
    show 1 - gaussCdf z = _
    rw [pow_zero, one_mul, Finset.sum_range_zero, sub_zero, gaussPdf_mul_millsRatio]
  | succ m ih =>
    show -tailRem m z + ((2 * m - 1)‼ : ℝ) * gaussPdf z / z ^ (2 * m + 1) = _
    rw [ih, Finset.sum_range_succ, pow_succ]
    have hs : (-1 : ℝ) ^ m * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-(((2 * m - 1)‼ : ℝ) * gaussPdf z / z ^ (2 * m + 1))) * hs

/-- **Lemma D.8 (ii), for real `z > 0`:** the partial sums of
`∑_l (−1)^l (2l−1)!! / z^{2l+1}` approximate the Mills ratio with an error of at most the first
omitted term. -/
theorem abs_millsRatio_sub_sum_le {z : ℝ} (hz : 0 < z) (m : ℕ) :
    |millsRatio z - ∑ l ∈ Finset.range m, (-1 : ℝ) ^ l * ((2 * l - 1)‼ : ℝ) / z ^ (2 * l + 1)|
      ≤ ((2 * m - 1)‼ : ℝ) / z ^ (2 * m + 1) := by
  -- with `s = (−1)^m` and `e = mr(z) − S_m(z)`: `h_m ≥ 0` gives `s e ≥ 0`, and `h_{m+1} ≥ 0` gives
  -- `s e ≤ (2m−1)!! / z^{2m+1}`; and `|e| = s e`
  have hφ := gaussPdf_pos z
  have hs : (-1 : ℝ) ^ m * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  have h0 := tailRem_nonneg m hz
  have h1 := tailRem_nonneg (m + 1) hz
  rw [tailRem_eq] at h0 h1
  rw [Finset.sum_range_succ] at h1
  have e1 : (-1 : ℝ) ^ (m + 1) * gaussPdf z * (millsRatio z -
      (∑ l ∈ Finset.range m, (-1 : ℝ) ^ l * ((2 * l - 1)‼ : ℝ) / z ^ (2 * l + 1) +
        (-1 : ℝ) ^ m * ((2 * m - 1)‼ : ℝ) / z ^ (2 * m + 1))) =
      gaussPdf z * (((2 * m - 1)‼ : ℝ) / z ^ (2 * m + 1) - (-1 : ℝ) ^ m * (millsRatio z -
        ∑ l ∈ Finset.range m, (-1 : ℝ) ^ l * ((2 * l - 1)‼ : ℝ) / z ^ (2 * l + 1))) := by
    rw [pow_succ]
    linear_combination (gaussPdf z * ((2 * m - 1)‼ : ℝ) / z ^ (2 * m + 1)) * hs
  rw [e1] at h1
  have hlow : 0 ≤ (-1 : ℝ) ^ m * (millsRatio z -
      ∑ l ∈ Finset.range m, (-1 : ℝ) ^ l * ((2 * l - 1)‼ : ℝ) / z ^ (2 * l + 1)) := by
    have h0' : 0 ≤ gaussPdf z * ((-1 : ℝ) ^ m * (millsRatio z -
        ∑ l ∈ Finset.range m, (-1 : ℝ) ^ l * ((2 * l - 1)‼ : ℝ) / z ^ (2 * l + 1))) := by
      linarith
    exact (mul_nonneg_iff_of_pos_left hφ).1 h0'
  have hup := sub_nonneg.1 ((mul_nonneg_iff_of_pos_left hφ).1 h1)
  calc _ = |(-1 : ℝ) ^ m * (millsRatio z -
        ∑ l ∈ Finset.range m, (-1 : ℝ) ^ l * ((2 * l - 1)‼ : ℝ) / z ^ (2 * l + 1))| := by
        rw [abs_mul, abs_neg_one_pow, one_mul]
    _ = _ := abs_of_nonneg hlow
    _ ≤ _ := hup

/-- `0 < mr(y) ≤ 1/y` for `y > 0` (Lemma D.8 (ii) with `m = 0`). -/
theorem millsRatio_pos_le {y : ℝ} (hy : 0 < y) : 0 < millsRatio y ∧ millsRatio y ≤ 1 / y := by
  -- `1 − Φ(y) > 0`, and `1 − Φ(y) ≤ φ(y)/y`
  have hφ := gaussPdf_pos y
  refine ⟨div_pos (sub_pos.2 (gaussCdf_lt_one y)) hφ, ?_⟩
  rw [millsRatio, div_le_iff₀ hφ]
  calc 1 - gaussCdf y ≤ gaussPdf y / y := one_sub_gaussCdf_le hy
    _ = 1 / y * gaussPdf y := by ring

/-- `|mr(y) − 1/y| ≤ 1/y³` for `y > 0` (Lemma D.8 (ii) with `m = 1`). -/
theorem abs_millsRatio_sub_inv_le {y : ℝ} (hy : 0 < y) : |millsRatio y - 1 / y| ≤ 1 / y ^ 3 := by
  -- Lemma D.8 (ii) with `m = 1`: `S_1(y) = 1/y` and `1!! = 1`
  have h := abs_millsRatio_sub_sum_le hy 1
  have e1 : ∑ l ∈ Finset.range 1, (-1 : ℝ) ^ l * ((2 * l - 1)‼ : ℝ) / y ^ (2 * l + 1) = 1 / y := by
    simp
  have e2 : ((2 * 1 - 1)‼ : ℝ) / y ^ (2 * 1 + 1) = 1 / y ^ 3 := by
    norm_num [Nat.doubleFactorial]
  rwa [e1, e2] at h

/-- `3/4 ≤ y mr(y) ≤ 1` and `|mr(y) − y| ≤ 2y` for `y ≥ 2`. -/
theorem mul_millsRatio_bounds {y : ℝ} (hy : 2 ≤ y) :
    3 / 4 ≤ y * millsRatio y ∧ y * millsRatio y ≤ 1 ∧ |millsRatio y - y| ≤ 2 * y := by
  have hy0 : 0 < y := by linarith
  obtain ⟨hpos, hle⟩ := millsRatio_pos_le hy0
  have hlow : 1 / y - 1 / y ^ 3 ≤ millsRatio y := by
    linarith [(abs_le.1 (abs_millsRatio_sub_inv_le hy0)).1]
  have hinv : 1 / y ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hy0 (by norm_num)]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · -- `y mr(y) ≥ y (1/y − 1/y³) = 1 − 1/y² ≥ 3/4`
    have h1 : y * (1 / y - 1 / y ^ 3) = 1 - 1 / y ^ 2 := by
      field_simp
    have h2 : 1 / y ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc 3 / 4 ≤ 1 - 1 / y ^ 2 := by linarith
      _ = y * (1 / y - 1 / y ^ 3) := h1.symm
      _ ≤ y * millsRatio y := mul_le_mul_of_nonneg_left hlow hy0.le
  · -- `y mr(y) ≤ y (1/y) = 1`
    calc y * millsRatio y ≤ y * (1 / y) := mul_le_mul_of_nonneg_left hle hy0.le
      _ = 1 := mul_one_div_cancel hy0.ne'
  · -- `0 < mr(y) ≤ 1/y ≤ 1/2 < y`
    rw [abs_le]
    constructor <;> linarith

/-! ### Equation (24) -/

/-- (24) for GELU: `σ(−y) = −δ(y)` and `σ'(−y) = δ'(y)`. -/
theorem gelu_neg_eq (y : ℝ) :
    gelu (-y) = -(y - gelu y) ∧ geluDeriv (-y) = 1 - geluDeriv y := by
  -- `Φ(−y) = 1 − Φ(y)` and `φ(−y) = φ(y)`
  constructor
  · simp only [gelu, gaussCdf_neg]
    ring
  · simp only [geluDeriv, gaussCdf_neg, gaussPdf_neg]
    ring

/-- (24) for SiLU: `σ(−y) = −δ(y)` and `σ'(−y) = δ'(y)`. -/
theorem silu_neg_eq (y : ℝ) :
    silu (-y) = -(y - silu y) ∧ siluDeriv (-y) = 1 - siluDeriv y := by
  -- `e^{−y} = 1/e^y`; clear the denominators
  have hx := Real.exp_pos y
  constructor
  · simp only [silu, neg_neg, Real.exp_neg]
    field_simp
    ring
  · simp only [siluDeriv, neg_neg, Real.exp_neg]
    field_simp
    ring

/-! ### The small terms `δ` and `δ'` -/

/-- For GELU, `δ(y) = φ(y) y mr(y)` and `δ'(y) = φ(y) (mr(y) − y)`. -/
theorem gelu_gap_eq (y : ℝ) :
    y - gelu y = gaussPdf y * y * millsRatio y ∧
      1 - geluDeriv y = gaussPdf y * (millsRatio y - y) := by
  -- Lemma D.8 (i)
  constructor
  · rw [gelu_eq_sub_millsRatio]
    ring
  · rw [geluDeriv_eq_sub_millsRatio]
    ring

/-- For SiLU, `δ(y) = y / (1 + e^y)` and `δ'(y) = (1 + e^y − y e^y) / (1 + e^y)²`. -/
theorem silu_gap_eq (y : ℝ) :
    y - silu y = y / (1 + Real.exp y) ∧
      1 - siluDeriv y = (1 + Real.exp y - y * Real.exp y) / (1 + Real.exp y) ^ 2 := by
  -- multiply numerator and denominator by `e^y` (resp. `e^{2y}`)
  have hx := Real.exp_pos y
  constructor
  · simp only [silu, Real.exp_neg]
    field_simp
    ring
  · simp only [siluDeriv, Real.exp_neg]
    field_simp
    ring

/-- **Equation (25) for GELU** (`p = 2`): for `y ≥ 2`,
`(1/6) e^{−y²/2} ≤ δ(y) ≤ y e^{−y²/2}` and `|δ'(y)| ≤ 4 y δ(y)`. -/
theorem gelu_gap_bounds {y : ℝ} (hy : 2 ≤ y) :
    1 / 6 * Real.exp (-y ^ 2 / 2) ≤ y - gelu y ∧ y - gelu y ≤ y * Real.exp (-y ^ 2 / 2) ∧
      |1 - geluDeriv y| ≤ 4 * y * (y - gelu y) := by
  have hy0 : 0 < y := by linarith
  obtain ⟨hδ, hδ'⟩ := gelu_gap_eq y
  obtain ⟨hl, hu, ha⟩ := mul_millsRatio_bounds hy
  have hP := gaussPdf_pos y
  have hE := Real.exp_pos (-y ^ 2 / 2)
  -- `1 ≤ √(2π) ≤ 9/2`, so `(2/9) e^{−y²/2} ≤ φ(y) ≤ e^{−y²/2}`
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs1 : 1 ≤ Real.sqrt (2 * Real.pi) := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hs2 : Real.sqrt (2 * Real.pi) ≤ 9 / 2 := by
    calc Real.sqrt (2 * Real.pi) ≤ Real.sqrt ((9 / 2) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_four])
      _ = 9 / 2 := Real.sqrt_sq (by norm_num)
  have hPE : gaussPdf y = Real.exp (-y ^ 2 / 2) / Real.sqrt (2 * Real.pi) := rfl
  have hP1 : 2 / 9 * Real.exp (-y ^ 2 / 2) ≤ gaussPdf y := by
    rw [hPE, le_div_iff₀ hs]
    nlinarith
  have hP2 : gaussPdf y ≤ Real.exp (-y ^ 2 / 2) := by
    rw [hPE, div_le_iff₀ hs]
    nlinarith
  -- `δ = (y mr(y)) φ(y)` with `3/4 ≤ y mr(y) ≤ 1`
  have hM := mul_le_mul_of_nonneg_right hl hP.le
  have hM' := mul_le_mul_of_nonneg_right hu hP.le
  have hEy : Real.exp (-y ^ 2 / 2) ≤ y * Real.exp (-y ^ 2 / 2) :=
    le_mul_of_one_le_left hE.le (by linarith)
  rw [hδ, hδ']
  have e : gaussPdf y * y * millsRatio y = y * millsRatio y * gaussPdf y := by ring
  rw [e]
  refine ⟨by linarith, by linarith, ?_⟩
  -- `|δ'| = φ |mr − y| ≤ 2y φ ≤ 4y (3/4) φ ≤ 4y δ`
  rw [abs_mul, abs_of_pos hP]
  have h4 := mul_le_mul_of_nonneg_left hM (by linarith : (0 : ℝ) ≤ 4 * y)
  have hyP := mul_pos hy0 hP
  calc gaussPdf y * |millsRatio y - y| ≤ gaussPdf y * (2 * y) :=
        mul_le_mul_of_nonneg_left ha hP.le
    _ ≤ 4 * y * (y * millsRatio y * gaussPdf y) := by linarith

/-- **Equation (25) for SiLU** (`p = 1`): for `y ≥ 2`,
`(1/6) e^{−y} ≤ δ(y) ≤ y e^{−y}` and `|δ'(y)| ≤ 4 y δ(y)`. -/
theorem silu_gap_bounds {y : ℝ} (hy : 2 ≤ y) :
    1 / 6 * Real.exp (-y) ≤ y - silu y ∧ y - silu y ≤ y * Real.exp (-y) ∧
      |1 - siluDeriv y| ≤ 4 * y * (y - silu y) := by
  have hy0 : 0 < y := by linarith
  obtain ⟨hδ, hδ'⟩ := silu_gap_eq y
  have hE := Real.exp_pos y
  have hE1 : 1 ≤ Real.exp y := Real.one_le_exp hy0.le
  rw [hδ, hδ', Real.exp_neg]
  refine ⟨?_, ?_, ?_⟩
  · -- `(1/6) e^{−y} ≤ y / (1 + e^y)`, since `1 + e^y ≤ 2 e^y`
    rw [← div_eq_mul_inv, div_le_div_iff₀ hE (by positivity)]
    nlinarith
  · -- `y / (1 + e^y) ≤ y / e^y`
    rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hE]
    nlinarith
  · -- `|1 + e^y − y e^y| ≤ (1 + y)(1 + e^y)` and `1 + y ≤ 4 y²`
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + Real.exp y) ^ 2)]
    have hN : |1 + Real.exp y - y * Real.exp y| ≤ (1 + y) * (1 + Real.exp y) := by
      rw [abs_le]
      constructor <;> nlinarith
    calc |1 + Real.exp y - y * Real.exp y| / (1 + Real.exp y) ^ 2
        ≤ (1 + y) * (1 + Real.exp y) / (1 + Real.exp y) ^ 2 := by gcongr
      _ = (1 + y) / (1 + Real.exp y) := by
        rw [pow_two, mul_div_mul_right _ _ (by positivity : (1 + Real.exp y) ≠ 0)]
      _ ≤ 4 * y * y / (1 + Real.exp y) := by gcongr; nlinarith
      _ = 4 * y * (y / (1 + Real.exp y)) := by ring

/-- For SiLU and `y ≥ 2`: `(1/2) y e^{−y} ≤ δ(y)` and `|δ'(y)| ≤ (2 + y) e^{−y}`. -/
theorem silu_gap_bounds' {y : ℝ} (hy : 2 ≤ y) :
    1 / 2 * y * Real.exp (-y) ≤ y - silu y ∧ |1 - siluDeriv y| ≤ (2 + y) * Real.exp (-y) := by
  have hy0 : 0 < y := by linarith
  obtain ⟨hδ, hδ'⟩ := silu_gap_eq y
  have hE := Real.exp_pos y
  have hE1 : 1 ≤ Real.exp y := Real.one_le_exp hy0.le
  rw [hδ, hδ', Real.exp_neg]
  constructor
  · -- `(1/2) y / e^y ≤ y / (1 + e^y)`, since `1 + e^y ≤ 2 e^y`
    rw [← div_eq_mul_inv, div_le_div_iff₀ hE (by positivity)]
    nlinarith
  · -- `|1 + e^y − y e^y| ≤ (2 + y) e^y` and `(1 + e^y)² ≥ e^{2y}`
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + Real.exp y) ^ 2)]
    have hN : |1 + Real.exp y - y * Real.exp y| ≤ (2 + y) * Real.exp y := by
      rw [abs_le]
      constructor <;> nlinarith
    calc |1 + Real.exp y - y * Real.exp y| / (1 + Real.exp y) ^ 2
        ≤ (2 + y) * Real.exp y / (1 + Real.exp y) ^ 2 := by gcongr
      _ ≤ (2 + y) * Real.exp y / Real.exp y ^ 2 := by gcongr; linarith
      _ = (2 + y) * (Real.exp y)⁻¹ := by field_simp

end Skips
