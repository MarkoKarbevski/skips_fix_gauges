import SkipsLean.Activations.MillsC

/-!
# The expansion of the Mills ratio at complex arguments

Paper (dimension paper): Appendix D.5, Lemma D.8 (ii).

"(ii) For `Re z > 0` and every integer `m ≥ 0`, with `(−1)!! = 1`,

  `|mr(z) − ∑_{l=0}^{m−1} (−1)^l (2l−1)!! / z^{2l+1}| ≤ (2m−1)!! / (Re z)^{2m+1}`."

Its proof: "`mr(z) = ∫_0^∞ e^{−zu−u²/2} du` […]. For a number `y ≥ 0`,
`|e^{−y} − ∑_{l<m} (−y)^l / l!| ≤ y^m / m!`. With `y = u²/2`, and with
`∫_0^∞ e^{−zu} u^{2l} du = (2l)! / z^{2l+1}` and `(2l)! / (2^l l!) = (2l−1)!!`, this gives (ii)."

Here `mr` is `millsRatioC` (`Activations/MillsC.lean`), defined by that integral. The double
factorial `(2l − 1)!!` is `(2 * l - 1)‼` with the subtraction of natural numbers, so that `l = 0`
gives `0‼ = 1`, the paper's `(−1)!! = 1` (as in `Activations/FarFromZero.lean`, which has the
lemma for real `z > 0`).
-/

namespace Skips

open scoped Nat

/-- The remainder `R_{m+1}(t) = e^{−t} − ∑_{l ≤ m} (−t)^l / l!` has derivative `−R_m`. -/
private theorem hasDerivAt_expRem_mce (m : ℕ) (s : ℝ) :
    HasDerivAt (fun t => Real.exp (-t) - ∑ l ∈ Finset.range (m + 1), (-t) ^ l / (l ! : ℝ))
      (-(Real.exp (-s) - ∑ l ∈ Finset.range m, (-s) ^ l / (l ! : ℝ))) s := by
  induction m with
  | zero =>
    have h := ((hasDerivAt_neg s).exp).sub_const 1
    convert h using 1
    · funext t; simp
    · simp
  | succ m ih =>
    have h := ih.sub (((hasDerivAt_neg s).pow (m + 1)).div_const ((m + 1)! : ℝ))
    convert h using 1
    · funext t; simp only [Pi.sub_apply, Pi.pow_apply]; rw [Finset.sum_range_succ]; ring
    · rw [Finset.sum_range_succ, Nat.factorial_succ, Nat.add_sub_cancel]; push_cast
      field_simp
      ring

/-- "For a number `y ≥ 0`, `|e^{−y} − ∑_{l<m} (−y)^l / l!| ≤ y^m / m!`." -/
private theorem abs_exp_neg_sub_sum_le_mce (m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    |Real.exp (-y) - ∑ l ∈ Finset.range m, (-y) ^ l / (l ! : ℝ)| ≤ y ^ m / m ! := by
  induction m generalizing y with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one]
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  | succ m ih =>
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := y)
      (f := fun t => Real.exp (-t) - ∑ l ∈ Finset.range (m + 1), (-t) ^ l / (l ! : ℝ))
      (f' := fun s => -(Real.exp (-s) - ∑ l ∈ Finset.range m, (-s) ^ l / (l ! : ℝ)))
      (B := fun t => t ^ (m + 1) / ((m + 1)! : ℝ)) (B' := fun t => t ^ m / (m ! : ℝ))
      (fun s _ => (hasDerivAt_expRem_mce m s).continuousAt.continuousWithinAt)
      (fun s _ => (hasDerivAt_expRem_mce m s).hasDerivWithinAt) ?_ ?_ ?_ ⟨hy, le_rfl⟩
    · simpa [Real.norm_eq_abs] using key
    · simp [Finset.sum_range_succ']
    · intro t
      have h := (hasDerivAt_pow (m + 1) t).div_const ((m + 1)! : ℝ)
      convert h using 1
      rw [Nat.factorial_succ, Nat.add_sub_cancel]; push_cast; field_simp
    · intro s hs
      rw [norm_neg, Real.norm_eq_abs]
      exact ih hs.1

/-- `(2l)! = 2^l l! (2l − 1)!!`. -/
private theorem factorial_two_mul_mce (l : ℕ) : (2 * l)! = 2 ^ l * l ! * (2 * l - 1)‼ := by
  cases l with
  | zero => rfl
  | succ k =>
    have h1 := Nat.factorial_eq_mul_doubleFactorial (2 * k + 1)
    have h2 := Nat.doubleFactorial_two_mul (k + 1)
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, h1]
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, h2]

/-- `∫_0^∞ u^n e^{−au} du = n! / a^{n+1}` for `a > 0`. -/
private theorem integral_pow_mul_exp_mce {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∫ u in Set.Ioi (0 : ℝ), u ^ n * Real.exp (-(a * u)) = n ! / a ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := a) (by positivity) ha
  have e1 : ∫ u in Set.Ioi (0 : ℝ), u ^ n * Real.exp (-(a * u))
      = ∫ t in Set.Ioi (0 : ℝ), t ^ ((n : ℝ) + 1 - 1) * Real.exp (-(a * t)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [add_sub_cancel_right, Real.rpow_natCast]
  rw [e1, h, Real.Gamma_nat_eq_factorial, ← Nat.cast_succ, Real.rpow_natCast, one_div_pow]
  simp only [Nat.succ_eq_add_one]
  ring

/-- `u ↦ u^n e^{−au}` is integrable on `(0, ∞)` for `a > 0`. -/
private theorem integrableOn_pow_mul_exp_mce {a : ℝ} (ha : 0 < a) (n : ℕ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-(a * u))) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := a)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos ha
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one, neg_mul]

/-- `u ↦ u^n e^{−zu}` is integrable on `(0, ∞)` for `Re z > 0`. -/
private theorem integrableOn_pow_mul_cexp_mce {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => (u : ℂ) ^ n * Complex.exp (-(z * u)))
      (Set.Ioi 0) := by
  refine MeasureTheory.Integrable.mono' (integrableOn_pow_mul_exp_mce hz n) ?_ ?_
  · exact (by fun_prop : Continuous fun u : ℝ => (u : ℂ) ^ n * Complex.exp (-(z * u)))
      |>.aestronglyMeasurable
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => le_of_eq ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu, Complex.norm_exp]
    simp

/-- `∫_0^∞ u^n e^{−zu} du = n! / z^{n+1}` for `Re z > 0`. -/
private theorem integral_pow_mul_cexp_mce {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ u in Set.Ioi (0 : ℝ), (u : ℂ) ^ n * Complex.exp (-(z * u)) = n ! / z ^ (n + 1) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  induction n with
  | zero =>
    have h := integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0
    simp only [neg_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one, h]
    field_simp
  | succ n ih =>
    have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
        HasDerivAt (fun u : ℝ => (u : ℂ) ^ (n + 1) * Complex.exp (-(z * u)))
          (((n : ℂ) + 1) * ((x : ℂ) ^ n * Complex.exp (-(z * x)))
            - z * ((x : ℂ) ^ (n + 1) * Complex.exp (-(z * x)))) x := by
      intro x _
      have h1 : HasDerivAt (fun w : ℂ => w ^ (n + 1) * Complex.exp (-(z * w)))
          (((n : ℂ) + 1) * ((x : ℂ) ^ n * Complex.exp (-(z * x)))
            - z * ((x : ℂ) ^ (n + 1) * Complex.exp (-(z * x)))) (x : ℂ) := by
        have h2 := (hasDerivAt_pow (n + 1) (x : ℂ)).mul
          (((hasDerivAt_id' (x : ℂ)).const_mul z).neg.cexp)
        convert h2 using 1
        rw [Nat.add_sub_cancel]; simp only [Pi.neg_apply]; push_cast; ring
      exact h1.comp_ofReal
    have hi1 := (integrableOn_pow_mul_cexp_mce hz n).const_mul ((n : ℂ) + 1)
    have hi2 := (integrableOn_pow_mul_cexp_mce hz (n + 1)).const_mul z
    have hlim : Filter.Tendsto (fun u : ℝ => (u : ℂ) ^ (n + 1) * Complex.exp (-(z * u)))
        Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((n + 1 : ℕ) : ℝ) z.re hz
      refine h.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 0] with u hu
      rw [Real.rpow_natCast, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hu, Complex.norm_exp]
      simp
    have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (hi1.sub hi2) hlim
    rw [MeasureTheory.integral_sub hi1 hi2, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, ih] at hftc
    simp only [Complex.ofReal_zero, ne_eq, add_eq_zero, one_ne_zero, and_false,
      not_false_eq_true, zero_pow, zero_mul, sub_zero] at hftc
    have h3 : z * ∫ u in Set.Ioi (0 : ℝ), (u : ℂ) ^ (n + 1) * Complex.exp (-(z * u))
        = ((n : ℂ) + 1) * (n ! / z ^ (n + 1)) := by
      linear_combination -hftc
    have h4 : z ^ (n + 1) * (z * ∫ u in Set.Ioi (0 : ℝ), (u : ℂ) ^ (n + 1)
        * Complex.exp (-(z * u))) = ((n : ℂ) + 1) * n ! := by
      rw [h3]; field_simp
    rw [eq_div_iff (pow_ne_zero _ hz0), Nat.factorial_succ]; push_cast
    linear_combination h4

/-- Each term of the sum is an integral:
`∫_0^∞ ((−1/2)^l / l!) u^{2l} e^{−zu} du = (−1)^l (2l−1)!! / z^{2l+1}`, since
`∫_0^∞ e^{−zu} u^{2l} du = (2l)! / z^{2l+1}` and `(2l)! / (2^l l!) = (2l−1)!!`. -/
private theorem integral_term_mce {z : ℂ} (hz : 0 < z.re) (l : ℕ) :
    ∫ u in Set.Ioi (0 : ℝ),
        ((-1 / 2 : ℂ) ^ l / (l ! : ℂ)) * ((u : ℂ) ^ (2 * l) * Complex.exp (-(z * u)))
      = (-1 : ℂ) ^ l * (((2 * l - 1)‼ : ℕ) : ℂ) / z ^ (2 * l + 1) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hl : (l ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos l).ne'
  rw [MeasureTheory.integral_const_mul, integral_pow_mul_cexp_mce hz, factorial_two_mul_mce,
    div_pow]
  push_cast
  field_simp

/-- The integrand of `mr(z)` minus the terms of the sum is `e^{−zu} R_m(u²/2)`, where
`R_m(y) = e^{−y} − ∑_{l<m} (−y)^l / l!`. -/
private theorem exp_sub_sum_eq_mce (z : ℂ) (m : ℕ) (u : ℝ) :
    Complex.exp (-(z * u) - (u : ℂ) ^ 2 / 2)
        - ∑ l ∈ Finset.range m,
          ((-1 / 2 : ℂ) ^ l / (l ! : ℂ)) * ((u : ℂ) ^ (2 * l) * Complex.exp (-(z * u)))
      = Complex.exp (-(z * u)) * ((Real.exp (-(u ^ 2 / 2))
          - ∑ l ∈ Finset.range m, (-(u ^ 2 / 2)) ^ l / (l ! : ℝ) : ℝ) : ℂ) := by
  push_cast
  rw [sub_eq_add_neg (-(z * (u : ℂ))), Complex.exp_add, mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [show -((u : ℂ) ^ 2 / 2) = (-1 / 2) * (u : ℂ) ^ 2 by ring, mul_pow, ← pow_mul]
  ring

/-- `|e^{−zu} R_m(u²/2)| ≤ e^{−(Re z) u} (u²/2)^m / m! = u^{2m} e^{−(Re z) u} / (2^m m!)`. -/
private theorem norm_rem_le_mce (z : ℂ) (m : ℕ) {u : ℝ} (hu : 0 < u) :
    ‖Complex.exp (-(z * u)) * ((Real.exp (-(u ^ 2 / 2))
          - ∑ l ∈ Finset.range m, (-(u ^ 2 / 2)) ^ l / (l ! : ℝ) : ℝ) : ℂ)‖
      ≤ (1 / (2 ^ m * m ! : ℝ)) * (u ^ (2 * m) * Real.exp (-(z.re * u))) := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have hre : (-(z * (u : ℂ))).re = -(z.re * u) := by simp
  rw [hre]
  have h := abs_exp_neg_sub_sum_le_mce m (y := u ^ 2 / 2) (by positivity)
  refine (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans (le_of_eq ?_)
  rw [div_pow, ← pow_mul]
  field_simp

/-- **Lemma D.8 (ii), for complex `z` with `Re z > 0`:** the partial sums of
`∑_l (−1)^l (2l−1)!! / z^{2l+1}` approximate the Mills ratio with an error of at most
`(2m−1)!! / (Re z)^{2m+1}`. -/
theorem norm_millsRatioC_sub_sum_le {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    ‖millsRatioC z
        - ∑ l ∈ Finset.range m, (-1 : ℂ) ^ l * (((2 * l - 1)‼ : ℕ) : ℂ) / z ^ (2 * l + 1)‖
      ≤ ((2 * m - 1)‼ : ℝ) / z.re ^ (2 * m + 1) := by
  -- the terms `((−1/2)^l / l!) u^{2l} e^{−zu}` of the sum, and their sum, are integrable
  have hT : ∀ l ∈ Finset.range m, MeasureTheory.IntegrableOn (fun u : ℝ =>
      ((-1 / 2 : ℂ) ^ l / (l ! : ℂ)) * ((u : ℂ) ^ (2 * l) * Complex.exp (-(z * u))))
      (Set.Ioi 0) :=
    fun l _ => (integrableOn_pow_mul_cexp_mce hz (2 * l)).const_mul _
  have hS := MeasureTheory.integrable_finsetSum _ hT
  -- the bound `u^{2m} e^{−(Re z) u} / (2^m m!)` of `e^{−zu} R_m(u²/2)` is integrable
  have hg := (integrableOn_pow_mul_exp_mce hz (2 * m)).const_mul (1 / (2 ^ m * m ! : ℝ))
  have hb := MeasureTheory.ae_restrict_of_forall_mem (μ := MeasureTheory.volume)
    measurableSet_Ioi (fun u (hu : u ∈ Set.Ioi (0 : ℝ)) => norm_rem_le_mce z m hu)
  have hR := MeasureTheory.Integrable.mono' hg (Continuous.aestronglyMeasurable (by fun_prop :
    Continuous fun u : ℝ => Complex.exp (-(z * u)) * ((Real.exp (-(u ^ 2 / 2))
      - ∑ l ∈ Finset.range m, (-(u ^ 2 / 2)) ^ l / (l ! : ℝ) : ℝ) : ℂ))) hb
  -- `mr(z) = ∫_0^∞ (e^{−zu} R_m(u²/2) + ∑_{l<m} ((−1/2)^l / l!) u^{2l} e^{−zu}) du`
  have hmr : millsRatioC z = ∫ u in Set.Ioi (0 : ℝ),
      (Complex.exp (-(z * u)) * ((Real.exp (-(u ^ 2 / 2))
        - ∑ l ∈ Finset.range m, (-(u ^ 2 / 2)) ^ l / (l ! : ℝ) : ℝ) : ℂ)
      + ∑ l ∈ Finset.range m,
        ((-1 / 2 : ℂ) ^ l / (l ! : ℂ)) * ((u : ℂ) ^ (2 * l) * Complex.exp (-(z * u)))) := by
    unfold millsRatioC
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    rw [← exp_sub_sum_eq_mce z m u, sub_add_cancel]
  -- the sum of the expansion is the integral of the sum of the terms
  have hsum : ∑ l ∈ Finset.range m, (-1 : ℂ) ^ l * (((2 * l - 1)‼ : ℕ) : ℂ) / z ^ (2 * l + 1)
      = ∫ u in Set.Ioi (0 : ℝ), ∑ l ∈ Finset.range m,
        ((-1 / 2 : ℂ) ^ l / (l ! : ℂ)) * ((u : ℂ) ^ (2 * l) * Complex.exp (-(z * u))) := by
    rw [MeasureTheory.integral_finsetSum _ hT]
    exact Finset.sum_congr rfl (fun l _ => (integral_term_mce hz l).symm)
  rw [hmr, MeasureTheory.integral_add hR hS, hsum, add_sub_cancel_right]
  -- `‖∫ e^{−zu} R_m(u²/2)‖ ≤ ∫ u^{2m} e^{−(Re z) u} / (2^m m!) = (2m−1)!! / (Re z)^{2m+1}`
  refine (MeasureTheory.norm_integral_le_of_norm_le hg hb).trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_pow_mul_exp_mce hz, factorial_two_mul_mce]
  push_cast
  field_simp

/-- The case `m = 0` of Lemma D.8 (ii): `|mr(z)| ≤ 1 / Re z` for `Re z > 0`. -/
theorem norm_millsRatioC_le {z : ℂ} (hz : 0 < z.re) : ‖millsRatioC z‖ ≤ 1 / z.re := by
  have h := norm_millsRatioC_sub_sum_le hz 0
  simpa using h

end Skips
