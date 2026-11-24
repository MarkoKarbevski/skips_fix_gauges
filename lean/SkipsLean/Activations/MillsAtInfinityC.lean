import SkipsLean.Activations.MillsAtInfinity
import SkipsLean.Activations.MillsCExpansion

/-!
# Maps that are meromorphic at infinity, and the Mills ratio, at complex arguments

Paper (dimension paper): Appendix D.5, after Lemma D.8, and Lemma D.9, in the form with complex
`ω`, `ω'` that the proof of Lemma D.19 (Appendix D.6, the case `ε = 0`) uses.

* "We say that a map `Θ` on an interval `(t₀, ∞)` is meromorphic at infinity if
  `Θ(t) = t^l Θ₀(1/t)` for an integer `l` and a map `Θ₀` that is holomorphic near `0`. Such a map
  vanishes identically if it tends to `0` faster than every power of `1/t`."
* "Lemma D.9 (The Mills ratio at infinity). Let `z(t) = ω t + ω'/t` with `ω, ω' ∈ ℂ` and
  `Re ω > 0`, and let `Θ₁` and `Θ₂` be meromorphic at infinity, with values in `ℂ^{1×d_out}`. If
  `Θ₁(t) mr(z(t)) + Θ₂(t)` tends to `0` faster than every power of `1/t` as `t → +∞`, then
  `Θ₁ = 0` and `Θ₂ = 0`."

Its proof: "Suppose that a component of `Θ₁` is not zero, and let `Θ₁`, `Θ₂` stand for this
component of both. Then `mr(z(t)) = −Θ₂(t)/Θ₁(t) + O(t^{−m})` for every `m`. For large `t`,
`t = (z/(2ω)) (1 + √(1 − 4ωω'/z²))` with `z = z(t)`, so `1/t` is a convergent power series in
`1/z` without constant term. Hence `−Θ₂/Θ₁` is, for large `t`, a convergent series in powers of
`1/z` with finitely many positive powers of `z`, and this series is an asymptotic expansion of
`mr(z)` along the curve `z = z(t)`. On this curve `Re z` is at least a positive constant times
`|z|` for large `t`, so by Lemma D.8 (ii) the series `∑_l (−1)^l (2l−1)!! z^{−2l−1}` is one as
well. Asymptotic expansions are unique, so the two series have the same coefficients. But the
numbers `(2l−1)!!` grow faster than every geometric sequence, so the second series converges for
no `z`, a contradiction. Hence `Θ₁ = 0`, then `Θ₂` tends to `0` faster than every power, and
`Θ₂ = 0`."

`Activations/MillsAtInfinity.lean` has the case of a real `ω > 0`, `ω' = 0` and maps `Θ₀` that are
real-analytic at `0`. Here `Θ₀ : ℂ → F` is holomorphic at `0`, the variable `t` stays real, the
values lie in a complex normed space, and `mr` is `millsRatioC`. As there, "`Θ = 0`" is stated as
"`Θ(t) = 0` for all large `t`", and "tends to `0` faster than every power of `1/t`" is
`FasterThanPowers`.
-/

namespace Skips

open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- "`Θ` is meromorphic at infinity", with a holomorphic `Θ₀`: `Θ(t) = t^l Θ₀(1/t)` for all large
real `t`, with `Θ₀ : ℂ → F` holomorphic at `0`. -/
def MeromorphicAtInfinityC (Θ : ℝ → F) : Prop :=
  ∃ (l : ℕ) (Θ₀ : ℂ → F), AnalyticAt ℂ Θ₀ 0 ∧
    ∀ᶠ t : ℝ in atTop, Θ t = ((t : ℂ) ^ l) • Θ₀ ((t : ℂ)⁻¹)

/-- `1/t → 0` in `ℂ` as `t → +∞`. -/
private lemma tendsto_ofReal_inv_mic : Tendsto (fun t : ℝ => (t : ℂ)⁻¹) atTop (𝓝 0) := by
  have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  rw [Complex.ofReal_zero] at h
  exact h.congr fun t => by simp

/-- **"Such a map vanishes identically if it tends to `0` faster than every power of `1/t`."** -/
theorem MeromorphicAtInfinityC.eventually_eq_zero {Θ : ℝ → F} (hΘ : MeromorphicAtInfinityC Θ)
    (h : FasterThanPowers Θ) : ∀ᶠ t in atTop, Θ t = 0 := by
  obtain ⟨l, Θ₀, hΘ₀, hEq⟩ := hΘ
  -- the restriction `f(s) = Θ₀(s)` of `Θ₀` to real `s` is real-analytic at `0`
  have hf : AnalyticAt ℝ (fun s : ℝ => Θ₀ (s : ℂ)) 0 := by
    have h1 : AnalyticAt ℝ Θ₀ ((0 : ℝ) : ℂ) := by
      rw [Complex.ofReal_zero]
      exact hΘ₀.restrictScalars
    exact h1.comp (Complex.ofRealCLM.analyticAt 0)
  -- `‖f(1/t)‖ ≤ t^l ‖Θ₀(1/t)‖ = ‖Θ(t)‖` for `t ≥ 1`, so `f(1/t)` tends to `0` faster than every
  -- power
  have hinv : ∀ t : ℝ, ((1 / t : ℝ) : ℂ) = (t : ℂ)⁻¹ := fun t => by push_cast; ring
  have h₀ : FasterThanPowers fun t : ℝ => (fun s : ℝ => Θ₀ (s : ℂ)) (1 / t) := by
    refine h.mono ?_
    filter_upwards [hEq, eventually_ge_atTop 1] with t ht ht1
    rw [ht, norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      hinv]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ ht1)
  -- so `f = 0` near `0`, and `Θ(t) = t^l Θ₀(1/t) = t^l f(1/t) = 0` for large `t`
  filter_upwards [hEq, tendsto_inv_atTop_zero.eventually
    (eventually_nhds_eq_zero_of_fasterThanPowers hf h₀)] with t ht ht0
  rw [ht, ← Complex.ofReal_inv, ht0, smul_zero]


/-! ### Helpers for Lemma D.9 -/

/-- A map whose norm is, for all large `t`, at most a function with superpolynomial decay tends to
`0` faster than every power. -/
private lemma fasterThanPowers_of_norm_le_mic {G : Type*} [NormedAddCommGroup G] {g : ℝ → G}
    {u : ℝ → ℝ} (hu : Asymptotics.SuperpolynomialDecay atTop (fun t : ℝ => t) u)
    (hg : ∀ᶠ t in atTop, ‖g t‖ ≤ u t) : FasterThanPowers g :=
  Asymptotics.SuperpolynomialDecay.trans_eventuallyLE (eventually_ge_atTop 0)
    (Asymptotics.superpolynomialDecay_zero _ _) hu
    (Eventually.of_forall fun t => norm_nonneg (g t)) hg

/-- A map that is, for all large `t`, at most a constant times one that tends to `0` faster than
every power does so too. -/
private lemma fasterThanPowers_of_le_mul_mic {E G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup G] {f : ℝ → E} {g : ℝ → G} (hf : FasterThanPowers f) (A : ℝ)
    (hgf : ∀ᶠ t in atTop, ‖g t‖ ≤ A * ‖f t‖) : FasterThanPowers g :=
  fasterThanPowers_of_norm_le_mic (Asymptotics.SuperpolynomialDecay.const_mul hf A) hgf

/-- If `f` tends to `0` faster than every power of `1/t`, then `‖f(t)‖ ≤ (1/t)^M` for large `t`. -/
private lemma eventually_norm_le_inv_pow_mic {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (h : FasterThanPowers f) (M : ℕ) : ∀ᶠ t in atTop, ‖f t‖ ≤ t⁻¹ ^ M := by
  have h1 : ∀ᶠ t in atTop, t ^ M * ‖f t‖ ≤ 1 :=
    ((fasterThanPowers_iff f).1 h M).eventually (Iic_mem_nhds zero_lt_one)
  filter_upwards [h1, eventually_gt_atTop 0] with t ht ht0
  calc ‖f t‖ = (t ^ M)⁻¹ * (t ^ M * ‖f t‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero M ht0.ne'), one_mul]
    _ ≤ (t ^ M)⁻¹ * 1 := by gcongr
    _ = t⁻¹ ^ M := by rw [mul_one, inv_pow]

/-- A polynomial `∑_{j<M} q_j w^j` that is `O(|w|^M)` along `w → 0` with `w ≠ 0` has only zero
coefficients (uniqueness of the asymptotic expansion). -/
private lemma eq_zero_of_norm_sum_le_mic {α : Type*} {L : Filter α} [L.NeBot] {w : α → ℂ}
    (hw : Tendsto w L (𝓝 0)) (hw0 : ∀ᶠ x in L, w x ≠ 0) :
    ∀ (M : ℕ) (q : ℕ → ℂ) (C : ℝ),
      (∀ᶠ x in L, ‖∑ j ∈ Finset.range M, q j * w x ^ j‖ ≤ C * ‖w x‖ ^ M) → ∀ j < M, q j = 0
  | 0, _, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | M + 1, q, C, h, j, hj => by
    -- the constant term is the limit of the polynomial along `w → 0`, which is `0`
    have hcont : Continuous fun y : ℂ => ∑ j ∈ Finset.range (M + 1), q j * y ^ j := by
      fun_prop
    have hT : Tendsto (fun x => ∑ j ∈ Finset.range (M + 1), q j * w x ^ j) L (𝓝 (q 0)) :=
      (hcont.tendsto' 0 (q 0) (by simp [Finset.sum_range_succ'])).comp hw
    have hb : Tendsto (fun x => C * ‖w x‖ ^ (M + 1)) L (𝓝 0) := by
      have h1 := (hw.norm.pow (M + 1)).const_mul C
      rwa [norm_zero, zero_pow (Nat.succ_ne_zero M), mul_zero] at h1
    have hZ : Tendsto (fun x => ∑ j ∈ Finset.range (M + 1), q j * w x ^ j) L (𝓝 0) :=
      squeeze_zero_norm' h hb
    have h0 : q 0 = 0 := tendsto_nhds_unique hT hZ
    -- divided by `w`, the remaining polynomial is `O(|w|^M)`
    have h' : ∀ᶠ x in L, ‖∑ j ∈ Finset.range M, q (j + 1) * w x ^ j‖ ≤ C * ‖w x‖ ^ M := by
      filter_upwards [h, hw0] with x hx hx0
      have hsum : ∑ j ∈ Finset.range (M + 1), q j * w x ^ j
          = w x * ∑ j ∈ Finset.range M, q (j + 1) * w x ^ j := by
        rw [Finset.sum_range_succ', h0, zero_mul, add_zero, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsum, norm_mul] at hx
      have hpos : 0 < ‖w x‖ := norm_pos_iff.2 hx0
      refine le_of_mul_le_mul_left ?_ hpos
      calc ‖w x‖ * ‖∑ j ∈ Finset.range M, q (j + 1) * w x ^ j‖ ≤ C * ‖w x‖ ^ (M + 1) := hx
        _ = ‖w x‖ * (C * ‖w x‖ ^ M) := by ring
    cases j with
    | zero => exact h0
    | succ j => exact eq_zero_of_norm_sum_le_mic hw hw0 M (fun i => q (i + 1)) C h' j (by omega)

/-- The coefficients of `∑_{i<m} c_i w^{e+2i+1}` as a polynomial in `w`. -/
private def oddShift_mic (e : ℕ) (c : ℕ → ℂ) (j : ℕ) : ℂ :=
  if e < j ∧ (j - e - 1) % 2 = 0 then c ((j - e - 1) / 2) else 0

private lemma oddShift_odd_mic (e : ℕ) (c : ℕ → ℂ) (i : ℕ) :
    oddShift_mic e c (e + 2 * i + 1) = c i := by
  have h1 : e < e + 2 * i + 1 ∧ (e + 2 * i + 1 - e - 1) % 2 = 0 := by omega
  have h2 : (e + 2 * i + 1 - e - 1) / 2 = i := by omega
  rw [oddShift_mic, ite_eq_left h1, h2]

private lemma oddShift_even_mic (e : ℕ) (c : ℕ → ℂ) (i : ℕ) :
    oddShift_mic e c (e + 2 * i + 2) = 0 := by
  have h1 : ¬(e < e + 2 * i + 2 ∧ (e + 2 * i + 2 - e - 1) % 2 = 0) := by omega
  rw [oddShift_mic, ite_eq_right h1]

private lemma oddShift_of_le_mic (e : ℕ) (c : ℕ → ℂ) {j : ℕ} (hj : j ≤ e) :
    oddShift_mic e c j = 0 := by
  have h1 : ¬(e < j ∧ (j - e - 1) % 2 = 0) := by omega
  rw [oddShift_mic, ite_eq_right h1]

/-- `∑_{i<m} c_i w^{e+2i+1} = ∑_{j<e+2m+1} d_j w^j` with `d = oddShift_mic e c`. -/
private lemma sum_oddShift_mic (e : ℕ) (c : ℕ → ℂ) (y : ℂ) (m : ℕ) :
    ∑ i ∈ Finset.range m, c i * y ^ (e + 2 * i + 1) =
      ∑ j ∈ Finset.range (e + 2 * m + 1), oddShift_mic e c j * y ^ j := by
  induction m with
  | zero =>
    rw [Finset.sum_range_zero, eq_comm]
    exact Finset.sum_eq_zero fun j hj => by
      rw [oddShift_of_le_mic e c (by rw [Finset.mem_range] at hj; omega), zero_mul]
  | succ m ih =>
    have hR : ∑ j ∈ Finset.range (e + 2 * (m + 1) + 1), oddShift_mic e c j * y ^ j =
        ∑ j ∈ Finset.range (e + 2 * m + 1), oddShift_mic e c j * y ^ j
          + oddShift_mic e c (e + 2 * m + 1) * y ^ (e + 2 * m + 1)
          + oddShift_mic e c (e + 2 * m + 2) * y ^ (e + 2 * m + 2) := by
      rw [show e + 2 * (m + 1) + 1 = e + 2 * m + 2 + 1 by ring,
        Finset.sum_range_succ _ (e + 2 * m + 2), show e + 2 * m + 2 = e + 2 * m + 1 + 1 by ring,
        Finset.sum_range_succ _ (e + 2 * m + 1)]
    rw [hR, oddShift_odd_mic, oddShift_even_mic, Finset.sum_range_succ _ m, ih, zero_mul,
      add_zero]

/-- The coefficient `(−1)^i (2i−1)!!` of `w^{2i+1}` in the expansion of `mr(1/w)`. -/
private noncomputable def millsCoeffC_mic (i : ℕ) : ℂ :=
  (-1 : ℂ) ^ i * (Nat.doubleFactorial (2 * i - 1) : ℂ)

/-- `l! ≤ (2l−1)!!`. -/
private lemma factorial_le_doubleFactorial_mic :
    ∀ l : ℕ, Nat.factorial l ≤ Nat.doubleFactorial (2 * l - 1)
  | 0 => le_rfl
  | 1 => le_rfl
  | l + 2 => by
    have h := factorial_le_doubleFactorial_mic (l + 1)
    rw [show 2 * (l + 2) - 1 = 2 * (l + 1) - 1 + 2 by omega, Nat.doubleFactorial_add_two,
      Nat.factorial_succ]
    exact Nat.mul_le_mul (by omega) h

/-- `(2l−1)!! x^{2l}` is unbounded for `x > 0`: "the numbers `(2l−1)!!` grow faster than every
geometric sequence". -/
private lemma exists_lt_doubleFactorial_mul_pow_mic {x R : ℝ} (hx : 0 < x) (hR : 0 < R) (C : ℝ) :
    ∃ l : ℕ, C < (Nat.doubleFactorial (2 * l - 1) : ℝ) * x ^ (2 * l) * R := by
  rcases le_or_gt C 0 with hC | hC
  · exact ⟨0, by simp; linarith⟩
  -- `(1/x²)^l / l! → 0`, so `C < l! x^{2l} R` for some `l`
  obtain ⟨l, hl⟩ := ((FloorSemiring.tendsto_pow_div_factorial_atTop ((x ^ 2)⁻¹)).eventually
    (gt_mem_nhds (div_pos hR hC))).exists
  refine ⟨l, ?_⟩
  have hf : (0 : ℝ) < Nat.factorial l := by exact_mod_cast Nat.factorial_pos l
  have hd : (Nat.factorial l : ℝ) ≤ Nat.doubleFactorial (2 * l - 1) := by
    exact_mod_cast factorial_le_doubleFactorial_mic l
  have hx2 : 0 < x ^ (2 * l) := pow_pos hx _
  rw [div_lt_div_iff₀ hf hC] at hl
  have h1 : (x ^ 2)⁻¹ ^ l * x ^ (2 * l) = 1 := by
    rw [inv_pow, ← pow_mul, inv_mul_cancel₀ (pow_ne_zero _ hx.ne')]
  calc C = (x ^ 2)⁻¹ ^ l * C * x ^ (2 * l) := by
        rw [mul_comm _ C, mul_assoc, h1, mul_one]
    _ < R * Nat.factorial l * x ^ (2 * l) := mul_lt_mul_of_pos_right hl hx2
    _ ≤ R * Nat.doubleFactorial (2 * l - 1) * x ^ (2 * l) := by gcongr
    _ = _ := by ring

/-- Taylor's formula at `0` for a complex function with the power series `p`. -/
private lemma norm_sub_sum_coeff_le_mic {K : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt K p 0) (N : ℕ) :
    ∃ C, ∀ᶠ y in 𝓝 (0 : ℂ), ‖K y - ∑ j ∈ Finset.range N, p.coeff j * y ^ j‖ ≤ C * ‖y‖ ^ N := by
  obtain ⟨C, hC⟩ := (hp.isBigO_sub_partialSum_pow N).bound
  refine ⟨C, hC.mono fun y hy => ?_⟩
  have hsum : p.partialSum N y = ∑ j ∈ Finset.range N, p.coeff j * y ^ j :=
    Finset.sum_congr rfl fun j _ => by
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  simpa only [zero_add, hsum, norm_pow, norm_norm] using hy

/-- **The uniqueness and divergence step of Lemma D.9.** Along a filter on which `w → 0` with
`w ≠ 0`, a function `Φ` cannot have both the expansion `w^e Φ = K(w) + O(|w|^M)` (every `M`) with
`K` holomorphic at `0`, and the expansion `w^e Φ = ∑_{i<m} (−1)^i (2i−1)!! w^{e+2i+1} +
O(|w|^{e+2m+1})` (every `m`) of Lemma D.8 (ii). -/
private lemma false_of_expansions_mic {α : Type*} {L : Filter α} [L.NeBot] {w Φ : α → ℂ}
    (hw : Tendsto w L (𝓝 0)) (hw0 : ∀ᶠ x in L, w x ≠ 0) (e : ℕ) {K : ℂ → ℂ}
    (hK : AnalyticAt ℂ K 0)
    (hA : ∀ M : ℕ, ∃ C, ∀ᶠ x in L, ‖w x ^ e * Φ x - K (w x)‖ ≤ C * ‖w x‖ ^ M)
    (hB : ∀ m : ℕ, ∃ C, ∀ᶠ x in L,
      ‖w x ^ e * Φ x - ∑ i ∈ Finset.range m, millsCoeffC_mic i * w x ^ (e + 2 * i + 1)‖
        ≤ C * ‖w x‖ ^ (e + 2 * m + 1)) : False := by
  obtain ⟨p, hp⟩ := hK
  -- "Asymptotic expansions are unique, so the two series have the same coefficients":
  -- the Taylor coefficient of `K` of order `e + 2l + 1` is `(−1)^l (2l−1)!!`
  have hcoef : ∀ l, p.coeff (e + 2 * l + 1) = millsCoeffC_mic l := by
    intro l
    obtain ⟨C₁, hC₁⟩ := norm_sub_sum_coeff_le_mic hp (e + 2 * (l + 1) + 1)
    obtain ⟨C₂, hC₂⟩ := hA (e + 2 * (l + 1) + 1)
    obtain ⟨C₃, hC₃⟩ := hB (l + 1)
    have hq := eq_zero_of_norm_sum_le_mic hw hw0 (e + 2 * (l + 1) + 1)
      (fun j => p.coeff j - oddShift_mic e millsCoeffC_mic j) (C₁ + C₂ + C₃) ?_
      (e + 2 * l + 1) (by omega)
    · rw [oddShift_odd_mic] at hq
      exact sub_eq_zero.1 hq
    filter_upwards [hw.eventually hC₁, hC₂, hC₃] with x h1 h2 h3
    rw [sum_oddShift_mic] at h3
    have hsplit : ∑ j ∈ Finset.range (e + 2 * (l + 1) + 1),
          (p.coeff j - oddShift_mic e millsCoeffC_mic j) * w x ^ j
        = -(K (w x) - ∑ j ∈ Finset.range (e + 2 * (l + 1) + 1), p.coeff j * w x ^ j)
          - (w x ^ e * Φ x - K (w x))
          + (w x ^ e * Φ x - ∑ j ∈ Finset.range (e + 2 * (l + 1) + 1),
              oddShift_mic e millsCoeffC_mic j * w x ^ j) := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    have tri : ∀ a b c : ℂ, ‖-a - b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := fun a b c => by
      have e1 := norm_add_le (-a - b) c
      have e2 := norm_sub_le (-a) b
      rw [norm_neg] at e2
      linarith
    rw [hsplit]
    refine (tri _ _ _).trans ?_
    rw [add_mul, add_mul]
    linarith
  -- the radius of convergence of `p` is positive: `|P_n| r^n ≤ C` for some `r > 0`
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.radius_pos
  obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius hr
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  -- "But the numbers `(2l−1)!!` grow faster than every geometric sequence"
  obtain ⟨l, hl⟩ := exists_lt_doubleFactorial_mul_pow_mic hr0' (pow_pos hr0' (e + 1)) C
  have h1 := hC (e + 2 * l + 1)
  rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, hcoef l] at h1
  have h2 : ‖millsCoeffC_mic l‖ * (r : ℝ) ^ (e + 2 * l + 1)
      = (Nat.doubleFactorial (2 * l - 1) : ℝ) * (r : ℝ) ^ (2 * l) * (r : ℝ) ^ (e + 1) := by
    rw [millsCoeffC_mic, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast]
    ring
  linarith

/-- The explicit inverse of `s ↦ s / (ω + ω' s²)`: `S(w) = w S₁(w)` with
`S₁(w) = 2ω / (1 + √(1 − 4ωω'w²))`, holomorphic at `0` with `S₁(0) = ω`; along the curve
`w = 1/(T σ)`, `σ = ω + ω'/T²`, it is `S₁(w) = σ`. -/
private lemma exists_invFactor_mic {ω : ℂ} (hω0 : ω ≠ 0) (ω' : ℂ) :
    ∃ S₁ : ℂ → ℂ, AnalyticAt ℂ S₁ 0 ∧ S₁ 0 = ω ∧
      ∀ T : ℂ, T ≠ 0 → ω + ω' * T⁻¹ ^ 2 ≠ 0 →
        0 < ((2 * ω - (ω + ω' * T⁻¹ ^ 2)) / (ω + ω' * T⁻¹ ^ 2)).re →
          S₁ (T * (ω + ω' * T⁻¹ ^ 2))⁻¹ = ω + ω' * T⁻¹ ^ 2 := by
  refine ⟨fun y => 2 * ω / (1 + (1 - 4 * ω * ω' * y ^ 2) ^ (2⁻¹ : ℂ)), ?_, ?_, ?_⟩
  · have h1 : AnalyticAt ℂ (fun y : ℂ => 1 - 4 * ω * ω' * y ^ 2) 0 :=
      analyticAt_const.fun_sub (analyticAt_const.fun_mul (analyticAt_id.fun_pow 2))
    have hs : (fun y : ℂ => 1 - 4 * ω * ω' * y ^ 2) 0 ∈ Complex.slitPlane := by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero]
      exact Complex.one_mem_slitPlane
    have h2 : AnalyticAt ℂ (fun y : ℂ => 1 + (1 - 4 * ω * ω' * y ^ 2) ^ (2⁻¹ : ℂ)) 0 :=
      analyticAt_const.fun_add (h1.cpow analyticAt_const hs)
    have h3 : (fun y : ℂ => 1 + (1 - 4 * ω * ω' * y ^ 2) ^ (2⁻¹ : ℂ)) 0 ≠ 0 := by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero,
        Complex.one_cpow]
      norm_num
    exact analyticAt_const.fun_div h2 h3
  · norm_num
  · intro T hT hσ hre
    have h' : ω' * T⁻¹ ^ 2 = (ω + ω' * T⁻¹ ^ 2) - ω := by ring
    show 2 * ω / (1 + (1 - 4 * ω * ω' * ((T * (ω + ω' * T⁻¹ ^ 2))⁻¹) ^ 2) ^ (2⁻¹ : ℂ)) = _
    generalize ω + ω' * T⁻¹ ^ 2 = σ at hσ hre h' ⊢
    -- `1 − 4ωω'w² = ((2ω − σ)/σ)²` on the curve
    have h1 : 1 - 4 * ω * ω' * ((T * σ)⁻¹) ^ 2 = ((2 * ω - σ) / σ) ^ 2 := by
      calc 1 - 4 * ω * ω' * ((T * σ)⁻¹) ^ 2 = 1 - 4 * ω * (ω' * T⁻¹ ^ 2) / σ ^ 2 := by
            rw [mul_inv, mul_pow]; ring
        _ = ((2 * ω - σ) / σ) ^ 2 := by rw [h']; field_simp; ring
    rw [h1, Complex.sq_cpow_two_inv hre]
    have h2 : 1 + (2 * ω - σ) / σ = 2 * ω / σ := by field_simp; ring
    rw [h2]
    field_simp

/-- **Lemma D.9 (the Mills ratio at infinity), for complex `ω`, `ω'` with `Re ω > 0`.** If `Θ₁`
and `Θ₂` are meromorphic at infinity and `Θ₁(t) mr(ω t + ω'/t) + Θ₂(t)` tends to `0` faster than
every power of `1/t`, then `Θ₁` and `Θ₂` vanish for all large `t`. -/
theorem eventually_eq_zero_of_millsRatioC_smul_add {ω ω' : ℂ} (hω : 0 < ω.re) {Θ₁ Θ₂ : ℝ → F}
    (h₁ : MeromorphicAtInfinityC Θ₁) (h₂ : MeromorphicAtInfinityC Θ₂)
    (h : FasterThanPowers fun t : ℝ =>
      millsRatioC (ω * (t : ℂ) + ω' / (t : ℂ)) • Θ₁ t + Θ₂ t) :
    (∀ᶠ t in atTop, Θ₁ t = 0) ∧ ∀ᶠ t in atTop, Θ₂ t = 0 := by
  sorry

end Skips
