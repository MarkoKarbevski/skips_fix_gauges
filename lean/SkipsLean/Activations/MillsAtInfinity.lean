import SkipsLean.Activations.FarFromZero
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Maps that are meromorphic at infinity, and the Mills ratio

Paper (dimension): Appendix D.5, after Lemma D.8, and Lemma D.9.

* "We say that a map `Θ` on an interval `(t₀, ∞)` is meromorphic at infinity if
  `Θ(t) = t^l Θ₀(1/t)` for an integer `l` and a map `Θ₀` that is holomorphic near `0`. Such a map
  vanishes identically if it tends to `0` faster than every power of `1/t`."
* Lemma D.9 (The Mills ratio at infinity): "Let `z(t) = ω t + ω'/t` with `ω, ω' ∈ ℂ` and
  `Re ω > 0`, and let `Θ₁` and `Θ₂` be meromorphic at infinity, with values in `ℂ^{1×d_out}`. If
  `Θ₁(t) mr(z(t)) + Θ₂(t)` tends to `0` faster than every power of `1/t` as `t → +∞`, then
  `Θ₁ = 0` and `Θ₂ = 0`."

Stated here for a real variable: `Θ₀` is real-analytic at `0`, the values lie in a real normed
space, and in Lemma D.9 `ω > 0` is real and `ω' = 0`, so `z(t) = ω t`. This is the form that the
proof of Lemma D.12 uses in the cases (n) and (+). The case of complex `ω`, `ω'`:
`Activations/MillsAtInfinityC.lean`. A negative exponent `l` is not needed: `t^{-l} Θ₀(1/t)` is
`Θ̃₀(1/t)` with `Θ̃₀(s) = s^l Θ₀(s)`. "`Θ = 0`" is stated as "`Θ(t) = 0` for all large `t`", which
is what the definition, an equation for large `t`, can give.
-/

namespace Skips

open Filter Topology Asymptotics

variable {F : Type*} [NormedAddCommGroup F]

/-- "`f(t)` tends to `0` faster than every power of `1/t` as `t → +∞`": `t^m ‖f(t)‖ → 0` for
every `m`. -/
def FasterThanPowers (f : ℝ → F) : Prop :=
  SuperpolynomialDecay atTop (fun t : ℝ => t) fun t => ‖f t‖

/-- The definition, written out. -/
theorem fasterThanPowers_iff (f : ℝ → F) :
    FasterThanPowers f ↔ ∀ m : ℕ, Tendsto (fun t : ℝ => t ^ m * ‖f t‖) atTop (𝓝 0) := by
  exact Iff.rfl

/-- Two maps that agree for all large `t` tend to `0` faster than every power together. -/
theorem FasterThanPowers.congr {f g : ℝ → F} (hf : FasterThanPowers f)
    (hfg : ∀ᶠ t in atTop, f t = g t) : FasterThanPowers g := by
  exact SuperpolynomialDecay.congr' hf (hfg.mono fun _ ht => congrArg norm ht)

/-- A map whose norm is, for all large `t`, at most a function with superpolynomial decay tends to
`0` faster than every power. -/
private lemma fasterThanPowers_of_norm_le {g : ℝ → F} {u : ℝ → ℝ}
    (hu : SuperpolynomialDecay atTop (fun t : ℝ => t) u) (hg : ∀ᶠ t in atTop, ‖g t‖ ≤ u t) :
    FasterThanPowers g :=
  SuperpolynomialDecay.trans_eventuallyLE (eventually_ge_atTop 0) (superpolynomialDecay_zero _ _)
    hu (Eventually.of_forall fun t => norm_nonneg (g t)) hg

/-- A map that is, for all large `t`, at most as large as one that tends to `0` faster than every
power does so too. -/
theorem FasterThanPowers.mono {G : Type*} [NormedAddCommGroup G] {f : ℝ → F} {g : ℝ → G}
    (hf : FasterThanPowers f) (hgf : ∀ᶠ t in atTop, ‖g t‖ ≤ ‖f t‖) : FasterThanPowers g := by
  exact fasterThanPowers_of_norm_le hf hgf

/-- A sum of two maps that tend to `0` faster than every power does so too. -/
theorem FasterThanPowers.add {f g : ℝ → F} (hf : FasterThanPowers f) (hg : FasterThanPowers g) :
    FasterThanPowers fun t => f t + g t := by
  -- `‖f(t) + g(t)‖ ≤ ‖f(t)‖ + ‖g(t)‖`
  exact fasterThanPowers_of_norm_le (SuperpolynomialDecay.add hf hg)
    (Eventually.of_forall fun t => norm_add_le (f t) (g t))

/-- A map that tends to `0` faster than every power still does after multiplication by a function
that is at most a fixed power of `t`. -/
theorem FasterThanPowers.smul_of_le_pow [NormedSpace ℝ F] {f : ℝ → F} (hf : FasterThanPowers f)
    {c : ℝ → ℝ} {A : ℝ} {N : ℕ} (hc : ∀ᶠ t in atTop, |c t| ≤ A * t ^ N) :
    FasterThanPowers fun t => c t • f t := by
  -- `‖c(t) f(t)‖ ≤ A t^N ‖f(t)‖`, and `A t^N ‖f(t)‖` decays faster than every power
  have hu : SuperpolynomialDecay atTop (fun t : ℝ => t) fun t => A * t ^ N * ‖f t‖ :=
    (SuperpolynomialDecay.const_mul (SuperpolynomialDecay.param_pow_mul hf N) A).congr
      fun t => by simp only [Pi.mul_apply, Pi.pow_apply]; ring
  refine fasterThanPowers_of_norm_le hu (hc.mono fun t ht => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)

/-- `e^{-κ t^p}` decays faster than every power of `1/t`, for `κ > 0` and `p ≥ 1`. -/
private lemma superpolynomialDecay_exp_neg {κ : ℝ} {p : ℕ} (hκ : 0 < κ) (hp : 1 ≤ p) :
    SuperpolynomialDecay atTop (fun t : ℝ => t) fun t => Real.exp (-(κ * t ^ p)) := by
  -- `t^n e^{-κ t} → 0`
  have hexp : SuperpolynomialDecay atTop (fun t : ℝ => t) fun t => Real.exp (-κ * t) := fun n =>
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero n κ hκ).congr fun t => by
      simp only [Real.rpow_natCast]
  refine SuperpolynomialDecay.trans_eventuallyLE (eventually_ge_atTop 0)
    (superpolynomialDecay_zero _ _) hexp (Eventually.of_forall fun t => (Real.exp_pos _).le) ?_
  -- `t ≤ t^p` for `t ≥ 1`, so `e^{-κ t^p} ≤ e^{-κ t}`
  filter_upwards [eventually_ge_atTop 1] with t ht
  have h1 : t ≤ t ^ p := le_self_pow₀ ht (by omega)
  show Real.exp (-(κ * t ^ p)) ≤ Real.exp (-κ * t)
  rw [Real.exp_le_exp, neg_mul]
  exact neg_le_neg (mul_le_mul_of_nonneg_left h1 hκ.le)

/-- A map that is at most a fixed power of `t` times `e^{-κ t^p}`, with `κ > 0` and `p ≥ 1`, tends
to `0` faster than every power of `1/t`. -/
theorem fasterThanPowers_of_le_pow_mul_exp {f : ℝ → F} {A κ : ℝ} {N p : ℕ} (hκ : 0 < κ)
    (hp : 1 ≤ p) (hf : ∀ᶠ t in atTop, ‖f t‖ ≤ A * t ^ N * Real.exp (-(κ * t ^ p))) :
    FasterThanPowers f := by
  have hu : SuperpolynomialDecay atTop (fun t : ℝ => t)
      fun t => A * t ^ N * Real.exp (-(κ * t ^ p)) :=
    (SuperpolynomialDecay.const_mul
      (SuperpolynomialDecay.param_pow_mul (superpolynomialDecay_exp_neg hκ hp) N) A).congr
      fun t => by simp only [Pi.mul_apply, Pi.pow_apply]; ring
  exact fasterThanPowers_of_norm_le hu hf

/-- `1/t → 0` as `t → +∞`. -/
private lemma tendsto_one_div_atTop_nhds_zero' : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
  simpa only [one_div] using tendsto_inv_atTop_zero

/-- If `g` tends to `0` faster than every power of `1/t`, then `‖g(1/s)‖ ≤ s^M` for all small
`s > 0`. -/
private lemma eventually_norm_inv_le_pow {g : ℝ → F} (h : FasterThanPowers g) (M : ℕ) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖g s⁻¹‖ ≤ s ^ M := by
  have h1 : ∀ᶠ t in atTop, t ^ M * ‖g t‖ ≤ 1 :=
    ((fasterThanPowers_iff g).1 h M).eventually (Iic_mem_nhds zero_lt_one)
  filter_upwards [tendsto_inv_nhdsGT_zero.eventually h1, self_mem_nhdsWithin]
    with s hs (hs0 : 0 < s)
  rwa [inv_pow, inv_mul_le_iff₀ (pow_pos hs0 M), mul_one] at hs

variable [NormedSpace ℝ F]

/-- "`Θ` is meromorphic at infinity": `Θ(t) = t^l Θ₀(1/t)` for all large `t`, with `Θ₀`
real-analytic at `0`. -/
def MeromorphicAtInfinity (Θ : ℝ → F) : Prop :=
  ∃ (l : ℕ) (Θ₀ : ℝ → F), AnalyticAt ℝ Θ₀ 0 ∧ ∀ᶠ t in atTop, Θ t = t ^ l • Θ₀ (1 / t)

/-- A map that is real-analytic at `0` and whose values at `1/t` tend to `0` faster than every
power of `1/t` vanishes near `0`. -/
theorem eventually_nhds_eq_zero_of_fasterThanPowers {f : ℝ → F} (hf : AnalyticAt ℝ f 0)
    (h : FasterThanPowers fun t => f (1 / t)) : ∀ᶠ s in 𝓝 (0 : ℝ), f s = 0 := by
  by_contra hne
  -- otherwise `f(s) = s^n g(s)` near `0`, with `g` analytic at `0` and `g(0) ≠ 0`
  obtain ⟨n, g, hg, hg0, hfg⟩ := hf.exists_eventuallyEq_pow_smul_ne_zero_iff.2 hne
  have hpos : 0 < ‖g 0‖ := norm_pos_iff.2 hg0
  have hgs : ∀ᶠ s in 𝓝 (0 : ℝ), ‖g 0‖ / 2 < ‖g s‖ :=
    Filter.Tendsto.eventually_const_lt (half_lt_self hpos) hg.continuousAt.norm
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ), s < ‖g 0‖ / 2 := eventually_lt_nhds (half_pos hpos)
  -- then `s^n ‖g(0)‖/2 ≤ ‖f(s)‖ ≤ s^{n+1}` for small `s > 0`, which fails for `s < ‖g(0)‖/2`
  have hF : ∀ᶠ s in 𝓝[>] (0 : ℝ), False := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hfg, nhdsWithin_le_nhds hgs,
      nhdsWithin_le_nhds hsmall, eventually_norm_inv_le_pow h (n + 1)]
      with s (hs0 : 0 < s) hfs hgs' hsm hle
    simp only [one_div, inv_inv] at hle
    rw [hfs, sub_zero, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos hs0, pow_succ] at hle
    have h2 := le_of_mul_le_mul_left hle (pow_pos hs0 n)
    linarith
  obtain ⟨_, hfalse⟩ := hF.exists
  exact hfalse

/-- **"Such a map vanishes identically if it tends to `0` faster than every power of `1/t`."** -/
theorem MeromorphicAtInfinity.eventually_eq_zero {Θ : ℝ → F} (hΘ : MeromorphicAtInfinity Θ)
    (h : FasterThanPowers Θ) : ∀ᶠ t in atTop, Θ t = 0 := by
  obtain ⟨l, Θ₀, hΘ₀, hEq⟩ := hΘ
  -- `‖Θ₀(1/t)‖ ≤ t^l ‖Θ₀(1/t)‖ = ‖Θ(t)‖` for `t ≥ 1`, so `Θ₀(1/t)` tends to `0` faster than
  -- every power
  have h₀ : FasterThanPowers fun t => Θ₀ (1 / t) := by
    refine h.mono ?_
    filter_upwards [hEq, eventually_ge_atTop 1] with t ht ht1
    rw [ht, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ ht1)
  -- so `Θ₀ = 0` near `0`, and `Θ(t) = t^l Θ₀(1/t) = 0` for large `t`
  filter_upwards [hEq, tendsto_one_div_atTop_nhds_zero'.eventually
    (eventually_nhds_eq_zero_of_fasterThanPowers hΘ₀ h₀)] with t ht ht0
  rw [ht, ht0, smul_zero]

/-! ### Helpers for Lemma D.9 -/

/-- A polynomial `∑_{j<M} q_j s^j` that is `O(s^M)` as `s → 0⁺` has only zero coefficients
(uniqueness of the asymptotic expansion). -/
private lemma eq_zero_of_abs_sum_le : ∀ (M : ℕ) (q : ℕ → ℝ) (C : ℝ),
    (∀ᶠ s in 𝓝[>] (0 : ℝ), |∑ j ∈ Finset.range M, q j * s ^ j| ≤ C * s ^ M) →
      ∀ j < M, q j = 0
  | 0, _, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | M + 1, q, C, h, j, hj => by
    -- the constant term is the limit at `0⁺` of the polynomial, which is `0`
    have hcont : Continuous fun s : ℝ => ∑ j ∈ Finset.range (M + 1), q j * s ^ j := by
      fun_prop
    have hT : Tendsto (fun s : ℝ => ∑ j ∈ Finset.range (M + 1), q j * s ^ j) (𝓝[>] 0)
        (𝓝 (q 0)) :=
      (hcont.tendsto' 0 (q 0) (by simp [Finset.sum_range_succ'])).mono_left
        nhdsWithin_le_nhds
    have hb : Tendsto (fun s : ℝ => C * s ^ (M + 1)) (𝓝[>] 0) (𝓝 0) :=
      ((continuous_const.mul (continuous_pow (M + 1))).tendsto' 0 0 (by simp)).mono_left
        nhdsWithin_le_nhds
    have hZ : Tendsto (fun s : ℝ => ∑ j ∈ Finset.range (M + 1), q j * s ^ j) (𝓝[>] 0) (𝓝 0) :=
      squeeze_zero_norm' (h.mono fun s hs => by rwa [Real.norm_eq_abs]) hb
    have h0 : q 0 = 0 := tendsto_nhds_unique hT hZ
    -- divided by `s`, the remaining polynomial is `O(s^M)`
    have h' : ∀ᶠ s in 𝓝[>] (0 : ℝ), |∑ j ∈ Finset.range M, q (j + 1) * s ^ j| ≤ C * s ^ M := by
      filter_upwards [h, self_mem_nhdsWithin] with s hs (hs0 : 0 < s)
      have hsum : ∑ j ∈ Finset.range (M + 1), q j * s ^ j
          = s * ∑ j ∈ Finset.range M, q (j + 1) * s ^ j := by
        rw [Finset.sum_range_succ', h0, zero_mul, add_zero, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsum, abs_mul, abs_of_pos hs0] at hs
      refine le_of_mul_le_mul_left ?_ hs0
      calc s * |∑ j ∈ Finset.range M, q (j + 1) * s ^ j| ≤ C * s ^ (M + 1) := hs
        _ = s * (C * s ^ M) := by ring
    cases j with
    | zero => exact h0
    | succ j => exact eq_zero_of_abs_sum_le M (fun i => q (i + 1)) C h' j (by omega)

/-- The coefficients of `∑_{i<m} c_i s^{e+2i+1}` as a polynomial in `s`. -/
private def oddShift (e : ℕ) (c : ℕ → ℝ) (j : ℕ) : ℝ :=
  if e < j ∧ (j - e - 1) % 2 = 0 then c ((j - e - 1) / 2) else 0

private lemma oddShift_odd (e : ℕ) (c : ℕ → ℝ) (i : ℕ) : oddShift e c (e + 2 * i + 1) = c i := by
  have h1 : e < e + 2 * i + 1 ∧ (e + 2 * i + 1 - e - 1) % 2 = 0 := by omega
  have h2 : (e + 2 * i + 1 - e - 1) / 2 = i := by omega
  rw [oddShift, ite_eq_left h1, h2]

private lemma oddShift_even (e : ℕ) (c : ℕ → ℝ) (i : ℕ) : oddShift e c (e + 2 * i + 2) = 0 := by
  have h1 : ¬(e < e + 2 * i + 2 ∧ (e + 2 * i + 2 - e - 1) % 2 = 0) := by omega
  rw [oddShift, ite_eq_right h1]

private lemma oddShift_of_le (e : ℕ) (c : ℕ → ℝ) {j : ℕ} (hj : j ≤ e) : oddShift e c j = 0 := by
  have h1 : ¬(e < j ∧ (j - e - 1) % 2 = 0) := by omega
  rw [oddShift, ite_eq_right h1]

/-- `∑_{i<m} c_i s^{e+2i+1} = ∑_{j<e+2m+1} d_j s^j` with `d = oddShift e c`. -/
private lemma sum_oddShift (e : ℕ) (c : ℕ → ℝ) (s : ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, c i * s ^ (e + 2 * i + 1) =
      ∑ j ∈ Finset.range (e + 2 * m + 1), oddShift e c j * s ^ j := by
  induction m with
  | zero =>
    rw [Finset.sum_range_zero, eq_comm]
    exact Finset.sum_eq_zero fun j hj => by
      rw [oddShift_of_le e c (by rw [Finset.mem_range] at hj; omega), zero_mul]
  | succ m ih =>
    have hR : ∑ j ∈ Finset.range (e + 2 * (m + 1) + 1), oddShift e c j * s ^ j =
        ∑ j ∈ Finset.range (e + 2 * m + 1), oddShift e c j * s ^ j
          + oddShift e c (e + 2 * m + 1) * s ^ (e + 2 * m + 1)
          + oddShift e c (e + 2 * m + 2) * s ^ (e + 2 * m + 2) := by
      rw [show e + 2 * (m + 1) + 1 = e + 2 * m + 2 + 1 by ring,
        Finset.sum_range_succ _ (e + 2 * m + 2), show e + 2 * m + 2 = e + 2 * m + 1 + 1 by ring,
        Finset.sum_range_succ _ (e + 2 * m + 1)]
    rw [hR, oddShift_odd, oddShift_even, Finset.sum_range_succ _ m, ih, zero_mul, add_zero]

/-- The coefficient `(−1)^i (2i−1)!! / ω^{2i+1}` of the expansion of `mr(ω/s)` in powers of `s`. -/
private noncomputable def millsCoeff (ω : ℝ) (i : ℕ) : ℝ :=
  (-1 : ℝ) ^ i * (Nat.doubleFactorial (2 * i - 1) : ℝ) / ω ^ (2 * i + 1)

/-- Lemma D.8 (ii) at `z = ω/s`, multiplied by `s^e`. -/
private lemma abs_pow_mul_millsRatio_sub_le {ω s : ℝ} (hω : 0 < ω) (hs : 0 < s) (e m : ℕ) :
    |s ^ e * millsRatio (ω * s⁻¹) - ∑ i ∈ Finset.range m, millsCoeff ω i * s ^ (e + 2 * i + 1)|
      ≤ (Nat.doubleFactorial (2 * m - 1) : ℝ) / ω ^ (2 * m + 1) * s ^ (e + 2 * m + 1) := by
  have hz : 0 < ω * s⁻¹ := mul_pos hω (inv_pos.2 hs)
  have h := abs_millsRatio_sub_sum_le hz m
  have hse : 0 < s ^ e := pow_pos hs e
  have hsum : ∑ i ∈ Finset.range m, millsCoeff ω i * s ^ (e + 2 * i + 1)
      = s ^ e * ∑ l ∈ Finset.range m,
          (-1 : ℝ) ^ l * (Nat.doubleFactorial (2 * l - 1) : ℝ) / (ω * s⁻¹) ^ (2 * l + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [millsCoeff, mul_pow, inv_pow, ← div_eq_mul_inv, div_div_eq_mul_div]
    ring
  rw [hsum, ← mul_sub, abs_mul, abs_of_pos hse]
  refine (mul_le_mul_of_nonneg_left h hse.le).trans_eq ?_
  rw [mul_pow, inv_pow, ← div_eq_mul_inv, div_div_eq_mul_div]
  ring

/-- `l! ≤ (2l−1)!!`. -/
private lemma factorial_le_doubleFactorial :
    ∀ l : ℕ, Nat.factorial l ≤ Nat.doubleFactorial (2 * l - 1)
  | 0 => le_rfl
  | 1 => le_rfl
  | l + 2 => by
    have h := factorial_le_doubleFactorial (l + 1)
    rw [show 2 * (l + 2) - 1 = 2 * (l + 1) - 1 + 2 by omega, Nat.doubleFactorial_add_two,
      Nat.factorial_succ]
    exact Nat.mul_le_mul (by omega) h

/-- `(2l−1)!! x^{2l}` is unbounded for `x > 0`: "the numbers `(2l−1)!!` grow faster than every
geometric sequence". -/
private lemma exists_lt_doubleFactorial_mul_pow {x R : ℝ} (hx : 0 < x) (hR : 0 < R) (C : ℝ) :
    ∃ l : ℕ, C < (Nat.doubleFactorial (2 * l - 1) : ℝ) * x ^ (2 * l) * R := by
  rcases le_or_gt C 0 with hC | hC
  · exact ⟨0, by simp; linarith⟩
  -- `(1/x²)^l / l! → 0`, so `C < l! x^{2l} R` for some `l`
  obtain ⟨l, hl⟩ := ((FloorSemiring.tendsto_pow_div_factorial_atTop ((x ^ 2)⁻¹)).eventually
    (gt_mem_nhds (div_pos hR hC))).exists
  refine ⟨l, ?_⟩
  have hf : (0 : ℝ) < Nat.factorial l := by exact_mod_cast Nat.factorial_pos l
  have hd : (Nat.factorial l : ℝ) ≤ Nat.doubleFactorial (2 * l - 1) := by
    exact_mod_cast factorial_le_doubleFactorial l
  have hx2 : 0 < x ^ (2 * l) := pow_pos hx _
  rw [div_lt_div_iff₀ hf hC] at hl
  have h1 : (x ^ 2)⁻¹ ^ l * x ^ (2 * l) = 1 := by
    rw [inv_pow, ← pow_mul, inv_mul_cancel₀ (pow_ne_zero _ hx.ne')]
  calc C = (x ^ 2)⁻¹ ^ l * C * x ^ (2 * l) := by
        rw [mul_comm _ C, mul_assoc, h1, mul_one]
    _ < R * Nat.factorial l * x ^ (2 * l) := mul_lt_mul_of_pos_right hl hx2
    _ ≤ R * Nat.doubleFactorial (2 * l - 1) * x ^ (2 * l) := by gcongr
    _ = _ := by ring

/-- Taylor's formula at `0` for a real function with the power series `p`. -/
private lemma abs_sub_sum_coeff_le {k : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    (hp : HasFPowerSeriesAt k p 0) (M : ℕ) :
    ∃ C, ∀ᶠ s in 𝓝 (0 : ℝ), |k s - ∑ j ∈ Finset.range M, p.coeff j * s ^ j| ≤ C * |s| ^ M := by
  obtain ⟨C, hC⟩ := (hp.isBigO_sub_partialSum_pow M).bound
  refine ⟨C, hC.mono fun s hs => ?_⟩
  have hsum : p.partialSum M s = ∑ j ∈ Finset.range M, p.coeff j * s ^ j :=
    Finset.sum_congr rfl fun j _ => by
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  simp only [zero_add, hsum, Real.norm_eq_abs, abs_pow, abs_abs] at hs
  exact hs

/-- **The scalar core of Lemma D.9.** If `k` is real-analytic at `0`, then
`(1/t)^e mr(ω t) − k(1/t)` does not tend to `0` faster than every power of `1/t`. -/
private lemma not_fasterThanPowers_millsRatio_sub {ω : ℝ} (hω : 0 < ω) (e : ℕ) {k : ℝ → ℝ}
    (hk : AnalyticAt ℝ k 0)
    (h : FasterThanPowers fun t => (1 / t) ^ e * millsRatio (ω * t) - k (1 / t)) : False := by
  -- `|s^e mr(ω/s) − k(s)| ≤ s^M` for small `s > 0`, for every `M`
  have hb : ∀ M : ℕ, ∀ᶠ s in 𝓝[>] (0 : ℝ), |s ^ e * millsRatio (ω * s⁻¹) - k s| ≤ s ^ M := by
    intro M
    filter_upwards [eventually_norm_inv_le_pow h M] with s hs
    simpa only [one_div, inv_inv, Real.norm_eq_abs] using hs
  obtain ⟨p, hp⟩ := hk
  -- "Asymptotic expansions are unique, so the two series have the same coefficients":
  -- the Taylor coefficient of `k` of order `e + 2l + 1` is `(−1)^l (2l−1)!! / ω^{2l+1}`
  have hcoef : ∀ l, p.coeff (e + 2 * l + 1) = millsCoeff ω l := by
    intro l
    obtain ⟨C, hC⟩ := abs_sub_sum_coeff_le hp (e + 2 * (l + 1) + 1)
    have hq := eq_zero_of_abs_sum_le (e + 2 * (l + 1) + 1)
      (fun j => p.coeff j - oddShift e (millsCoeff ω) j)
      (C + 1 + (Nat.doubleFactorial (2 * (l + 1) - 1) : ℝ) / ω ^ (2 * (l + 1) + 1)) ?_
      (e + 2 * l + 1) (by omega)
    · rw [oddShift_odd] at hq
      linarith
    filter_upwards [nhdsWithin_le_nhds hC, hb (e + 2 * (l + 1) + 1), self_mem_nhdsWithin]
      with s hs1 hs2 (hs0 : 0 < s)
    have hs3 := abs_pow_mul_millsRatio_sub_le hω hs0 e (l + 1)
    rw [sum_oddShift] at hs3
    rw [abs_of_pos hs0] at hs1
    have hsplit : ∑ j ∈ Finset.range (e + 2 * (l + 1) + 1),
          (p.coeff j - oddShift e (millsCoeff ω) j) * s ^ j
        = -(k s - ∑ j ∈ Finset.range (e + 2 * (l + 1) + 1), p.coeff j * s ^ j)
          - (s ^ e * millsRatio (ω * s⁻¹) - k s)
          + (s ^ e * millsRatio (ω * s⁻¹) - ∑ j ∈ Finset.range (e + 2 * (l + 1) + 1),
              oddShift e (millsCoeff ω) j * s ^ j) := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    have tri : ∀ a b c : ℝ, |-a - b + c| ≤ |a| + |b| + |c| := fun a b c => by
      have e1 := abs_add_le (-a - b) c
      have e2 := abs_sub (-a) b
      rw [abs_neg] at e2
      linarith
    rw [hsplit]
    refine (tri _ _ _).trans ?_
    rw [add_mul, add_mul, one_mul]
    linarith
  -- the radius of convergence of `p` is positive: `|a_n| r^n ≤ C` for some `r > 0`
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.radius_pos
  obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius hr
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  -- "But the numbers `(2l−1)!!` grow faster than every geometric sequence"
  obtain ⟨l, hl⟩ := exists_lt_doubleFactorial_mul_pow (div_pos hr0' hω)
    (by positivity : (0 : ℝ) < r ^ (e + 1) / ω) C
  have h1 := hC (e + 2 * l + 1)
  rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, hcoef l, Real.norm_eq_abs] at h1
  have h2 : |millsCoeff ω l| * (r : ℝ) ^ (e + 2 * l + 1)
      = (Nat.doubleFactorial (2 * l - 1) : ℝ) * ((r : ℝ) / ω) ^ (2 * l)
          * ((r : ℝ) ^ (e + 1) / ω) := by
    rw [millsCoeff, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast,
      abs_pow, abs_of_pos hω, div_pow]
    ring
  linarith

/-- **Lemma D.9 (the Mills ratio at infinity), for real `ω > 0` and `ω' = 0`.** If `Θ₁` and `Θ₂`
are meromorphic at infinity and `Θ₁(t) mr(ω t) + Θ₂(t)` tends to `0` faster than every power of
`1/t`, then `Θ₁` and `Θ₂` vanish for all large `t`. -/
theorem eventually_eq_zero_of_millsRatio_smul_add {ω : ℝ} (hω : 0 < ω) {Θ₁ Θ₂ : ℝ → F}
    (h₁ : MeromorphicAtInfinity Θ₁) (h₂ : MeromorphicAtInfinity Θ₂)
    (h : FasterThanPowers fun t => millsRatio (ω * t) • Θ₁ t + Θ₂ t) :
    (∀ᶠ t in atTop, Θ₁ t = 0) ∧ ∀ᶠ t in atTop, Θ₂ t = 0 := by
  obtain ⟨l₁, f₁, hf₁, hΘ₁⟩ := h₁
  -- "Suppose that a component of `Θ₁` is not zero": then `f₁(s) = s^n g(s)` near `0` with
  -- `g(0) ≠ 0`, and we take the component `ψ` with `ψ(g(0)) = ‖g(0)‖ ≠ 0`
  have key : ∀ᶠ s in 𝓝 (0 : ℝ), f₁ s = 0 := by
    by_contra hne
    obtain ⟨l₂, f₂, hf₂, hΘ₂⟩ := h₂
    obtain ⟨n, g, hg, hg0, hfg⟩ := hf₁.exists_eventuallyEq_pow_smul_ne_zero_iff.2 hne
    obtain ⟨ψ, hψ1, hψg⟩ := exists_dual_vector ℝ (g 0) (norm_ne_zero_iff.2 hg0)
    have hpos : 0 < ‖g 0‖ := norm_pos_iff.2 hg0
    have hγ : AnalyticAt ℝ (fun s => ψ (g s)) 0 := (ψ.analyticAt (g 0)).comp hg
    have hβ : AnalyticAt ℝ (fun s => ψ (f₂ s)) 0 := (ψ.analyticAt (f₂ 0)).comp hf₂
    have hγ0 : ψ (g 0) ≠ 0 := by rw [hψg]; simpa using hg0
    have hγnear : ∀ᶠ s in 𝓝 (0 : ℝ), ‖g 0‖ / 2 < |ψ (g s)| := by
      have hv : |ψ (g 0)| = ‖g 0‖ := by rw [hψg]; simp
      have ht : Tendsto (fun s => |ψ (g s)|) (𝓝 0) (𝓝 ‖g 0‖) := by
        rw [← hv]; exact hγ.continuousAt.abs
      exact ht.eventually_const_lt (half_lt_self hpos)
    -- the component `φ(t) = mr(ω t) ψ(Θ₁(t)) + ψ(Θ₂(t))` tends to `0` faster than every power
    have hφ : FasterThanPowers fun t => ψ (millsRatio (ω * t) • Θ₁ t + Θ₂ t) :=
      h.mono (Eventually.of_forall fun t => (ψ.le_opNorm _).trans (by rw [hψ1, one_mul]))
    -- multiplied by `(1/t)^{l₁+l₂} / ψ(g(1/t))`, it is `(1/t)^{l₂+n} mr(ω t) − k(1/t)` with
    -- `k(s) = −s^{l₁} ψ(f₂(s)) / ψ(g(s))` analytic at `0`
    have hk : AnalyticAt ℝ (fun s => -(s ^ l₁ * ψ (f₂ s) / ψ (g s))) 0 :=
      (((analyticAt_id.pow l₁).mul hβ).div hγ hγ0).neg
    have hS : FasterThanPowers fun t => (1 / t) ^ (l₂ + n) * millsRatio (ω * t)
        - (fun s => -(s ^ l₁ * ψ (f₂ s) / ψ (g s))) (1 / t) := by
      refine (hφ.smul_of_le_pow (c := fun t => (1 / t) ^ (l₁ + l₂) / ψ (g (1 / t)))
        (A := 2 / ‖g 0‖) (N := 0) ?_).congr ?_
      · filter_upwards [eventually_ge_atTop 1, tendsto_one_div_atTop_nhds_zero'.eventually hγnear]
          with t ht hγt
        have ht0 : 0 < 1 / t := one_div_pos.2 (by linarith)
        have hpow : (1 / t) ^ (l₁ + l₂) ≤ 1 :=
          pow_le_one₀ ht0.le ((div_le_one (by linarith)).2 ht)
        rw [pow_zero, mul_one, abs_div, abs_of_pos (pow_pos ht0 _)]
        calc (1 / t) ^ (l₁ + l₂) / |ψ (g (1 / t))| ≤ 1 / (‖g 0‖ / 2) := by
              gcongr
          _ = 2 / ‖g 0‖ := by ring
      · filter_upwards [eventually_gt_atTop 0, hΘ₁, hΘ₂,
          tendsto_one_div_atTop_nhds_zero'.eventually hfg,
          tendsto_one_div_atTop_nhds_zero'.eventually hγnear] with t ht h1 h2 h3 h4
        have hγt : ψ (g (1 / t)) ≠ 0 := by
          intro h0
          rw [h0, abs_zero] at h4
          linarith
        have hu : ∀ l : ℕ, t ^ l * (1 / t) ^ l = 1 := fun l => by
          rw [← mul_pow, mul_one_div_cancel ht.ne', one_pow]
        have hγinv : ψ (g (1 / t)) * (ψ (g (1 / t)))⁻¹ = 1 := mul_inv_cancel₀ hγt
        simp only [smul_eq_mul, map_add, map_smul, h1, h2, h3, sub_zero]
        linear_combination
          ((1 / t) ^ l₂ * (1 / t) ^ n * millsRatio (ω * t) * (ψ (g (1 / t)) * (ψ (g (1 / t)))⁻¹))
            * hu l₁
          + ((1 / t) ^ l₂ * (1 / t) ^ n * millsRatio (ω * t)) * hγinv
          + ((1 / t) ^ l₁ * ψ (f₂ (1 / t)) * (ψ (g (1 / t)))⁻¹) * hu l₂
    exact not_fasterThanPowers_millsRatio_sub hω (l₂ + n) hk hS
  -- "Hence `Θ₁ = 0`"
  have hΘ₁0 : ∀ᶠ t in atTop, Θ₁ t = 0 := by
    filter_upwards [hΘ₁, tendsto_one_div_atTop_nhds_zero'.eventually key] with t h1 h2
    rw [h1, h2, smul_zero]
  refine ⟨hΘ₁0, ?_⟩
  -- "then `Θ₂` tends to `0` faster than every power, and `Θ₂ = 0`"
  refine h₂.eventually_eq_zero (h.congr ?_)
  filter_upwards [hΘ₁0] with t ht
  rw [ht, smul_zero, zero_add]

end Skips
