import SkipsLean.Activations.FarFromZero
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

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
proof of Lemma D.12 uses in the cases (n) and (+). The case of complex `ω`, `ω'` is not stated
here. A negative exponent `l` is not needed: `t^{-l} Θ₀(1/t)` is `Θ̃₀(1/t)` with
`Θ̃₀(s) = s^l Θ₀(s)`. "`Θ = 0`" is stated as "`Θ(t) = 0` for all large `t`", which is what the
definition, an equation for large `t`, can give.
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
    FasterThanPowers f ↔ ∀ m : ℕ, Tendsto (fun t : ℝ => t ^ m * ‖f t‖) atTop (𝓝 0) :=
  Iff.rfl

/-- Two maps that agree for all large `t` tend to `0` faster than every power together. -/
theorem FasterThanPowers.congr {f g : ℝ → F} (hf : FasterThanPowers f)
    (hfg : ∀ᶠ t in atTop, f t = g t) : FasterThanPowers g :=
  SuperpolynomialDecay.congr' hf (hfg.mono fun _ ht => congrArg norm ht)

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
    (hf : FasterThanPowers f) (hgf : ∀ᶠ t in atTop, ‖g t‖ ≤ ‖f t‖) : FasterThanPowers g :=
  fasterThanPowers_of_norm_le hf hgf

/-- A sum of two maps that tend to `0` faster than every power does so too. -/
theorem FasterThanPowers.add {f g : ℝ → F} (hf : FasterThanPowers f) (hg : FasterThanPowers g) :
    FasterThanPowers fun t => f t + g t :=
  -- `‖f(t) + g(t)‖ ≤ ‖f(t)‖ + ‖g(t)‖`
  fasterThanPowers_of_norm_le (SuperpolynomialDecay.add hf hg)
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

/-- **Lemma D.9 (the Mills ratio at infinity), for real `ω > 0` and `ω' = 0`.** If `Θ₁` and `Θ₂`
are meromorphic at infinity and `Θ₁(t) mr(ω t) + Θ₂(t)` tends to `0` faster than every power of
`1/t`, then `Θ₁` and `Θ₂` vanish for all large `t`. -/
theorem eventually_eq_zero_of_millsRatio_smul_add {ω : ℝ} (hω : 0 < ω) {Θ₁ Θ₂ : ℝ → F}
    (h₁ : MeromorphicAtInfinity Θ₁) (h₂ : MeromorphicAtInfinity Θ₂)
    (h : FasterThanPowers fun t => millsRatio (ω * t) • Θ₁ t + Θ₂ t) :
    (∀ᶠ t in atTop, Θ₁ t = 0) ∧ ∀ᶠ t in atTop, Θ₂ t = 0 := by
  sorry

end Skips
