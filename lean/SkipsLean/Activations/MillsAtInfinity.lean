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
    FasterThanPowers f ↔ ∀ m : ℕ, Tendsto (fun t : ℝ => t ^ m * ‖f t‖) atTop (𝓝 0) := by
  sorry

/-- Two maps that agree for all large `t` tend to `0` faster than every power together. -/
theorem FasterThanPowers.congr {f g : ℝ → F} (hf : FasterThanPowers f)
    (hfg : ∀ᶠ t in atTop, f t = g t) : FasterThanPowers g := by
  sorry

/-- A map that is, for all large `t`, at most as large as one that tends to `0` faster than every
power does so too. -/
theorem FasterThanPowers.mono {G : Type*} [NormedAddCommGroup G] {f : ℝ → F} {g : ℝ → G}
    (hf : FasterThanPowers f) (hgf : ∀ᶠ t in atTop, ‖g t‖ ≤ ‖f t‖) : FasterThanPowers g := by
  sorry

/-- A sum of two maps that tend to `0` faster than every power does so too. -/
theorem FasterThanPowers.add {f g : ℝ → F} (hf : FasterThanPowers f) (hg : FasterThanPowers g) :
    FasterThanPowers fun t => f t + g t := by
  sorry

/-- A map that tends to `0` faster than every power still does after multiplication by a function
that is at most a fixed power of `t`. -/
theorem FasterThanPowers.smul_of_le_pow [NormedSpace ℝ F] {f : ℝ → F} (hf : FasterThanPowers f)
    {c : ℝ → ℝ} {A : ℝ} {N : ℕ} (hc : ∀ᶠ t in atTop, |c t| ≤ A * t ^ N) :
    FasterThanPowers fun t => c t • f t := by
  sorry

/-- A map that is at most a fixed power of `t` times `e^{-κ t^p}`, with `κ > 0` and `p ≥ 1`, tends
to `0` faster than every power of `1/t`. -/
theorem fasterThanPowers_of_le_pow_mul_exp {f : ℝ → F} {A κ : ℝ} {N p : ℕ} (hκ : 0 < κ)
    (hp : 1 ≤ p) (hf : ∀ᶠ t in atTop, ‖f t‖ ≤ A * t ^ N * Real.exp (-(κ * t ^ p))) :
    FasterThanPowers f := by
  sorry

variable [NormedSpace ℝ F]

/-- "`Θ` is meromorphic at infinity": `Θ(t) = t^l Θ₀(1/t)` for all large `t`, with `Θ₀`
real-analytic at `0`. -/
def MeromorphicAtInfinity (Θ : ℝ → F) : Prop :=
  ∃ (l : ℕ) (Θ₀ : ℝ → F), AnalyticAt ℝ Θ₀ 0 ∧ ∀ᶠ t in atTop, Θ t = t ^ l • Θ₀ (1 / t)

/-- A map that is real-analytic at `0` and whose values at `1/t` tend to `0` faster than every
power of `1/t` vanishes near `0`. -/
theorem eventually_nhds_eq_zero_of_fasterThanPowers {f : ℝ → F} (hf : AnalyticAt ℝ f 0)
    (h : FasterThanPowers fun t => f (1 / t)) : ∀ᶠ s in 𝓝 (0 : ℝ), f s = 0 := by
  sorry

/-- **"Such a map vanishes identically if it tends to `0` faster than every power of `1/t`."** -/
theorem MeromorphicAtInfinity.eventually_eq_zero {Θ : ℝ → F} (hΘ : MeromorphicAtInfinity Θ)
    (h : FasterThanPowers Θ) : ∀ᶠ t in atTop, Θ t = 0 := by
  sorry

/-- **Lemma D.9 (the Mills ratio at infinity), for real `ω > 0` and `ω' = 0`.** If `Θ₁` and `Θ₂`
are meromorphic at infinity and `Θ₁(t) mr(ω t) + Θ₂(t)` tends to `0` faster than every power of
`1/t`, then `Θ₁` and `Θ₂` vanish for all large `t`. -/
theorem eventually_eq_zero_of_millsRatio_smul_add {ω : ℝ} (hω : 0 < ω) {Θ₁ Θ₂ : ℝ → F}
    (h₁ : MeromorphicAtInfinity Θ₁) (h₂ : MeromorphicAtInfinity Θ₂)
    (h : FasterThanPowers fun t => millsRatio (ω * t) • Θ₁ t + Θ₂ t) :
    (∀ᶠ t in atTop, Θ₁ t = 0) ∧ ∀ᶠ t in atTop, Θ₂ t = 0 := by
  sorry

end Skips
