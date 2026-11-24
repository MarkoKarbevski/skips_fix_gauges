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
