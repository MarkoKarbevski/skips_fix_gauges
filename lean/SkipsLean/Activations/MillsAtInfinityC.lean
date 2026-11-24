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

/-- **"Such a map vanishes identically if it tends to `0` faster than every power of `1/t`."** -/
theorem MeromorphicAtInfinityC.eventually_eq_zero {Θ : ℝ → F} (hΘ : MeromorphicAtInfinityC Θ)
    (h : FasterThanPowers Θ) : ∀ᶠ t in atTop, Θ t = 0 := by
  sorry

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
