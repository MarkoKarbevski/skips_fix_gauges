import SkipsLean.Generic.AnalyticZeroSet
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The zero set of an analytic function on a connected open set has measure zero

Paper (dimension paper): Appendix D.7, "The parts together", the case (0): "The sum of the squares
of the minors of this size of the Jacobian of `F_{X*}` is real-analytic on the connected open set
`O_{X*}` and does not vanish at `θ*`, so its zero set has measure zero".

In the case (0) the outputs are real-analytic only on the set of parameters at which no hidden
state vanishes, so the fact of `Generic/AnalyticZeroSet.lean` (for functions analytic on the whole
space) is needed on a connected open set: a real-analytic function on a connected open set that
does not vanish identically vanishes on a set of measure zero.
-/

namespace Skips

open MeasureTheory

/-- **A real-analytic function on a connected open set that is not identically zero vanishes on a
set of measure zero** (for any additive Haar measure of a finite-dimensional real normed space). -/
theorem measure_zeroSet_of_analyticOnNhd_of_isPreconnected {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U) (hUc : IsPreconnected U) {f : E → ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hne : ∃ x ∈ U, f x ≠ 0) :
    μ {x | x ∈ U ∧ f x = 0} = 0 := by
  sorry

end Skips
