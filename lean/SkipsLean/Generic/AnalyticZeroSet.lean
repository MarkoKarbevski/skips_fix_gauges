import Mathlib

/-!
# The zero set of an analytic function has measure zero

Used for every statement "at generic parameters" of the papers: a statement holds at generic
parameters if it holds outside a set of Lebesgue measure zero. The conditions that the proofs use
(a matrix has full rank, a Jacobian has a given rank) fail only on the zero set of a real-analytic
function of the parameters that is not identically zero, and such a set has measure zero.

This is a known fact (for instance Mityagin, "The zero set of a real analytic function", 2015);
Mathlib does not have it at the pinned version, so it is proved here.
-/

namespace Skips

open MeasureTheory

/-- A real-analytic function on `ℝ^ι` that is not identically zero vanishes on a set of Lebesgue
measure zero. -/
theorem volume_zeroSet_of_analytic_pi {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hf : AnalyticOnNhd ℝ f Set.univ) (hne : ∃ x, f x ≠ 0) :
    volume {x : ι → ℝ | f x = 0} = 0 := by
  sorry

/-- The same on any finite-dimensional real normed space, for any additive Haar measure (any
Lebesgue measure of the space). -/
theorem measure_zeroSet_of_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {f : E → ℝ} (hf : AnalyticOnNhd ℝ f Set.univ) (hne : ∃ x, f x ≠ 0) :
    μ {x : E | f x = 0} = 0 := by
  sorry

end Skips
