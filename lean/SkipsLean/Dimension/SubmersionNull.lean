import SkipsLean.Imports

/-!
# The preimage of a null set under a submersion

Paper (skips paper): proof of Lemma A.26, "So `G_X(ℝ^{P'}) ∩ Y` has measure zero in `Y`, and so
does its preimage under `F_X` in `U`" (and the same step in the proof of Lemma A.24). In the Lean
route the constant rank theorem is not used: a linear projection `π` is chosen so that `π ∘ F_X`
has an onto derivative near the point, and this file states the fact that is then needed: the
preimage of a set of measure zero under a continuously differentiable map whose derivative is onto
at every point of an open set has measure zero in that set.
-/

namespace Skips

open MeasureTheory

/-- **The preimage of a null set under a `C¹` submersion is null:** let `f` be continuously
differentiable on the open set `U`, with an onto derivative at every point of `U`. Then for every
set `N` of measure zero in the target, `U ∩ f⁻¹(N)` has measure zero. -/
theorem measure_inter_preimage_eq_zero_of_surjective_fderiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F)
    [ν.IsAddHaarMeasure] (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hsurj : ∀ x ∈ U, Function.Surjective (fderiv ℝ f x)) (N : Set F) (hN : ν N = 0) :
    μ (U ∩ f ⁻¹' N) = 0 := by
  sorry

end Skips
