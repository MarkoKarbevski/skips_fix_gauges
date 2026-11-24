import SkipsLean.Imports

/-!
# Sard's theorem, assumed from the literature

Paper (skips paper): proofs of Lemma A.24 and of Lemma A.26 ("so all its values are critical, and by
Sard's theorem its image has measure zero"). The paper names the theorem and gives no reference.

We rely on the result "if `f : M → N` is a `C^r` map between `C^r` manifolds and
`r > max {0, dim M - dim N}`, then the critical values of `f` form a set of measure zero" from
A. Sard, *The measure of the critical values of differentiable maps*, Bull. Amer. Math. Soc. 48
(1942), 883–890, which is formalized as `SardCriticalValues` below, for real-analytic maps between
two finite-dimensional real normed spaces (a real-analytic map is of class `C^r` for every `r`).
A point is critical if the derivative there is not onto.

It is not proved here, and it is not an axiom: the theorems that use it take it as a hypothesis.
Mathlib (v4.36.0) has the case of equal dimensions
(`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`) and the case of a source of
smaller dimension, not the general one.
-/

namespace Skips

open MeasureTheory

/-- **Sard's theorem for real-analytic maps `E → F`, as a hypothesis from the literature:** the
critical values of a real-analytic map (the images of the points where its derivative is not onto)
form a set of measure zero, for every additive Haar measure of `F`. -/
def SardCriticalValues (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] : Prop :=
  ∀ (μ : Measure F) [μ.IsAddHaarMeasure] (g : E → F), AnalyticOnNhd ℝ g Set.univ →
    μ (g '' {x | ¬ Function.Surjective (fderiv ℝ g x)}) = 0

end Skips
