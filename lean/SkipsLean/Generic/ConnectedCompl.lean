import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Removing a regular zero set of codimension at least two keeps a set connected

Paper (dimension paper): Appendix D.6, proof of Lemma D.20 (The domain): "Removing finitely many
closed submanifolds of codimension at least two, one after the other, from a connected open set
leaves a connected open set".

Here a submanifold of codimension `dim F ≥ 2` is given as the zero set of a map `g` into `F` whose
derivative is onto at every zero (in the proof of Lemma D.20 the submanifolds are of this kind:
"because the derivative with respect to `W_read^ℓ` is onto", "the derivative of `h_ℓ` with respect
to `W_write^ℓ` is onto"). One such set is removed; the proof of Lemma D.20 applies this once per
removal.

The first statement is the topological step: if every point of `Z` in the open connected set `U`
has an open neighbourhood `N ⊆ U` such that `N ∖ Z` is connected, and is a limit of points of
`U ∖ Z`, then `U ∖ Z` is connected.
-/

namespace Skips

open Topology

/-- **Local to global:** let `U` be open and preconnected, and let every point of `Z` in `U` have
an open neighbourhood `N ⊆ U` with `N ∖ Z` preconnected, and lie in the closure of `U ∖ Z`. Then
`U ∖ Z` is preconnected. -/
theorem isPreconnected_diff_of_forall_exists_nhds {α : Type*} [TopologicalSpace α] {U Z : Set α}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hloc : ∀ z ∈ U ∩ Z, ∃ N : Set α, IsOpen N ∧ z ∈ N ∧ N ⊆ U ∧ IsPreconnected (N \ Z))
    (hdense : ∀ z ∈ U ∩ Z, z ∈ closure (U \ Z)) :
    IsPreconnected (U \ Z) := by
  sorry

/-- **Removing a regular zero set of codimension at least two:** let `U` be an open preconnected
subset of a finite-dimensional real normed space `E`, and `g : E → F` a map into a space of
dimension at least two that is strictly differentiable with an onto derivative at every zero of
`g` in `U`. Then `U` without the zeros of `g` is preconnected. -/
theorem isPreconnected_diff_zeroSet_of_surjective {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (hF : 2 ≤ Module.finrank ℝ F) {U : Set E} (hU : IsOpen U)
    (hUc : IsPreconnected U) (g : E → F)
    (hg : ∀ x ∈ U, g x = 0 →
      ∃ g' : E →L[ℝ] F, HasStrictFDerivAt g g' x ∧ Function.Surjective g') :
    IsPreconnected (U \ {x | g x = 0}) := by
  sorry

end Skips
