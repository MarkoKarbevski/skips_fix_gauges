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

/-- The points of `U` that go to the side `u`: those of `U ∖ Z` in `u`, and those of `U ∩ Z` with
an open neighbourhood `N ⊆ U` such that `N ∖ Z ⊆ u`. -/
private def side_cc {α : Type*} [TopologicalSpace α] (U Z u : Set α) : Set α :=
  {x | x ∈ U \ Z ∧ x ∈ u} ∪ {z | z ∈ U ∩ Z ∧ ∃ N : Set α, IsOpen N ∧ z ∈ N ∧ N ⊆ U ∧ N \ Z ⊆ u}

/-- A side is open. -/
private lemma isOpen_side_cc {α : Type*} [TopologicalSpace α] {U Z u : Set α} (hU : IsOpen U)
    (hu : IsOpen u) : IsOpen (side_cc U Z u) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x (⟨hxUZ, hxu⟩ | ⟨-, N, hN, hxN, hNU, hNu⟩)
  · -- a point off `Z`: the open set `U ∩ u` lies in the side
    refine ⟨U ∩ u, fun y hy => ?_, hU.inter hu, hxUZ.1, hxu⟩
    by_cases hyZ : y ∈ Z
    · exact Or.inr ⟨⟨hy.1, hyZ⟩, U ∩ u, hU.inter hu, hy, Set.inter_subset_left,
        fun w hw => hw.1.2⟩
    · exact Or.inl ⟨⟨hy.1, hyZ⟩, hy.2⟩
  · -- a point of `Z`: its neighbourhood `N` lies in the side
    refine ⟨N, fun y hyN => ?_, hN, hxN⟩
    by_cases hyZ : y ∈ Z
    · exact Or.inr ⟨⟨hNU hyN, hyZ⟩, N, hN, hyN, hNU, hNu⟩
    · exact Or.inl ⟨⟨hNU hyN, hyZ⟩, hNu ⟨hyN, hyZ⟩⟩

/-- A point in both sides, and in the closure of `U ∖ Z` if it is in `Z`, gives a point of
`U ∖ Z` in `u ∩ v`. -/
private lemma nonempty_of_mem_side_cc {α : Type*} [TopologicalSpace α] {U Z u v : Set α} {x : α}
    (hxu : x ∈ side_cc U Z u) (hxv : x ∈ side_cc U Z v)
    (hcl : x ∈ U ∩ Z → x ∈ closure (U \ Z)) : ((U \ Z) ∩ (u ∩ v)).Nonempty := by
  rcases hxu with ⟨h1, h2⟩ | ⟨h1, N₁, hN₁, hxN₁, -, hN₁u⟩
  · rcases hxv with ⟨-, h3⟩ | ⟨h3, -⟩
    · exact ⟨x, h1, h2, h3⟩
    · exact absurd h3.2 h1.2
  · rcases hxv with ⟨h3, -⟩ | ⟨-, N₂, hN₂, hxN₂, -, hN₂v⟩
    · exact absurd h1.2 h3.2
    · -- `N₁ ∩ N₂` is an open neighbourhood of `x`, so it meets `U ∖ Z`
      obtain ⟨y, hyN, hyUZ⟩ :=
        mem_closure_iff.1 (hcl h1) (N₁ ∩ N₂) (hN₁.inter hN₂) ⟨hxN₁, hxN₂⟩
      exact ⟨y, hyUZ, hN₁u ⟨hyN.1, hyUZ.2⟩, hN₂v ⟨hyN.2, hyUZ.2⟩⟩

/-- If `U ∖ Z ⊆ u ∪ v` does not meet `u ∩ v`, the two sides cover `U`. -/
private lemma subset_side_union_cc {α : Type*} [TopologicalSpace α] {U Z u v : Set α}
    (hloc : ∀ z ∈ U ∩ Z, ∃ N : Set α, IsOpen N ∧ z ∈ N ∧ N ⊆ U ∧ IsPreconnected (N \ Z))
    (hu : IsOpen u) (hv : IsOpen v) (huv : U \ Z ⊆ u ∪ v)
    (hne : ¬((U \ Z) ∩ (u ∩ v)).Nonempty) : U ⊆ side_cc U Z u ∪ side_cc U Z v := by
  intro x hxU
  by_cases hxZ : x ∈ Z
  · obtain ⟨N, hN, hxN, hNU, hNc⟩ := hloc x ⟨hxU, hxZ⟩
    have hNuv : N \ Z ⊆ u ∪ v := fun y hy => huv ⟨hNU hy.1, hy.2⟩
    by_cases hNv : ((N \ Z) ∩ v).Nonempty
    · -- `N ∖ Z` meets `v`; being preconnected, it does not meet `u`, so it lies in `v`
      have hNu : ¬((N \ Z) ∩ u).Nonempty := fun hNu' => hne <| by
        obtain ⟨y, hy, hyuv⟩ := hNc u v hu hv hNuv hNu' hNv
        exact ⟨y, ⟨hNU hy.1, hy.2⟩, hyuv⟩
      refine Or.inr (Or.inr ⟨⟨hxU, hxZ⟩, N, hN, hxN, hNU, fun y hy => ?_⟩)
      rcases hNuv hy with h | h
      · exact absurd ⟨y, hy, h⟩ hNu
      · exact h
    · -- `N ∖ Z` does not meet `v`, so it lies in `u`
      refine Or.inl (Or.inr ⟨⟨hxU, hxZ⟩, N, hN, hxN, hNU, fun y hy => ?_⟩)
      rcases hNuv hy with h | h
      · exact h
      · exact absurd ⟨y, hy, h⟩ hNv
  · rcases huv ⟨hxU, hxZ⟩ with h | h
    · exact Or.inl (Or.inl ⟨⟨hxU, hxZ⟩, h⟩)
    · exact Or.inr (Or.inl ⟨⟨hxU, hxZ⟩, h⟩)

/-- **Local to global:** let `U` be open and preconnected, and let every point of `Z` in `U` have
an open neighbourhood `N ⊆ U` with `N ∖ Z` preconnected, and lie in the closure of `U ∖ Z`. Then
`U ∖ Z` is preconnected. -/
theorem isPreconnected_diff_of_forall_exists_nhds {α : Type*} [TopologicalSpace α] {U Z : Set α}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hloc : ∀ z ∈ U ∩ Z, ∃ N : Set α, IsOpen N ∧ z ∈ N ∧ N ⊆ U ∧ IsPreconnected (N \ Z))
    (hdense : ∀ z ∈ U ∩ Z, z ∈ closure (U \ Z)) :
    IsPreconnected (U \ Z) := by
  rintro u v hu hv huv ⟨a, haUZ, hau⟩ ⟨b, hbUZ, hbv⟩
  by_contra hne
  -- the two sides are open, cover `U`, and meet `U`; so they meet in `U`
  obtain ⟨x, -, hxA, hxB⟩ := hUc (side_cc U Z u) (side_cc U Z v) (isOpen_side_cc hU hu)
    (isOpen_side_cc hU hv) (subset_side_union_cc hloc hu hv huv hne)
    ⟨a, haUZ.1, Or.inl ⟨haUZ, hau⟩⟩ ⟨b, hbUZ.1, Or.inl ⟨hbUZ, hbv⟩⟩
  exact hne (nonempty_of_mem_side_cc hxA hxB (hdense x))

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
