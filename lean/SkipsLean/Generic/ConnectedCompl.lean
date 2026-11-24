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

/-- A punctured ball in a space of dimension at least two is preconnected: it is the image of
`(0, r) × S` under `(s, w) ↦ s • w`. -/
private lemma isPreconnected_ball_diff_zero_cc {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (h : 1 < Module.rank ℝ F) (r : ℝ) :
    IsPreconnected (Metric.ball (0 : F) r \ {0}) := by
  have heq : Metric.ball (0 : F) r \ {0} =
      (fun p : ℝ × F => p.1 • p.2) '' (Set.Ioo 0 r ×ˢ Metric.sphere (0 : F) 1) := by
    ext y
    constructor
    · rintro ⟨hyr, hy0⟩
      have hy : 0 < ‖y‖ := norm_pos_iff.2 hy0
      refine ⟨(‖y‖, ‖y‖⁻¹ • y), ⟨⟨hy, mem_ball_zero_iff.1 hyr⟩, ?_⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hy.ne']
      · show ‖y‖ • ‖y‖⁻¹ • y = y
        rw [smul_smul, mul_inv_cancel₀ hy.ne', one_smul]
    · rintro ⟨⟨s, w⟩, ⟨⟨hs0, hsr⟩, hw⟩, rfl⟩
      show s • w ∈ Metric.ball (0 : F) r \ {0}
      have hn : ‖s • w‖ = s := by
        rw [norm_smul, mem_sphere_zero_iff_norm.1 hw, mul_one, Real.norm_eq_abs, abs_of_pos hs0]
      refine ⟨mem_ball_zero_iff.2 (by rw [hn]; exact hsr), fun h0 => ?_⟩
      rw [Set.mem_singleton_iff] at h0
      rw [h0, norm_zero] at hn
      exact hs0.ne hn
  rw [heq]
  exact (isPreconnected_Ioo.prod (isPreconnected_sphere h 0 1)).image _
    (by fun_prop : Continuous fun p : ℝ × F => p.1 • p.2).continuousOn

/-- Near a zero `z` of `g` in `U` where `g` has an onto strict derivative, an open `N ∋ z`
inside `U` such that `N ∖ {g = 0}` is preconnected and has `z` in its closure. -/
private lemma exists_nhds_zeroSet_cc {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (hF : 2 ≤ Module.finrank ℝ F) {U : Set E} (hU : IsOpen U)
    {g : E → F} {g' : E →L[ℝ] F} {z : E} (hzU : z ∈ U) (hgz : g z = 0)
    (hstrict : HasStrictFDerivAt g g' z) (hsurj : Function.Surjective g') :
    ∃ N : Set E, IsOpen N ∧ z ∈ N ∧ N ⊆ U ∧ IsPreconnected (N \ {x | g x = 0}) ∧
      z ∈ closure (N \ {x | g x = 0}) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have hsurj' : g'.range = ⊤ := LinearMap.range_eq_top.2 hsurj
  -- the chart `φ : E → F × ker g'` of the implicit function theorem, with first coordinate `g`
  obtain ⟨φ, hfst, hsrc, hφz⟩ : ∃ φ : OpenPartialHomeomorph E (F × g'.ker),
      (∀ x, (φ x).1 = g x) ∧ z ∈ φ.source ∧ φ z = (0, 0) :=
    ⟨hstrict.implicitToOpenPartialHomeomorph g g' hsurj',
      hstrict.implicitToOpenPartialHomeomorph_fst hsurj',
      hstrict.mem_implicitToOpenPartialHomeomorph_source hsurj',
      by rw [hstrict.implicitToOpenPartialHomeomorph_self hsurj', hgz]⟩
  have hp₀ : ((0 : F), (0 : g'.ker)) ∈ φ.target := by rw [← hφz]; exact φ.map_source hsrc
  have hsymm₀ : φ.symm (0, 0) = z := by rw [← hφz]; exact φ.left_inv hsrc
  have hgsymm : ∀ p ∈ φ.target, g (φ.symm p) = p.1 := fun p hp => by
    rw [← hfst, φ.right_inv hp]
  -- a product of balls `P` around `(0, 0)` inside `φ.target ∩ φ.symm ⁻¹' U`
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 ((φ.isOpen_inter_preimage_symm hU).mem_nhds
    ⟨hp₀, by rw [Set.mem_preimage, hsymm₀]; exact hzU⟩)
  rw [← ball_prod_same] at hball
  set P := Metric.ball (0 : F) r ×ˢ Metric.ball (0 : g'.ker) r with hP
  set Q := (Metric.ball (0 : F) r \ {0}) ×ˢ Metric.ball (0 : g'.ker) r with hQ
  have hPt : P ⊆ φ.target := fun p hp => (hball hp).1
  have hQP : Q ⊆ P := Set.prod_mono Set.sdiff_subset le_rfl
  have hPo : IsOpen P := Metric.isOpen_ball.prod Metric.isOpen_ball
  -- `N ∖ {g = 0}` is the image of `Q`, where the first coordinate is not zero
  have hND : φ.symm '' P \ {x | g x = 0} = φ.symm '' Q := by
    ext x
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hgx⟩
      refine ⟨p, ⟨⟨hp.1, fun h0 => hgx ?_⟩, hp.2⟩, rfl⟩
      show g (φ.symm p) = 0
      rw [hgsymm p (hPt hp)]
      exact h0
    · rintro ⟨p, hp, rfl⟩
      refine ⟨⟨p, hQP hp, rfl⟩, fun h0 => hp.1.2 ?_⟩
      have h0' : g (φ.symm p) = 0 := h0
      rw [hgsymm p (hPt (hQP hp))] at h0'
      exact h0'
  have hFr : 1 < Module.rank ℝ F := Module.one_lt_rank_of_one_lt_finrank (by omega)
  have : Nontrivial F := Module.nontrivial_of_finrank_pos (R := ℝ) (M := F) (by omega)
  refine ⟨φ.symm '' P, φ.isOpen_image_symm_of_subset_target hPo hPt,
    ⟨(0, 0), ⟨Metric.mem_ball_self hr, Metric.mem_ball_self hr⟩, hsymm₀⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (hball hp).2
  · -- the image of the preconnected set `Q`
    rw [hND]
    exact ((isPreconnected_ball_diff_zero_cc hFr r).prod
      (convex_ball _ _).isPreconnected).image _ (φ.continuousOn_symm.mono (hQP.trans hPt))
  · -- `z` is the limit of `φ.symm (s • y₁, 0)` as `s → 0`, `s ≠ 0`
    rw [hND]
    obtain ⟨y₁, hy₁⟩ := exists_ne (0 : F)
    have hc : Continuous fun s : ℝ => ((s • y₁, (0 : g'.ker)) : F × g'.ker) := by fun_prop
    have ht : Filter.Tendsto (fun s : ℝ => ((s • y₁, (0 : g'.ker)) : F × g'.ker)) (𝓝[≠] 0)
        (𝓝 (0, 0)) := by
      have h0 := hc.tendsto 0
      simp only [zero_smul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have ht2 : Filter.Tendsto (fun s : ℝ => φ.symm (s • y₁, 0)) (𝓝[≠] 0) (𝓝 z) := by
      have h0 := (φ.continuousAt_symm hp₀).tendsto.comp ht
      rwa [hsymm₀] at h0
    have hev : ∀ᶠ s in 𝓝[≠] (0 : ℝ), ((s • y₁, (0 : g'.ker)) : F × g'.ker) ∈ P :=
      ht.eventually (hPo.mem_nhds ⟨Metric.mem_ball_self hr, Metric.mem_ball_self hr⟩)
    refine mem_closure_of_tendsto ht2 ?_
    filter_upwards [hev, self_mem_nhdsWithin] with s hs hs0
    exact ⟨_, ⟨⟨hs.1, smul_ne_zero hs0 hy₁⟩, hs.2⟩, rfl⟩

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
  -- a good neighbourhood of each zero of `g` in `U`
  have key : ∀ z ∈ U ∩ {x | g x = 0}, ∃ N : Set E, IsOpen N ∧ z ∈ N ∧ N ⊆ U ∧
      IsPreconnected (N \ {x | g x = 0}) ∧ z ∈ closure (N \ {x | g x = 0}) := by
    rintro z ⟨hzU, hgz⟩
    obtain ⟨g', hstrict, hsurj⟩ := hg z hzU hgz
    exact exists_nhds_zeroSet_cc hF hU hzU hgz hstrict hsurj
  refine isPreconnected_diff_of_forall_exists_nhds hU hUc (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨N, hN, hzN, hNU, hNc, -⟩ := key z hz
    exact ⟨N, hN, hzN, hNU, hNc⟩
  · obtain ⟨N, -, -, hNU, -, hcl⟩ := key z hz
    exact closure_mono (Set.sdiff_subset_sdiff_left hNU) hcl

end Skips
