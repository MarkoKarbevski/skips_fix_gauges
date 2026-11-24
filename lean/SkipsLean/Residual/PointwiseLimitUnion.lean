import SkipsLean.Residual.PointwiseLimit

/-!
# Pointwise limits of a finite union of sets of networks

Paper (skips paper): proof of Theorem A.28 (iv), "In (iii) this covers the finitely many choices
of widths with every `d'_hidden,ℓ ≥ d_model`, on the same batch, and the smallest of their `δ`
serves for all." In terms of Definition A.29: a pointwise limit of a finite union of sets of
networks is a pointwise limit of one of them (the batches of the sets are put together, and the
smallest `δ` is taken).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T dIn dOut : Type*} [Fintype T] [Fintype dOut]

/-- A pointwise limit of a set of networks is a pointwise limit of every larger set. -/
theorem IsPointwiseLimit.mono {𝓕 𝓖 : Set (Matrix T dIn ℝ → Matrix T dOut ℝ)}
    {F : Matrix T dIn ℝ → Matrix T dOut ℝ} (h : IsPointwiseLimit 𝓕 F) (h𝓕 : 𝓕 ⊆ 𝓖) :
    IsPointwiseLimit 𝓖 F := by
  intro n hn X δ hδ
  obtain ⟨F', hF', hX⟩ := h n hn X δ hδ
  exact ⟨F', h𝓕 hF', hX⟩

/-- A pointwise limit of the union of two sets of networks is a pointwise limit of one of them. -/
theorem isPointwiseLimit_union {𝓕 𝓖 : Set (Matrix T dIn ℝ → Matrix T dOut ℝ)}
    {F : Matrix T dIn ℝ → Matrix T dOut ℝ} (h : IsPointwiseLimit (𝓕 ∪ 𝓖) F) :
    IsPointwiseLimit 𝓕 F ∨ IsPointwiseLimit 𝓖 F := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  -- a batch and a `δ` that separate `F` from each set
  simp only [IsPointwiseLimit, not_forall, not_exists, not_and, not_lt] at h1 h2
  obtain ⟨n₁, hn₁, X₁, δ₁, hδ₁, hX₁⟩ := h1
  obtain ⟨n₂, hn₂, X₂, δ₂, hδ₂, hX₂⟩ := h2
  -- the two batches put together, and the smaller `δ`
  obtain ⟨F', hF', hlt⟩ := h (n₁ + n₂) (by omega) (Fin.append X₁ X₂) (min δ₁ δ₂)
    (lt_min hδ₁ hδ₂)
  rcases hF' with hF' | hF'
  · obtain ⟨i, hi⟩ := hX₁ F' hF'
    have := hlt (Fin.castAdd n₂ i)
    rw [Fin.append_left] at this
    exact absurd (hi.trans_lt this |>.trans_le (min_le_left _ _)) (lt_irrefl _)
  · obtain ⟨i, hi⟩ := hX₂ F' hF'
    have := hlt (Fin.natAdd n₁ i)
    rw [Fin.append_right] at this
    exact absurd (hi.trans_lt this |>.trans_le (min_le_right _ _)) (lt_irrefl _)

/-- **Proof of Theorem A.28 (iv) of the skips paper, "the smallest of their `δ` serves for all":**
a pointwise limit of a finite union of sets of networks is a pointwise limit of one of them. -/
theorem exists_isPointwiseLimit_of_biUnion_finite {ι : Type*} {s : Set ι} (hs : s.Finite)
    {𝓕 : ι → Set (Matrix T dIn ℝ → Matrix T dOut ℝ)} {F : Matrix T dIn ℝ → Matrix T dOut ℝ}
    (h : IsPointwiseLimit (⋃ i ∈ s, 𝓕 i) F) :
    ∃ i ∈ s, IsPointwiseLimit (𝓕 i) F := by
  by_contra hcon
  push Not at hcon
  -- induction on the finite set
  have key : ∀ t : Set ι, t.Finite → IsPointwiseLimit (⋃ i ∈ t, 𝓕 i) F →
      ∃ i ∈ t, IsPointwiseLimit (𝓕 i) F := by
    intro t ht
    induction t, ht using Set.Finite.induction_on with
    | empty =>
      intro h0
      rw [Set.biUnion_empty] at h0
      obtain ⟨F', hF', _⟩ := h0 1 le_rfl (fun _ => 0) 1 one_pos
      exact absurd hF' (Set.notMem_empty _)
    | insert ha hs ih =>
      intro h0
      rw [Set.biUnion_insert] at h0
      rcases isPointwiseLimit_union h0 with h1 | h1
      · exact ⟨_, Set.mem_insert _ _, h1⟩
      · obtain ⟨i, hi, hi'⟩ := ih h1
        exact ⟨i, Set.mem_insert_of_mem _ hi, hi'⟩
  obtain ⟨i, hi, hi'⟩ := key s hs h
  exact hcon i hi hi'

end Skips
