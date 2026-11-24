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
  sorry

/-- A pointwise limit of the union of two sets of networks is a pointwise limit of one of them. -/
theorem isPointwiseLimit_union {𝓕 𝓖 : Set (Matrix T dIn ℝ → Matrix T dOut ℝ)}
    {F : Matrix T dIn ℝ → Matrix T dOut ℝ} (h : IsPointwiseLimit (𝓕 ∪ 𝓖) F) :
    IsPointwiseLimit 𝓕 F ∨ IsPointwiseLimit 𝓖 F := by
  sorry

/-- **Proof of Theorem A.28 (iv) of the skips paper, "the smallest of their `δ` serves for all":**
a pointwise limit of a finite union of sets of networks is a pointwise limit of one of them. -/
theorem exists_isPointwiseLimit_of_biUnion_finite {ι : Type*} {s : Set ι} (hs : s.Finite)
    {𝓕 : ι → Set (Matrix T dIn ℝ → Matrix T dOut ℝ)} {F : Matrix T dIn ℝ → Matrix T dOut ℝ}
    (h : IsPointwiseLimit (⋃ i ∈ s, 𝓕 i) F) :
    ∃ i ∈ s, IsPointwiseLimit (𝓕 i) F := by
  sorry

end Skips
