import SkipsLean.Dimension.IdentifiableConverseCob

/-!
# From local identifiability to the equality condition, with countably many further images

Paper (dimension paper, proof of Proposition 4.6; skips paper, proof of Proposition 4.5):
"Conversely, let every `θ′` in a neighborhood of `θ` in `Z` be the image of `θ` under a symmetry.
With the permutations and the sign flips, the symmetries form a Lie group of dimension `k` with
finitely many components, and the images of `θ` under it form the image of a manifold of dimension
`k` under a smooth map. By Sard's theorem this image contains no open subset of a manifold of
larger dimension, so `P − r ≤ k`". The symmetries inside the blocks are listed in Appendix B of the
dimension paper: "Permutations of hidden units or heads and sign flips of tanh hidden units are
finite and remove no parameters".

`Dimension/IdentifiableConverseCob.lean` states this direction for one family `Ψ θ : N → Params` of
images of `θ` (the continuous symmetries inside the blocks) composed with the changes of basis.
Here the same four statements for countably many families `Ψ θ i`, `i : ι`: one for each
component of the group, that is, for each composition of permutations and sign flips. A
composition of symmetries in any order is a permutation and sign flip, then a continuous symmetry
inside the blocks, then a change of basis, because the changes of basis commute with the
symmetries inside the blocks and the permutations and sign flips normalize the continuous ones.
As in `IdentifiableConverseCob.lean`, the statements do not ask that the images are symmetries.
They follow from `ae_finrank_le_funDim_add_of_ae_locally_mem_iUnion_image`
(`Dimension/IdentifiableConverse.lean`), which takes countably many maps.

The forms "equality condition if and only if locally identifiable" with these further images, for
the kinds of network of the papers: `Dimension/IdentifiableIffFamily.lean`,
`Residual/IdentifiableIffFamily.lean`, `Dimension/IdentifiableIffTransformerFamily.lean`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **From local identifiability to the equality condition, one invertible change of basis per
hidden state, countably many families of further images:** if at almost every `θ` every `θ'` near
`θ` with the same function is `(Ψ θ i n).cob G G` with `i : ι`, `n ∈ Ω i` and invertible `G_0, …,
G_L`, then at almost every `θ` `P ≤ fd(θ) + (L + 1) d² + dim N`. -/
theorem ae_finrank_le_funDim_add_of_ae_locally_cob_family (A : Arch T d L)
    (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {ι : Type*} [Countable ι] (Ψ : Params A dIn dOut → ι → N → Params A dIn dOut)
    (Ω : ι → Set N) (hΨ : ∀ θ i, ContDiffOn ℝ 1 (Ψ θ i) (Ω i))
    (hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ i, ∃ n ∈ Ω i, ∃ G : Fin (L + 1) → GL d ℝ, θ' = (Ψ θ i n).cob G G) :
    ∀ᵐ θ ∂μ, Module.finrank ℝ (Params A dIn dOut)
      ≤ funDim A S θ + ((L + 1) * Fintype.card d ^ 2 + Module.finrank ℝ N) := by
  sorry

/-- **From local identifiability to the equality condition, one invertible change of basis at all
hidden states, countably many families of further images:** if at almost every `θ` every `θ'` near
`θ` with the same function is `(Ψ θ i n).cob (fun _ => G) (fun _ => G)` with `i : ι`, `n ∈ Ω i` and
one invertible `G`, then at almost every `θ` `P ≤ fd(θ) + d² + dim N`. -/
theorem ae_finrank_le_funDim_add_of_ae_locally_cob_const_family (A : Arch T d L)
    (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {ι : Type*} [Countable ι] (Ψ : Params A dIn dOut → ι → N → Params A dIn dOut)
    (Ω : ι → Set N) (hΨ : ∀ θ i, ContDiffOn ℝ 1 (Ψ θ i) (Ω i))
    (hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ i, ∃ n ∈ Ω i, ∃ G : GL d ℝ, θ' = (Ψ θ i n).cob (fun _ => G) (fun _ => G)) :
    ∀ᵐ θ ∂μ, Module.finrank ℝ (Params A dIn dOut)
      ≤ funDim A S θ + (Fintype.card d ^ 2 + Module.finrank ℝ N) := by
  sorry

/-- **From local identifiability to the equality condition, one orthogonal change of basis per
hidden state, countably many families of further images:** if at almost every `θ` every `θ'` near
`θ` with the same function is `(Ψ θ i n).cob Q Q` with `i : ι`, `n ∈ Ω i` and orthogonal `Q_0, …,
Q_L`, then at almost every `θ` `P ≤ fd(θ) + (L + 1) d(d−1)/2 + dim N`. -/
theorem ae_finrank_le_funDim_add_of_ae_locally_cob_orthogonal_family (A : Arch T d L)
    (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {ι : Type*} [Countable ι] (Ψ : Params A dIn dOut → ι → N → Params A dIn dOut)
    (Ω : ι → Set N) (hΨ : ∀ θ i, ContDiffOn ℝ 1 (Ψ θ i) (Ω i))
    (hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ i, ∃ n ∈ Ω i, ∃ Q : Fin (L + 1) → GL d ℝ,
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (Ψ θ i n).cob Q Q) :
    ∀ᵐ θ ∂μ, Module.finrank ℝ (Params A dIn dOut)
      ≤ funDim A S θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + Module.finrank ℝ N) := by
  sorry

/-- **From local identifiability to the equality condition, one orthogonal change of basis at all
hidden states, countably many families of further images:** if at almost every `θ` every `θ'` near
`θ` with the same function is `(Ψ θ i n).cob (fun _ => Q) (fun _ => Q)` with `i : ι`, `n ∈ Ω i` and
one orthogonal `Q`, then at almost every `θ` `P ≤ fd(θ) + d(d−1)/2 + dim N`. -/
theorem ae_finrank_le_funDim_add_of_ae_locally_cob_const_orthogonal_family (A : Arch T d L)
    (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {ι : Type*} [Countable ι] (Ψ : Params A dIn dOut → ι → N → Params A dIn dOut)
    (Ω : ι → Set N) (hΨ : ∀ θ i, ContDiffOn ℝ 1 (Ψ θ i) (Ω i))
    (hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ i, ∃ n ∈ Ω i, ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
          θ' = (Ψ θ i n).cob (fun _ => Q) (fun _ => Q)) :
    ∀ᵐ θ ∂μ, Module.finrank ℝ (Params A dIn dOut)
      ≤ funDim A S θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Module.finrank ℝ N) := by
  sorry

end Skips
