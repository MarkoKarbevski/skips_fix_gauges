import SkipsLean.Dimension.IdentifiableConverse
import SkipsLean.Generic.Cayley
import SkipsLean.Symmetry.ChangeOfBasis

/-!
# From local identifiability up to changes of basis to the equality condition

Paper (dimension paper): Proposition 4.6, "A network satisfies the equality condition if and only
if, at generic parameters, it is locally identifiable up to its symmetries", the direction from
local identifiability to the equality condition; Definition 4.5: "A network is identifiable up to
its symmetries at `θ` if every `θ′` with `F_{θ′} = F_θ` is the image of `θ` under a symmetry: a
change of basis of Proposition 3.2, a symmetry inside a block, or a composition of these. It is
locally identifiable at `θ` if this holds for every `θ′` in some neighborhood of `θ`." The skips
paper: Proposition 4.5 and Definition 4.4, the same for skipless and residual networks.

Here for the changes of basis of the papers, composed with any family `Ψ θ` of images of `θ` that
is of class `C¹` on a subset `Ω` of a space `N` (for the symmetries inside the blocks: the
rescalings, the changes of basis inside the heads; `N` of dimension `s`; for blocks without such
symmetries `N` is the zero space and `Ψ θ n = θ`). Four cases: one change of basis per hidden
state (skipless networks: `G_0, …, G_L`) or the same at all hidden states (residual networks),
invertible (no normalization) or orthogonal (pre-RMSNorm). If at almost every `θ` every `θ'` near
`θ` with the same function is such an image, then at almost every `θ`
`P ≤ fd(θ) + dim 𝒢 · (number of changes of basis) + dim N`. With the upper bound this is the
equality condition. The statements hold for any stream matrices `S` and any real-analytic `f_ℓ`
and `χ`; they do not ask that the images are symmetries.

They follow from `ae_finrank_le_funDim_add_of_ae_locally_mem_iUnion_image`
(`Dimension/IdentifiableConverse.lean`): the invertible matrices are an open subset of the space
of matrices, on which the inverse is of class `C¹`; the orthogonal matrices are covered by
finitely many smooth images of the antisymmetric matrices (`Generic/Cayley.lean`).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **From local identifiability to the equality condition, one invertible change of basis per
hidden state:** if at almost every `θ` every `θ'` near `θ` with the same function is
`(Ψ θ n).cob G G` with `n ∈ Ω` and invertible `G_0, …, G_L`, then at almost every `θ`
`P ≤ fd(θ) + (L + 1) d² + dim N`. -/
theorem ae_finrank_le_funDim_add_of_ae_locally_cob (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (Ψ : Params A dIn dOut → N → Params A dIn dOut) (Ω : Set N)
    (hΨ : ∀ θ, ContDiffOn ℝ 1 (Ψ θ) Ω)
    (hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ n ∈ Ω, ∃ G : Fin (L + 1) → GL d ℝ, θ' = (Ψ θ n).cob G G) :
    ∀ᵐ θ ∂μ, Module.finrank ℝ (Params A dIn dOut)
      ≤ funDim A S θ + ((L + 1) * Fintype.card d ^ 2 + Module.finrank ℝ N) := by
  sorry

/-- **From local identifiability to the equality condition, one invertible change of basis at
all hidden states:** if at almost every `θ` every `θ'` near `θ` with the same function is
`(Ψ θ n).cob G G` with `n ∈ Ω` and one invertible `G`, then at almost every `θ`
`P ≤ fd(θ) + d² + dim N`. -/
theorem ae_finrank_le_funDim_add_of_ae_locally_cob_const (A : Arch T d L)
    (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (Ψ : Params A dIn dOut → N → Params A dIn dOut) (Ω : Set N)
    (hΨ : ∀ θ, ContDiffOn ℝ 1 (Ψ θ) Ω)
    (hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ n ∈ Ω, ∃ G : GL d ℝ, θ' = (Ψ θ n).cob (fun _ => G) (fun _ => G)) :
    ∀ᵐ θ ∂μ, Module.finrank ℝ (Params A dIn dOut)
      ≤ funDim A S θ + (Fintype.card d ^ 2 + Module.finrank ℝ N) := by
  sorry

/-- **From local identifiability to the equality condition, one orthogonal change of basis per
hidden state:** if at almost every `θ` every `θ'` near `θ` with the same function is
`(Ψ θ n).cob Q Q` with `n ∈ Ω` and orthogonal `Q_0, …, Q_L`, then at almost every `θ`
`P ≤ fd(θ) + (L + 1) d (d − 1) / 2 + dim N`. -/
theorem ae_finrank_le_funDim_add_of_ae_locally_cob_orthogonal (A : Arch T d L)
    (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (Ψ : Params A dIn dOut → N → Params A dIn dOut) (Ω : Set N)
    (hΨ : ∀ θ, ContDiffOn ℝ 1 (Ψ θ) Ω)
    (hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ n ∈ Ω, ∃ Q : Fin (L + 1) → GL d ℝ,
          (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧ θ' = (Ψ θ n).cob Q Q) :
    ∀ᵐ θ ∂μ, Module.finrank ℝ (Params A dIn dOut)
      ≤ funDim A S θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + Module.finrank ℝ N) := by
  sorry

/-- **From local identifiability to the equality condition, one orthogonal change of basis at
all hidden states:** if at almost every `θ` every `θ'` near `θ` with the same function is
`(Ψ θ n).cob Q Q` with `n ∈ Ω` and one orthogonal `Q`, then at almost every `θ`
`P ≤ fd(θ) + d (d − 1) / 2 + dim N`. -/
theorem ae_finrank_le_funDim_add_of_ae_locally_cob_const_orthogonal (A : Arch T d L)
    (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (Ψ : Params A dIn dOut → N → Params A dIn dOut) (Ω : Set N)
    (hΨ : ∀ θ, ContDiffOn ℝ 1 (Ψ θ) Ω)
    (hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
        ∃ n ∈ Ω, ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
          θ' = (Ψ θ n).cob (fun _ => Q) (fun _ => Q)) :
    ∀ᵐ θ ∂μ, Module.finrank ℝ (Params A dIn dOut)
      ≤ funDim A S θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Module.finrank ℝ N) := by
  sorry

end Skips
