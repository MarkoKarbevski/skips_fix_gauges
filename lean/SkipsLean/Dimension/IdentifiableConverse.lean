import SkipsLean.Generic.LevelSetImages
import SkipsLean.Dimension.GenericRank

/-!
# From local identifiability to the equality condition, for any family of symmetries

Paper (dimension paper): Proposition 4.6 (The equality condition and local identifiability): "A
network satisfies the equality condition if and only if, at generic parameters, it is locally
identifiable up to its symmetries." Its proof (Appendix B), the converse direction: "Conversely,
let every `θ′` in a neighborhood of `θ` in `Z` be the image of `θ` under a symmetry. With the
permutations and the sign flips, the symmetries form a Lie group of dimension `k` with finitely
many components, and the images of `θ` under it form the image of a manifold of dimension `k`
under a smooth map. By Sard's theorem this image contains no open subset of a manifold of larger
dimension, so `P − r ≤ k`, which with `r ≤ P − k` is the equality condition." Proposition 4.5 of
the skips paper is the same statement for skipless and residual networks, with the same proof.

Stated here, once for all kinds of network (any stream matrices `S`, any real-analytic maps
`f_ℓ` and `χ`) and any family of symmetries: the images of `θ` under the symmetries are the union
of the images of countably many maps `Φ i` of class `C¹` on open subsets `Ω i` of a space `M` of
dimension `k`. If `θ` is a parameter of the largest functional dimension (as generic parameters
are, `ae_funDim_ge`) and every `θ'` near `θ` with the same function is such an image, then
`P ≤ fd(θ) + k`. The second statement is the form at generic parameters. With the upper bounds
(Theorem 4.3 of the dimension paper, Theorem 4.2 of the skips paper) this is the equality
condition. The other direction: `Dimension/OrbitNetwork.lean`.

The statements follow from `finrank_ker_le_of_level_set_subset_iUnion_image`
(`Generic/LevelSetImages.lean`), with `F` the outputs on a batch `X` on which the rank at `θ` is
the functional dimension and `g x` the outputs on `X` with one more input `x`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **Proof of Proposition 4.6 (dimension paper) and of Proposition 4.5 (skips paper), from local
identifiability to the equality condition, at one parameter, for any family of symmetries:** let
`θ` have the largest functional dimension. If every `θ'` near `θ` with the same function is
`Φ i m` for one of countably many maps `Φ i` of class `C¹` on open subsets `Ω i` of `M`, then
`P ≤ fd(θ) + dim M`. -/
theorem finrank_le_funDim_add_of_locally_mem_iUnion_image (A : Arch T d L)
    (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (θ : Params A dIn dOut) (hmax : ∀ θ' : Params A dIn dOut, funDim A S θ' ≤ funDim A S θ)
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    {ι : Type*} [Countable ι] (Φ : ι → M → Params A dIn dOut) (Ω : ι → Set M)
    (hΩ : ∀ i, IsOpen (Ω i)) (hΦ : ∀ i, ContDiffOn ℝ 1 (Φ i) (Ω i))
    (hloc : ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U, (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
      ∃ i, ∃ m ∈ Ω i, Φ i m = θ') :
    Module.finrank ℝ (Params A dIn dOut) ≤ funDim A S θ + Module.finrank ℝ M := by
  sorry

/-- **Proposition 4.6 (dimension paper) and Proposition 4.5 (skips paper), from local
identifiability to the equality condition, at generic parameters, for any family of symmetries:**
if at almost every `θ` every `θ'` near `θ` with the same function is `Φ θ i m` for one of
countably many maps `Φ θ i` of class `C¹` on open subsets `Ω i` of `M`, then `P ≤ fd(θ) + dim M`
at almost every `θ`. -/
theorem ae_finrank_le_funDim_add_of_ae_locally_mem_iUnion_image (A : Arch T d L)
    (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    {ι : Type*} [Countable ι] (Φ : Params A dIn dOut → ι → M → Params A dIn dOut)
    (Ω : ι → Set M) (hΩ : ∀ i, IsOpen (Ω i)) (hΦ : ∀ θ i, ContDiffOn ℝ 1 (Φ θ i) (Ω i))
    (hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) → ∃ i, ∃ m ∈ Ω i, Φ θ i m = θ') :
    ∀ᵐ θ ∂μ, Module.finrank ℝ (Params A dIn dOut) ≤ funDim A S θ + Module.finrank ℝ M := by
  sorry

end Skips
