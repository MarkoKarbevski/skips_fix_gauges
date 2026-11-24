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
of the images of countably many maps `Φ i` of class `C¹` on subsets `Ω i` of a space `M` of
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

omit [DecidableEq d] in
/-- **Proof of Proposition 4.6 (dimension paper) and of Proposition 4.5 (skips paper), from local
identifiability to the equality condition, at one parameter, for any family of symmetries:** let
`θ` have the largest functional dimension. If every `θ'` near `θ` with the same function is
`Φ i m` for one of countably many maps `Φ i` of class `C¹` on subsets `Ω i` of `M`, then
`P ≤ fd(θ) + dim M`. -/
theorem finrank_le_funDim_add_of_locally_mem_iUnion_image (A : Arch T d L)
    (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (θ : Params A dIn dOut) (hmax : ∀ θ' : Params A dIn dOut, funDim A S θ' ≤ funDim A S θ)
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    {ι : Type*} [Countable ι] (Φ : ι → M → Params A dIn dOut) (Ω : ι → Set M)
    (hΦ : ∀ i, ContDiffOn ℝ 1 (Φ i) (Ω i))
    (hloc : ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U, (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) →
      ∃ i, ∃ m ∈ Ω i, Φ i m = θ') :
    Module.finrank ℝ (Params A dIn dOut) ≤ funDim A S θ + Module.finrank ℝ M := by
  -- a batch `X` on which the rank of the Jacobian at `θ` is the functional dimension
  obtain ⟨n, X, hX⟩ := exists_jacobianRank_eq_funDim (S := S) θ
  -- the outputs on a batch are analytic in the parameters, hence of class `C¹`
  have hB : ∀ {k : ℕ} (Y : Fin k → Matrix T dIn ℝ),
      ContDiff ℝ 1 (evalBatch A S Y : Params A dIn dOut → Fin k → Matrix T dOut ℝ) := fun Y =>
    (AnalyticOnNhd.pi fun i => analyticOnNhd_eval_params A S hf hχ (Y i)).contDiff
  -- `g x`: the outputs on the batch `X` with one more input `x`, in front
  let g : Matrix T dIn ℝ → Params A dIn dOut → Fin (n + 1) → Matrix T dOut ℝ :=
    fun x => evalBatch A S (Fin.cons x X : Fin (n + 1) → Matrix T dIn ℝ)
  -- forgetting the first output is a continuous linear map
  let proj : (Fin (n + 1) → Matrix T dOut ℝ) →L[ℝ] (Fin n → Matrix T dOut ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ
  have hFg : ∀ x, evalBatch A S X = fun θ' => proj (g x θ') := fun x => by
    funext θ' i
    simp [g, proj, evalBatch]
  -- the kernel of the derivative of `g x` lies in that of the derivative of `F` (chain rule)
  have hker : ∀ x θ', LinearMap.ker (fderiv ℝ (g x) θ').toLinearMap
      ≤ LinearMap.ker (fderiv ℝ (evalBatch A S X) θ').toLinearMap := by
    intro x θ' v hv
    have hd : HasFDerivAt (g x) (fderiv ℝ (g x) θ') θ' :=
      ((hB _).differentiable one_ne_zero θ').hasFDerivAt
    have hc := proj.hasFDerivAt.comp θ' hd
    rw [hFg x]
    have he : fderiv ℝ (fun θ' => proj (g x θ')) θ' = proj.comp (fderiv ℝ (g x) θ') :=
      hc.fderiv
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv ⊢
    rw [he, ContinuousLinearMap.comp_apply, hv, map_zero]
  -- the rank of the derivative of `g x` is at most `fd(θ') ≤ fd(θ)`
  have hrank : ∀ x θ', Module.finrank ℝ (LinearMap.range (fderiv ℝ (g x) θ').toLinearMap)
      ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ (evalBatch A S X) θ).toLinearMap) := by
    intro x θ'
    have h1 : Module.finrank ℝ (LinearMap.range (fderiv ℝ (g x) θ').toLinearMap)
        = jacobianRank A S (Fin.cons x X : Fin (n + 1) → Matrix T dIn ℝ) θ' := rfl
    have h2 : Module.finrank ℝ (LinearMap.range (fderiv ℝ (evalBatch A S X) θ).toLinearMap)
        = jacobianRank A S X θ := rfl
    rw [h1, h2, hX]
    exact (jacobianRank_le_funDim θ' _).trans (hmax θ')
  -- near `θ`, equal outputs on all the batches `X ∪ {x}` give the same function
  have hloc' : ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U, (∀ x, g x θ' = g x θ) → ∃ i, ∃ m ∈ Ω i, Φ i m = θ' := by
    obtain ⟨U, hU, hUΦ⟩ := hloc
    exact ⟨U, hU, fun θ' hθ' h => hUΦ θ' hθ' fun x => congrFun (h x) 0⟩
  have hk : Module.finrank ℝ (LinearMap.ker (fderiv ℝ (evalBatch A S X) θ).toLinearMap)
      ≤ Module.finrank ℝ M :=
    finrank_ker_le_of_level_set_subset_iUnion_image (hB X) θ g (fun x => hB _) hker
      hrank Φ Ω hΦ hloc'
  -- rank–nullity: `P = rank + dim ker`, with rank `fd(θ)`
  have hrn := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ (evalBatch A S X) θ).toLinearMap
  have h2 : Module.finrank ℝ (LinearMap.range (fderiv ℝ (evalBatch A S X) θ).toLinearMap)
      = jacobianRank A S X θ := rfl
  omega

omit [DecidableEq d] in
/-- **Proposition 4.6 (dimension paper) and Proposition 4.5 (skips paper), from local
identifiability to the equality condition, at generic parameters, for any family of symmetries:**
if at almost every `θ` every `θ'` near `θ` with the same function is `Φ θ i m` for one of
countably many maps `Φ θ i` of class `C¹` on subsets `Ω i` of `M`, then `P ≤ fd(θ) + dim M`
at almost every `θ`. -/
theorem ae_finrank_le_funDim_add_of_ae_locally_mem_iUnion_image (A : Arch T d L)
    (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    {ι : Type*} [Countable ι] (Φ : Params A dIn dOut → ι → M → Params A dIn dOut)
    (Ω : ι → Set M) (hΦ : ∀ θ i, ContDiffOn ℝ 1 (Φ θ i) (Ω i))
    (hloc : ∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A S θ' x = eval A S θ x) → ∃ i, ∃ m ∈ Ω i, Φ θ i m = θ') :
    ∀ᵐ θ ∂μ, Module.finrank ℝ (Params A dIn dOut) ≤ funDim A S θ + Module.finrank ℝ M := by
  -- the functional dimensions are at most `P`, so one of them is the largest
  have hbdd : BddAbove (Set.range (funDim A S : Params A dIn dOut → ℕ)) := by
    refine ⟨Module.finrank ℝ (Params A dIn dOut), ?_⟩
    rintro _ ⟨θ, rfl⟩
    obtain ⟨n, X, hX⟩ := exists_jacobianRank_eq_funDim (S := S) θ
    rw [← hX]
    exact jacobianRank_le_finrank θ X
  obtain ⟨θ₀, hθ₀⟩ := Nat.sSup_mem (Set.range_nonempty (funDim A S :
    Params A dIn dOut → ℕ)) hbdd
  have hmax₀ : ∀ θ', funDim A S θ' ≤ funDim A S θ₀ := fun θ' => by
    rw [hθ₀]
    exact le_csSup hbdd ⟨θ', rfl⟩
  -- generic parameters have the largest functional dimension; apply the first statement there
  filter_upwards [ae_funDim_ge A S hf hχ μ θ₀, hloc] with θ h1 h2
  exact finrank_le_funDim_add_of_locally_mem_iUnion_image A S hf hχ θ
    (fun θ' => (hmax₀ θ').trans h1) (Φ θ) Ω (hΦ θ) h2

end Skips
