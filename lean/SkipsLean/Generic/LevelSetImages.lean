import SkipsLean.Imports
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# A level set that lies in images of a space of smaller dimension

Paper (dimension paper): Appendix B, proof of Proposition 4.6 (the equality condition and local
identifiability), the direction from local identifiability to the equality condition; the same
argument proves Proposition 4.5 of the skips paper:

"By the constant rank theorem, after shrinking `U`, the set `Z = {θ′ ∈ U : F_X(θ′) = F_X(θ)}` is
a connected manifold of dimension `P − r`, whose tangent space at each point is the kernel of the
Jacobian. For any further input `x`, the Jacobian on `X ∪ {x}` has rank `r` on `U` as well, so it
has the same kernel, and `θ′ ↦ F_{θ′}(x)` is constant on `Z`. […] Conversely, let every `θ′` in a
neighborhood of `θ` in `Z` be the image of `θ` under a symmetry. With the permutations and the
sign flips, the symmetries form a Lie group of dimension `k` with finitely many components, and
the images of `θ` under it form the image of a manifold of dimension `k` under a smooth map. By
Sard's theorem this image contains no open subset of a manifold of larger dimension, so
`P − r ≤ k`".

Stated here without manifolds and without the constant rank theorem, for maps between
finite-dimensional real spaces. `F` is the map of the outputs on a batch `X`, of class `C¹`, and
`θ₀` a point; `r` is the rank of its derivative at `θ₀`. The maps `g j` are the outputs on the
larger batches `X ∪ {x}`: the kernel of the derivative of `g j` lies in that of `F` at every
point, and its rank is at most `r` at every point (so `θ₀` is a point of the largest rank). The
images of `θ₀` under the symmetries are the union of the images of countably many maps `Φ i` of
class `C¹` on subsets `Ω i` of a space `M` (of dimension `k`). If near `θ₀` every point with
`g j θ = g j θ₀` for all `j` is in one of these images, then the kernel of the derivative of `F` at
`θ₀` has dimension at most that of `M`: `P − r ≤ k`.

In place of Sard's theorem the proof uses the Hausdorff dimension (Mathlib:
`DifferentiableOn.dimH_image_le`, `dimH_iUnion`, `Real.dimH_of_mem_nhds`): the level set contains
the image of a ball of the kernel under a map with a Lipschitz left inverse. The sets `Ω i` need
not be open.
-/

namespace Skips

open Filter Topology

/-- A continuous left inverse of an injective continuous linear map into a finite-dimensional
space. -/
private lemma exists_leftInverse_lsi {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {f' : E →L[ℝ] Z} (hinj : Function.Injective f') : ∃ L : Z →L[ℝ] E, ∀ x, L (f' x) = x := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f'.toLinearMap
    (LinearMap.ker_eq_bot.2 hinj)
  exact ⟨LinearMap.toContinuousLinearMap g, fun x => LinearMap.congr_fun hg x⟩

/-- Step 1 (a chart): with `Ψ θ = (ρ (F θ), c (θ - θ₀))`, whose derivative at `θ₀` is injective,
the map `ψ κ = Ψ⁻¹ (ρ (F θ₀), κ)` parametrizes the level set of `ρ ∘ F` near `θ₀`. -/
private lemma chart_lsi {P Y R K : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]
    {F : P → Y} (hF : ContDiff ℝ 1 F) (θ₀ : P) (ρ : Y →L[ℝ] R) (c : P →L[ℝ] K)
    (hinj : Function.Injective ((ρ.comp (fderiv ℝ F θ₀)).prod c))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ (R × K)) :
    ∃ ψ : K → P, ψ 0 = θ₀ ∧ ContinuousAt ψ 0 ∧ ∀ᶠ κ in 𝓝 (0 : K),
      ρ (F (ψ κ)) = ρ (F θ₀) ∧ c (ψ κ - θ₀) = κ ∧ DifferentiableAt ℝ ψ κ := by
  set L := (ρ.comp (fderiv ℝ F θ₀)).prod c with hL
  let e : P ≃L[ℝ] R × K :=
    (L.toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
  have hΨ : ContDiff ℝ 1 (fun θ => (ρ (F θ), c (θ - θ₀))) :=
    (ρ.contDiff.comp hF).prodMk (c.contDiff.comp (contDiff_id.sub contDiff_const))
  have hΨ' : HasFDerivAt (fun θ => (ρ (F θ), c (θ - θ₀))) (e : P →L[ℝ] R × K) θ₀ := by
    have h1 : HasFDerivAt (fun θ => ρ (F θ)) (ρ.comp (fderiv ℝ F θ₀)) θ₀ :=
      ρ.hasFDerivAt.comp θ₀ ((hF.differentiable one_ne_zero) θ₀).hasFDerivAt
    have h2 : HasFDerivAt (fun θ => c (θ - θ₀)) c θ₀ :=
      (c.hasFDerivAt.comp θ₀ ((hasFDerivAt_id θ₀).sub_const θ₀)).congr_fderiv
        (ContinuousLinearMap.comp_id c)
    exact h1.prodMk h2
  have hn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  set Ψ := hΨ.contDiffAt.toOpenPartialHomeomorph _ hΨ' hn with hΨdef
  have hsymm : ContDiffAt ℝ 1 Ψ.symm (ρ (F θ₀), c (θ₀ - θ₀)) :=
    hΨ.contDiffAt.to_localInverse hΨ' hn
  have hsrc : θ₀ ∈ Ψ.source := hΨ.contDiffAt.mem_toOpenPartialHomeomorph_source hΨ' hn
  have htgt : (ρ (F θ₀), c (θ₀ - θ₀)) ∈ Ψ.target :=
    hΨ.contDiffAt.image_mem_toOpenPartialHomeomorph_target hΨ' hn
  have h00 : (ρ (F θ₀), (0 : K)) = (ρ (F θ₀), c (θ₀ - θ₀)) := by simp
  set ι : K → R × K := fun κ => (ρ (F θ₀), κ) with hι
  have hιc : Continuous ι := continuous_const.prodMk continuous_id
  have hιd : Differentiable ℝ ι := (differentiable_const _).prodMk differentiable_id
  refine ⟨fun κ => Ψ.symm (ι κ), ?_, ?_, ?_⟩
  · show Ψ.symm (ρ (F θ₀), 0) = θ₀
    rw [h00]
    exact Ψ.left_inv hsrc
  · have h1 : ContinuousAt Ψ.symm (ι 0) := by
      show ContinuousAt Ψ.symm (ρ (F θ₀), 0)
      rw [h00]
      exact hsymm.continuousAt
    exact h1.comp hιc.continuousAt
  · have hev : ∀ᶠ y in 𝓝 (ρ (F θ₀), c (θ₀ - θ₀)), y ∈ Ψ.target ∧ ContDiffAt ℝ 1 Ψ.symm y :=
      (Ψ.open_target.eventually_mem htgt).and (hsymm.eventually (by simp))
    rw [← h00] at hev
    have hev' : ∀ᶠ κ in 𝓝 (0 : K), ι κ ∈ Ψ.target ∧ ContDiffAt ℝ 1 Ψ.symm (ι κ) :=
      hιc.continuousAt.eventually hev
    filter_upwards [hev'] with κ hκ
    have hr : Ψ (Ψ.symm (ι κ)) = ι κ := Ψ.right_inv hκ.1
    have hr' : (ρ (F (Ψ.symm (ι κ))), c (Ψ.symm (ι κ) - θ₀)) = (ρ (F θ₀), κ) := hr
    refine ⟨congrArg Prod.fst hr', congrArg Prod.snd hr', ?_⟩
    exact (hκ.2.differentiableAt hn).comp κ (hιd κ)

/-- Step 2 (the kernels agree near `θ₀`): near `θ₀` the derivative of `Ψ` stays invertible, so the
kernel of `D(ρ ∘ F)(θ)` has dimension at most `dim K`, and it contains the kernel of every
`Dg_j(θ)`, of dimension at least `dim K`. -/
private lemma eventually_ker_le_lsi {P Y Y' R K : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Y'] [NormedSpace ℝ Y']
    [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]
    {F : P → Y} (hF : ContDiff ℝ 1 F) (θ₀ : P) (ρ : Y →L[ℝ] R) (c : P →L[ℝ] K)
    (hinj : Function.Injective ((ρ.comp (fderiv ℝ F θ₀)).prod c))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ R + Module.finrank ℝ K)
    {J : Type*} (g : J → P → Y')
    (hker : ∀ j θ, LinearMap.ker (fderiv ℝ (g j) θ).toLinearMap
      ≤ LinearMap.ker (fderiv ℝ F θ).toLinearMap)
    (hrank : ∀ j θ, Module.finrank ℝ (LinearMap.range (fderiv ℝ (g j) θ).toLinearMap)
      ≤ Module.finrank ℝ R) :
    ∀ᶠ θ in 𝓝 θ₀, ∀ j, LinearMap.ker (ρ.comp (fderiv ℝ F θ)).toLinearMap
      ≤ LinearMap.ker (fderiv ℝ (g j) θ).toLinearMap := by
  set L : P → (P →L[ℝ] R × K) := fun θ => (ρ.comp (fderiv ℝ F θ)).prod c with hLdef
  have hF' : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  have hL : Continuous L :=
    (ContinuousLinearMap.prodL ℝ).continuous.comp
      ((continuous_const.clm_comp hF').prodMk continuous_const)
  have hdim' : Module.finrank ℝ P = Module.finrank ℝ (R × K) := by
    rw [Module.finrank_prod]; exact hdim
  let e : P ≃L[ℝ] R × K :=
    ((L θ₀).toLinearMap.linearEquivOfInjective hinj hdim').toContinuousLinearEquiv
  have he : (e : P →L[ℝ] R × K) = L θ₀ := ContinuousLinearMap.ext fun _ => rfl
  have hmem : ∀ᶠ θ in 𝓝 θ₀, L θ ∈ Set.range ((↑) : (P ≃L[ℝ] R × K) → P →L[ℝ] R × K) :=
    hL.continuousAt.preimage_mem_nhds (he ▸ ContinuousLinearEquiv.nhds e)
  filter_upwards [hmem] with θ hθ j
  obtain ⟨e', he'⟩ := hθ
  have hinjθ : Function.Injective (L θ) := he' ▸ e'.injective
  set N := LinearMap.ker (ρ.comp (fderiv ℝ F θ)).toLinearMap with hN
  -- `c` is injective on `N`
  have hNK : Module.finrank ℝ N ≤ Module.finrank ℝ K := by
    apply LinearMap.finrank_le_finrank_of_injective (f := c.toLinearMap ∘ₗ N.subtype)
    intro x y hxy
    apply Subtype.ext
    apply hinjθ
    have hx : (ρ.comp (fderiv ℝ F θ)) x = 0 := x.2
    have hy : (ρ.comp (fderiv ℝ F θ)) y = 0 := y.2
    exact Prod.ext (hx.trans hy.symm) hxy
  have hle : LinearMap.ker (fderiv ℝ (g j) θ).toLinearMap ≤ N := by
    intro v hv
    have h1 : fderiv ℝ F θ v = 0 := hker j θ hv
    show ρ (fderiv ℝ F θ v) = 0
    rw [h1, map_zero]
  have h1 := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ (g j) θ).toLinearMap
  have h2 := hrank j θ
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  exact heq.ge

/-- Step 3 (constancy): if `ρ ∘ F ∘ ψ` is constant on an open convex set `s` and the kernel of
`D(ρ ∘ F)` lies in that of `DG` along `ψ`, then `G ∘ ψ` is constant on `s`. -/
private lemma const_lsi {K P Y R Y' : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup R] [NormedSpace ℝ R] [NormedAddCommGroup Y'] [NormedSpace ℝ Y']
    {F : P → Y} (hF : Differentiable ℝ F) (ρ : Y →L[ℝ] R) {G : P → Y'}
    (hG : Differentiable ℝ G) {ψ : K → P} {s : Set K} (hs : IsOpen s) (hsc : Convex ℝ s)
    (hψ : ∀ κ ∈ s, DifferentiableAt ℝ ψ κ) {a : R} (hc : ∀ κ ∈ s, ρ (F (ψ κ)) = a)
    (hker : ∀ κ ∈ s, LinearMap.ker (ρ.comp (fderiv ℝ F (ψ κ))).toLinearMap
      ≤ LinearMap.ker (fderiv ℝ G (ψ κ)).toLinearMap)
    {x y : K} (hx : x ∈ s) (hy : y ∈ s) : G (ψ x) = G (ψ y) := by
  have hd : DifferentiableOn ℝ (G ∘ ψ) s := fun κ hκ =>
    ((hG _).comp κ (hψ κ hκ)).differentiableWithinAt
  refine hsc.is_const_of_fderivWithin_eq_zero hd (fun κ hκ => ?_) hx hy
  rw [fderivWithin_of_isOpen hs hκ]
  have h1 : HasFDerivAt (fun κ => ρ (F (ψ κ)))
      ((ρ.comp (fderiv ℝ F (ψ κ))).comp (fderiv ℝ ψ κ)) κ :=
    (ρ.hasFDerivAt.comp (ψ κ) (hF _).hasFDerivAt).comp κ (hψ κ hκ).hasFDerivAt
  have h2 : HasFDerivAt (fun κ => ρ (F (ψ κ))) (0 : K →L[ℝ] R) κ := by
    refine (hasFDerivAt_const a κ).congr_of_eventuallyEq ?_
    filter_upwards [hs.mem_nhds hκ] with κ' hκ'
    exact hc κ' hκ'
  have h3 := h1.unique h2
  rw [fderiv_comp κ (hG _) (hψ κ hκ)]
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : fderiv ℝ ψ κ v ∈ LinearMap.ker (ρ.comp (fderiv ℝ F (ψ κ))).toLinearMap :=
    DFunLike.congr_fun h3 v
  exact hker κ hκ hv

/-- Step 4 (dimension): if `ψ` maps a neighborhood `s` of `0` in `K` into the union of the images
of the `Φ i`, and `θ ↦ c (θ - θ₀)` is a left inverse of `ψ` on `s`, then `dim K ≤ dim M`. -/
private lemma finrank_le_lsi {K P M : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    [FiniteDimensional ℝ K] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    {ι : Type*} [Countable ι] (Φ : ι → M → P) (Ω : ι → Set M)
    (hΦ : ∀ i, DifferentiableOn ℝ (Φ i) (Ω i)) (ψ : K → P) (c : P →L[ℝ] K) (θ₀ : P)
    {s : Set K} (hs : s ∈ 𝓝 (0 : K)) (hc : ∀ κ ∈ s, c (ψ κ - θ₀) = κ)
    (hsub : ψ '' s ⊆ ⋃ i, Φ i '' Ω i) :
    Module.finrank ℝ K ≤ Module.finrank ℝ M := by
  have h1 : dimH s = Module.finrank ℝ K := Real.dimH_of_mem_nhds hs
  have h2 : s ⊆ (fun θ => c (θ - θ₀)) '' (ψ '' s) := fun κ hκ =>
    ⟨ψ κ, ⟨κ, hκ, rfl⟩, hc κ hκ⟩
  have hdiff : DifferentiableOn ℝ (fun θ => c (θ - θ₀)) (ψ '' s) :=
    (c.differentiable.comp (differentiable_id.sub_const θ₀)).differentiableOn
  have h3 : dimH s ≤ dimH (ψ '' s) := (dimH_mono h2).trans hdiff.dimH_image_le
  have h4 : dimH (ψ '' s) ≤ Module.finrank ℝ M := by
    refine (dimH_mono hsub).trans ?_
    rw [dimH_iUnion]
    refine iSup_le fun i => ?_
    exact (hΦ i).dimH_image_le.trans
      ((dimH_mono (Set.subset_univ _)).trans (Real.dimH_univ_eq_finrank M).le)
  have h5 : (Module.finrank ℝ K : ENNReal) ≤ Module.finrank ℝ M := h1 ▸ h3.trans h4
  exact_mod_cast h5

/-- **Proof of Proposition 4.6 (dimension paper) and of Proposition 4.5 (skips paper), from local
identifiability to the equality condition, for maps between finite-dimensional spaces:** let `F`
and the maps `g j` be of class `C¹`, with `ker Dg_j(θ) ⊆ ker DF(θ)` and
`rank Dg_j(θ) ≤ rank DF(θ₀)` at every `θ`. If every `θ` near `θ₀` with `g j θ = g j θ₀` for all
`j` lies in the image of one of countably many maps `Φ i` of class `C¹` on subsets of `M`,
then `dim ker DF(θ₀) ≤ dim M`. -/
theorem finrank_ker_le_of_level_set_subset_iUnion_image
    {P Y Y' M : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Y'] [NormedSpace ℝ Y'] [FiniteDimensional ℝ Y']
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    {F : P → Y} (hF : ContDiff ℝ 1 F) (θ₀ : P)
    {J : Type*} (g : J → P → Y') (hg : ∀ j, ContDiff ℝ 1 (g j))
    (hker : ∀ j θ, LinearMap.ker (fderiv ℝ (g j) θ).toLinearMap
      ≤ LinearMap.ker (fderiv ℝ F θ).toLinearMap)
    (hrank : ∀ j θ, Module.finrank ℝ (LinearMap.range (fderiv ℝ (g j) θ).toLinearMap)
      ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ F θ₀).toLinearMap))
    {ι : Type*} [Countable ι] (Φ : ι → M → P) (Ω : ι → Set M)
    (hΦ : ∀ i, ContDiffOn ℝ 1 (Φ i) (Ω i))
    (hloc : ∃ U ∈ 𝓝 θ₀, ∀ θ ∈ U, (∀ j, g j θ = g j θ₀) → ∃ i, ∃ m ∈ Ω i, Φ i m = θ) :
    Module.finrank ℝ (LinearMap.ker (fderiv ℝ F θ₀).toLinearMap) ≤ Module.finrank ℝ M := by
  set F' := fderiv ℝ F θ₀ with hF'
  set K := LinearMap.ker F'.toLinearMap with hK
  set R := LinearMap.range F'.toLinearMap with hR
  -- Step 1: a projection `ρ` onto the range `R` and a projection `c` onto the kernel `K`.
  obtain ⟨ρ, hρ⟩ := exists_leftInverse_lsi (f' := R.subtypeL) Subtype.val_injective
  obtain ⟨c, hc⟩ := exists_leftInverse_lsi (f' := K.subtypeL) Subtype.val_injective
  have hinj : Function.Injective ((ρ.comp F').prod c) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    have h1 : ρ (F' v) = 0 := congrArg Prod.fst hv
    have h2 : c v = 0 := congrArg Prod.snd hv
    have h3 : F' v = 0 := by
      have h4 := hρ ⟨F' v, ⟨v, rfl⟩⟩
      have h5 : ρ (F' v) = ⟨F' v, ⟨v, rfl⟩⟩ := h4
      rw [h1] at h5
      exact (congrArg Subtype.val h5).symm
    have h6 := hc ⟨v, h3⟩
    have h7 : c v = ⟨v, h3⟩ := h6
    rw [h2] at h7
    exact (congrArg Subtype.val h7).symm
  have hdim : Module.finrank ℝ P = Module.finrank ℝ R + Module.finrank ℝ K :=
    (LinearMap.finrank_range_add_finrank_ker F'.toLinearMap).symm
  obtain ⟨ψ, hψ0, hψc, hψev⟩ :=
    chart_lsi hF θ₀ ρ c hinj (by rw [Module.finrank_prod]; exact hdim)
  -- Step 2: the kernels agree near `θ₀`.
  have hkerev := eventually_ker_le_lsi hF θ₀ ρ c hinj hdim g hker hrank
  obtain ⟨U, hU, hUsub⟩ := hloc
  have hev2 : ∀ᶠ κ in 𝓝 (0 : K), (∀ j, LinearMap.ker (ρ.comp (fderiv ℝ F (ψ κ))).toLinearMap
      ≤ LinearMap.ker (fderiv ℝ (g j) (ψ κ)).toLinearMap) ∧ ψ κ ∈ U := by
    rw [← hψ0] at hkerev hU
    exact hψc.eventually (hkerev.and hU)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hψev.and hev2)
  -- Step 3: the `g j` are constant on the graph `ψ (ball 0 δ)`.
  have hconst : ∀ κ ∈ Metric.ball (0 : K) δ, ∀ j, g j (ψ κ) = g j θ₀ := by
    intro κ hκ j
    have h := const_lsi (hF.differentiable one_ne_zero) ρ ((hg j).differentiable one_ne_zero)
      Metric.isOpen_ball (convex_ball 0 δ) (fun κ hκ => (hball κ hκ).1.2.2)
      (fun κ hκ => (hball κ hκ).1.1) (fun κ hκ => (hball κ hκ).2.1 j) hκ
      (Metric.mem_ball_self hδ)
    rwa [hψ0] at h
  -- Step 4: dimension.
  have hsub : ψ '' Metric.ball (0 : K) δ ⊆ ⋃ i, Φ i '' Ω i := by
    rintro _ ⟨κ, hκ, rfl⟩
    obtain ⟨i, m, hm, hΦm⟩ := hUsub (ψ κ) (hball κ hκ).2.2 (hconst κ hκ)
    exact Set.mem_iUnion.2 ⟨i, m, hm, hΦm⟩
  exact finrank_le_lsi Φ Ω (fun i => (hΦ i).differentiableOn one_ne_zero) ψ c θ₀
    (Metric.ball_mem_nhds 0 hδ) (fun κ hκ => (hball κ hκ).1.2.1) hsub


end Skips
