import SkipsLean.Imports
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The preimage of a null set under a submersion

Paper (skips paper): proof of Lemma A.26, "So `G_X(ℝ^{P'}) ∩ Y` has measure zero in `Y`, and so
does its preimage under `F_X` in `U`" (and the same step in the proof of Lemma A.24). In the Lean
route the constant rank theorem is not used: a linear projection `π` is chosen so that `π ∘ F_X`
has an onto derivative near the point, and this file states the fact that is then needed: the
preimage of a set of measure zero under a continuously differentiable map whose derivative is onto
at every point of an open set has measure zero in that set.
-/

namespace Skips

open MeasureTheory

open Set Filter Topology in
/-- Step 1 (change of variables): if `φ : E → E` is injective on an open set `V`, differentiable
there with an invertible derivative, and `S` is a measurable null set, then `V ∩ φ⁻¹(S)` is null:
`∫_{V ∩ φ⁻¹ S} |det φ'| = μ (φ (V ∩ φ⁻¹ S)) ≤ μ S = 0`, and the integrand is positive. -/
private lemma measure_inter_preimage_null_of_injOn_sn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {φ : E → E} {φ' : E → E →L[ℝ] E} {V S : Set E}
    (hV : IsOpen V) (hS : MeasurableSet S) (hS0 : μ S = 0)
    (hφ : ∀ y ∈ V, HasFDerivAt φ (φ' y) y) (hdet : ∀ y ∈ V, (φ' y).det ≠ 0)
    (hinj : InjOn φ V) : μ (V ∩ φ ⁻¹' S) = 0 := by
  classical
  -- `V ∩ φ⁻¹ S` is measurable: on `V`, `φ` agrees with a measurable map
  have hcont : ContinuousOn φ V := fun y hy => (hφ y hy).continuousAt.continuousWithinAt
  have hmeas : Measurable (V.piecewise φ 0) :=
    hcont.measurable_piecewise continuous_zero.continuousOn hV.measurableSet
  have hs : MeasurableSet (V ∩ φ ⁻¹' S) := by
    have : V ∩ φ ⁻¹' S = V ∩ (V.piecewise φ 0) ⁻¹' S := by
      ext y
      constructor
      · rintro ⟨hy, hyS⟩
        exact ⟨hy, by simpa only [mem_preimage, Set.piecewise_eq_of_mem _ _ _ hy] using hyS⟩
      · rintro ⟨hy, hyS⟩
        exact ⟨hy, by simpa only [mem_preimage, Set.piecewise_eq_of_mem _ _ _ hy] using hyS⟩
    rw [this]
    exact hV.measurableSet.inter (hmeas hS)
  have hderiv : ∀ y ∈ V ∩ φ ⁻¹' S, HasFDerivWithinAt φ (φ' y) (V ∩ φ ⁻¹' S) y :=
    fun y hy => (hφ y hy.1).hasFDerivWithinAt
  -- change of variables: the integral of `|det φ'|` over the set is `μ (φ '' _) ≤ μ S = 0`
  have hint : ∫⁻ y in V ∩ φ ⁻¹' S, ENNReal.ofReal |(φ' y).det| ∂μ = 0 := by
    rw [lintegral_abs_det_fderiv_eq_addHaar_image μ hs hderiv (hinj.mono inter_subset_left)]
    exact measure_mono_null (by rintro _ ⟨y, hy, rfl⟩; exact hy.2) hS0
  -- the integrand is positive on the set, so the set is null
  have hae := (lintegral_eq_zero_iff'
    (aemeasurable_ofReal_abs_det_fderivWithin μ hs hderiv)).1 hint
  have hfalse : ∀ᵐ y ∂(μ.restrict (V ∩ φ ⁻¹' S)), False := by
    filter_upwards [hae, ae_restrict_mem hs] with y h1 h2
    have hpos : 0 < |(φ' y).det| := abs_pos.2 (hdet y h2.1)
    have h0 : ENNReal.ofReal |(φ' y).det| = 0 := h1
    rw [ENNReal.ofReal_eq_zero] at h0
    linarith
  rw [← Measure.restrict_eq_zero]
  exact ae_eq_bot.1 (eventually_false_iff_eq_bot.1 hfalse)

open Set Filter Topology in
/-- The preimage of a null set under an onto linear map is null. -/
private lemma measure_preimage_linear_null_sn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure F) [ν.IsAddHaarMeasure] (L : E →L[ℝ] F) (hL : Function.Surjective L)
    {N : Set F} (hNm : MeasurableSet N) (hN : ν N = 0) : μ (L ⁻¹' N) = 0 := by
  have h := (ae_comp_linearMap_mem_iff (L : E →ₗ[ℝ] F) μ ν hL hNm.compl).2
    (by rw [ae_iff]; simpa only [mem_compl_iff, not_not, ofPred_mem_eq] using hN)
  rw [ae_iff] at h
  simp only [mem_compl_iff, not_not, ContinuousLinearMap.coe_coe] at h
  exact h

open Set Filter Topology in
/-- Continuity of `B ↦ B.prod p`. -/
private lemma continuous_prod_const_sn {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p : E →L[ℝ] G) : Continuous fun B : E →L[ℝ] F => B.prod p := by
  -- `B.prod p = inl ∘ B + inr ∘ p`
  have h : (fun B : E →L[ℝ] F => B.prod p) =
      fun B => (ContinuousLinearMap.inl ℝ F G).comp B + (ContinuousLinearMap.inr ℝ F G).comp p := by
    funext B
    ext v <;> simp
  rw [h]
  exact (continuous_const.clm_comp continuous_id).add continuous_const

open Set Filter Topology in
/-- Step 2 (local): near each point `x` of `U`, `f⁻¹(N)` is null. With `K = ker f'(x)` and a
continuous linear projection `p : E → K`, the map `e = (f'(x), p) : E → F × K` is a linear
equivalence; `φ = e⁻¹ ∘ (f, p)` has derivative `id` at `x`, so it is injective with invertible
derivative near `x`, and `f = f'(x) ∘ φ`, so `f⁻¹(N) = φ⁻¹(f'(x)⁻¹(N))`. -/
private lemma exists_nhds_measure_inter_preimage_eq_zero_sn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure F) [ν.IsAddHaarMeasure] {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {x : E} (hx : x ∈ U) (hsurj : Function.Surjective (fderiv ℝ f x))
    {N : Set F} (hNm : MeasurableSet N) (hN : ν N = 0) :
    ∃ V ∈ 𝓝 x, μ (V ∩ f ⁻¹' N) = 0 := by
  classical
  set f' : E →L[ℝ] F := fderiv ℝ f x
  -- a continuous linear projection `p` onto the kernel `K` of `f'`
  let K : Submodule ℝ E := LinearMap.ker (f' : E →ₗ[ℝ] F)
  obtain ⟨q, hq⟩ := K.subtype.exists_leftInverse_of_injective K.ker_subtype
  let p : E →L[ℝ] K := LinearMap.toContinuousLinearMap q
  have hp : ∀ k : K, p k = k := fun k => LinearMap.congr_fun hq k
  -- `A = (f', p) : E → F × K` is a linear bijection
  let A : E →L[ℝ] F × K := f'.prod p
  have hA : Function.Bijective A := by
    constructor
    · intro v w hvw
      have h1 : f' v = f' w := congrArg Prod.fst hvw
      have h2 : p v = p w := congrArg Prod.snd hvw
      have hmem : v - w ∈ K := by
        change f' (v - w) = 0
        rw [map_sub, h1, sub_self]
      have h3 := hp ⟨v - w, hmem⟩
      rw [map_sub, h2, sub_self] at h3
      have h4 : v - w = 0 := congrArg Subtype.val h3.symm
      exact sub_eq_zero.1 h4
    · rintro ⟨w, k⟩
      obtain ⟨u, rfl⟩ := hsurj w
      have hpu : ((p u : K) : E) ∈ K := (p u).2
      have hk : (k : E) ∈ K := k.2
      refine ⟨u - (p u : E) + (k : E), ?_⟩
      have e1 : f' (u - (p u : E) + (k : E)) = f' u := by
        have a1 : f' ((p u : K) : E) = 0 := hpu
        have a2 : f' (k : E) = 0 := hk
        rw [map_add, map_sub, a1, a2, sub_zero, add_zero]
      have e2 : p (u - (p u : E) + (k : E)) = k := by
        rw [map_add, map_sub, hp, hp, sub_self, zero_add]
      exact Prod.ext e1 e2
  let e : E ≃L[ℝ] F × K :=
    (LinearEquiv.ofBijective (A : E →ₗ[ℝ] F × K) hA).toContinuousLinearEquiv
  have he : ∀ v, e v = A v := fun v => rfl
  -- `φ = e⁻¹ ∘ (f, p)`, with `f = f' ∘ φ`
  let φ : E → E := fun y => e.symm (f y, p y)
  have hfφ : ∀ y, f' (φ y) = f y := by
    intro y
    have h : A (φ y) = (f y, p y) := by rw [← he]; exact e.apply_symm_apply _
    exact congrArg Prod.fst h
  -- derivatives of `f` and of `φ` on `U`
  have hfd : ∀ y ∈ U, HasFDerivAt f (fderiv ℝ f y) y := fun y hy =>
    ((hf.differentiableOn one_ne_zero y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  let φ' : E → E →L[ℝ] E := fun y => (e.symm : F × K →L[ℝ] E).comp ((fderiv ℝ f y).prod p)
  have hφ : ∀ y ∈ U, HasFDerivAt φ (φ' y) y := fun y hy =>
    (e.symm : F × K →L[ℝ] E).hasFDerivAt.comp y ((hfd y hy).prodMk p.hasFDerivAt)
  have hφx : φ' x = ContinuousLinearMap.id ℝ E := by
    ext v
    exact e.symm_apply_apply v
  -- `φ` is injective near `x` (inverse function theorem: strict derivative `id`)
  have hstrict : HasStrictFDerivAt φ ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) x := by
    have h1 : HasStrictFDerivAt f f' x :=
      (hf.contDiffAt (hU.mem_nhds hx)).hasStrictFDerivAt (hfd x hx) one_ne_zero
    have h2 := (e.symm : F × K →L[ℝ] E).hasStrictFDerivAt.comp x (h1.prodMk p.hasStrictFDerivAt)
    exact h2.congr_fderiv hφx
  let H := hstrict.toOpenPartialHomeomorph φ
  -- `det φ'` is continuous at `x` with value `1`, so it is nonzero near `x`
  have hcont : ContinuousAt (fun y => (φ' y).det) x := by
    have hc1 : ContinuousAt (fderiv ℝ f) x :=
      (hf.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hx)
    have hc2 : Continuous fun B : E →L[ℝ] F => (e.symm : F × K →L[ℝ] E).comp (B.prod p) :=
      continuous_const.clm_comp (continuous_prod_const_sn p)
    exact ContinuousLinearMap.continuous_det.continuousAt.comp (hc2.continuousAt.comp hc1)
  have hdet1 : (φ' x).det ≠ 0 := by
    have h1 : (ContinuousLinearMap.id ℝ E).det = 1 := LinearMap.det_id
    rw [hφx, h1]
    exact one_ne_zero
  obtain ⟨t, ht, htopen, hxt⟩ := mem_nhds_iff.1 (hcont.eventually_ne hdet1)
  -- the neighbourhood `V = U ∩ source ∩ t`
  refine ⟨U ∩ H.source ∩ t, ?_, ?_⟩
  · exact (hU.inter H.open_source).inter htopen |>.mem_nhds
      ⟨⟨hx, hstrict.mem_toOpenPartialHomeomorph_source⟩, hxt⟩
  have hpre : f ⁻¹' N = φ ⁻¹' (f' ⁻¹' N) := by
    ext y
    simp only [mem_preimage, hfφ]
  rw [hpre]
  refine measure_inter_preimage_null_of_injOn_sn μ ((hU.inter H.open_source).inter htopen)
    (hNm.preimage f'.measurable) (measure_preimage_linear_null_sn μ ν f' hsurj hNm hN)
    (fun y hy => hφ y hy.1.1) (fun y hy => ht hy.2) ?_
  exact H.injOn.mono fun y hy => hy.1.2

/-- **The preimage of a null set under a `C¹` submersion is null:** let `f` be continuously
differentiable on the open set `U`, with an onto derivative at every point of `U`. Then for every
set `N` of measure zero in the target, `U ∩ f⁻¹(N)` has measure zero. -/
theorem measure_inter_preimage_eq_zero_of_surjective_fderiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F)
    [ν.IsAddHaarMeasure] (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hsurj : ∀ x ∈ U, Function.Surjective (fderiv ℝ f x)) (N : Set F) (hN : ν N = 0) :
    μ (U ∩ f ⁻¹' N) = 0 := by
  -- reduce to a measurable null set `N' ⊇ N`
  obtain ⟨N', hNN', hN'm, hN'0⟩ := exists_measurable_superset_of_null hN
  refine measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono hNN')) ?_
  -- local to global: every point of `U ∩ f⁻¹(N')` has a neighbourhood in which the set is null
  refine measure_null_of_locally_null _ fun x hx => ?_
  obtain ⟨V, hV, hV0⟩ := exists_nhds_measure_inter_preimage_eq_zero_sn μ ν hU hf hx.1
    (hsurj x hx.1) hN'm hN'0
  refine ⟨(U ∩ f ⁻¹' N') ∩ V, inter_mem_nhdsWithin _ hV, measure_mono_null ?_ hV0⟩
  exact fun y hy => ⟨hy.2, hy.1.2⟩

end Skips
