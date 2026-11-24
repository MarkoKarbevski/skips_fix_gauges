import SkipsLean.Literature.Sard
import SkipsLean.Literature.OMinimal
import SkipsLean.Dimension.SubmersionNull
import SkipsLean.Generic.AnalyticZeroSet

/-!
# A rank criterion

Paper (skips paper): Lemma A.26 (A rank criterion), without networks. Two parametrized families
are given by their outputs on a finite batch, `F : P → Y` and `G : P' → Y`, real-analytic in the
parameters. In the paper the rank of the Jacobian of `G` is at most `r₀ = P' - k` at every
parameter because a Lie group acts on the parameters of `G` with orbits of dimension at least `k`
(at generic parameters, then everywhere, the rank being lower semicontinuous); here the bound
`rank DG ≤ r₀` at every point is the hypothesis. The rank of the Jacobian of `F` exceeds `r₀` at
one parameter `θ₀`.

(i) For almost every `θ`, `F θ` is not an output of the family `G`.
(ii) If the set of outputs of `G` has the property of definable sets used in the paper
(`ClosureNullOfNull`), then for almost every `θ`, `F θ` is not in the closure of the outputs of
`G`: some `δ > 0` separates it from all of them.

The Lean route follows the paper's proof, without the constant rank theorem: at a `θ` where the
Jacobian of `F` has its largest rank `r*`, a linear `π : Y → ℝ^{r*}` is chosen with `π ∘ DF(θ)`
onto; `π ∘ F` is a submersion near `θ`; `π ∘ G` has rank less than `r*` everywhere, "so all its
values are critical, and by Sard's theorem its image has measure zero"; the preimage of this image
under `π ∘ F` has measure zero near `θ` (`Dimension/SubmersionNull.lean`); countably many
neighbourhoods cover the set where the rank is `r*`, whose complement has measure zero (analytic
minors). Sard's theorem is a hypothesis from the literature (`Literature/Sard.lean`).
-/

namespace Skips

open MeasureTheory

variable {P P' Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P] [NormedAddCommGroup P'] [NormedSpace ℝ P']
  [FiniteDimensional ℝ P'] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

omit [FiniteDimensional ℝ P] in
/-- Helper: for a linear map `A : E → Y` of rank `r`, a linear `π : Y → ℝ^r` with `π ∘ A` onto (a
left inverse of the inclusion of the range, followed by coordinates on the range). -/
private theorem exists_surjective_comp_rc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] Y) :
    ∃ π : Y →L[ℝ] (Fin (Module.finrank ℝ (LinearMap.range A.toLinearMap)) → ℝ),
      Function.Surjective (π.comp A) := by
  set R := LinearMap.range A.toLinearMap
  -- a left inverse `p` of the inclusion `R → Y`, and coordinates `e` on `R`
  obtain ⟨p, hp⟩ := R.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype R)
  let e : R ≃ₗ[ℝ] (Fin (Module.finrank ℝ R) → ℝ) :=
    LinearEquiv.ofFinrankEq _ _ (Module.finrank_fin_fun ℝ).symm
  refine ⟨LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ p), fun v => ?_⟩
  -- `e⁻¹ v` lies in the range of `A`
  obtain ⟨w, hw⟩ := (e.symm v).2
  refine ⟨w, ?_⟩
  have hpv : p (e.symm v : Y) = e.symm v := LinearMap.congr_fun hp (e.symm v)
  show e (p (A w)) = v
  have hw' : A w = (e.symm v : Y) := hw
  rw [hw', hpv, LinearEquiv.apply_symm_apply]

omit [FiniteDimensional ℝ P] [MeasurableSpace P] [BorelSpace P] [FiniteDimensional ℝ Y] in
/-- Helper: the derivative of `π ∘ F` is `π ∘ DF`. -/
private theorem fderiv_clm_comp_rc {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (π : Y →L[ℝ] Z) {F : P → Y} {θ : P} (hF : DifferentiableAt ℝ F θ) :
    fderiv ℝ (fun x => π (F x)) θ = π.comp (fderiv ℝ F θ) :=
  (π.hasFDerivAt.comp θ hF.hasFDerivAt).fderiv

/-- Helper: if `π ∘ DF(θ₀)` is onto `ℝ^r`, then `π ∘ DF(θ)` is onto on an open set `U` of full
measure. With a right inverse `N` of `π ∘ DF(θ₀)`, the determinant of `π ∘ DF(θ) ∘ N` is analytic
in `θ` and equal to `1` at `θ₀`: `U` is the set where it does not vanish. -/
private theorem exists_isOpen_surjective_rc {r : ℕ} {F : P → Y} (hF : AnalyticOnNhd ℝ F Set.univ)
    (π : Y →L[ℝ] (Fin r → ℝ)) {θ₀ : P} (h₀ : Function.Surjective (π.comp (fderiv ℝ F θ₀)))
    (μ : Measure P) [μ.IsAddHaarMeasure] :
    ∃ U : Set P, IsOpen U ∧ μ Uᶜ = 0 ∧ ∀ θ ∈ U, Function.Surjective (π.comp (fderiv ℝ F θ)) := by
  -- a right inverse `N` of `π ∘ DF(θ₀)`
  obtain ⟨N, hN⟩ := ((π.comp (fderiv ℝ F θ₀) : P →L[ℝ] (Fin r → ℝ)) :
    P →ₗ[ℝ] (Fin r → ℝ)).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 h₀)
  -- the matrix of `π ∘ L ∘ N`, a linear function of `L`
  let b := Pi.basisFun ℝ (Fin r)
  let Ψ : (P →L[ℝ] Y) →ₗ[ℝ] Matrix (Fin r) (Fin r) ℝ :=
    (LinearMap.toMatrix b b).toLinearMap ∘ₗ
      (LinearMap.llcomp ℝ (Fin r → ℝ) Y (Fin r → ℝ) (π : Y →ₗ[ℝ] (Fin r → ℝ))) ∘ₗ
      (LinearMap.lcomp ℝ Y N) ∘ₗ (ContinuousLinearMap.coeLM ℝ)
  have hΨ : ∀ L : P →L[ℝ] Y, Ψ L = LinearMap.toMatrix b b
      ((π : Y →ₗ[ℝ] (Fin r → ℝ)) ∘ₗ ((L : P →ₗ[ℝ] Y) ∘ₗ N)) := fun L => rfl
  -- its determinant at `DF(θ)` is analytic in `θ`
  let φ : P → ℝ := fun θ => (Ψ (fderiv ℝ F θ)).det
  have hentry : ∀ i j, AnalyticOnNhd ℝ (fun θ => Ψ (fderiv ℝ F θ) i j) Set.univ := fun i j =>
    ((LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℝ ℝ i j) ∘ₗ Ψ)).analyticOnNhd
      _).comp hF.fderiv (Set.mapsTo_univ _ _)
  have hφ : AnalyticOnNhd ℝ φ Set.univ := by
    show AnalyticOnNhd ℝ (fun θ => (Ψ (fderiv ℝ F θ)).det) Set.univ
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (σ i) i)
  -- `φ θ₀ = det 1 = 1`
  have hφ₀ : φ θ₀ = 1 := by
    show (Ψ (fderiv ℝ F θ₀)).det = 1
    rw [hΨ]
    have h1 : (π : Y →ₗ[ℝ] (Fin r → ℝ)) ∘ₗ (((fderiv ℝ F θ₀ : P →L[ℝ] Y) : P →ₗ[ℝ] Y) ∘ₗ N) =
        LinearMap.id := hN
    rw [h1, LinearMap.toMatrix_id, Matrix.det_one]
  -- `U = {φ ≠ 0}` is open, and its complement is null
  refine ⟨{θ | φ θ ≠ 0}, ?_, ?_, ?_⟩
  · exact isOpen_ne_fun (continuousOn_univ.mp hφ.continuousOn) continuous_const
  · have hnull := measure_zeroSet_of_analytic μ hφ ⟨θ₀, by rw [hφ₀]; exact one_ne_zero⟩
    have hc : {θ | φ θ ≠ 0}ᶜ = {θ | φ θ = 0} := by
      ext θ
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
    rw [hc]
    exact hnull
  -- on `U`, `π ∘ DF(θ) ∘ N` is invertible, so `π ∘ DF(θ)` is onto
  · intro θ hθ
    have hdet : LinearMap.det ((π : Y →ₗ[ℝ] (Fin r → ℝ)) ∘ₗ
        (((fderiv ℝ F θ : P →L[ℝ] Y) : P →ₗ[ℝ] Y) ∘ₗ N)) ≠ 0 := by
      rw [← LinearMap.det_toMatrix b]
      exact hθ
    have hbij := (Module.End.isUnit_iff _).1
      ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
    exact fun v => let ⟨w, hw⟩ := hbij.2 v; ⟨N w, hw⟩

omit [FiniteDimensional ℝ Y] in
/-- Helper: with `π ∘ DF` onto on an open set `U` of full measure, the preimage under `π ∘ F` of a
null set is null. -/
private theorem ae_notMem_of_null_rc {r : ℕ} {F : P → Y} (hF : AnalyticOnNhd ℝ F Set.univ)
    (π : Y →L[ℝ] (Fin r → ℝ)) (μ : Measure P) [μ.IsAddHaarMeasure] {U : Set P} (hU : IsOpen U)
    (hUc : μ Uᶜ = 0) (hsurj : ∀ θ ∈ U, Function.Surjective (π.comp (fderiv ℝ F θ)))
    {C : Set (Fin r → ℝ)} (hC : volume C = 0) :
    ∀ᵐ θ ∂μ, π (F θ) ∉ C := by
  -- `π ∘ F` is analytic, hence `C¹`, with derivative `π ∘ DF`
  have hf : AnalyticOnNhd ℝ (fun x => π (F x)) Set.univ :=
    (π.analyticOnNhd Set.univ).comp hF (Set.mapsTo_univ _ _)
  have hf1 : ContDiffOn ℝ 1 (fun x => π (F x)) U :=
    (hf.contDiffOn_of_completeSpace).mono (Set.subset_univ U)
  have hs : ∀ θ ∈ U, Function.Surjective (fderiv ℝ (fun x => π (F x)) θ) := fun θ hθ => by
    rw [fderiv_clm_comp_rc π (hF θ (Set.mem_univ θ)).differentiableAt]
    exact hsurj θ hθ
  have hnull := measure_inter_preimage_eq_zero_of_surjective_fderiv μ volume
    (fun x => π (F x)) U hU hf1 hs C hC
  -- the bad set lies in `Uᶜ ∪ (U ∩ (π ∘ F)⁻¹ C)`
  rw [ae_iff]
  refine measure_mono_null (fun θ hθ => ?_) (measure_union_null hUc hnull)
  simp only [Set.mem_ofPred_eq, not_not] at hθ
  by_cases hθU : θ ∈ U
  · exact Or.inr ⟨hθU, hθ⟩
  · exact Or.inl hθU

omit [FiniteDimensional ℝ Y] in
/-- Helper (Sard's step): if `DG` has rank at most `r₀ < r` everywhere, the image of `π ∘ G` in
`ℝ^r` is null, for every linear `π : Y → ℝ^r`: every point is critical. -/
private theorem volume_range_eq_zero_rc {r : ℕ} (hSard : SardCriticalValues P' (Fin r → ℝ))
    {G : P' → Y} (hG : AnalyticOnNhd ℝ G Set.univ) {r₀ : ℕ}
    (hGr : ∀ η, Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap) ≤ r₀)
    (hr : r₀ < r) (π : Y →L[ℝ] (Fin r → ℝ)) :
    volume (Set.range fun η => π (G η)) = 0 := by
  have hg : AnalyticOnNhd ℝ (fun η => π (G η)) Set.univ :=
    (π.analyticOnNhd Set.univ).comp hG (Set.mapsTo_univ _ _)
  -- no derivative of `π ∘ G` is onto: its rank is at most `r₀ < r`
  have hcrit : {η | ¬ Function.Surjective (fderiv ℝ (fun η => π (G η)) η)} = Set.univ := by
    refine Set.eq_univ_of_forall fun η => ?_
    simp only [Set.mem_ofPred_eq]
    rw [fderiv_clm_comp_rc π (hG η (Set.mem_univ η)).differentiableAt]
    intro hs
    have htop : LinearMap.range ((π.comp (fderiv ℝ G η) : P' →L[ℝ] (Fin r → ℝ)) :
        P' →ₗ[ℝ] (Fin r → ℝ)) = ⊤ := LinearMap.range_eq_top.2 hs
    have h1 : Module.finrank ℝ (LinearMap.range ((π.comp (fderiv ℝ G η) :
        P' →L[ℝ] (Fin r → ℝ)) : P' →ₗ[ℝ] (Fin r → ℝ))) = r := by
      rw [htop, finrank_top, Module.finrank_fin_fun]
    have h2 : Module.finrank ℝ (LinearMap.range ((π.comp (fderiv ℝ G η) :
        P' →L[ℝ] (Fin r → ℝ)) : P' →ₗ[ℝ] (Fin r → ℝ))) ≤
        Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap) := by
      have h3 : ((π.comp (fderiv ℝ G η) : P' →L[ℝ] (Fin r → ℝ)) : P' →ₗ[ℝ] (Fin r → ℝ)) =
          (π : Y →ₗ[ℝ] (Fin r → ℝ)) ∘ₗ (fderiv ℝ G η).toLinearMap := rfl
      rw [h3, LinearMap.range_comp]
      exact Submodule.finrank_map_le _ _
    have := hGr η
    omega
  have h := hSard volume (fun η => π (G η)) hg
  rw [hcrit, Set.image_univ] at h
  exact h

/-- **Lemma A.26 (i) of the skips paper, without networks, given Sard's theorem:** if the
Jacobian of `G` has rank at most `r₀` at every parameter and the Jacobian of `F` has rank greater
than `r₀` at one parameter, then for almost every `θ` the output `F θ` is not an output of `G`. -/
theorem ae_notMem_range_of_rank_lt (hSard : ∀ r : ℕ, SardCriticalValues P' (Fin r → ℝ))
    (F : P → Y) (G : P' → Y) (hF : AnalyticOnNhd ℝ F Set.univ) (hG : AnalyticOnNhd ℝ G Set.univ)
    (r₀ : ℕ)
    (hGr : ∀ η, Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap) ≤ r₀)
    (θ₀ : P) (hθ₀ : r₀ < Module.finrank ℝ (LinearMap.range (fderiv ℝ F θ₀).toLinearMap))
    (μ : Measure P) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, F θ ∉ Set.range G := by
  -- `π : Y → ℝ^r`, `r = rank DF(θ₀) > r₀`, with `π ∘ DF` onto on an open set `U` of full measure
  obtain ⟨π, hπ⟩ := exists_surjective_comp_rc (fderiv ℝ F θ₀)
  obtain ⟨U, hU, hUc, hsurj⟩ := exists_isOpen_surjective_rc hF π hπ μ
  -- the image of `π ∘ G` is null (Sard), and so is its preimage under `π ∘ F`
  have hC := volume_range_eq_zero_rc (hSard _) hG hGr hθ₀ π
  filter_upwards [ae_notMem_of_null_rc hF π μ hU hUc hsurj hC] with θ hθ hmem
  obtain ⟨η, hη⟩ := hmem
  exact hθ ⟨η, congrArg π hη⟩

/-- **Lemma A.26 (ii) of the skips paper, without networks, given Sard's theorem and the
property of definable sets:** under the same hypotheses, if the set of outputs of `G` satisfies
`ClosureNullOfNull`, then for almost every `θ` the output `F θ` is not in the closure of the set of
outputs of `G`. -/
theorem ae_notMem_closure_range_of_rank_lt (hSard : ∀ r : ℕ, SardCriticalValues P' (Fin r → ℝ))
    (F : P → Y) (G : P' → Y) (hF : AnalyticOnNhd ℝ F Set.univ) (hG : AnalyticOnNhd ℝ G Set.univ)
    (hcl : ClosureNullOfNull (Set.range G)) (r₀ : ℕ)
    (hGr : ∀ η, Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap) ≤ r₀)
    (θ₀ : P) (hθ₀ : r₀ < Module.finrank ℝ (LinearMap.range (fderiv ℝ F θ₀).toLinearMap))
    (μ : Measure P) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, F θ ∉ closure (Set.range G) := by
  obtain ⟨π, hπ⟩ := exists_surjective_comp_rc (fderiv ℝ F θ₀)
  obtain ⟨U, hU, hUc, hsurj⟩ := exists_isOpen_surjective_rc hF π hπ μ
  -- `π(range G)` is null (Sard), so its closure `C` is null
  have h0 := volume_range_eq_zero_rc (hSard _) hG hGr hθ₀ π
  have hC : volume (closure (π '' Set.range G)) = 0 := by
    refine hcl _ π ?_
    rw [← Set.range_comp]
    exact h0
  filter_upwards [ae_notMem_of_null_rc hF π μ hU hUc hsurj hC] with θ hθ hmem
  -- `π` is continuous: `π(closure (range G)) ⊆ closure (π (range G))`
  exact hθ (image_closure_subset_closure_image π.continuous ⟨F θ, hmem, rfl⟩)

/-- The conclusion of Lemma A.26 (ii) in the paper's words: a point outside the closure of a set
has a positive distance `δ` to every point of the set. -/
theorem exists_pos_le_norm_sub_of_notMem_closure {y : Y} {S : Set Y} (h : y ∉ closure S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ S, δ ≤ ‖y - z‖ := by
  -- `y ∉ closure S`: some `ε > 0` is at most the distance from `y` to every point of `S`
  rw [Metric.mem_closure_iff] at h
  push Not at h
  obtain ⟨ε, hε, hS⟩ := h
  exact ⟨ε, hε, fun z hz => by rw [← dist_eq_norm]; exact hS z hz⟩

end Skips
