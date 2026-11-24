import SkipsLean.Dimension.RankCriterion

/-!
# A rank criterion on an open set, against countably many maps

Paper (absorb paper): proof of Proposition 4.7, Step 4: "By the constant rank theorem, after
shrinking `V`, `F_Z` maps `V` onto an embedded manifold `Y` of dimension `r`, and a linear
projection `pr` onto `ℝ^r` maps `Y` diffeomorphically onto an open set. Let
`n < L d_model² / (2 d_model − 1)`, so that every map `F'^π_Z` of a skipless network with `n` more
units has rank less than `r`. Then all values of `pr ∘ F'^π_Z` are critical, and by Sard's theorem
its image is a null set of `ℝ^r`. If the residual network with weights `θ ∈ V` equals a skipless
network with weights `η`, then `F_Z(θ) = F'^π_Z(η)` for the pattern `π` of `η`, so `pr(F_Z(θ))`
lies in this null set. As `pr ∘ F_Z` is a submersion on `V`, such `θ` form a null set. There are
finitely many `n` below the bound, finitely many choices of widths with `n` more units and
finitely many patterns on `Z`".

This is Lemma A.26 (i) of the skips paper (`ae_notMem_range_of_rank_lt`,
`Dimension/RankCriterion.lean`) in a local form: the map `F` is continuously differentiable on an
open set `U` only, the maps `G i` are countably many real-analytic maps on spaces that may
differ, and the conclusion holds at almost every point of `U`. Sard's theorem is the hypothesis
from the literature `SardCriticalValues` (`Literature/Sard.lean`). No constant rank theorem is
used: near a point of `U`, a linear `π` onto `ℝ^r` makes `π ∘ F` a submersion
(`measure_inter_preimage_eq_zero_of_surjective_fderiv`, `Dimension/SubmersionNull.lean`).
-/

namespace Skips

open MeasureTheory

variable {P Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y]

omit [FiniteDimensional ℝ P] [MeasurableSpace P] [BorelSpace P] in
/-- Helper (copy of the private `exists_surjective_comp_rc`, `Dimension/RankCriterion.lean`): for
a linear map `A : E → Y` of rank `r`, a linear `π : Y → ℝ^r` with `π ∘ A` onto (a left inverse of
the inclusion of the range, followed by coordinates on the range). -/
private theorem exists_surjective_comp_rco {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
/-- Helper (copy of the private `fderiv_clm_comp_rc`): the derivative of `π ∘ F` is `π ∘ DF`. -/
private theorem fderiv_clm_comp_rco {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (π : Y →L[ℝ] Z) {F : P → Y} {θ : P} (hF : DifferentiableAt ℝ F θ) :
    fderiv ℝ (fun x => π (F x)) θ = π.comp (fderiv ℝ F θ) :=
  (π.hasFDerivAt.comp θ hF.hasFDerivAt).fderiv

omit [FiniteDimensional ℝ P] [MeasurableSpace P] [BorelSpace P] [FiniteDimensional ℝ Y] in
/-- Helper: if `F` is `C¹` on the open set `U` and `π ∘ DF(θ₀)` is onto `ℝ^r` at a point `θ₀` of
`U`, then `π ∘ DF(θ)` is onto on an open set `U₀ ⊆ U` that contains `θ₀`. With a right inverse `N`
of `π ∘ DF(θ₀)`, the determinant of `π ∘ DF(θ) ∘ N` is continuous on `U` and equal to `1` at `θ₀`:
`U₀` is the set of points of `U` where it does not vanish. -/
private theorem exists_isOpen_surjective_on_rco {r : ℕ} {F : P → Y} {U : Set P}
    (hF : ContDiffOn ℝ 1 F U) (hU : IsOpen U) (π : Y →L[ℝ] (Fin r → ℝ)) {θ₀ : P}
    (hθ₀ : θ₀ ∈ U) (h₀ : Function.Surjective (π.comp (fderiv ℝ F θ₀))) :
    ∃ U₀ : Set P, IsOpen U₀ ∧ θ₀ ∈ U₀ ∧ U₀ ⊆ U ∧
      ∀ θ ∈ U₀, Function.Surjective (π.comp (fderiv ℝ F θ)) := by
  -- a right inverse `N` of `π ∘ DF(θ₀)`, as a continuous linear map `N'`
  obtain ⟨N, hN⟩ := ((π.comp (fderiv ℝ F θ₀) : P →L[ℝ] (Fin r → ℝ)) :
    P →ₗ[ℝ] (Fin r → ℝ)).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 h₀)
  let N' : (Fin r → ℝ) →L[ℝ] P := LinearMap.toContinuousLinearMap N
  -- the determinant `φ θ` of `π ∘ DF(θ) ∘ N` is continuous on `U` (`DF` is continuous there)
  let φ : P → ℝ := fun θ => (π.comp ((fderiv ℝ F θ).comp N')).det
  have hφ : ContinuousOn φ U :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (continuousOn_const.clm_comp ((hF.continuousOn_fderiv_of_isOpen hU le_rfl).clm_comp
        continuousOn_const))
  -- `φ θ₀ = det id = 1`
  have hφ₀ : φ θ₀ = 1 := by
    have h1 : ((π.comp ((fderiv ℝ F θ₀).comp N') : (Fin r → ℝ) →L[ℝ] (Fin r → ℝ)) :
        (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ)) = LinearMap.id := hN
    show LinearMap.det _ = 1
    rw [h1, LinearMap.det_id]
  -- `U₀ = U ∩ {φ ≠ 0}` is open and contains `θ₀`
  have hθ₀' : θ₀ ∈ φ ⁻¹' {0}ᶜ := by
    rw [Set.mem_preimage, hφ₀]
    exact one_ne_zero
  refine ⟨U ∩ φ ⁻¹' {0}ᶜ, hφ.isOpen_inter_preimage hU isOpen_compl_singleton, ⟨hθ₀, hθ₀'⟩,
    Set.inter_subset_left, fun θ hθ => ?_⟩
  -- on `U₀`, `π ∘ DF(θ) ∘ N` is invertible, so `π ∘ DF(θ)` is onto
  have hdet : LinearMap.det ((π.comp ((fderiv ℝ F θ).comp N') :
      (Fin r → ℝ) →L[ℝ] (Fin r → ℝ)) : (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ)) ≠ 0 := hθ.2
  have hbij := (Module.End.isUnit_iff _).1
    ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  exact fun v => let ⟨w, hw⟩ := hbij.2 v; ⟨N' w, hw⟩

omit [FiniteDimensional ℝ Y] in
/-- Helper (copy of the private `volume_range_eq_zero_rc`, Sard's step): if `DG` has rank at most
`r₀ < r` everywhere, the image of `π ∘ G` in `ℝ^r` is null, for every linear `π : Y → ℝ^r`: every
point is critical. -/
private theorem volume_range_eq_zero_rco {P' : Type*} [NormedAddCommGroup P'] [NormedSpace ℝ P']
    [FiniteDimensional ℝ P'] {r : ℕ} (hSard : SardCriticalValues P' (Fin r → ℝ))
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
    rw [fderiv_clm_comp_rco π (hG η (Set.mem_univ η)).differentiableAt]
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

/-- **Proof of Proposition 4.7 of the absorb paper, Step 4, without networks, given Sard's
theorem:** let `F` be continuously differentiable on the open set `U`, with a Jacobian of rank
greater than `r₀` at every point of `U`, and let `G i`, for `i` in a countable set, be
real-analytic maps whose Jacobians have rank at most `r₀` everywhere. Then for almost every
`θ ∈ U` the value `F θ` is a value of no `G i`. -/
theorem ae_notMem_iUnion_range_of_rank_lt_on {ι : Type*} [Countable ι] {P' : ι → Type*}
    [∀ i, NormedAddCommGroup (P' i)] [∀ i, NormedSpace ℝ (P' i)]
    [∀ i, FiniteDimensional ℝ (P' i)]
    (hSard : ∀ (i : ι) (r : ℕ), SardCriticalValues (P' i) (Fin r → ℝ))
    (F : P → Y) (U : Set P) (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U)
    (G : ∀ i, P' i → Y) (hG : ∀ i, AnalyticOnNhd ℝ (G i) Set.univ) (r₀ : ℕ)
    (hGr : ∀ i η, Module.finrank ℝ (LinearMap.range (fderiv ℝ (G i) η).toLinearMap) ≤ r₀)
    (hFr : ∀ θ ∈ U, r₀ < Module.finrank ℝ (LinearMap.range (fderiv ℝ F θ).toLinearMap))
    (μ : Measure P) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, θ ∈ U → ∀ i, F θ ∉ Set.range (G i) := by
  -- the bad set `B`: the points of `U` at which `F` takes a value of some `G i`
  set B : Set P := {θ | θ ∈ U ∧ ∃ i, F θ ∈ Set.range (G i)} with hBdef
  have hB : μ B = 0 := by
    -- locally null is null: a neighbourhood of each `θ₀ ∈ B` meets `B` in a null set
    refine measure_null_of_locally_null B fun θ₀ hθ₀ => ?_
    -- `π : Y → ℝ^r`, `r = rank DF(θ₀) > r₀`, with `π ∘ DF` onto on an open `U₀ ∋ θ₀`
    obtain ⟨π, hπ⟩ := exists_surjective_comp_rco (fderiv ℝ F θ₀)
    obtain ⟨U₀, hU₀, hθ₀U₀, hU₀U, hsurj⟩ :=
      exists_isOpen_surjective_on_rco hF hU π hθ₀.1 hπ
    -- `π ∘ F` is a `C¹` submersion on `U₀`: its derivative is `π ∘ DF`
    have hc := π.contDiff.comp_contDiffOn hF
    have hf : ContDiffOn ℝ 1 (fun θ => π (F θ)) U₀ := hc.mono hU₀U
    have hs : ∀ θ ∈ U₀, Function.Surjective (fderiv ℝ (fun x => π (F x)) θ) := fun θ hθ => by
      have hd : DifferentiableAt ℝ F θ :=
        (hF.differentiableOn one_ne_zero θ (hU₀U hθ)).differentiableAt (hU.mem_nhds (hU₀U hθ))
      rw [fderiv_clm_comp_rco π hd]
      exact hsurj θ hθ
    -- the values of the maps `π ∘ G i` form a null set of `ℝ^r` (Sard, `ι` countable)
    have hN : volume (⋃ i, Set.range fun η => π (G i η)) = 0 :=
      measure_iUnion_null fun i =>
        volume_range_eq_zero_rco (hSard i _) (hG i) (hGr i) (hFr θ₀ hθ₀.1) π
    -- its preimage under the submersion `π ∘ F` on `U₀` is null, and contains `B ∩ U₀`
    have h0 := measure_inter_preimage_eq_zero_of_surjective_fderiv μ volume
      (fun x => π (F x)) U₀ hU₀ hf hs _ hN
    refine ⟨B ∩ U₀, inter_mem_nhdsWithin B (hU₀.mem_nhds hθ₀U₀), measure_mono_null ?_ h0⟩
    rintro θ ⟨⟨-, i, η, hη⟩, hθU₀⟩
    exact ⟨hθU₀, Set.mem_iUnion.2 ⟨i, η, congrArg π hη⟩⟩
  -- the exceptional set of the claim lies in `B`
  rw [ae_iff]
  refine measure_mono_null (fun θ hθ => ?_) hB
  by_contra h
  exact hθ fun hθU i hi => h ⟨hθU, i, hi⟩

end Skips
