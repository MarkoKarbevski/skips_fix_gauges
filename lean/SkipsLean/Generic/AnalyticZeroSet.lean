import Mathlib

/-!
# The zero set of an analytic function has measure zero

Used for every statement "at generic parameters" of the papers: a statement holds at generic
parameters if it holds outside a set of Lebesgue measure zero. The conditions that the proofs use
(a matrix has full rank, a Jacobian has a given rank) fail only on the zero set of a real-analytic
function of the parameters that is not identically zero, and such a set has measure zero.

This is a known fact (for instance Mityagin, "The zero set of a real analytic function", 2015);
Mathlib does not have it at the pinned version, so it is proved here.
-/

namespace Skips

open MeasureTheory Filter

/-- One variable: a real-analytic function on `ℝ` that is not identically zero has a null zero set
(its zeros are isolated, hence countable). -/
private lemma volume_zeroSet_real {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g Set.univ)
    (hne : ∃ t, g t ≠ 0) : volume {t | g t = 0} = 0 := by
  rcases hg.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h | h
  · obtain ⟨t, ht⟩ := hne
    exact absurd (h (Set.mem_univ t)) ht
  · have hae : ∀ᵐ t ∂(volume.restrict Set.univ), g t ≠ 0 :=
      ae_restrict_le_codiscreteWithin MeasurableSet.univ h
    rw [Measure.restrict_univ, ae_iff] at hae
    simpa using hae

/-- The map `(t, y) ↦ (t, y₀, …, y_{n-1})` is analytic. -/
private lemma analyticOnNhd_cons (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ))
      Set.univ := by
  refine AnalyticOnNhd.pi (fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using
      (analyticOnNhd_fst : AnalyticOnNhd ℝ (fun p : ℝ × (Fin n → ℝ) => p.1) Set.univ)
  · simp only [Fin.cons_succ]
    exact ((ContinuousLinearMap.proj (R := ℝ) j).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ))).analyticOnNhd Set.univ

/-- The inverse of the splitting `ℝ^(n+1) ≃ ℝ × ℝ^n` at the first coordinate is `Fin.cons`. -/
private lemma piFinSuccAbove_zero_symm_apply (n : ℕ) (p : ℝ × (Fin n → ℝ)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p = Fin.cons p.1 p.2 := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

/-- Fubini step: on `ℝ × F`, if `g` is analytic and not identically zero, and every slice
`y ↦ g (t, y)` that is not identically zero has a null zero set, then the zero set of `g` is
null. The slices in `t` are analytic in one variable; outside the null set of `t` where
`g (t, y₀) = 0` (for a fixed `y₀` with `g (t₁, y₀) ≠ 0`), the slice in `y` is not identically zero. -/
private lemma prod_zeroSet_null {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] (ν : Measure F) {g : ℝ × F → ℝ} (hg : AnalyticOnNhd ℝ g Set.univ)
    (hmeas : MeasurableSet {p | g p = 0})
    (hslice : ∀ t, (∃ y, g (t, y) ≠ 0) → ν {y | g (t, y) = 0} = 0) (hne : ∃ p, g p ≠ 0) :
    (volume.prod ν) {p | g p = 0} = 0 := by
  obtain ⟨⟨t₁, y₀⟩, h₁⟩ := hne
  -- the slice `t ↦ g (t, y₀)` is analytic in one variable and not identically zero
  have hT : volume {t | g (t, y₀) = 0} = 0 :=
    volume_zeroSet_real (fun t _ => (hg (t, y₀) (Set.mem_univ _)).curry_left) ⟨t₁, h₁⟩
  have hT' : ∀ᵐ t ∂volume, g (t, y₀) ≠ 0 := by
    rw [ae_iff]; simpa using hT
  refine Measure.measure_prod_null_of_ae_null hmeas ?_
  filter_upwards [hT'] with t ht
  exact hslice t ⟨y₀, ht⟩

/-- The statement on `ℝ^n = Fin n → ℝ`, by induction on `n`, splitting off the first coordinate. -/
private lemma volume_zeroSet_fin (n : ℕ) {f : (Fin n → ℝ) → ℝ}
    (hf : AnalyticOnNhd ℝ f Set.univ) (hne : ∃ x, f x ≠ 0) :
    volume {x : Fin n → ℝ | f x = 0} = 0 := by
  induction n with
  | zero =>
    -- `ℝ^0` has one point, where `f` does not vanish
    obtain ⟨x₀, hx₀⟩ := hne
    have : {x : Fin 0 → ℝ | f x = 0} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx => hx₀ (Subsingleton.elim x₀ x ▸ hx)
    rw [this, measure_empty]
  | succ n ih =>
    -- identify `ℝ^(n+1)` with `ℝ × ℝ^n`, measure-preservingly
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have he : MeasurePreserving e volume (volume.prod volume) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    set g : ℝ × (Fin n → ℝ) → ℝ := fun p => f (Fin.cons p.1 p.2) with hg_def
    have hg : AnalyticOnNhd ℝ g Set.univ :=
      hf.comp (analyticOnNhd_cons n) (Set.mapsTo_univ _ _)
    have hset : {x : Fin (n + 1) → ℝ | f x = 0} = e ⁻¹' {p | g p = 0} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, hg_def, ← piFinSuccAbove_zero_symm_apply,
        e, MeasurableEquiv.symm_apply_apply]
    rw [hset, he.measure_preimage_equiv]
    refine prod_zeroSet_null volume hg ?_ (fun t ht => ?_) ?_
    · -- the zero set is closed, hence measurable
      exact (isClosed_eq (continuousOn_univ.mp hg.continuousOn) continuous_const).measurableSet
    · -- a slice in `y` that is not identically zero: induction hypothesis
      exact ih (fun y _ => (hg (t, y) (Set.mem_univ _)).curry_right) ht
    · obtain ⟨x, hx⟩ := hne
      refine ⟨e x, ?_⟩
      simpa only [hg_def, ← piFinSuccAbove_zero_symm_apply, e, MeasurableEquiv.symm_apply_apply]
        using hx

/-- The statement on a finite-dimensional space, for any additive Haar measure: transport to
`ℝ^n` along a continuous linear equivalence `e`; the image of `μ` under `e` is an additive Haar
measure on `ℝ^n`, hence absolutely continuous with respect to `volume`. -/
private lemma measure_zeroSet_of_analytic_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {f : E → ℝ} (hf : AnalyticOnNhd ℝ f Set.univ) (hne : ∃ x, f x ≠ 0) :
    μ {x : E | f x = 0} = 0 := by
  set n := Module.finrank ℝ E
  let e : E ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  -- `f ∘ e.symm` is analytic on `ℝ^n` and not identically zero, so its zero set `N` is null
  have hF : AnalyticOnNhd ℝ (fun y => f (e.symm y)) Set.univ :=
    hf.comp ((e.symm : (Fin n → ℝ) →L[ℝ] E).analyticOnNhd Set.univ) (Set.mapsTo_univ _ _)
  have hFne : ∃ y, f (e.symm y) ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨e x, by simpa using hx⟩
  have hN : volume {y : Fin n → ℝ | f (e.symm y) = 0} = 0 := volume_zeroSet_fin n hF hFne
  have hNmeas : MeasurableSet {y : Fin n → ℝ | f (e.symm y) = 0} :=
    (isClosed_eq ((continuousOn_univ.mp hf.continuousOn).comp e.symm.continuous)
      continuous_const).measurableSet
  -- `μ.map e` is an additive Haar measure on `ℝ^n`, so it does not charge `N` either
  have hac : μ.map e ≪ volume := Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have hset : {x : E | f x = 0} = e ⁻¹' {y | f (e.symm y) = 0} := by
    ext x
    simp
  rw [hset, ← Measure.map_apply e.continuous.measurable hNmeas]
  exact hac hN

/-- A real-analytic function on `ℝ^ι` that is not identically zero vanishes on a set of Lebesgue
measure zero. -/
theorem volume_zeroSet_of_analytic_pi {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hf : AnalyticOnNhd ℝ f Set.univ) (hne : ∃ x, f x ≠ 0) :
    volume {x : ι → ℝ | f x = 0} = 0 :=
  -- `volume` on `ℝ^ι` is an additive Haar measure
  measure_zeroSet_of_analytic_aux volume hf hne

/-- The same on any finite-dimensional real normed space, for any additive Haar measure (any
Lebesgue measure of the space). -/
theorem measure_zeroSet_of_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {f : E → ℝ} (hf : AnalyticOnNhd ℝ f Set.univ) (hne : ∃ x, f x ≠ 0) :
    μ {x : E | f x = 0} = 0 :=
  measure_zeroSet_of_analytic_aux μ hf hne

end Skips
