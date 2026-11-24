import SkipsLean.Generic.AnalyticZeroSet
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The zero set of an analytic function on a connected open set has measure zero

Paper (dimension paper): Appendix D.7, "The parts together", the case (0): "The sum of the squares
of the minors of this size of the Jacobian of `F_{X*}` is real-analytic on the connected open set
`O_{X*}` and does not vanish at `θ*`, so its zero set has measure zero".

In the case (0) the outputs are real-analytic only on the set of parameters at which no hidden
state vanishes, so the fact of `Generic/AnalyticZeroSet.lean` (for functions analytic on the whole
space) is needed on a connected open set: a real-analytic function on a connected open set that
does not vanish identically vanishes on a set of measure zero.
-/

namespace Skips

open MeasureTheory

/-- Helper: around a point `x` of an open set `U` of a finite-dimensional space, a real-analytic
map `ψ` of the whole space into `U` whose image contains a neighbourhood of `x`: in coordinates,
`ψ z = x + (r sin z₁, …, r sin zₙ)`, onto the closed cube of radius `r`. -/
private lemma exists_analytic_cover_zs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) :
    ∃ ψ : E → E, AnalyticOnNhd ℝ ψ Set.univ ∧ Set.MapsTo ψ Set.univ U ∧
      ∃ V ∈ nhds x, V ⊆ Set.range ψ := by
  set n := Module.finrank ℝ E
  let e : E ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  -- a ball of radius `δ` around `0` in coordinates that `v ↦ x + e⁻¹ v` maps into `U`
  have hcont : Continuous fun v : Fin n → ℝ => x + e.symm v :=
    continuous_const.add e.symm.continuous
  have hpre : (fun v : Fin n → ℝ => x + e.symm v) ⁻¹' U ∈ nhds (0 : Fin n → ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hx)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hpre
  set r := δ / 2 with hr_def
  have hr : 0 < r := by positivity
  -- `S v = (r sin v₁, …, r sin vₙ)`
  let S : (Fin n → ℝ) → (Fin n → ℝ) := fun v i => r * Real.sin (v i)
  refine ⟨fun z => x + e.symm (S (e z)), ?_, ?_, ?_⟩
  · -- `ψ` is analytic: sines, linear maps and a translation
    have hS : AnalyticOnNhd ℝ S Set.univ := AnalyticOnNhd.pi fun i =>
      analyticOnNhd_const.mul (Real.analyticOnNhd_sin.comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).analyticOnNhd _)
        (Set.mapsTo_univ _ _))
    exact analyticOnNhd_const.add (((e.symm : (Fin n → ℝ) →L[ℝ] E).analyticOnNhd _).comp
      (hS.comp ((e : E →L[ℝ] (Fin n → ℝ)).analyticOnNhd _) (Set.mapsTo_univ _ _))
      (Set.mapsTo_univ _ _))
  · -- `ψ` maps into `U`: `‖S v‖ ≤ r < δ` in the sup norm
    intro z _
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hr.le).2 fun i => ?_) (by linarith)
    simp only [S, Real.norm_eq_abs, abs_mul, abs_of_pos hr]
    exact mul_le_of_le_one_right hr.le (Real.abs_sin_le_one _)
  · -- the image contains `V = {y | ‖e (y - x)‖ < r}`: invert the sines by `arcsin`
    refine ⟨(fun y => e (y - x)) ⁻¹' Metric.ball 0 r, ?_, ?_⟩
    · have hc : Continuous fun y => e (y - x) :=
        e.continuous.comp (continuous_id.sub continuous_const)
      apply hc.continuousAt.preimage_mem_nhds
      simpa using Metric.ball_mem_nhds (0 : Fin n → ℝ) hr
    · intro y hy
      have hy' : ‖e (y - x)‖ < r := by simpa using hy
      refine ⟨e.symm (fun i => Real.arcsin (e (y - x) i / r)), ?_⟩
      have hSy : S (fun i => Real.arcsin (e (y - x) i / r)) = e (y - x) := by
        funext i
        have hi := (pi_norm_lt_iff hr).1 hy' i
        rw [Real.norm_eq_abs, abs_lt] at hi
        simp only [S]
        rw [Real.sin_arcsin (by rw [le_div_iff₀ hr]; linarith) (by rw [div_le_one hr]; linarith)]
        field_simp
      simp only [ContinuousLinearEquiv.apply_symm_apply, hSy,
        ContinuousLinearEquiv.symm_apply_apply]
      abel

/-- **A real-analytic function on a connected open set that is not identically zero vanishes on a
set of measure zero** (for any additive Haar measure of a finite-dimensional real normed space). -/
theorem measure_zeroSet_of_analyticOnNhd_of_isPreconnected {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U) (hUc : IsPreconnected U) {f : E → ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hne : ∃ x ∈ U, f x ≠ 0) :
    μ {x | x ∈ U ∧ f x = 0} = 0 := by
  -- (a) by the identity theorem, `f` is not eventually zero at any point of `U`
  have hnev : ∀ x ∈ U, ¬ (f =ᶠ[nhds x] 0) := by
    intro x hx h
    obtain ⟨y, hy, hfy⟩ := hne
    exact hfy (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hx h hy)
  -- (b) every point of the zero set has a neighbourhood in it of measure zero
  refine measure_null_of_locally_null _ fun x hx => ?_
  obtain ⟨ψ, hψ, hψU, V, hV, hVψ⟩ := exists_analytic_cover_zs hU hx.1
  -- `f ∘ ψ` is analytic on the whole space, and not identically zero by (a)
  have hfψ : AnalyticOnNhd ℝ (fun z => f (ψ z)) Set.univ := hf.comp hψ hψU
  have hfψne : ∃ z, f (ψ z) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hnev x hx.1
    filter_upwards [hV] with y hy
    obtain ⟨z, rfl⟩ := hVψ hy
    exact hcon z
  -- so its zero set `N` is null, and so is `ψ '' N`, which contains the zeros of `f` in `V`
  have hN := measure_zeroSet_of_analytic μ hfψ hfψne
  have himg := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ
    (hψ.differentiableOn.mono (Set.subset_univ _)) hN
  refine ⟨{x | x ∈ U ∧ f x = 0} ∩ V, inter_mem_nhdsWithin _ hV, measure_mono_null ?_ himg⟩
  rintro y ⟨⟨-, hy0⟩, hyV⟩
  obtain ⟨z, rfl⟩ := hVψ hyV
  exact ⟨z, hy0, rfl⟩

end Skips
