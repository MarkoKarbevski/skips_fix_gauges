import SkipsLean.Generic.AnalyticZeroSetOn
import SkipsLean.Dimension.GenericRank

/-!
# From the rank at one parameter to generic parameters, on a connected open set

Paper (dimension paper): Appendix D.7, "The parts together", the case (0): "By Proposition D.4
there is a finite batch `X*`, with `xE ≠ 0` for all its inputs, on which the Jacobian at `θ*` has
the rank (13). By (R2), `θ* ∈ O_{X*}`. The sum of the squares of the minors of this size of the
Jacobian of `F_{X*}` is real-analytic on the connected open set `O_{X*}` and does not vanish at
`θ*`, so its zero set has measure zero, and so has the complement of `O_{X*}` (Lemma D.20). Hence
the rank on `X*` is at least (13) at almost every parameter."

Stated here for any map `G` that is real-analytic on a connected open set `U` whose complement has
measure zero: at almost every point the rank of the derivative of `G` is at least its rank at any
given point of `U`; and for the outputs of a network on a batch. (`Dimension/GenericRank.lean` has
the case `U` the whole space.)
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut]

omit [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper: let `x ↦ J x` be a family of linear maps between finite-dimensional spaces, analytic on
a connected open set `U` whose complement is null, and `N` a fixed linear map. If `J x₀ ∘ N` is
injective at some `x₀ ∈ U`, then `J x ∘ N` is injective at almost every `x`. With a left inverse
`K` of `J x₀ ∘ N`, the determinant of `K ∘ J x ∘ N` is analytic on `U` and equal to `1` at `x₀`, so
it vanishes only on a null subset of `U`. -/
private theorem ae_injective_comp_of_analyticOn_zs
    {X E E' F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [AddCommGroup E']
    [Module ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {U : Set X} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUnull : μ Uᶜ = 0) {J : X → E →L[ℝ] F} (hJ : AnalyticOnNhd ℝ J U) (N : E' →ₗ[ℝ] E)
    {x₀ : X} (hx₀ : x₀ ∈ U) (h₀ : Function.Injective ((J x₀ : E →ₗ[ℝ] F) ∘ₗ N)) :
    ∀ᵐ x ∂μ, Function.Injective ((J x : E →ₗ[ℝ] F) ∘ₗ N) := by
  -- a left inverse `K` of `J x₀ ∘ N`
  obtain ⟨K, hK⟩ :=
    ((J x₀ : E →ₗ[ℝ] F) ∘ₗ N).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 h₀)
  -- the matrix of `K ∘ J x ∘ N` in a basis `b` of `E'`, a linear function of `J x`
  let b := Module.finBasis ℝ E'
  let Ψ : (E →L[ℝ] F) →ₗ[ℝ]
      Matrix (Fin (Module.finrank ℝ E')) (Fin (Module.finrank ℝ E')) ℝ :=
    (LinearMap.toMatrix b b).toLinearMap ∘ₗ (LinearMap.llcomp ℝ E' F E' K) ∘ₗ
      (LinearMap.lcomp ℝ F N) ∘ₗ (ContinuousLinearMap.coeLM ℝ)
  have hΨ : ∀ x, Ψ (J x) = LinearMap.toMatrix b b (K ∘ₗ ((J x : E →ₗ[ℝ] F) ∘ₗ N)) :=
    fun x => rfl
  -- its determinant `φ x` is analytic on `U`: a polynomial in the entries
  let φ : X → ℝ := fun x => (Ψ (J x)).det
  have hentry : ∀ i j, AnalyticOnNhd ℝ (fun x => Ψ (J x) i j) U := fun i j =>
    ((LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℝ ℝ i j) ∘ₗ Ψ)).analyticOnNhd
      _).comp hJ (Set.mapsTo_univ _ _)
  have hφ : AnalyticOnNhd ℝ φ U := by
    show AnalyticOnNhd ℝ (fun x => (Ψ (J x)).det) U
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (σ i) i)
  -- `φ x₀ = det 1 = 1`
  have hφ₀ : φ x₀ = 1 := by
    show (Ψ (J x₀)).det = 1
    rw [hΨ, hK, LinearMap.toMatrix_id, Matrix.det_one]
  -- the zeros of `φ` in `U` form a null set, and so does the complement of `U`
  have hnull := measure_zeroSet_of_analyticOnNhd_of_isPreconnected μ hU hUc hφ
    ⟨x₀, hx₀, by rw [hφ₀]; exact one_ne_zero⟩
  have hae0 : ∀ᵐ x ∂μ, ¬ (x ∈ U ∧ φ x = 0) := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  have haeU : ∀ᵐ x ∂μ, x ∈ U := mem_ae_iff.2 hUnull
  -- where `φ x ≠ 0`, `K ∘ J x ∘ N` is invertible, so `J x ∘ N` is injective
  filter_upwards [hae0, haeU] with x hx hxU
  have hdet : LinearMap.det (K ∘ₗ ((J x : E →ₗ[ℝ] F) ∘ₗ N)) ≠ 0 := by
    rw [← LinearMap.det_toMatrix b]
    exact fun h => hx ⟨hxU, h⟩
  have hbij := (Module.End.isUnit_iff _).1
    ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  have hinj := hbij.1
  rw [LinearMap.coe_comp] at hinj
  exact hinj.of_comp

omit [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper: for a family `x ↦ J x` of linear maps between finite-dimensional spaces, analytic on a
connected open set `U` whose complement is null, the rank of `J x` is at least the rank of `J x₀`
(`x₀ ∈ U`) for almost every `x`. On a complement `C` of the kernel of `J x₀`, the map `J x₀` is
injective and `C` has the dimension of its range; the restrictions of `J x` to `C` are injective
at almost every `x`. -/
private theorem ae_finrank_range_ge_on_zs
    {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set X} (hU : IsOpen U) (hUc : IsPreconnected U) (hUnull : μ Uᶜ = 0)
    {J : X → X →L[ℝ] F} (hJ : AnalyticOnNhd ℝ J U) {x₀ : X} (hx₀ : x₀ ∈ U) :
    ∀ᵐ x ∂μ, Module.finrank ℝ (LinearMap.range (J x₀).toLinearMap) ≤
      Module.finrank ℝ (LinearMap.range (J x).toLinearMap) := by
  -- a complement `C` of the kernel of `J x₀`: its dimension is the rank of `J x₀`
  obtain ⟨C, hC⟩ := (LinearMap.ker (J x₀).toLinearMap).exists_isCompl
  have hdimC : Module.finrank ℝ C = Module.finrank ℝ (LinearMap.range (J x₀).toLinearMap) := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC
    have h2 := LinearMap.finrank_range_add_finrank_ker (J x₀).toLinearMap
    omega
  -- the restriction `J x₀ ∘ ι_C` is injective
  have hinj₀ : Function.Injective ((J x₀ : X →ₗ[ℝ] F) ∘ₗ C.subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv' : (v : X) ∈ LinearMap.ker (J x₀).toLinearMap := hv
    exact Subtype.ext (Submodule.disjoint_def.1 hC.disjoint _ hv' v.2)
  -- where `J x ∘ ι_C` is injective, the range of `J x` contains a copy of `C`
  refine (ae_injective_comp_of_analyticOn_zs μ hU hUc hUnull hJ C.subtype hx₀ hinj₀).mono
    fun x hx => ?_
  rw [← hdimC, ← LinearMap.finrank_range_of_inj hx]
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

/-- **The generic rank on a connected open set:** let `G` be real-analytic on a connected open set
`U` whose complement has measure zero. Then at almost every `x` the rank of the derivative of `G`
is at least its rank at `x₀ ∈ U`. -/
theorem ae_finrank_range_fderiv_ge_of_isPreconnected
    {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set X} (hU : IsOpen U) (hUc : IsPreconnected U) (hUnull : μ Uᶜ = 0)
    {G : X → F} (hG : AnalyticOnNhd ℝ G U) {x₀ : X} (hx₀ : x₀ ∈ U) :
    ∀ᵐ x ∂μ, Module.finrank ℝ (LinearMap.range (fderiv ℝ G x₀).toLinearMap) ≤
      Module.finrank ℝ (LinearMap.range (fderiv ℝ G x).toLinearMap) := by
  -- the derivative `x ↦ G'(x)` is analytic on `U`
  exact ae_finrank_range_ge_on_zs μ hU hUc hUnull hG.fderiv hx₀

/-- **Appendix D.7, the case (0), "Hence the rank on `X*` is at least (13) at almost every
parameter":** if the outputs of a network on the batch `X` are real-analytic on a connected open
set `U` of parameters whose complement has measure zero, then at almost every parameter the rank
of the Jacobian on `X` is at least its rank at `θ₀ ∈ U`. -/
theorem ae_jacobianRank_ge_of_isPreconnected (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) {U : Set (Params A dIn dOut)} (hU : IsOpen U)
    (hUc : IsPreconnected U) (hUnull : μ Uᶜ = 0)
    (hG : AnalyticOnNhd ℝ (evalBatch A S X : Params A dIn dOut → Fin n → Matrix T dOut ℝ) U)
    {θ₀ : Params A dIn dOut} (hθ₀ : θ₀ ∈ U) :
    ∀ᵐ θ ∂μ, jacobianRank A S X θ₀ ≤ jacobianRank A S X θ := by
  -- `jacobianRank A S X θ` is the rank of the derivative of `evalBatch A S X` at `θ`
  have h := ae_finrank_range_fderiv_ge_of_isPreconnected μ hU hUc hUnull hG hθ₀
  exact h

end Skips
