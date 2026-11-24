import SkipsLean.Dimension.Functional
import SkipsLean.Generic.Params
import SkipsLean.Network.Analytic

/-!
# From the rank at one parameter to generic parameters

Paper (dimension): Appendix D.7, "The parts together", the paragraph on GELU blocks in the case (+)
and gated blocks in the cases (n) and (+). "By Proposition D.4, the Jacobian at `θ†` has the rank
(13) on some finite batch `X`. In the cases (n) and (+) the outputs on `X` are real-analytic in
`θ ∈ ℝ^P`, and so are the minors of the Jacobian. A minor of the size (13) does not vanish at `θ†`,
so it vanishes only on a set of measure zero. At generic parameters the Jacobian on `X` therefore
has at least the rank (13)".

Stated here for every network whose fixed maps `f_ℓ` and `χ` are real-analytic (the cases (n),
`χ = id`, and (+), `χ` RMSNorm with `ε > 0`), for all stream matrices (with or without skips), and
for every batch and every parameter `θ₀`: at generic parameters the rank of the Jacobian on the
batch is at least its rank at `θ₀`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut]

omit [Fintype T] in
/-- Helper: a linear map of the parameters is analytic (it is continuous, the space being
finite-dimensional). -/
private theorem analyticOnNhd_params_linear {A : Arch T d L} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (l : Params A dIn dOut →ₗ[ℝ] F) : AnalyticOnNhd ℝ l Set.univ := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).analyticOnNhd _

omit [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two analytic matrix-valued maps is analytic (matrix multiplication is a
continuous bilinear map). -/
private theorem analyticOnNhd_matMul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : E → Matrix m n ℝ} {g : E → Matrix n p ℝ} {s : Set E}
    (hf : AnalyticOnNhd ℝ f s) (hg : AnalyticOnNhd ℝ g s) :
    AnalyticOnNhd ℝ (fun y => f y * g y) s := by
  -- matrix multiplication as a bilinear map
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  -- the same map with continuous linear maps (all spaces are finite-dimensional)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact fun y hy => (B'.analyticAt_bilinear (f y, g y)).comp₂ (hf y hy) (hg y hy)

/-- The output of a network with real-analytic maps `f_ℓ` and `χ` at a fixed input is a
real-analytic function of the parameters, for all stream matrices. -/
theorem analyticOnNhd_eval_params (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (x : Matrix T dIn ℝ) :
    AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => eval A S θ x) Set.univ := by
  -- the weights are linear, hence analytic, functions of the parameters
  have hE : AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => θ.E) Set.univ :=
    analyticOnNhd_params_linear (F := Matrix dIn d ℝ)
      { toFun := fun θ => θ.E, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hr : ∀ ℓ, AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => θ.read ℓ) Set.univ := fun ℓ =>
    analyticOnNhd_params_linear (F := Matrix d (A.r ℓ) ℝ)
      { toFun := fun θ => θ.read ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hw : ∀ ℓ, AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => θ.write ℓ) Set.univ := fun ℓ =>
    analyticOnNhd_params_linear (F := Matrix (A.w ℓ) d ℝ)
      { toFun := fun θ => θ.write ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hD : AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => θ.D) Set.univ :=
    analyticOnNhd_params_linear (F := Matrix d dOut ℝ)
      { toFun := fun θ => θ.D, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  -- every hidden state is an analytic function of the parameters, by induction on `ℓ`
  have hh : ∀ ℓ : Fin (L + 1),
      AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => hidden A S θ x ℓ) Set.univ := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero =>
      -- `h_0 = x E`
      simp only [hidden_zero]
      exact analyticOnNhd_matMul analyticOnNhd_const hE
    | succ ℓ ih =>
      -- `h_{ℓ+1} = h_ℓ S_ℓ + f_ℓ (χ(h_ℓ) W_read) W_write`: products, compositions and a sum
      simp only [hidden_succ]
      exact (analyticOnNhd_matMul ih analyticOnNhd_const).add
        (analyticOnNhd_matMul ((hf ℓ).comp (analyticOnNhd_matMul
          (hχ.comp ih (Set.mapsTo_univ _ _)) (hr ℓ)) (Set.mapsTo_univ _ _)) (hw ℓ))
  -- the output `χ(h_L) D`
  simp only [eval]
  exact analyticOnNhd_matMul (hχ.comp (hh (Fin.last L)) (Set.mapsTo_univ _ _)) hD

omit [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper: let `x ↦ J x` be an analytic family of linear maps between finite-dimensional spaces,
and `N` a fixed linear map. If `J x₀ ∘ N` is injective, then `J x ∘ N` is injective at almost every
`x`. With a left inverse `K` of `J x₀ ∘ N`, the determinant of `K ∘ J x ∘ N` is analytic in `x`
and equal to `1` at `x₀`, so it vanishes only on a null set. -/
private theorem ae_injective_comp_of_analytic
    {X E E' F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [AddCommGroup E']
    [Module ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {J : X → E →L[ℝ] F} (hJ : AnalyticOnNhd ℝ J Set.univ) (N : E' →ₗ[ℝ] E) {x₀ : X}
    (h₀ : Function.Injective ((J x₀ : E →ₗ[ℝ] F) ∘ₗ N)) :
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
  -- its determinant `φ x` is an analytic function of `x`: a polynomial in the entries
  let φ : X → ℝ := fun x => (Ψ (J x)).det
  have hentry : ∀ i j, AnalyticOnNhd ℝ (fun x => Ψ (J x) i j) Set.univ := fun i j =>
    ((LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℝ ℝ i j) ∘ₗ Ψ)).analyticOnNhd
      _).comp hJ (Set.mapsTo_univ _ _)
  have hφ : AnalyticOnNhd ℝ φ Set.univ := by
    show AnalyticOnNhd ℝ (fun x => (Ψ (J x)).det) Set.univ
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (σ i) i)
  -- `φ x₀ = det 1 = 1`
  have hφ₀ : φ x₀ = 1 := by
    show (Ψ (J x₀)).det = 1
    rw [hΨ, hK, LinearMap.toMatrix_id, Matrix.det_one]
  -- so `φ x ≠ 0` for almost every `x`
  have hnull := measure_zeroSet_of_analytic μ hφ ⟨x₀, by rw [hφ₀]; exact one_ne_zero⟩
  have hae : ∀ᵐ x ∂μ, φ x ≠ 0 := by
    rw [ae_iff]
    simpa only [ne_eq, not_not] using hnull
  -- where `φ x ≠ 0`, `K ∘ J x ∘ N` is invertible, so `J x ∘ N` is injective
  refine hae.mono fun x hx => ?_
  have hdet : LinearMap.det (K ∘ₗ ((J x : E →ₗ[ℝ] F) ∘ₗ N)) ≠ 0 := by
    rw [← LinearMap.det_toMatrix b]
    exact hx
  have hbij := (Module.End.isUnit_iff _).1
    ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  have hinj := hbij.1
  rw [LinearMap.coe_comp] at hinj
  exact hinj.of_comp

omit [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper: for an analytic family `x ↦ J x` of linear maps between finite-dimensional spaces, the
rank of `J x` is at least the rank of `J x₀` for almost every `x`. On a complement `C` of the
kernel of `J x₀`, the map `J x₀` is injective and `C` has the dimension of its range; the
restrictions of `J x` to `C` form an analytic family, injective at almost every `x`. -/
private theorem ae_finrank_range_ge
    {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {J : X → X →L[ℝ] F} (hJ : AnalyticOnNhd ℝ J Set.univ) (x₀ : X) :
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
  refine (ae_injective_comp_of_analytic μ hJ C.subtype hinj₀).mono fun x hx => ?_
  rw [← hdimC, ← LinearMap.finrank_range_of_inj hx]
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

/-- **The generic rank is the largest rank** (Appendix D.7). For a network with real-analytic maps
`f_ℓ` and `χ`, a batch `X` and a parameter `θ₀`: at generic parameters the Jacobian on `X` has at
least the rank that it has at `θ₀`. -/
theorem ae_jacobianRank_ge (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (θ₀ : Params A dIn dOut) :
    ∀ᵐ θ ∂μ, jacobianRank A S X θ₀ ≤ jacobianRank A S X θ := by
  -- the outputs on the batch, and hence their derivative, are analytic in `θ`
  have hB : AnalyticOnNhd ℝ (evalBatch A S X : Params A dIn dOut → Fin n → Matrix T dOut ℝ)
      Set.univ :=
    AnalyticOnNhd.pi fun i => analyticOnNhd_eval_params A S hf hχ (X i)
  have h := ae_finrank_range_ge μ hB.fderiv θ₀
  exact h

/-- At generic parameters the functional dimension is at least the rank of the Jacobian on any
batch at any one parameter. -/
theorem ae_jacobianRank_le_funDim (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (θ₀ : Params A dIn dOut) :
    ∀ᵐ θ ∂μ, jacobianRank A S X θ₀ ≤ funDim A S θ := by
  -- at generic `θ` the rank on `X` is at least that at `θ₀`, and at most `fd(θ)`
  filter_upwards [ae_jacobianRank_ge A S hf hχ μ X θ₀] with θ hθ
  exact hθ.trans (jacobianRank_le_funDim θ X)

/-- At generic parameters the functional dimension is at least the functional dimension at any one
parameter: `fd(θ₀) ≤ fd(θ)` for almost every `θ`. -/
theorem ae_funDim_ge (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] (θ₀ : Params A dIn dOut) :
    ∀ᵐ θ ∂μ, funDim A S θ₀ ≤ funDim A S θ := by
  -- a batch `X` on which the rank at `θ₀` is `fd(θ₀)`
  obtain ⟨n, X, hX⟩ := exists_jacobianRank_eq_funDim (S := S) θ₀
  rw [← hX]
  exact ae_jacobianRank_le_funDim A S hf hχ μ X θ₀

end Skips
