import SkipsLean.OneBlock.LearnedSkipTriangular
import SkipsLean.OneBlock.LearnedSkipNarrowGated

/-!
# One tanh, GELU, SwiGLU or GeGLU block of any width with an upper triangular learned skip, `ε > 0`

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. For generic parameters and `ε > 0`, its functional
dimension exceeds that of the residual network of part (ii) by exactly `d_model (d_model + 1)/2`,
and it satisfies the equality condition." Step 5 of its proof: "For an upper triangular `A` […]
`K(θ)` is larger than for the residual network by `d_model (d_model − 1)/2`, respectively `0`,
while the network has `d_model²`, respectively `d_model (d_model + 1)/2`, more parameters. In both
cases the functional dimension is larger by `d_model (d_model + 1)/2`."

`OneBlock/LearnedSkipTriangular.lean` has the upper triangular skip for these four kinds of
block of width at least `d_model`. Here the same **for blocks of any width with at least one
hidden unit**, from the values for the full skip (`OneBlock/LearnedSkipNarrowMlp.lean`,
`OneBlock/LearnedSkipNarrowGated.lean`) and the step from the full to the upper triangular
family of `OneBlock/LearnedSkipTriangular.lean`: at almost every weights and upper triangular
skip `(θ, A)` (for every Haar measure on the pairs), the value
`P + d (d + 1)/2 − d (d − 1)/2 − s` (`s = 0` for tanh and GELU, `s = d_hidden` for SwiGLU and
GeGLU), and the difference `d (d + 1)/2` to the residual network with the same weights `θ`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [LinearOrder d] [Fintype dIn] [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)] {ε : ℝ}

omit [DecidableEq d] [LinearOrder d] in
/-- Helper: the full skips `Fin 1 → Matrix d d ℝ` carry the Borel σ-algebra of their norm
topology (a copy of the private `borelSpace_skips_lst` of `OneBlock/LearnedSkipTriangular.lean`). -/
private theorem borelSpace_skips_ltn : BorelSpace (Fin 1 → Matrix d d ℝ) :=
  inferInstanceAs (BorelSpace (Fin 1 → d → d → ℝ))

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [LinearOrder d] [Fintype dIn]
  [Fintype dOut] in
/-- Helper: `d (d + 1)/2 + d (d − 1)/2 = d²` (both products are even; a copy of the private
`half_add_half_lst` of `OneBlock/LearnedSkipTriangular.lean`). -/
private theorem half_add_half_ltn (n : ℕ) : n * (n + 1) / 2 + n * (n - 1) / 2 = n ^ 2 := by
  have h1 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  have h3 : n * (n + 1) + n * (n - 1) = 2 * n ^ 2 := by
    cases n with
    | zero => rfl
    | succ m => rw [Nat.add_sub_cancel]; ring
  generalize n * (n + 1) = y at h1 h3 ⊢
  generalize n * (n - 1) = x at h2 h3 ⊢
  generalize n ^ 2 = q at h3 ⊢
  omega

omit [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper: `ae_funDimSkips_ge` with the Borel structure of `V` and the Haar property of `μ` as
explicit arguments (a copy of the private `ae_funDimSkips_ge_lst` of
`OneBlock/LearnedSkipTriangular.lean`). -/
private theorem ae_funDimSkips_ge_ltn {L : ℕ} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] (hB : BorelSpace V)
    (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut × V)) (hμ : μ.IsAddHaarMeasure)
    (p₀ : Params A dIn dOut × V) :
    ∀ᵐ p ∂μ, funDimSkips A ι p₀ ≤ funDimSkips A ι p :=
  ae_funDimSkips_ge A ι hf hχ μ p₀

omit [LinearOrder d] in
/-- Helper: if a square matrix that depends linearly on a point of `E` is the identity at one
point, it is invertible at almost every point (a copy of the private `ae_isUnit_det_lst` of
`OneBlock/LearnedSkipTriangular.lean`). -/
private theorem ae_isUnit_det_ltn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] (hB : BorelSpace E) (μ : Measure E)
    (hμ : μ.IsAddHaarMeasure) (Φ : E →ₗ[ℝ] Matrix d d ℝ) (x₀ : E) (h₀ : Φ x₀ = 1) :
    ∀ᵐ x ∂μ, IsUnit (Φ x).det := by
  -- the entries are linear, so the determinant is analytic
  have hentry : ∀ i j, AnalyticOnNhd ℝ (fun x => Φ x i j) Set.univ := fun i j =>
    (LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℝ ℝ i j) ∘ₗ Φ)).analyticOnNhd _
  have hφ : AnalyticOnNhd ℝ (fun x => (Φ x).det) Set.univ := by
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (σ i) i)
  -- it is `1` at `x₀`, so its zero set is null
  have hnull := measure_zeroSet_of_analytic μ hφ ⟨x₀, by rw [h₀, Matrix.det_one]; exact one_ne_zero⟩
  rw [ae_iff]
  simpa only [isUnit_iff_ne_zero, not_not] using hnull

omit [Nonempty T] in
/-- Helper (the common part of the four kinds; a copy of the private
`ae_funDimLearnedTri_of_full_lst` of `OneBlock/LearnedSkipTriangular.lean`): for one
real-analytic block under pre-RMSNorm (`ε > 0`), if the family of all skips has
`fd + (d (d − 1) + s) = P + d²` at almost every `(θ, A)`, then the family of upper triangular
skips has `fd + (d (d − 1)/2 + s) = P + d (d + 1)/2` at almost every `(θ, A)`, `A` upper
triangular. -/
private theorem ae_funDimLearnedTri_of_full_ltn {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params A dIn dOut × (Fin 1 → upperTriangular d))) [hμ : μ.IsAddHaarMeasure]
    {s : ℕ}
    (hval : ∀ (ν : Measure (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))) [ν.IsAddHaarMeasure],
      ∀ᵐ p ∂ν, funDimLearned A p + (Fintype.card d * (Fintype.card d - 1) + s)
        = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2) :
    ∀ᵐ p ∂μ, funDimLearnedTri A p + (Fintype.card d * (Fintype.card d - 1) / 2 + s)
      = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d * (Fintype.card d + 1) / 2 := by
  have hf' : ∀ ℓ, Differentiable ℝ (A.f ℓ) :=
    fun ℓ => differentiableOn_univ.1 (hf ℓ).differentiableOn
  have hχ : AnalyticOnNhd ℝ A.χ Set.univ := by
    rw [hA]
    exact analyticOnNhd_rmsNorm hε
  have hχ' : Differentiable ℝ A.χ := by
    rw [hA]
    exact differentiable_rmsNorm hε
  -- a Haar measure `ν` on the weights and the full skips, with the value of the full family
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := borelSpace_skips_ltn
  have : LocallyCompactSpace (Fin 1 → Matrix d d ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 1 → d → d → ℝ))
  have hBp : BorelSpace (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) := Prod.borelSpace
  let ν : Measure (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) := Measure.addHaar
  have hνH : ν.IsAddHaarMeasure := inferInstance
  have hν := hval ν
  -- the upper bound: at every point the triangular family has at most the generic value of the
  -- full family (it is a restriction, and the generic value of the full family is the largest)
  have hup : ∀ p : Params A dIn dOut × (Fin 1 → upperTriangular d),
      funDimLearnedTri A p + (Fintype.card d * (Fintype.card d - 1) + s)
        ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
    intro p
    have h1 : funDimLearnedTri A p ≤ funDimLearned A (p.1, triSkips d 1 p.2) :=
      funDimSkips_comp_le A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (triSkips d 1)
        hf' hχ' p.1 p.2
    obtain ⟨q, hq1, hq2⟩ := ((ae_funDimSkips_ge_ltn hBs A (ContinuousLinearMap.id ℝ _) hf hχ ν
      hνH (p.1, triSkips d 1 p.2)).and hν).exists
    change funDimLearned A _ ≤ funDimLearned A q at hq1
    omega
  -- at almost every full point the skip `S_0` is invertible
  have hdet : ∀ᵐ p ∂ν, IsUnit (p.2 0).det :=
    ae_isUnit_det_ltn hBp ν hνH ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix d d ℝ) 0)
      ∘ₗ (LinearMap.snd ℝ (Params A dIn dOut) (Fin 1 → Matrix d d ℝ))) (0, fun _ => 1) rfl
  -- the lower bound: a generic full point `p₁` with `S_0` invertible
  obtain ⟨p₁, hp₁, hdet₁⟩ := (hν.and hdet).exists
  -- QR: an orthogonal `Q₀` with `Q₀ᵀ S_0` upper triangular
  obtain ⟨Q₀, hQ₀, htri⟩ := exists_orthogonal_transpose_mul_upperTriangular (p₁.2 0)
  let G₀ : GL d ℝ := ⟨Q₀, Q₀ᵀ, (Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ₀,
    (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hQ₀⟩
  -- the changes of basis `Q₀` at `h_0` and `1` at `h_1`
  let Q : Fin (1 + 1) → GL d ℝ := Fin.cons G₀ fun _ => 1
  have hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
    intro ℓ
    refine Fin.cases hQ₀ (fun i => ?_) ℓ
    simp only [Q, Fin.cons_succ, Units.val_one]
    exact one_mem _
  -- they carry `S` to the triangular skip `R = Q₀ᵀ S_0`, invertible
  let R : Fin 1 → upperTriangular d := fun _ => ⟨Q₀ᵀ * p₁.2 0, htri⟩
  have hR : IsUnit (R 0 : Matrix d d ℝ).det := by
    show IsUnit (Q₀ᵀ * p₁.2 0).det
    rw [Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse ((Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ₀)).mul
      hdet₁
  have hcob : cobSkip p₁.2 Q = fun ℓ => (R ℓ : Matrix d d ℝ) := by
    funext ℓ
    obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
    show (↑(Q (Fin.castSucc 0))⁻¹ : Matrix d d ℝ) * p₁.2 0 * (Q (Fin.succ 0) : Matrix d d ℝ)
      = Q₀ᵀ * p₁.2 0
    simp only [Q, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Units.val_one, Matrix.mul_one]
    rfl
  -- so the triangular family has at `(θ₁.cob Q Q, R)` the generic value of the full family
  have hval₁ : funDimLearnedTri A (p₁.1.cob Q Q, R) = funDimLearned A p₁ := by
    rw [funDimLearnedTri_eq_funDimLearned hε hA hf' _ R hR, ← hcob]
    exact funDimLearned_cob hε hA hf' p₁.1 p₁.2 Q hQ
  -- and almost every triangular point has at least that
  have hBt : BorelSpace (Fin 1 → upperTriangular d) := inferInstance
  have hge := ae_funDimSkips_ge_ltn hBt A (triSkips d 1) hf hχ μ hμ (p₁.1.cob Q Q, R)
  have h1 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  have h2 := half_add_half_ltn (Fintype.card d)
  filter_upwards [hge] with p hp
  have hp' := hup p
  change funDimLearnedTri A _ ≤ funDimLearnedTri A p at hp
  rw [hval₁] at hp
  generalize Fintype.card d * (Fintype.card d - 1) = x at h1 h2 hp' hp₁ ⊢
  generalize Fintype.card d * (Fintype.card d + 1) = y at h2 ⊢
  generalize Fintype.card d ^ 2 = q at h2 hp' hp₁
  omega

omit [Fintype T] [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper: a condition on the weights that holds at almost every `θ` holds at almost every
`(θ, v)` (a copy of the private `ae_fst_ltz` of
`OneBlock/LearnedSkipTriangularRMSZeroRescale.lean`). -/
private theorem ae_fst_ltn {A : Arch T d 1} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] (hB : BorelSpace V)
    (μ : Measure (Params A dIn dOut × V)) (hμ : μ.IsAddHaarMeasure) {Q : Params A dIn dOut → Prop}
    (h : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), Q θ) :
    ∀ᵐ p ∂μ, Q p.1 := by
  rw [ae_iff] at h
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null h
  have hc : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), θ ∈ Nᶜ :=
    measure_eq_zero_iff_ae_notMem.1 hN0
  have h1 := (ae_comp_linearMap_mem_iff (LinearMap.fst ℝ (Params A dIn dOut) V) μ
    Measure.addHaar (LinearMap.fst_surjective) hN.compl).2 hc
  refine h1.mono fun p hp => ?_
  by_contra hq
  exact hp (hsub hq)

/-- **Theorem B.1 (iii) of the skips paper for one tanh block of any width with an upper
triangular learned skip, `ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and at least one hidden unit, at
almost every `(θ, A)`, `A` upper triangular, the functional dimension is
`P + d (d + 1)/2 − d (d − 1)/2`. -/
theorem ae_funDimLearnedTri_tanh_rmsNorm_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.mlp Real.tanh (rmsNorm ε) hid) p
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  have hf : ∀ ℓ, AnalyticOnNhd ℝ
      ((Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_tanh ℓ
  -- the value of the family of all skips at generic `(θ, A)` (with `s = 0`)
  have h := ae_funDimLearnedTri_of_full_ltn (s := 0) hε rfl hf μ fun ν =>
    (ae_funDimLearned_tanh_rmsNorm_of_nonempty hε ν hd hdIn hdOut).mono fun p hp => by
      rw [add_zero]
      exact hp
  simpa only [add_zero] using h

/-- **Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly
`d_model (d_model + 1)/2`", for one tanh block of any width with an upper triangular learned
skip, `ε > 0`:** at almost every `(θ, A)`, `A` upper triangular, the functional dimension is that
of the residual network with the weights `θ` plus `d (d + 1)/2`. -/
theorem ae_funDimLearnedTri_tanh_rmsNorm_eq_residual_add_of_nonempty (hε : 0 < ε)
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.mlp Real.tanh (rmsNorm ε) hid) p
      = funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 p.1
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- `fd + (d (d − 1)/2 + s) = P + d (d + 1)/2`, and `fd₁ + (d (d − 1)/2 + s) = P` at the same `θ`
  have hBt : BorelSpace (Fin 1 → upperTriangular d) := inferInstance
  have hres := ae_fst_ltn hBt μ ‹_›
    (ae_funDim_tanh_oneBlock_residual_rmsNorm hε Measure.addHaar hd hdIn hdOut)
  filter_upwards [ae_funDimLearnedTri_tanh_rmsNorm_of_nonempty hε μ hd hdIn hdOut, hres]
    with p hp hθ
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at hp hθ
  generalize Fintype.card d * (Fintype.card d + 1) / 2 = b at hp ⊢
  omega

/-- **Theorem B.1 (iii) of the skips paper for one GELU block of any width with an upper
triangular learned skip, `ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and at least one hidden unit, at
almost every `(θ, A)`, `A` upper triangular, the functional dimension is
`P + d (d + 1)/2 − d (d − 1)/2`. -/
theorem ae_funDimLearnedTri_gelu_rmsNorm_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.mlp gelu (rmsNorm ε) hid) p
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  have hf : ∀ ℓ, AnalyticOnNhd ℝ
      ((Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_gelu ℓ
  -- the value of the family of all skips at generic `(θ, A)` (with `s = 0`)
  have h := ae_funDimLearnedTri_of_full_ltn (s := 0) hε rfl hf μ fun ν =>
    (ae_funDimLearned_gelu_rmsNorm_of_nonempty hε ν hd hdIn hdOut).mono fun p hp => by
      rw [add_zero]
      exact hp
  simpa only [add_zero] using h

/-- **Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly
`d_model (d_model + 1)/2`", for one GELU block of any width with an upper triangular learned
skip, `ε > 0`:** at almost every `(θ, A)`, `A` upper triangular, the functional dimension is that
of the residual network with the weights `θ` plus `d (d + 1)/2`. -/
theorem ae_funDimLearnedTri_gelu_rmsNorm_eq_residual_add_of_nonempty (hε : 0 < ε)
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.mlp gelu (rmsNorm ε) hid) p
      = funDim (Arch.mlp gelu (rmsNorm ε) hid) 1 p.1
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- `fd + (d (d − 1)/2 + s) = P + d (d + 1)/2`, and `fd₁ + (d (d − 1)/2 + s) = P` at the same `θ`
  have hBt : BorelSpace (Fin 1 → upperTriangular d) := inferInstance
  have hres := ae_fst_ltn hBt μ ‹_›
    (ae_funDim_gelu_oneBlock_residual_rmsNorm hε Measure.addHaar hd hdIn hdOut)
  filter_upwards [ae_funDimLearnedTri_gelu_rmsNorm_of_nonempty hε μ hd hdIn hdOut, hres]
    with p hp hθ
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at hp hθ
  generalize Fintype.card d * (Fintype.card d + 1) / 2 = b at hp ⊢
  omega

/-- **Theorem B.1 (iii) of the skips paper for one SwiGLU block of any width with an upper
triangular learned skip, `ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and at least one hidden unit, at
almost every `(θ, A)`, `A` upper triangular, the functional dimension is
`P + d (d + 1)/2 − d (d − 1)/2 − d_hidden`. -/
theorem ae_funDimLearnedTri_swiglu_rmsNorm_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.gated silu (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  have hf : ∀ ℓ, AnalyticOnNhd ℝ
      ((Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_gated analyticOnNhd_silu ℓ
  -- the value of the family of all skips at generic `(θ, A)` (with `s = d_hidden`)
  exact ae_funDimLearnedTri_of_full_ltn (s := Fintype.card (hid 0)) hε rfl hf μ fun ν =>
    ae_funDimLearned_swiglu_rmsNorm_of_nonempty hε ν hd hdIn hdOut

/-- **Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly
`d_model (d_model + 1)/2`", for one SwiGLU block of any width with an upper triangular learned
skip, `ε > 0`:** at almost every `(θ, A)`, `A` upper triangular, the functional dimension is that
of the residual network with the weights `θ` plus `d (d + 1)/2`. -/
theorem ae_funDimLearnedTri_swiglu_rmsNorm_eq_residual_add_of_nonempty (hε : 0 < ε)
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.gated silu (rmsNorm ε) hid) p
      = funDim (Arch.gated silu (rmsNorm ε) hid) 1 p.1
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- `fd + (d (d − 1)/2 + s) = P + d (d + 1)/2`, and `fd₁ + (d (d − 1)/2 + s) = P` at the same `θ`
  have hBt : BorelSpace (Fin 1 → upperTriangular d) := inferInstance
  have hres := ae_fst_ltn hBt μ ‹_›
    (ae_funDim_swiglu_oneBlock_residual_rmsNorm hε Measure.addHaar hd hdIn hdOut)
  filter_upwards [ae_funDimLearnedTri_swiglu_rmsNorm_of_nonempty hε μ hd hdIn hdOut, hres]
    with p hp hθ
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at hp hθ
  generalize Fintype.card d * (Fintype.card d + 1) / 2 = b at hp ⊢
  omega

/-- **Theorem B.1 (iii) of the skips paper for one GeGLU block of any width with an upper
triangular learned skip, `ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and at least one hidden unit, at
almost every `(θ, A)`, `A` upper triangular, the functional dimension is
`P + d (d + 1)/2 − d (d − 1)/2 − d_hidden`. -/
theorem ae_funDimLearnedTri_geglu_rmsNorm_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.gated gelu (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  have hf : ∀ ℓ, AnalyticOnNhd ℝ
      ((Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_gated analyticOnNhd_gelu ℓ
  -- the value of the family of all skips at generic `(θ, A)` (with `s = d_hidden`)
  exact ae_funDimLearnedTri_of_full_ltn (s := Fintype.card (hid 0)) hε rfl hf μ fun ν =>
    ae_funDimLearned_geglu_rmsNorm_of_nonempty hε ν hd hdIn hdOut

/-- **Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly
`d_model (d_model + 1)/2`", for one GeGLU block of any width with an upper triangular learned
skip, `ε > 0`:** at almost every `(θ, A)`, `A` upper triangular, the functional dimension is that
of the residual network with the weights `θ` plus `d (d + 1)/2`. -/
theorem ae_funDimLearnedTri_geglu_rmsNorm_eq_residual_add_of_nonempty (hε : 0 < ε)
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.gated gelu (rmsNorm ε) hid) p
      = funDim (Arch.gated gelu (rmsNorm ε) hid) 1 p.1
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- `fd + (d (d − 1)/2 + s) = P + d (d + 1)/2`, and `fd₁ + (d (d − 1)/2 + s) = P` at the same `θ`
  have hBt : BorelSpace (Fin 1 → upperTriangular d) := inferInstance
  have hres := ae_fst_ltn hBt μ ‹_›
    (ae_funDim_geglu_oneBlock_residual_rmsNorm hε Measure.addHaar hd hdIn hdOut)
  filter_upwards [ae_funDimLearnedTri_geglu_rmsNorm_of_nonempty hε μ hd hdIn hdOut, hres]
    with p hp hθ
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at hp hθ
  generalize Fintype.card d * (Fintype.card d + 1) / 2 = b at hp ⊢
  omega

end Skips
