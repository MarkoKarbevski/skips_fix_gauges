import SkipsLean.OneBlock.LearnedSkipRMSZeroReGLU

/-!
# One ReGLU block with a full learned skip under pre-RMSNorm with `ε = 0`: generic parameters

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. […] For `ε = 0` it exceeds that of the residual
network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and
ReGLU blocks."

`OneBlock/LearnedSkipRMSZeroReGLU.lean` has the value at one parameter under the conditions of
the proof, among them the condition that the paper does not state (`TurnsActiveRowsGatedSkip`).
Here, for one ReGLU block with `d ≥ 2`:

* this condition, and "the block turns some row off the kinks of the gates", at almost every
  weights and skip `(θ, A)` (the twins for a learned skip of `ae_turnsActiveRowsGated_reglu` and
  `ae_exists_turned_row_reglu`, `OneBlock/ResidualRMSZeroReGLUGeneric.lean`);
* the theorem at almost every `(θ, A)`, for `d_in, d_out ≥ d ≥ 2` and a block of any width with
  a hidden unit: the value `P + d² − (d(d−1) + 2) − 2 d_hidden` of Lean's `funDimLearned`, a batch
  of the paper's inputs with this rank, and the equality with the residual network at the same
  weights, `funDimLearned = funDim + d(d+1)/2 − 1`.

Not stated: the upper triangular skip.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **A ReGLU block turns a dense set of the rows with an active gate for the skip `A` at almost
every weights and skip `(θ, A)`,** for `d ≥ 2`. -/
theorem ae_turnsActiveRowsGatedSkip_reglu
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, TurnsActiveRowsGatedSkip p.1 (p.2 0) := by
  sorry

/-- **A ReGLU block with a hidden unit turns some row off the kinks of the gates, for the skip
`A`, at almost every weights and skip `(θ, A)`,** for `d ≥ 2`. -/
theorem ae_exists_turned_row_skip_reglu [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* p.1.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* p.2 0, gatedBlock relu ((p.1.read 0).submatrix id Sum.inl)
        ((p.1.read 0).submatrix id Sum.inr) (p.1.write 0) v] := by
  sorry

/-! ### Helpers: almost every `(θ, A)` -/

omit [DecidableEq d] in
/-- Helper: the skips `Fin 1 → Matrix d d ℝ` carry the Borel σ-algebra of their norm topology (a
copy of the private `borelSpace_skips_lsk` of `OneBlock/LearnedSkipKinds.lean`). -/
private theorem borelSpace_skips_lzh : BorelSpace (Fin 1 → Matrix d d ℝ) :=
  inferInstanceAs (BorelSpace (Fin 1 → d → d → ℝ))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: a condition on the weights that holds at almost every `θ` holds at almost every
`(θ, v)` (a copy of the private `ae_fst_lsk` of `OneBlock/LearnedSkipKinds.lean`). -/
private theorem ae_fst_lzh {A : Arch T d 1} {V : Type*} [NormedAddCommGroup V]
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

/-- Helper: if a square matrix that depends linearly on a point of `E` is the identity at one
point, it is invertible at almost every point (a copy of the private `ae_isUnit_det_lst` of
`OneBlock/LearnedSkipTriangular.lean`). -/
private theorem ae_isUnit_det_lzh {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] (hB : BorelSpace E) (μ : Measure E)
    (hμ : μ.IsAddHaarMeasure) (Φ : E →ₗ[ℝ] Matrix d d ℝ) (x₀ : E) (h₀ : Φ x₀ = 1) :
    ∀ᵐ x ∂μ, IsUnit (Φ x).det := by
  have hentry : ∀ i j, AnalyticOnNhd ℝ (fun x => Φ x i j) Set.univ := fun i j =>
    (LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℝ ℝ i j) ∘ₗ Φ)).analyticOnNhd _
  have hφ : AnalyticOnNhd ℝ (fun x => (Φ x).det) Set.univ := by
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (σ i) i)
  have hnull := measure_zeroSet_of_analytic μ hφ ⟨x₀, by rw [h₀, Matrix.det_one]; exact one_ne_zero⟩
  rw [ae_iff]
  simpa only [isUnit_iff_ne_zero, not_not] using hnull

/-- Helper: at almost every `(θ, A)` the conditions `OneBlockGenericReGLURMS θ` hold and the skip
`A = R 0` is invertible, for `d_in, d_out ≥ d ≥ 2`. -/
private theorem ae_generic_lzh
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [hμ : μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, OneBlockGenericReGLURMS p.1 ∧ IsUnit (p.2 0).det := by
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := borelSpace_skips_lzh
  have hBp : BorelSpace (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)) := Prod.borelSpace
  have h1 := ae_fst_lzh hBs μ hμ (ae_oneBlockGenericReGLURMS Measure.addHaar hd hdIn hdOut)
  have h2 := ae_isUnit_det_lzh hBp μ hμ
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix d d ℝ) 0)
      ∘ₗ (LinearMap.snd ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
        (Fin 1 → Matrix d d ℝ))) (0, fun _ => 1) rfl
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", for one ReGLU block with
a hidden unit and a full learned skip:** with `d_in, d_out ≥ d ≥ 2`, at almost every weights and
skip `(θ, A)`, `funDimLearned = P + d² − (d(d−1) + 2) − 2 d_hidden`. -/
theorem ae_funDimLearned_reglu_oneBlock_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.gated relu (rmsNorm 0) hid) p
        + ((Fintype.card d * (Fintype.card d - 1) + 2) + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  -- the conditions of the proof at almost every `(θ, A)`
  filter_upwards [ae_generic_lzh μ hd hdIn hdOut, ae_turnsActiveRowsGatedSkip_reglu μ hd,
    ae_exists_turned_row_skip_reglu μ hd] with p hp hturn hw
  exact funDimLearned_reglu_oneBlock_rmsNorm_zero p.1 hp.1 hd p.2 hp.2 hturn hw

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", in the paper's own
sense, for one ReGLU block with a hidden unit and a full learned skip:** at almost every weights
and skip `(θ, A)`, a finite batch of inputs at which no normalized row vanishes and no gate sits
at its kink, on which the Jacobian in the weights and the skip has the rank
`P + d² − (d(d−1) + 2) − 2 d_hidden`. -/
theorem ae_exists_jacobianRankSkips_reglu_oneBlock_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) p.1 p.2
        ∩ noKinkGateRMS p.1) ∧
      jacobianRankSkips (Arch.gated relu (rmsNorm 0) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X p
          + ((Fintype.card d * (Fintype.card d - 1) + 2) + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  -- the conditions of the proof at almost every `(θ, A)`
  filter_upwards [ae_generic_lzh μ hd hdIn hdOut, ae_turnsActiveRowsGatedSkip_reglu μ hd,
    ae_exists_turned_row_skip_reglu μ hd] with p hp hturn hw
  exact exists_jacobianRankSkips_reglu_oneBlock_rmsNorm_zero p.1 hp.1 hd p.2 hp.2 hturn hw

/-- **Theorem B.1 (iii) of the skips paper, "For `ε = 0` it exceeds that of the residual network
with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for […] ReGLU blocks", for
one ReGLU block with a hidden unit:** with `d_in, d_out ≥ d ≥ 2`, at almost every weights and
full learned skip `(θ, A)` the functional dimension exceeds that of the residual network with
the weights `θ` by exactly `d(d+1)/2 − 1`. -/
theorem ae_funDimLearned_reglu_oneBlock_rmsNorm_zero_eq_residual_add [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [hμ : μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.gated relu (rmsNorm 0) hid) p
      = funDim (Arch.gated relu (rmsNorm 0) hid) 1 p.1
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := borelSpace_skips_lzh
  -- `d(d−1)` and `d(d+1)` are even, `d(d+1) + d(d−1) = 2 d²`, and `d(d+1) ≥ 2`
  have e1 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  have e2 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (Fintype.card d))
  have e3 : Fintype.card d * (Fintype.card d + 1) + Fintype.card d * (Fintype.card d - 1)
      = 2 * Fintype.card d ^ 2 := by
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card d = m + 1 := ⟨Fintype.card d - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    ring
  have e4 : 2 ≤ Fintype.card d * (Fintype.card d + 1) := by nlinarith
  filter_upwards [ae_funDimLearned_reglu_oneBlock_rmsNorm_zero μ hd hdIn hdOut,
    ae_fst_lzh hBs μ hμ
      (ae_funDim_reglu_oneBlock_residual_rmsNorm_zero Measure.addHaar hd hdIn hdOut)]
    with p hp hr
  generalize Fintype.card d * (Fintype.card d + 1) = y at e2 e3 e4 ⊢
  generalize Fintype.card d * (Fintype.card d - 1) = x at hp hr e1 e3
  generalize Fintype.card d ^ 2 = q at hp e3
  omega

end Skips
