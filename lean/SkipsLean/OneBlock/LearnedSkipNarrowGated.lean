import SkipsLean.OneBlock.LearnedSkipNarrowMlp
import SkipsLean.OneBlock.ResidualRMSGated
import SkipsLean.OneBlock.GatedUnitsNoSymmetricPart

/-!
# One SwiGLU or GeGLU block of any width with a full learned skip under pre-RMSNorm, `ε > 0`

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. For generic parameters and `ε > 0`, its functional
dimension exceeds that of the residual network of part (ii) by exactly `d_model (d_model + 1)/2`,
and it satisfies the equality condition."

The twin for gated blocks of `OneBlock/LearnedSkipNarrowMlp.lean`: part (iii) has no condition on
the width, and `OneBlock/LearnedSkipKinds.lean` proves it for blocks of width at least `d_model`.
Here the paper's route **for SwiGLU and GeGLU blocks of any width with at least one hidden
unit**: Step 4 is `GatedUnitsNoSymmetricPart` (`OneBlock/GatedUnitsNoSymmetricPart.lean`), which
gives `NoSymmetricPart` at all inputs under the conditions `OneBlockGenericGatedRMS`; Steps 1 to 3
and 5 are `funDimLearned_eq_funDim_residual_add_of_noSymmetricPart`
(`OneBlock/LearnedSkipGain.lean`). The value `P + d² − d (d − 1) − d_hidden` follows from the
value `P − d (d − 1)/2 − d_hidden` of the residual network (`OneBlock/ResidualRMSGated.lean`, any
width; `s = d_hidden`, the rescalings of the values).

Not stated here: the upper triangular skip for narrow blocks.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-! ### Helpers: equation (17) along a row -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `τ ↦ a + τ b` has the derivative `b` at `0` (a copy of the private
`hasDerivAt_affine_rg` of `OneBlock/ResidualRMSGated.lean`). -/
private theorem hasDerivAt_affine_gun (a b : ℝ) :
    HasDerivAt (fun τ : ℝ => a + τ * b) b 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const b).const_add a
  rw [one_mul] at h
  exact h

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the derivative of the map of the gated block at `M` along `N`: entry `(t, i)` is
`σ'(M_{t, g i}) N_{t, g i} M_{t, v i} + σ(M_{t, g i}) N_{t, v i}` (a copy of the private
`fderiv_f_gated_apply_rg` of `OneBlock/ResidualRMSGated.lean`). -/
private theorem fderiv_f_gated_apply_gun (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (M N : Matrix T (hid 0 ⊕ hid 0) ℝ) (t : T) (i : hid 0) :
    fderiv ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f 0) M N t i
      = σ' (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + σ (M t (Sum.inl i)) * N t (Sum.inr i) := by
  have hd := differentiable_f_gated (T := T) (d := d) (χ := rmsNorm ε) (hid := hid)
    (fun z => (hσ z).differentiableAt) 0
  -- the chain rule along the line `τ ↦ M + τ N`
  have hline : HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
    rw [one_smul] at h
    exact h
  have h1 := (hd M).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by rw [zero_smul, add_zero])
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) i
  -- the same derivative computed on the entry `(t, i)`
  have h3 : HasDerivAt (fun τ : ℝ => σ (M t (Sum.inl i) + τ * N t (Sum.inl i))
      * (M t (Sum.inr i) + τ * N t (Sum.inr i)))
      (σ' (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + σ (M t (Sum.inl i)) * N t (Sum.inr i)) 0 := by
    have hu := hasDerivAt_affine_gun (M t (Sum.inl i)) (N t (Sum.inl i))
    have hw := hasDerivAt_affine_gun (M t (Sum.inr i)) (N t (Sum.inr i))
    have h := ((hσ _).comp (0 : ℝ) hu).mul hw
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, add_zero]
  exact h2.unique h3

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `N_ε(0) = 0` (a copy of the private `rmsNorm_zero_lnm` of
`OneBlock/LearnedSkipNarrowMlp.lean`). -/
private theorem rmsNorm_zero_gun : rmsNorm ε (0 : Matrix T d ℝ) = 0 := by
  ext t k
  simp [rmsNorm, rmsRow]

omit [Nonempty T] [DecidableEq d] in
/-- Helper: equation (17) at the input whose rows are all `v`, at the token `t` and the coordinate
`j`, is the equation of `GatedUnitsNoSymmetricPart` at `v`, with the gate columns
`c_i = (W_read)_{g i}`, the value columns `e_i = (W_read)_{v i}`,
`ψc_i = X c_i + (ψ_read)_{g i}`, `ψe_i = X e_i + (ψ_read)_{v i}` and `X / d` in place of `X` (the
twin of the private `entry_lnm` of `OneBlock/LearnedSkipNarrowMlp.lean`). -/
private theorem entry_gun (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (Wr ψr : Matrix d (hid 0 ⊕ hid 0) ℝ) (Ww ψw : Matrix (hid 0) d ℝ) (X : Matrix d d ℝ)
    (v : d → ℝ) (t : T) (j : d) :
    (fderiv ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f 0) ((of fun _ : T => v) * Wr)
          (tangentRMS X (of fun _ : T => v) * Wr + (of fun _ : T => v) * ψr) * Ww
        + (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f 0 ((of fun _ : T => v) * Wr)
          * ψw) t j
      = (∑ i, ((σ (v ⬝ᵥ Wrᵀ (Sum.inl i)) * (v ⬝ᵥ Wrᵀ (Sum.inr i))) • ψw i
            + (σ' (v ⬝ᵥ Wrᵀ (Sum.inl i)) * (v ⬝ᵥ (X *ᵥ Wrᵀ (Sum.inl i) + ψrᵀ (Sum.inl i)))
              * (v ⬝ᵥ Wrᵀ (Sum.inr i))) • Ww i
            + (σ (v ⬝ᵥ Wrᵀ (Sum.inl i))
              * (v ⬝ᵥ (X *ᵥ Wrᵀ (Sum.inr i) + ψrᵀ (Sum.inr i)))) • Ww i)
          - ((v ᵥ* ((Fintype.card d : ℝ)⁻¹ • X)) ⬝ᵥ v)
            • ∑ i, (σ' (v ⬝ᵥ Wrᵀ (Sum.inl i)) * (v ⬝ᵥ Wrᵀ (Sum.inl i))
                * (v ⬝ᵥ Wrᵀ (Sum.inr i))
              + σ (v ⬝ᵥ Wrᵀ (Sum.inl i)) * (v ⬝ᵥ Wrᵀ (Sum.inr i))) • Ww i) j := by
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib,
    Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_gated_apply_gun hσ]
  -- the entries of `(v, …, v) W_read`, of the tangent of `N_ε` times `W_read`, of
  -- `(v, …, v) ψ_read` and of the block
  have h1 : ∀ col, ((of fun _ : T => v) * Wr) t col = v ⬝ᵥ Wrᵀ col := fun _ => rfl
  have h2 : ∀ col, (tangentRMS X (of fun _ : T => v) * Wr) t col
      = (v ᵥ* X) ⬝ᵥ Wrᵀ col - ((v ᵥ* X) ⬝ᵥ v) / Fintype.card d * (v ⬝ᵥ Wrᵀ col) :=
    fun col => by
      show (v ᵥ* X - (((v ᵥ* X) ⬝ᵥ v) / Fintype.card d) • v) ⬝ᵥ Wrᵀ col = _
      rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
  have h3 : ∀ col, ((of fun _ : T => v) * ψr) t col = v ⬝ᵥ ψrᵀ col := fun _ => rfl
  have h4 : (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f 0 ((of fun _ : T => v) * Wr) t i
      = σ (v ⬝ᵥ Wrᵀ (Sum.inl i)) * (v ⬝ᵥ Wrᵀ (Sum.inr i)) := rfl
  rw [h4]
  simp only [Matrix.add_apply, h1, h2, h3, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    dotProduct_add, Matrix.dotProduct_mulVec, Matrix.vecMul_smul, smul_dotProduct]
  ring

/-- **Proof of Theorem B.1 (iii), Step 4, for a gated block of any width whose units have the
property `GatedUnitsNoSymmetricPart`:** for `ε > 0` and a differentiable gate activation, under
the conditions `OneBlockGenericGatedRMS`, equation (17) at all inputs forces `X_s = 0`. -/
theorem noSymmetricPart_gated_rmsNorm_of_units (hε : 0 < ε) (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsNoSymmetricPart σ σ' d d (hid 0))
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericGatedRMS θ) :
    NoSymmetricPart (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) ε θ Set.univ := by
  intro X ψr ψw hXs h
  rcases isEmpty_or_nonempty d with hd | hd
  · ext a
    exact (IsEmpty.false a).elim
  have hc : (Fintype.card d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  -- `x ↦ x E` is onto, through a left inverse `B` of `E`
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hθ.rank_E)
  -- the rows `v` of the inputs `(v, …, v)` in the image of `N_ε`: an open set that contains `0`
  have hopen : IsOpen {v : d → ℝ |
      (Matrix.of fun _ : T => v) ∈ Set.range (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ)} :=
    (isOpenMap_rmsNorm hε).isOpen_range.preimage (continuous_pi fun _ => continuous_id)
  have h0 : (0 : d → ℝ) ∈ {v : d → ℝ |
      (Matrix.of fun _ : T => v) ∈ Set.range (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ)} :=
    ⟨0, by rw [rmsNorm_zero_gun]; rfl⟩
  -- equation (17) at the input `g B` with `N_ε(g) = (v, …, v)`, at one token, is the equation of
  -- `GatedUnitsNoSymmetricPart` with `ψc_i = X c_i + (ψ_read)_{g i}`,
  -- `ψe_i = X e_i + (ψ_read)_{v i}` and `X / d`
  have hX := hU (fun i => (θ.read 0)ᵀ (Sum.inl i)) (fun i => (θ.read 0)ᵀ (Sum.inr i))
    (fun i => θ.write 0 i) ((Fintype.card d : ℝ)⁻¹ • X)
    (fun i => X *ᵥ (θ.read 0)ᵀ (Sum.inl i) + ψrᵀ (Sum.inl i))
    (fun i => X *ᵥ (θ.read 0)ᵀ (Sum.inr i) + ψrᵀ (Sum.inr i)) (fun i => ψw i) _
    hθ.row_ne_zero hθ.gate_ne_zero hθ.gate_not_collinear hθ.value_ne_zero
    (by rw [transpose_smul, hXs]) hopen ⟨0, h0⟩ (by
      intro v hv
      obtain ⟨g, hg⟩ := hv
      have e := h (g * B) (Set.mem_univ _)
      rw [Matrix.mul_assoc, hB, Matrix.mul_one, hg] at e
      refine sub_eq_zero.1 (funext fun j => ?_)
      have e2 := congrFun (congrFun e (Classical.arbitrary T)) j
      rw [entry_gun hσ] at e2
      exact e2)
  -- `X / d = 0`, so `X = 0`
  exact (smul_eq_zero.1 hX).resolve_left (inv_ne_zero hc)

/-! ### Helpers: almost every `(θ, A)` (copies of the private helpers of
`OneBlock/LearnedSkipNarrowMlp.lean`) -/

omit [DecidableEq d] in
/-- Helper: the skips `Fin 1 → Matrix d d ℝ` carry the Borel σ-algebra of their norm topology (a
copy of the private `borelSpace_skips_lnm` of `OneBlock/LearnedSkipNarrowMlp.lean`). -/
private theorem borelSpace_skips_gun : BorelSpace (Fin 1 → Matrix d d ℝ) :=
  inferInstanceAs (BorelSpace (Fin 1 → d → d → ℝ))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: a condition on the weights that holds at almost every `θ` holds at almost every
`(θ, v)` (a copy of the private `ae_fst_lnm`). -/
private theorem ae_fst_gun {A : Arch T d 1} {V : Type*} [NormedAddCommGroup V]
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
point, it is invertible at almost every point (a copy of the private `ae_isUnit_det_lnm`). -/
private theorem ae_isUnit_det_gun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

/-- Helper: at almost every `(θ, A)` the conditions `OneBlockGenericGatedRMS θ` hold and the skip
`A = R 0` is invertible, for `d_in, d_out ≥ d ≥ 2` (the twin of the private `ae_generic_lnm`). -/
private theorem ae_generic_gun
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [hμ : μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, OneBlockGenericGatedRMS p.1 ∧ IsUnit (p.2 0).det := by
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := borelSpace_skips_gun
  have hBp : BorelSpace (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)) := Prod.borelSpace
  have h1 := ae_fst_gun hBs μ hμ (ae_oneBlockGenericGatedRMS Measure.addHaar hd hdIn hdOut)
  have h2 := ae_isUnit_det_gun hBp μ hμ
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix d d ℝ) 0)
      ∘ₗ (LinearMap.snd ℝ (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
        (Fin 1 → Matrix d d ℝ))) (0, fun _ => 1) rfl
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

/-- Helper: `d (d + 1)/2 + d (d − 1)/2 = d²` (both products are even; a copy of the private
`half_add_half_lnm`). -/
private theorem half_add_half_gun (n : ℕ) : n * (n + 1) / 2 + n * (n - 1) / 2 = n ^ 2 := by
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

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper (the value from the difference): `fd = fd₁ + d (d + 1)/2` and
`fd₁ + (d (d − 1)/2 + s) = P` give `fd + (d (d − 1) + s) = P + d²` (the twin of the private
`value_of_eq_residual_add_lnm`, with the `s` rescalings of the values). -/
private theorem value_of_eq_residual_add_gun {fd fd₁ P s : ℕ}
    (h1 : fd = fd₁ + Fintype.card d * (Fintype.card d + 1) / 2)
    (h2 : fd₁ + (Fintype.card d * (Fintype.card d - 1) / 2 + s) = P) :
    fd + (Fintype.card d * (Fintype.card d - 1) + s) = P + Fintype.card d ^ 2 := by
  have h3 := half_add_half_gun (Fintype.card d)
  have h4 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  generalize Fintype.card d * (Fintype.card d + 1) = y at h1 h3
  generalize Fintype.card d * (Fintype.card d - 1) = x at h2 h3 h4 ⊢
  generalize Fintype.card d ^ 2 = q at h3 ⊢
  omega

/-- **Theorem B.1 (iii) of the skips paper, "exceeds that of the residual network of part (ii) by
exactly `d_model (d_model + 1)/2`", for one SwiGLU block of any width with a full learned skip,
`ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and at least one hidden unit, at almost every weights and
skip `(θ, A)` the functional dimension is that of the residual network with the weights `θ` plus
`d (d + 1)/2`. -/
theorem ae_funDimLearned_swiglu_rmsNorm_eq_residual_add_of_nonempty (hε : 0 < ε)
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.gated silu (rmsNorm ε) hid) p
      = funDim (Arch.gated silu (rmsNorm ε) hid) 1 p.1
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the block is analytic, hence `C¹`
  have hf : ContDiff ℝ 1 ((Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid).f 0) :=
    (analyticOnNhd_f_gated analyticOnNhd_silu 0).contDiff
  -- the conditions of the proof and an invertible skip hold at almost every `(θ, A)`; Step 4 from
  -- `silu_gatedUnitsNoSymmetricPart`, Steps 1 to 3 and 5 from `LearnedSkipGain`
  filter_upwards [ae_generic_gun μ hd hdIn hdOut] with p hp
  exact funDimLearned_eq_funDim_residual_add_of_noSymmetricPart hε rfl hf p.1 p.2 hp.1.rank_E
    hp.1.rank_D hp.2 (noSymmetricPart_gated_rmsNorm_of_units hε hasDerivAt_silu
      (silu_gatedUnitsNoSymmetricPart d d (hid 0)) p.1 hp.1)

/-- **Theorem B.1 (iii), "and it satisfies the equality condition", for one SwiGLU block of any
width with a full learned skip, `ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and at least one hidden
unit, at almost every `(θ, A)` the functional dimension is `P + d² − d (d − 1) − d_hidden`. -/
theorem ae_funDimLearned_swiglu_rmsNorm_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.gated silu (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  -- the difference to the residual network, and its value `P − d (d − 1)/2 − d_hidden` at
  -- almost every `θ`
  have hres := ae_fst_gun borelSpace_skips_gun μ ‹_›
    (ae_funDim_swiglu_oneBlock_residual_rmsNorm hε Measure.addHaar hd hdIn hdOut)
  filter_upwards [ae_funDimLearned_swiglu_rmsNorm_eq_residual_add_of_nonempty hε μ hd hdIn hdOut,
    hres] with p h1 h2
  exact value_of_eq_residual_add_gun h1 h2

/-- **The same difference for one GeGLU block of any width with a full learned skip,
`ε > 0`.** -/
theorem ae_funDimLearned_geglu_rmsNorm_eq_residual_add_of_nonempty (hε : 0 < ε)
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.gated gelu (rmsNorm ε) hid) p
      = funDim (Arch.gated gelu (rmsNorm ε) hid) 1 p.1
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the block is analytic, hence `C¹`
  have hf : ContDiff ℝ 1 ((Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid).f 0) :=
    (analyticOnNhd_f_gated analyticOnNhd_gelu 0).contDiff
  -- the conditions of the proof and an invertible skip hold at almost every `(θ, A)`; Step 4 from
  -- `gelu_gatedUnitsNoSymmetricPart`, Steps 1 to 3 and 5 from `LearnedSkipGain`
  filter_upwards [ae_generic_gun μ hd hdIn hdOut] with p hp
  exact funDimLearned_eq_funDim_residual_add_of_noSymmetricPart hε rfl hf p.1 p.2 hp.1.rank_E
    hp.1.rank_D hp.2 (noSymmetricPart_gated_rmsNorm_of_units (σ' := geluDeriv) hε hasDerivAt_gelu
      (gelu_gatedUnitsNoSymmetricPart d d (hid 0)) p.1 hp.1)

/-- **The same value for one GeGLU block of any width with a full learned skip, `ε > 0`.** -/
theorem ae_funDimLearned_geglu_rmsNorm_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.gated gelu (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  -- the difference to the residual network, and its value `P − d (d − 1)/2 − d_hidden` at
  -- almost every `θ`
  have hres := ae_fst_gun borelSpace_skips_gun μ ‹_›
    (ae_funDim_geglu_oneBlock_residual_rmsNorm hε Measure.addHaar hd hdIn hdOut)
  filter_upwards [ae_funDimLearned_geglu_rmsNorm_eq_residual_add_of_nonempty hε μ hd hdIn hdOut,
    hres] with p h1 h2
  exact value_of_eq_residual_add_gun h1 h2

end Skips
