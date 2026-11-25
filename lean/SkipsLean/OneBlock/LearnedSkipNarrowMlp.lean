import SkipsLean.OneBlock.LearnedSkipKinds
import SkipsLean.OneBlock.LearnedSkipRescale
import SkipsLean.OneBlock.UnitsNoSymmetricPart

/-!
# One tanh or GELU block of any width with a full learned skip under pre-RMSNorm, `ε > 0`

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. For generic parameters and `ε > 0`, its functional
dimension exceeds that of the residual network of part (ii) by exactly `d_model (d_model + 1)/2`,
and it satisfies the equality condition."

Part (iii) has no condition on the width of the block. `OneBlock/LearnedSkipKinds.lean` proves it
for tanh, GELU, SwiGLU and GeGLU blocks of width at least `d_model`, by another route than the
paper's (the skip `A = 0` and the value of the skipless network). Here the paper's route, **for
tanh and GELU blocks of any width with at least one hidden unit**: Step 4 of the proof ("For the
other blocks both sides are analytic in `n`, so (17) holds for all `n`, and we take `n = t n̂` […]
In every case `q` vanishes on an open set for generic parameters, so `X_s = 0`") is
`UnitsNoSymmetricPart` (`OneBlock/UnitsNoSymmetricPart.lean`); it gives `NoSymmetricPart` at all
inputs under the conditions `OneBlockGenericRMS`, and Steps 1 to 3 and 5, proved once for all
kinds of block in `OneBlock/LearnedSkipGain.lean`
(`funDimLearned_eq_funDim_residual_add_of_noSymmetricPart`), give the difference to the residual
network at the same weights. The value `P + d² − d (d − 1)` follows from the value
`P − d (d − 1)/2` of the residual network (`OneBlock/ResidualRMSMlp.lean`, any width).

Not stated here: SwiGLU and GeGLU blocks narrower than `d_model`; the upper triangular skip for
narrow blocks.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-! ### Helpers: equation (17) along a row -/

/-- Helper: the derivative of `M ↦ σ(M)` (entrywise) at `P` along `Q` has the entries
`σ'(P_{t i}) Q_{t i}` (a copy of the private `fderiv_map_apply_rm` of
`OneBlock/ResidualRMSMlp.lean`). -/
private theorem fderiv_map_apply_lnm (hσ : ∀ z, HasDerivAt σ (σ' z) z) {m n : Type*} [Fintype m]
    [Fintype n] (P Q : Matrix m n ℝ) (t : m) (i : n) :
    fderiv ℝ (fun M : Matrix m n ℝ => M.map σ) P Q t i = σ' (P t i) * Q t i := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  have hd : Differentiable ℝ (fun M : Matrix m n ℝ => M.map σ) :=
    differentiable_pi.2 fun t => differentiable_pi.2 fun i =>
      hσd.comp (differentiable_pi.1 (differentiable_pi.1 differentiable_id t) i)
  -- the chain rule along the line `τ ↦ P + τ Q`
  have hline : HasDerivAt (fun τ : ℝ => P + τ • Q) Q 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const Q).const_add P
    rw [one_smul] at h
    exact h
  have h0 : P = P + (0 : ℝ) • Q := by rw [zero_smul, add_zero]
  have h1 := (hd P).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) i
  -- the same derivative, entrywise: `τ ↦ σ(P_{t i} + τ Q_{t i})`
  have h3 : HasDerivAt (fun τ : ℝ => σ (P t i + τ * Q t i)) (σ' (P t i) * Q t i) 0 := by
    have hu : HasDerivAt (fun τ : ℝ => P t i + τ * Q t i) (Q t i) 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).mul_const (Q t i)).const_add (P t i)
      rw [one_mul] at h
      exact h
    exact (hσ (P t i)).comp_of_eq (0 : ℝ) hu (by rw [zero_mul, add_zero])
  exact h2.unique h3

omit [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper: the same for the map of the block. -/
private theorem fderiv_f_lnm (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    {χ : Matrix T d ℝ → Matrix T d ℝ} (P Q : Matrix T (hid 0) ℝ) (t : T) (i : hid 0) :
    fderiv ℝ ((Arch.mlp (T := T) (d := d) σ χ hid).f 0) P Q t i = σ' (P t i) * Q t i :=
  fderiv_map_apply_lnm hσ P Q t i

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `N_ε(0) = 0`. -/
private theorem rmsNorm_zero_lnm : rmsNorm ε (0 : Matrix T d ℝ) = 0 := by
  ext t k
  simp [rmsNorm, rmsRow]

omit [Nonempty T] [DecidableEq d] in
/-- Helper: equation (17) at the input whose rows are all `v`, at the token `t` and the coordinate
`j`, is the equation of `UnitsNoSymmetricPart` at `v`, with `ψc_i = X c_i + (ψ_read)_i` and
`X / d` in place of `X`. -/
private theorem entry_lnm (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (Wr ψr : Matrix d (hid 0) ℝ) (Ww ψw : Matrix (hid 0) d ℝ) (X : Matrix d d ℝ)
    (v : d → ℝ) (t : T) (j : d) :
    (fderiv ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f 0) ((of fun _ : T => v) * Wr)
          (tangentRMS X (of fun _ : T => v) * Wr + (of fun _ : T => v) * ψr) * Ww
        + (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f 0 ((of fun _ : T => v) * Wr) * ψw) t j
      = (∑ i, (σ (v ⬝ᵥ Wrᵀ i) • ψw i
            + (σ' (v ⬝ᵥ Wrᵀ i) * (v ⬝ᵥ (X *ᵥ Wrᵀ i + ψrᵀ i))) • Ww i)
          - ((v ᵥ* ((Fintype.card d : ℝ)⁻¹ • X)) ⬝ᵥ v)
            • ∑ i, (σ' (v ⬝ᵥ Wrᵀ i) * (v ⬝ᵥ Wrᵀ i)) • Ww i) j := by
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib,
    Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_lnm hσ, Matrix.add_apply]
  have h1 : ((of fun _ : T => v) * Wr) t i = v ⬝ᵥ Wrᵀ i := rfl
  have h2 : (tangentRMS X (of fun _ : T => v) * Wr) t i
      = (v ᵥ* X) ⬝ᵥ Wrᵀ i - ((v ᵥ* X) ⬝ᵥ v) / Fintype.card d * (v ⬝ᵥ Wrᵀ i) := by
    show (v ᵥ* X - (((v ᵥ* X) ⬝ᵥ v) / Fintype.card d) • v) ⬝ᵥ Wrᵀ i = _
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
  have h3 : ((of fun _ : T => v) * ψr) t i = v ⬝ᵥ ψrᵀ i := rfl
  have h4 : (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f 0 ((of fun _ : T => v) * Wr) t i
      = σ (v ⬝ᵥ Wrᵀ i) := rfl
  rw [h1, h2, h3, h4, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul, smul_eq_mul, dotProduct_add, Matrix.dotProduct_mulVec, Matrix.vecMul_smul,
    smul_dotProduct, smul_eq_mul]
  ring

/-- **Proof of Theorem B.1 (iii), Step 4, for an MLP block of any width whose units have the
property `UnitsNoSymmetricPart`:** for `ε > 0` and a differentiable activation, under the
conditions `OneBlockGenericRMS`, equation (17) at all inputs forces `X_s = 0`. -/
theorem noSymmetricPart_mlp_rmsNorm_of_units (hε : 0 < ε) (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsNoSymmetricPart σ σ' d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) :
    NoSymmetricPart (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) ε θ Set.univ := by
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
    ⟨0, by rw [rmsNorm_zero_lnm]; rfl⟩
  -- equation (17) at the input `g B` with `N_ε(g) = (v, …, v)`, at one token, is the equation of
  -- `UnitsNoSymmetricPart` with `ψc_i = X c_i + (ψ_read)_i` and `X / d`
  have hX := hU (fun i => (θ.read 0)ᵀ i) (fun i => θ.write 0 i)
    ((Fintype.card d : ℝ)⁻¹ • X) (fun i => X *ᵥ (θ.read 0)ᵀ i + ψrᵀ i) (fun i => ψw i) _
    hθ.row_ne_zero hθ.col_ne_zero hθ.col_not_collinear (by rw [transpose_smul, hXs]) hopen
    ⟨0, h0⟩ (by
      intro v hv
      obtain ⟨g, hg⟩ := hv
      have e := h (g * B) (Set.mem_univ _)
      rw [Matrix.mul_assoc, hB, Matrix.mul_one, hg] at e
      refine sub_eq_zero.1 (funext fun j => ?_)
      have e2 := congrFun (congrFun e (Classical.arbitrary T)) j
      rw [entry_lnm hσ] at e2
      exact e2)
  -- `X / d = 0`, so `X = 0`
  exact (smul_eq_zero.1 hX).resolve_left (inv_ne_zero hc)

/-! ### Helpers: almost every `(θ, A)` (copies of the private helpers of
`OneBlock/LearnedSkipRescale.lean`) -/

omit [DecidableEq d] in
/-- Helper: the skips `Fin 1 → Matrix d d ℝ` carry the Borel σ-algebra of their norm topology (a
copy of the private `borelSpace_skips_lsr` of `OneBlock/LearnedSkipRescale.lean`). -/
private theorem borelSpace_skips_lnm : BorelSpace (Fin 1 → Matrix d d ℝ) :=
  inferInstanceAs (BorelSpace (Fin 1 → d → d → ℝ))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: a condition on the weights that holds at almost every `θ` holds at almost every
`(θ, v)` (a copy of the private `ae_fst_lsr` of `OneBlock/LearnedSkipRescale.lean`). -/
private theorem ae_fst_lnm {A : Arch T d 1} {V : Type*} [NormedAddCommGroup V]
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
point, it is invertible at almost every point (a copy of the private `ae_isUnit_det_lsr` of
`OneBlock/LearnedSkipRescale.lean`). -/
private theorem ae_isUnit_det_lnm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

/-- Helper: at almost every `(θ, A)` the conditions `OneBlockGenericRMS θ` hold and the skip
`A = R 0` is invertible, for `d_in, d_out ≥ d ≥ 2` (a copy of the private `ae_generic_lsr` of
`OneBlock/LearnedSkipRescale.lean`). -/
private theorem ae_generic_lnm
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [hμ : μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, OneBlockGenericRMS p.1 ∧ IsUnit (p.2 0).det := by
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := borelSpace_skips_lnm
  have hBp : BorelSpace (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)) := Prod.borelSpace
  have h1 := ae_fst_lnm hBs μ hμ (ae_oneBlockGenericRMS Measure.addHaar hd hdIn hdOut)
  have h2 := ae_isUnit_det_lnm hBp μ hμ
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix d d ℝ) 0)
      ∘ₗ (LinearMap.snd ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
        (Fin 1 → Matrix d d ℝ))) (0, fun _ => 1) rfl
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

/-- Helper: `d (d + 1)/2 + d (d − 1)/2 = d²` (both products are even; a copy of the private
`half_add_half_lsr` of `OneBlock/LearnedSkipRescale.lean`). -/
private theorem half_add_half_lnm (n : ℕ) : n * (n + 1) / 2 + n * (n - 1) / 2 = n ^ 2 := by
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
`fd₁ + d (d − 1)/2 = P` give `fd + d (d − 1) = P + d²`. -/
private theorem value_of_eq_residual_add_lnm {fd fd₁ P : ℕ}
    (h1 : fd = fd₁ + Fintype.card d * (Fintype.card d + 1) / 2)
    (h2 : fd₁ + Fintype.card d * (Fintype.card d - 1) / 2 = P) :
    fd + Fintype.card d * (Fintype.card d - 1) = P + Fintype.card d ^ 2 := by
  have h3 := half_add_half_lnm (Fintype.card d)
  have h4 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  generalize Fintype.card d * (Fintype.card d + 1) = y at h1 h3
  generalize Fintype.card d * (Fintype.card d - 1) = x at h2 h3 h4 ⊢
  generalize Fintype.card d ^ 2 = q at h3 ⊢
  omega

/-- **Theorem B.1 (iii) of the skips paper, "exceeds that of the residual network of part (ii) by
exactly `d_model (d_model + 1)/2`", for one tanh block of any width with a full learned skip,
`ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and at least one hidden unit, at almost every weights and
skip `(θ, A)` the functional dimension is that of the residual network with the weights `θ` plus
`d (d + 1)/2`. -/
theorem ae_funDimLearned_tanh_rmsNorm_eq_residual_add_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp Real.tanh (rmsNorm ε) hid) p
      = funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 p.1
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the block is analytic, hence `C¹`
  have hf : ContDiff ℝ 1 ((Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid).f 0) :=
    (analyticOnNhd_f_mlp analyticOnNhd_tanh 0).contDiff
  -- the conditions of the proof and an invertible skip hold at almost every `(θ, A)`; Step 4 from
  -- `tanh_unitsNoSymmetricPart`, Steps 1 to 3 and 5 from `LearnedSkipGain`
  filter_upwards [ae_generic_lnm μ hd hdIn hdOut] with p hp
  exact funDimLearned_eq_funDim_residual_add_of_noSymmetricPart hε rfl hf p.1 p.2 hp.1.rank_E
    hp.1.rank_D hp.2 (noSymmetricPart_mlp_rmsNorm_of_units hε hasDerivAt_tanh
      (tanh_unitsNoSymmetricPart d d (hid 0)) p.1 hp.1)

/-- **Theorem B.1 (iii), "and it satisfies the equality condition", for one tanh block of any
width with a full learned skip, `ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and at least one hidden
unit, at almost every `(θ, A)` the functional dimension is `P + d² − d (d − 1)`. -/
theorem ae_funDimLearned_tanh_rmsNorm_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp Real.tanh (rmsNorm ε) hid) p
        + Fintype.card d * (Fintype.card d - 1)
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  -- the difference to the residual network, and its value `P − d (d − 1)/2` at almost every `θ`
  have hres := ae_fst_lnm borelSpace_skips_lnm μ ‹_›
    (ae_funDim_tanh_oneBlock_residual_rmsNorm hε Measure.addHaar hd hdIn hdOut)
  filter_upwards [ae_funDimLearned_tanh_rmsNorm_eq_residual_add_of_nonempty hε μ hd hdIn hdOut,
    hres] with p h1 h2
  exact value_of_eq_residual_add_lnm h1 h2

/-- **The same difference for one GELU block of any width with a full learned skip, `ε > 0`.** -/
theorem ae_funDimLearned_gelu_rmsNorm_eq_residual_add_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp gelu (rmsNorm ε) hid) p
      = funDim (Arch.mlp gelu (rmsNorm ε) hid) 1 p.1
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the block is analytic, hence `C¹`
  have hf : ContDiff ℝ 1 ((Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid).f 0) :=
    (analyticOnNhd_f_mlp analyticOnNhd_gelu 0).contDiff
  -- the conditions of the proof and an invertible skip hold at almost every `(θ, A)`; Step 4 from
  -- `gelu_unitsNoSymmetricPart`, Steps 1 to 3 and 5 from `LearnedSkipGain`
  filter_upwards [ae_generic_lnm μ hd hdIn hdOut] with p hp
  exact funDimLearned_eq_funDim_residual_add_of_noSymmetricPart hε rfl hf p.1 p.2 hp.1.rank_E
    hp.1.rank_D hp.2 (noSymmetricPart_mlp_rmsNorm_of_units (σ' := geluDeriv) hε hasDerivAt_gelu
      (gelu_unitsNoSymmetricPart d d (hid 0)) p.1 hp.1)

/-- **The same value for one GELU block of any width with a full learned skip, `ε > 0`.** -/
theorem ae_funDimLearned_gelu_rmsNorm_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp gelu (rmsNorm ε) hid) p
        + Fintype.card d * (Fintype.card d - 1)
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  -- the difference to the residual network, and its value `P − d (d − 1)/2` at almost every `θ`
  have hres := ae_fst_lnm borelSpace_skips_lnm μ ‹_›
    (ae_funDim_gelu_oneBlock_residual_rmsNorm hε Measure.addHaar hd hdIn hdOut)
  filter_upwards [ae_funDimLearned_gelu_rmsNorm_eq_residual_add_of_nonempty hε μ hd hdIn hdOut,
    hres] with p h1 h2
  exact value_of_eq_residual_add_lnm h1 h2

end Skips
