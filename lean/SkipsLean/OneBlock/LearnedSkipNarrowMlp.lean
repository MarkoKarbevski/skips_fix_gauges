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
  sorry

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
  sorry

/-- **The same difference for one GELU block of any width with a full learned skip, `ε > 0`.** -/
theorem ae_funDimLearned_gelu_rmsNorm_eq_residual_add_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp gelu (rmsNorm ε) hid) p
      = funDim (Arch.mlp gelu (rmsNorm ε) hid) 1 p.1
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

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
  sorry

end Skips
