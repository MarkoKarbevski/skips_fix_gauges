import SkipsLean.OneBlock.LearnedSkipTriangular
import SkipsLean.OneBlock.LearnedSkipRescale
import SkipsLean.OneBlock.LearnedSkipReGLU

/-!
# One ReLU, ReLU² or ReGLU block with an upper triangular learned skip under pre-RMSNorm

Paper (skips paper): Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. For generic parameters and `ε > 0`, its functional
dimension exceeds that of the residual network of part (ii) by exactly `d_model (d_model + 1)/2`,
and it satisfies the equality condition." Its proof: "For an upper triangular `A`, view the network
as the network with a full `A` restricted to triangular skips: its flat directions are those of the
full network whose entry `η_A` is upper triangular." Appendix B, "Notation and flat directions":
"For the ReLU-type activations, `F(θ, x)` is differentiable in `θ` at the inputs `x` at which no
hidden unit sits at its kink, which form an open set of full measure, and 'every input' means every
such input."

For these blocks the statements are in the paper's own sense, on the inputs with no hidden unit at
its kink:

* `funDimSkipsOn A ι p U`: the largest rank of the Jacobian in the weights and the skips over the
  finite batches of inputs of the set `U` (for `U` the inputs off the kinks: the paper's functional
  dimension of a network with ReLU-type blocks);
* at one parameter, under the generic conditions of the residual statements and for an invertible
  upper triangular skip: a batch of inputs off the kinks on which the Jacobian of the triangular
  family has the rank `P + d (d + 1)/2 − d (d − 1)/2 − s`; no batch of such inputs has a larger
  rank; so `funDimSkipsOn` has this value (the equality condition: `P + d (d + 1)/2` parameters,
  symmetries of dimension `d (d − 1)/2 + s`), with `s = d_hidden` for ReLU and ReLU² and
  `s = 2 d_hidden` for ReGLU;
* for `d_in, d_out ≥ d ≥ 2`: the same at almost every `(θ, A)`, `A` upper triangular, and
  `d (d + 1)/2` more than the residual network at almost every `θ'`.

The route: on a batch of inputs off the kinks both families are differentiable, the Jacobian of the
triangular family is that of the full family restricted to triangular directions of the skip, and
every direction of the skip is a triangular one plus `−X_0 A` with `X_0` antisymmetric, whose
rotation direction is flat (as in `funDimLearnedTri_eq_funDimLearned`); so the two Jacobians have
the same range, and the values for the full skip (`OneBlock/LearnedSkipRescale.lean`,
`OneBlock/LearnedSkipReGLU.lean`) carry over. The value of Lean's `funDimLearnedTri`, which also
uses the inputs on the kinks at which the output happens to be differentiable, is not stated.
Numeric check: `learned_skip_relu_attention_check_2026-11-24.py`. Not stated: `ε = 0`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [LinearOrder d] [Fintype dIn] [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **The functional dimension on a set of inputs,** for the network whose skips are parameters: the
largest rank of the Jacobian in the weights and the skips over the finite batches of inputs of `U`.
For `U` the inputs with no hidden unit at its kink this is the paper's functional dimension of a
network with ReLU-type blocks. -/
noncomputable def funDimSkipsOn {L : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V)
    (U : Set (Matrix T dIn ℝ)) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
    r = jacobianRankSkips A ι X p}

/-- **Theorem B.1 (iii) for the upper triangular skip, in the paper's own sense, for ReLU-type MLP
blocks, at one parameter:** under the conditions `OneBlockGenericRMS`, for an invertible upper
triangular skip, a finite batch of inputs with no hidden unit at its kink on which the Jacobian in
the weights and the triangular skip has the rank `P + d (d + 1)/2 − d (d − 1)/2 − s`. -/
theorem exists_jacobianRankSkips_tri_mlp_rescale_rmsNorm
    {k : ℕ} (hk : k ≠ 0) (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0)) [Nonempty (hid 0)]
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkRMS θ) ∧
      jacobianRankSkips (Arch.mlp σ (rmsNorm ε) hid) (triSkips d 1) X (θ, R)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
          + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **No batch of inputs off the kinks has a larger rank,** for ReLU-type MLP blocks with an upper
triangular learned skip, at one parameter: under the conditions `OneBlockGenericRMS`, for an
invertible upper triangular skip and every finite batch of inputs with no hidden unit at its kink,
the rank of the Jacobian in the weights and the triangular skip is at most `P + d (d + 1)/2 − d (d −
1)/2 − s`. -/
theorem jacobianRankSkips_tri_add_le_mlp_rescale_rmsNorm
    {k : ℕ} (hk : k ≠ 0) (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0)) [Nonempty (hid 0)]
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (hX : ∀ i, X i ∈ noKinkRMS θ) :
    jacobianRankSkips (Arch.mlp σ (rmsNorm ε) hid) (triSkips d 1) X (θ, R)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) for the upper triangular skip, for ReLU-type MLP blocks, at one parameter:**
under the conditions `OneBlockGenericRMS`, for an invertible upper triangular skip, the functional
dimension on the inputs with no hidden unit at its kink is `P + d (d + 1)/2 − d (d − 1)/2 − s`. -/
theorem funDimSkipsOn_tri_mlp_rescale_rmsNorm
    {k : ℕ} (hk : k ≠ 0) (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0)) [Nonempty (hid 0)]
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) :
    funDimSkipsOn (Arch.mlp σ (rmsNorm ε) hid) (triSkips d 1) (θ, R) (noKinkRMS θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one ReLU block with an upper triangular learned skip,
`ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and a block of any width with at least one hidden unit, at
almost every `(θ, A)`, `A` upper triangular, the functional dimension on the inputs with no hidden
unit at its kink is `P + d (d + 1)/2 − d (d − 1)/2 − d_hidden`. -/
theorem ae_funDimSkipsOn_tri_relu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp relu (rmsNorm ε) hid) (triSkips d 1) p (noKinkRMS p.1)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly `d (d +
1)/2`", for one ReLU block with an upper triangular learned skip, `ε > 0`:** at almost every `(θ,
A)`, `A` upper triangular, and almost every `θ'`, the functional dimension on the inputs with no
hidden unit at its kink is that of the residual network at `θ'` plus `d (d + 1)/2`. -/
theorem ae_funDimSkipsOn_tri_relu_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimSkipsOn (Arch.mlp relu (rmsNorm ε) hid) (triSkips d 1) p (noKinkRMS
        p.1)
      = funDim (Arch.mlp relu (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one ReLU² block with an upper triangular learned
skip, `ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and a block of any width with at least one hidden unit,
at almost every `(θ, A)`, `A` upper triangular, the functional dimension on the inputs with no
hidden unit at its kink is `P + d (d + 1)/2 − d (d − 1)/2 − d_hidden`. -/
theorem ae_funDimSkipsOn_tri_reluSq_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp reluSq (rmsNorm ε) hid) (triSkips d 1) p (noKinkRMS p.1)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly `d (d +
1)/2`", for one ReLU² block with an upper triangular learned skip, `ε > 0`:** at almost every `(θ,
A)`, `A` upper triangular, and almost every `θ'`, the functional dimension on the inputs with no
hidden unit at its kink is that of the residual network at `θ'` plus `d (d + 1)/2`. -/
theorem ae_funDimSkipsOn_tri_reluSq_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimSkipsOn (Arch.mlp reluSq (rmsNorm ε) hid) (triSkips d 1) p (noKinkRMS
        p.1)
      = funDim (Arch.mlp reluSq (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) for the upper triangular skip, in the paper's own sense, for a ReGLU block,
at one parameter:** under the conditions `OneBlockGenericReGLURMS`, for an invertible upper
triangular skip, a finite batch of inputs with no gate at its kink on which the Jacobian in the
weights and the triangular skip has the rank `P + d (d + 1)/2 − d (d − 1)/2 − 2 d_hidden`. -/
theorem exists_jacobianRankSkips_tri_reglu_rmsNorm
    (hε : 0 < ε) [Nonempty (hid 0)]
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateRMS θ) ∧
      jacobianRankSkips (Arch.gated relu (rmsNorm ε) hid) (triSkips d 1) X (θ, R)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
          + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **No batch of inputs off the kinks has a larger rank,** for a ReGLU block with an upper
triangular learned skip, at one parameter: under the conditions `OneBlockGenericReGLURMS`, for an
invertible upper triangular skip and every finite batch of inputs with no gate at its kink, the rank
of the Jacobian in the weights and the triangular skip is at most `P + d (d + 1)/2 − d (d − 1)/2 − 2
d_hidden`. -/
theorem jacobianRankSkips_tri_add_le_reglu_rmsNorm
    (hε : 0 < ε) [Nonempty (hid 0)]
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (hX : ∀ i, X i ∈ noKinkGateRMS θ) :
    jacobianRankSkips (Arch.gated relu (rmsNorm ε) hid) (triSkips d 1) X (θ, R)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * Fintype.card (hid 0))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) for the upper triangular skip, for a ReGLU block, at one parameter:** under
the conditions `OneBlockGenericReGLURMS`, for an invertible upper triangular skip, the functional
dimension on the inputs with no gate at its kink is `P + d (d + 1)/2 − d (d − 1)/2 − 2 d_hidden`. -/
theorem funDimSkipsOn_tri_reglu_rmsNorm
    (hε : 0 < ε) [Nonempty (hid 0)]
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) :
    funDimSkipsOn (Arch.gated relu (rmsNorm ε) hid) (triSkips d 1) (θ, R) (noKinkGateRMS θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one ReGLU block with an upper triangular learned
skip, `ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and a block of any width with at least one hidden unit,
at almost every `(θ, A)`, `A` upper triangular, the functional dimension on the inputs with no gate
at its kink is `P + d (d + 1)/2 − d (d − 1)/2 − 2 d_hidden`. -/
theorem ae_funDimSkipsOn_tri_reglu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.gated relu (rmsNorm ε) hid) (triSkips d 1) p (noKinkGateRMS p.1)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly `d (d +
1)/2`", for one ReGLU block with an upper triangular learned skip, `ε > 0`:** at almost every `(θ,
A)`, `A` upper triangular, and almost every `θ'`, the functional dimension on the inputs with no
gate at its kink is that of the residual network at `θ'` plus `d (d + 1)/2`. -/
theorem ae_funDimSkipsOn_tri_reglu_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimSkipsOn (Arch.gated relu (rmsNorm ε) hid) (triSkips d 1) p
        (noKinkGateRMS p.1)
      = funDim (Arch.gated relu (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

end Skips
