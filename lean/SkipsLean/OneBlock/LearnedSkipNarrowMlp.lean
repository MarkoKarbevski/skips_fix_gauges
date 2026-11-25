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

/-- **Proof of Theorem B.1 (iii), Step 4, for an MLP block of any width whose units have the
property `UnitsNoSymmetricPart`:** for `ε > 0` and a differentiable activation, under the
conditions `OneBlockGenericRMS`, equation (17) at all inputs forces `X_s = 0`. -/
theorem noSymmetricPart_mlp_rmsNorm_of_units (hε : 0 < ε) (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsNoSymmetricPart σ σ' d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) :
    NoSymmetricPart (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) ε θ Set.univ := by
  sorry

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
