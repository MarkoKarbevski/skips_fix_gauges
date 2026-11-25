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

/-- **Proof of Theorem B.1 (iii), Step 4, for a gated block of any width whose units have the
property `GatedUnitsNoSymmetricPart`:** for `ε > 0` and a differentiable gate activation, under
the conditions `OneBlockGenericGatedRMS`, equation (17) at all inputs forces `X_s = 0`. -/
theorem noSymmetricPart_gated_rmsNorm_of_units (hε : 0 < ε) (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsNoSymmetricPart σ σ' d d (hid 0))
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericGatedRMS θ) :
    NoSymmetricPart (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) ε θ Set.univ := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end Skips
