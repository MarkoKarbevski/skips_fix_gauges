import SkipsLean.OneBlock.GatedBiases

/-!
# The one-block theorem with biases for a SwiGLU block and for a GeGLU block, by name

Paper (skips paper), Theorem B.1 (i): "For generic parameters the skipless network has functional
dimension `P − 2 d_model² − s` and the residual network `P − d_model² − s`; with biases on the
embedding, the block and the readout, counted in `P`, both values are `2 d_model` lower".

`OneBlock/GatedBiases.lean` states the two values for every gate activation with the conclusion
of Lemma B.3 for SwiGLU and GeGLU (`GatedUnitsRescale`), and names SwiGLU and GeGLU only in "the
skip raises the functional dimension by exactly `d_model²`". Here the two values with SwiGLU and
with GeGLU written in; `s = d_hidden`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Theorem B.1 (i) with biases for one SwiGLU block, without the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − 2 d² − 2 d − d_hidden`,
with `P` counting the biases. -/
theorem ae_funDimB_swiglu_oneBlock
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated silu id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) :=
  ae_funDimB_gated_oneBlock hasDerivAt_silu (silu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one SwiGLU block, with the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − d² − 2 d − d_hidden`,
with `P` counting the biases. -/
theorem ae_funDimB_swiglu_oneBlock_residual
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated silu id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) :=
  ae_funDimB_gated_oneBlock_residual hasDerivAt_silu (silu_gatedUnitsRescale _ _ _) μ hd hdIn
    hdOut hhid

/-- **Theorem B.1 (i) with biases for one GeGLU block, without the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − 2 d² − 2 d − d_hidden`,
with `P` counting the biases. -/
theorem ae_funDimB_geglu_oneBlock
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated gelu id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) :=
  ae_funDimB_gated_oneBlock hasDerivAt_gelu (gelu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one GeGLU block, with the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − d² − 2 d − d_hidden`,
with `P` counting the biases. -/
theorem ae_funDimB_geglu_oneBlock_residual
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated gelu id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) :=
  ae_funDimB_gated_oneBlock_residual hasDerivAt_gelu (gelu_gatedUnitsRescale _ _ _) μ hd hdIn
    hdOut hhid

end Skips
