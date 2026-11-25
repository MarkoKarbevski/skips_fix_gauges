import SkipsLean.OneBlock.MlpBiases

/-!
# The one-block theorem with biases for a tanh block and for a GELU block, by name

Paper (skips paper), Theorem B.1 (i): "For generic parameters the skipless network has functional
dimension `P − 2 d_model² − s` and the residual network `P − d_model² − s`; with biases on the
embedding, the block and the readout, counted in `P`, both values are `2 d_model` lower".

`OneBlock/MlpBiases.lean` states the two values for every activation with the conclusion of Lemma
B.3 with `s = 0` (`UnitsRigid`), and names tanh and GELU only in "the skip raises the functional
dimension by exactly `d_model²`". Here the two values with tanh and with GELU written in.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Theorem B.1 (i) with biases for one `tanh` block, without the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − 2 d² − 2 d`, with `P`
counting the biases. -/
theorem ae_funDimB_tanh_oneBlock
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp Real.tanh id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :=
  ae_funDimB_mlp_oneBlock hasDerivAt_tanh (tanh_unitsRigid _ _ _) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one `tanh` block, with the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − d² − 2 d`, with `P`
counting the biases. -/
theorem ae_funDimB_tanh_oneBlock_residual
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp Real.tanh id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :=
  ae_funDimB_mlp_oneBlock_residual hasDerivAt_tanh (tanh_unitsRigid _ _ _) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one GELU block, without the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − 2 d² − 2 d`, with `P`
counting the biases. -/
theorem ae_funDimB_gelu_oneBlock
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp gelu id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) :=
  ae_funDimB_mlp_oneBlock hasDerivAt_gelu (gelu_unitsRigid _ _ _) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one GELU block, with the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − d² − 2 d`, with `P`
counting the biases. -/
theorem ae_funDimB_gelu_oneBlock_residual
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp gelu id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) :=
  ae_funDimB_mlp_oneBlock_residual hasDerivAt_gelu (gelu_unitsRigid _ _ _) μ hd hdIn hdOut hhid

end Skips
