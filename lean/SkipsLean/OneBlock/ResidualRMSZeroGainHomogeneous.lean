import SkipsLean.OneBlock.ResidualRMSZeroRescaleGeneric
import SkipsLean.OneBlock.ResidualRMSZeroReGLUGeneric
import SkipsLean.OneBlock.SkiplessHomogeneousRMSZero
import SkipsLean.OneBlock.SkiplessHomogeneousGatedRMSZero

/-!
# One ReLU, ReLU² or ReGLU block under pre-RMSNorm with `ε = 0`: the gain of the skip

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`, and the skipless
network at most `P − d_model² − d_model (d_model − 1)/2 − 1 − s`, with equality for ReLU and ReLU²
blocks. So the skip raises the functional dimension by at least `d_model²`, and by exactly
`d_model²` for ReLU and ReLU² blocks."

Here the sentence "So the skip raises the functional dimension by at least `d_model²`", for the
three kinds of block, from the value for the residual network
(`OneBlock/ResidualRMSZeroRescaleGeneric.lean`, `OneBlock/ResidualRMSZeroReGLUGeneric.lean`) and
the bound for the skipless network (`OneBlock/SkiplessHomogeneousRMSZero.lean`,
`OneBlock/SkiplessHomogeneousGatedRMSZero.lean`).

Both sides are Lean's `funDim` (all inputs; the derivative is `0` where the output is not
differentiable). For the residual network it is the paper's functional dimension (a batch of the
paper's inputs has the same rank); for the skipless network it is at least the paper's. So the
inequality here gives the paper's sentence for the paper's functional dimensions. Not here: "by
exactly `d_model²` for ReLU and ReLU² blocks", which needs the equality for the skipless network.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Theorem B.1 (iv) of the skips paper, "the skip raises the functional dimension by at least
`d_model²`", for one ReLU block:** for `ε = 0`, `d_in, d_out ≥ d ≥ 2` and a block of at least `d`
hidden units, at almost every parameter `funDim` of the residual network exceeds `funDim` of the
skipless network by at least `d²`. -/
theorem ae_funDim_skipless_add_le_relu_oneBlock_residual_rmsNorm_zero
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ + Fintype.card d ^ 2
      ≤ funDim (Arch.mlp relu (rmsNorm 0) hid) 1 θ := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have : Nonempty (hid 0) := Fintype.card_pos_iff.1 (by have := hhid 0; omega)
  -- `fd_1 + (d(d−1)/2 + 1) + s = P` with the skip, `fd_0 + d² + (d(d−1)/2 + 1) + s ≤ P` without
  filter_upwards [ae_funDim_relu_oneBlock_residual_rmsNorm_zero μ hd hdIn hdOut,
    ae_funDim_add_le_skipless_relu_oneBlock_rmsNorm_zero μ hdIn hhid] with θ h1 h0
  omega

/-- **The same for one ReLU² block.** -/
theorem ae_funDim_skipless_add_le_reluSq_oneBlock_residual_rmsNorm_zero
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ + Fintype.card d ^ 2
      ≤ funDim (Arch.mlp reluSq (rmsNorm 0) hid) 1 θ := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have : Nonempty (hid 0) := Fintype.card_pos_iff.1 (by have := hhid 0; omega)
  filter_upwards [ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero μ hd hdIn hdOut,
    ae_funDim_add_le_skipless_reluSq_oneBlock_rmsNorm_zero μ hdIn hhid] with θ h1 h0
  omega

/-- **The same for one ReGLU block** (`s = 2 d_hidden`). -/
theorem ae_funDim_skipless_add_le_reglu_oneBlock_residual_rmsNorm_zero
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm 0) hid) 0 θ + Fintype.card d ^ 2
      ≤ funDim (Arch.gated relu (rmsNorm 0) hid) 1 θ := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have : Nonempty (hid 0) := Fintype.card_pos_iff.1 (by have := hhid 0; omega)
  filter_upwards [ae_funDim_reglu_oneBlock_residual_rmsNorm_zero μ hd hdIn hdOut,
    ae_funDim_add_le_skipless_reglu_oneBlock_rmsNorm_zero μ hdIn hhid] with θ h1 h0
  omega

end Skips
