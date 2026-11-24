import SkipsLean.OneBlock.LearnedSkipRMSZeroBound
import SkipsLean.Dimension.UpperBoundTransformerRescale
import SkipsLean.OneBlock.ResidualRMSZeroRescaleGeneric
import SkipsLean.OneBlock.ResidualRMSZeroReGLUGeneric

/-!
# One ReLU, ReLU² or ReGLU block with a learned skip under pre-RMSNorm with `ε = 0`: "at most"

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. […] For `ε = 0` it exceeds that of the residual
network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and
ReGLU blocks." Its proof, "The case `ε = 0`": "the scalings of `h_0` and `h_1` are symmetries
too, since `N_ε(c h) = N_ε(h)` for `c > 0`. […] For the learned skip, `η^rot` and `K_B` are flat,
which gives at least `d_model (d_model − 1) + 2` […] dimensions besides `K_B`".

Here the half "at most" for ReLU, ReLU² and ReGLU blocks and a full learned skip:

* the bound for one block with a full learned skip and any space `U` of directions of symmetries
  inside the block, for `ε = 0`: the rotation and the scaling of `h_0` and of `h_1` and `U` are
  flat at every input and independent, so `fd ≤ P + d² − (d(d−1) + 2) − dim U` (the twin for
  `ε = 0` of `funDimLearned_add_le_rmsNorm'`, `OneBlock/LearnedSkipOn.lean`, which counts the
  rotations only);
* with `U` the rescalings of the hidden units (`s` dimensions) and the value for the residual
  network (`OneBlock/ResidualRMSZeroRescaleGeneric.lean`,
  `OneBlock/ResidualRMSZeroReGLUGeneric.lean`): at almost every weights and skip `(θ, A)` the
  functional dimension with the learned skip `A` exceeds that of the residual network with the
  weights `θ` by at most `d(d+1)/2 − 1`.

The functional dimensions are Lean's `funDimLearned` and `funDim` (all inputs). For the residual
network `funDim` is the paper's functional dimension (a batch of the paper's inputs has the same
rank) and for the network with the learned skip `funDimLearned` is at least the paper's, so the
inequality gives the paper's "at most". Not stated: the equality; the upper triangular skip.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **Proof of Theorem B.1 (iii) of the skips paper, "The case `ε = 0`", the bound for the learned
skip with symmetries inside the block:** for one block with a full learned skip `A` that is
invertible, under pre-RMSNorm with `ε = 0`, if `E` has rank `d ≥ 1` and `U` is a space spanned by
directions of symmetries inside the block, then `fd + (d(d−1) + 2) + dim U ≤ P + d²`, where `P`
counts the weights without the skip. -/
theorem funDimLearned_add_le_rmsNorm_zero' {A : Arch T d 1} [Nonempty d] (hA : A.χ = rmsNorm 0)
    (p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
    (hE : p.1.E.rank = Fintype.card d) (hR : IsUnit (p.2 0).det)
    (U : Submodule ℝ (Params A dIn dOut))
    (hU : U ≤ Submodule.span ℝ {η | InsideBlocks A p.1 η}) :
    funDimLearned A p + ((Fintype.card d * (Fintype.card d - 1) + 2) + Module.finrank ℝ U)
      ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
  sorry

variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one ReLU block:** for `d_in,
d_out ≥ d ≥ 2` and a block with at least one hidden unit, at almost every weights and full learned
skip `(θ, A)` the functional dimension exceeds that of the residual network with the weights `θ` by
at most `d(d+1)/2 − 1`. -/
theorem ae_funDimLearned_le_residual_add_relu_oneBlock_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp relu (rmsNorm 0) hid) p
      ≤ funDim (Arch.mlp relu (rmsNorm 0) hid) 1 p.1
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one ReLU² block:** for
`d_in, d_out ≥ d ≥ 2` and a block with at least one hidden unit, at almost every weights and full
learned skip `(θ, A)` the functional dimension exceeds that of the residual network with the
weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimLearned_le_residual_add_reluSq_oneBlock_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp reluSq (rmsNorm 0) hid) p
      ≤ funDim (Arch.mlp reluSq (rmsNorm 0) hid) 1 p.1
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one ReGLU block:** for
`d_in, d_out ≥ d ≥ 2` and a block with at least one hidden unit, at almost every weights and full
learned skip `(θ, A)` the functional dimension exceeds that of the residual network with the
weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimLearned_le_residual_add_reglu_oneBlock_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.gated relu (rmsNorm 0) hid) p
      ≤ funDim (Arch.gated relu (rmsNorm 0) hid) 1 p.1
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  sorry

end Skips
