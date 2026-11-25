import SkipsLean.OneBlock.SkiplessReluSqWideRMSZero
import SkipsLean.OneBlock.ResidualRMSZeroRescaleGeneric
import SkipsLean.OneBlock.ResidualRMSZeroReGLUGeneric

/-!
# One block under pre-RMSNorm with `ε = 0`: the redundancy is that of the symmetries

Paper (skips paper), Theorem B.1 (iv), last sentence: "The redundancy is then that of the
symmetries: besides those inside the block, `GL(d_model)` at `h_0` and `CO(d_model)` at `h_1`
without the skip, and one `CO(d_model)` with it."

The statements at one parameter, under the conditions "for generic parameters" of the proof, are
`flatOn_le_mlp_rescale_skipless_rmsNorm_zero_of_unitsParallelAt`
(`OneBlock/SkiplessHomogeneousRMSZeroEqAt.lean`),
`flatOn_noKink_le_mlp_rescale_residual_rmsNorm_zero` (`OneBlock/ResidualRMSZeroRescale.lean`) and
`flatOn_noKinkGate_le_reglu_residual_rmsNorm_zero` (`OneBlock/ResidualRMSZeroReGLU.lean`). Here
the sentence at almost every parameter, for the blocks for which the theorem has equality:

* without the skip, for a ReLU or ReLU² block of width at least `d`: a direction that is flat at
  the paper's inputs (no normalized row vanishes, no hidden unit at its kink) is the direction of
  a change of basis at `h_0` (`GL(d)`), of a rotation and a scaling at `h_1` (`CO(d)`), plus a
  rescaling of the hidden units (the symmetries inside the block);
* with the skip, for a ReLU, ReLU² or ReGLU block of any width with a hidden unit: such a
  direction is the direction of a rotation and a scaling shared by `h_0` and `h_1` (one `CO(d)`),
  plus the rescalings inside the block.

That the directions of these symmetries are flat is the content of the upper bounds on the
functional dimension. For a skipless ReGLU block the theorem claims the bound only, and nothing is
stated here.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

omit [Nonempty T] in
/-- Helper: at almost every parameter `E` and `D` have rank `d` (`d_in, d_out ≥ d`, width at
least `d`); a copy of `ae_rank_E_D_srw`. -/
private theorem ae_rank_E_D_rsz {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d ∧ θ.D.rank = Fintype.card d := by
  obtain ⟨ρD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  filter_upwards [ae_rank_E_write μ hdIn
      (fun ℓ => by obtain rfl := Subsingleton.elim ℓ 0; exact hcard),
    ae_isUnit_det_submatrix μ] with θ h1 h2
  exact ⟨h1.1, rank_eq_card_of_isUnit_det θ.D ρD (h2.2.1 ρD)⟩

/-- **Theorem B.1 (iv), "The redundancy is then that of the symmetries: besides those inside the
block, `GL(d_model)` at `h_0` and `CO(d_model)` at `h_1` without the skip", for one ReLU block of
width at least `d`:** for `ε = 0` and `d_in, d_out ≥ d ≥ 2`, at almost every parameter a direction
that is flat at every input at which no normalized row vanishes and no hidden unit sits at its
kink is the direction of a change of basis at `h_0`, of a rotation and a scaling at `h_1`, plus a
rescaling of the hidden units. -/
theorem ae_flatOn_le_relu_oneBlock_skipless_rmsNorm_zero_of_le
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∀ η ∈ flatOn (Arch.mlp relu (rmsNorm 0) hid) 0 θ
        (skiplessZeroDomain (Arch.mlp relu (rmsNorm 0) hid) θ ∩ noKinkRMS θ),
      ∃ (X Y : Matrix d d ℝ) (c : ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
        η = cobDir θ ![X, Y] + c • scaleDir θ ![0, 1] + rescaleDirMlp 1 θ α := by
  filter_upwards [ae_rank_E_D_rsz μ hdIn hdOut hcard,
    ae_unitsGeneralPosition μ hd hcard] with θ hθ hG η hη
  obtain ⟨hR, hW, -⟩ := rank_of_unitsGeneralPosition hd hcard hG
  exact flatOn_le_mlp_rescale_skipless_rmsNorm_zero_of_unitsParallelAt
    (fun _ hz => hasDerivAt_relu hz) relu_homogeneous θ hd hθ.1 hθ.2 hR hW
    (relu_unitsParallelAt_of_unitsGeneralPosition θ.E hd hcard hθ.1 hG)
    (exists_open_relu_of_unitsGeneralPosition θ.E hd hcard hθ.1 hG) η hη

/-- **The same for one ReLU² block of width at least `d`.** -/
theorem ae_flatOn_le_reluSq_oneBlock_skipless_rmsNorm_zero_of_le
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∀ η ∈ flatOn (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ
        (skiplessZeroDomain (Arch.mlp reluSq (rmsNorm 0) hid) θ ∩ noKinkRMS θ),
      ∃ (X Y : Matrix d d ℝ) (c : ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
        η = cobDir θ ![X, Y] + c • scaleDir θ ![0, 1] + rescaleDirMlp 2 θ α := by
  filter_upwards [ae_rank_E_D_rsz μ hdIn hdOut hcard,
    ae_unitsGeneralPositionSq μ hd hcard] with θ hθ hG η hη
  obtain ⟨hR, hW, -⟩ := rank_of_unitsGeneralPositionSq hd hG
  exact flatOn_le_mlp_rescale_skipless_rmsNorm_zero_of_unitsParallelAt
    (fun z _ => hasDerivAt_reluSq z) reluSq_homogeneous θ hd hθ.1 hθ.2 hR hW
    (reluSq_unitsParallelAt_of_unitsGeneralPositionSq θ.E hθ.1 hG)
    (exists_open_reluSq_of_unitsGeneralPositionSq θ.E hθ.1 hG) η hη

/-- **Theorem B.1 (iv), "The redundancy is then that of the symmetries: besides those inside the
block, […] one `CO(d_model)` with it", for one ReLU block with a hidden unit:** for `ε = 0` and
`d_in, d_out ≥ d ≥ 2`, at almost every parameter a direction of the residual network that is flat
at every input at which no normalized row vanishes and no hidden unit sits at its kink is the
direction of a rotation and of a scaling shared by `h_0` and `h_1`, plus a rescaling of the hidden
units. -/
theorem ae_flatOn_le_relu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ η ∈ flatOn (Arch.mlp relu (rmsNorm 0) hid) 1 θ
        (residualZeroDomain (Arch.mlp relu (rmsNorm 0) hid) θ ∩ noKinkRMS θ),
      ∃ (Y : Matrix d d ℝ) (c : ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
        η = cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c) + rescaleDirMlp 1 θ α := by
  filter_upwards [ae_oneBlockGenericRMS μ hd hdIn hdOut, ae_turnsActiveRows_relu μ hd,
    ae_exists_turned_row_relu μ hd] with θ hθ hturn hw η hη
  exact flatOn_noKink_le_mlp_rescale_residual_rmsNorm_zero (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous (relu_unitsRescale d d (hid 0)) θ hθ hd hturn hw η hη

/-- **The same for one ReLU² block with a hidden unit.** -/
theorem ae_flatOn_le_reluSq_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ η ∈ flatOn (Arch.mlp reluSq (rmsNorm 0) hid) 1 θ
        (residualZeroDomain (Arch.mlp reluSq (rmsNorm 0) hid) θ ∩ noKinkRMS θ),
      ∃ (Y : Matrix d d ℝ) (c : ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
        η = cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c) + rescaleDirMlp 2 θ α := by
  filter_upwards [ae_oneBlockGenericRMS μ hd hdIn hdOut, ae_turnsActiveRows_reluSq μ hd,
    ae_exists_turned_row_reluSq μ hd] with θ hθ hturn hw η hη
  exact flatOn_noKink_le_mlp_rescale_residual_rmsNorm_zero (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous (reluSq_unitsRescale d d (hid 0)) θ hθ hd hturn hw η hη

/-- **The same for one ReGLU block with a hidden unit:** at almost every parameter a direction of
the residual network that is flat at every input at which no normalized row vanishes and no gate
sits at its kink is the direction of a rotation and of a scaling shared by `h_0` and `h_1`, plus a
rescaling of the values and a rescaling of the gates of the hidden units. -/
theorem ae_flatOn_le_reglu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ η ∈ flatOn (Arch.gated relu (rmsNorm 0) hid) 1 θ
        (residualZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ ∩ noKinkGateRMS θ),
      ∃ (Y : Matrix d d ℝ) (c : ℝ) (α β : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
        η = cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c) + rescaleDir θ α
          + rescaleDirGate 1 θ β := by
  filter_upwards [ae_oneBlockGenericReGLURMS μ hd hdIn hdOut, ae_turnsActiveRowsGated_reglu μ hd,
    ae_exists_turned_row_reglu μ hd] with θ hθ hturn hw η hη
  exact flatOn_noKinkGate_le_reglu_residual_rmsNorm_zero θ hθ hd hturn hw η hη

end Skips
