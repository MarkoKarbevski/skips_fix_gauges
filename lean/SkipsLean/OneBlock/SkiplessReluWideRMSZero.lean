import SkipsLean.OneBlock.SkiplessHomogeneousRMSZeroEqAt
import SkipsLean.OneBlock.UnitsGeneralPosition

/-!
# One skipless ReLU block of width at least `d` under pre-RMSNorm with `ε = 0`: the equality

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`, and the skipless
network at most `P − d_model² − d_model (d_model − 1)/2 − 1 − s`, with equality for ReLU and ReLU²
blocks. So the skip raises the functional dimension by at least `d_model²`, and by exactly
`d_model²` for ReLU and ReLU² blocks."

Here "with equality" and "by exactly `d_model²`" **for a ReLU block of width at least `d_model`**
(the file `OneBlock/SkiplessHomogeneousRMSZeroEq.lean` has width exactly `d_model`, for ReLU and
ReLU²):

* at almost every parameter of a block of width at least `d ≥ 2` the hidden units are in general
  position (`UnitsGeneralPosition`, `OneBlock/UnitsGeneralPosition.lean`);
* then the statements at one parameter (`OneBlock/SkiplessHomogeneousRMSZeroEqAt.lean`) apply.

The functional dimension: the value of Lean's `funDim`, and a finite batch of the paper's inputs
(no normalized row vanishes, no hidden unit at its kink) with this rank; the two together are the
paper's statement. Not stated: ReLU² blocks wider than `d_model`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **The conditions "for generic parameters" of the proof of Theorem B.1 (iv), "The skipless
network: equality":** for one MLP block with at least `d ≥ 2` hidden units, at almost every
parameter the hidden units are in general position. -/
theorem ae_unitsGeneralPosition {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, UnitsGeneralPosition (θ.read 0) (θ.write 0) := by
  sorry

omit [Nonempty T] in
/-- Helper: at almost every parameter `E` and `D` have rank `d` (`d_in, d_out ≥ d`, width at
least `d`). -/
private theorem ae_rank_E_D_srw {σ : ℝ → ℝ}
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

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, "with equality", for one ReLU
block of width at least `d`:** for `ε = 0`, `d_in, d_out ≥ d ≥ 2` and a block of at least `d`
hidden units, at almost every parameter `funDim = P − d² − d(d−1)/2 − 1 − s`. -/
theorem ae_funDim_relu_oneBlock_skipless_rmsNorm_zero_of_le
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_D_srw μ hdIn hdOut hcard, ae_unitsGeneralPosition μ hd hcard] with θ hθ hG
  obtain ⟨hR, hW, hc⟩ := rank_of_unitsGeneralPosition hd hcard hG
  exact funDim_mlp_oneBlock_rescale_skipless_rmsNorm_zero_of_unitsParallelAt
    (fun _ hz => hasDerivAt_relu hz) relu_homogeneous θ hd hθ.1 hθ.2 hR hW hc
    (relu_unitsParallelAt_of_unitsGeneralPosition θ.E hd hcard hθ.1 hG)
    (exists_open_relu_of_unitsGeneralPosition θ.E hd hcard hθ.1 hG)

/-- **The same in the paper's own sense:** at almost every parameter a finite batch of inputs at
which no normalized row vanishes and no hidden unit sits at its kink, on which the Jacobian has
the rank `P − d² − d(d−1)/2 − 1 − s`. -/
theorem ae_exists_jacobianRank_relu_oneBlock_skipless_rmsNorm_zero_of_le
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ skiplessZeroDomain (Arch.mlp relu (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp relu (rmsNorm 0) hid) 0 X θ
          + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
            + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_D_srw μ hdIn hdOut hcard, ae_unitsGeneralPosition μ hd hcard] with θ hθ hG
  obtain ⟨hR, hW, hc⟩ := rank_of_unitsGeneralPosition hd hcard hG
  exact exists_jacobianRank_mlp_oneBlock_rescale_skipless_rmsNorm_zero_of_unitsParallelAt
    (fun _ hz => hasDerivAt_relu hz) relu_homogeneous θ hd hθ.1 hθ.2 hR hW hc
    (relu_unitsParallelAt_of_unitsGeneralPosition θ.E hd hcard hθ.1 hG)
    (exists_open_relu_of_unitsGeneralPosition θ.E hd hcard hθ.1 hG)

/-- **Theorem B.1 (iv) of the skips paper, "by exactly `d_model²` for ReLU and ReLU² blocks", for
one ReLU block of width at least `d`:** at almost every parameter `funDim` of the residual
network is `funDim` of the skipless network plus `d²`. -/
theorem ae_funDim_relu_oneBlock_residual_rmsNorm_zero_eq_add_of_le
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 1 θ
      = funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ + Fintype.card d ^ 2 := by
  have : Nonempty (hid 0) := Fintype.card_pos_iff.1 (by omega)
  filter_upwards [ae_funDim_relu_oneBlock_residual_rmsNorm_zero μ hd hdIn hdOut,
    ae_funDim_relu_oneBlock_skipless_rmsNorm_zero_of_le μ hd hdIn hdOut hcard] with θ h1 h0
  omega

end Skips
