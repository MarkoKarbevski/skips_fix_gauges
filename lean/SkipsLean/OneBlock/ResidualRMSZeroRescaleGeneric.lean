import SkipsLean.OneBlock.ResidualRMSZeroRescale

/-!
# One residual ReLU or ReLU² block under pre-RMSNorm with `ε = 0`: generic parameters

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`".

`OneBlock/ResidualRMSZeroRescale.lean` has this value at one parameter under the conditions of the
proof, among them the condition that the paper does not state: the block turns a dense set of the
rows at which some hidden unit is active (`TurnsActiveRows`). Here: this condition, and "the block
turns some row off the kinks", at almost every parameter for ReLU and ReLU² blocks with `d ≥ 2`
(for every nonempty set `S` of hidden units, the map `v ↦ ∑_{i ∈ S} (v c_i)^k a_i` is at almost
every parameter not parallel to `v` for all `v`, and a nonzero polynomial does not vanish on an
open set); and Theorem B.1 (iv) for the residual network at almost every parameter, as the value
of Lean's `funDim` and as a batch of the paper's inputs with this rank. No width of the block is
asked; for the batch and the value the block has at least one hidden unit.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **A ReLU block turns a dense set of the active rows at almost every parameter,** for
`d ≥ 2`. -/
theorem ae_turnsActiveRows_relu
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, TurnsActiveRows θ := by
  sorry

/-- **A ReLU² block turns a dense set of the active rows at almost every parameter,** for
`d ≥ 2`. -/
theorem ae_turnsActiveRows_reluSq
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, TurnsActiveRows θ := by
  sorry

/-- **A ReLU block with a hidden unit turns some row off the kinks at almost every parameter,**
for `d ≥ 2`. -/
theorem ae_exists_turned_row_relu [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v, vanillaBlock relu (θ.read 0) (θ.write 0) v] := by
  sorry

/-- **A ReLU² block with a hidden unit turns some row off the kinks at almost every parameter,**
for `d ≥ 2`. -/
theorem ae_exists_turned_row_reluSq [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v, vanillaBlock reluSq (θ.read 0) (θ.write 0) v] := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the residual network, for one ReLU block with a hidden
unit:** with `d_in, d_out ≥ d ≥ 2` and `ε = 0`, at almost every parameter
`funDim = P − d(d−1)/2 − 1 − s`. -/
theorem ae_funDim_relu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the residual network, in the paper's own sense, for
one ReLU block with a hidden unit:** at almost every parameter, a finite batch of inputs at which
no normalized row vanishes and no hidden unit sits at its kink, on which the Jacobian has the rank
`P − d(d−1)/2 − 1 − s`. -/
theorem ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ residualZeroDomain (Arch.mlp relu (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp relu (rmsNorm 0) hid) 1 X θ
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the residual network, for one ReLU² block with a
hidden unit:** with `d_in, d_out ≥ d ≥ 2` and `ε = 0`, at almost every parameter
`funDim = P − d(d−1)/2 − 1 − s`. -/
theorem ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the residual network, in the paper's own sense, for
one ReLU² block with a hidden unit:** at almost every parameter, a finite batch of inputs at which
no normalized row vanishes and no hidden unit sits at its kink, on which the Jacobian has the rank
`P − d(d−1)/2 − 1 − s`. -/
theorem ae_exists_jacobianRank_reluSq_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ residualZeroDomain (Arch.mlp reluSq (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp reluSq (rmsNorm 0) hid) 1 X θ
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  sorry

end Skips
