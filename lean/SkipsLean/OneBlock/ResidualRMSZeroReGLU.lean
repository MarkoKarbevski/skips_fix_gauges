import SkipsLean.OneBlock.ResidualRMSZeroStepsOn
import SkipsLean.OneBlock.ResidualRMSReGLU
import SkipsLean.Residual.UpperBoundRescaleRMSNormZero
import SkipsLean.Absorb.Block

/-!
# One residual ReGLU block under pre-RMSNorm with `ε = 0`: the functional dimension

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`". For ReGLU
`s = 2 d_hidden`: one rescaling of the gate and one of the value for each hidden unit.

Its proof, "The residual network": "The case `ε = 0` of part (iii), with `A = I`, shows that a
flat direction is the sum of a direction of the rotation and scaling of all hidden states and a
direction `ψ` of the weights of the block along which `B` has derivative zero on the sphere of
radius `√d_model`. This derivative is positively homogeneous of degree `k` in `n`, so it vanishes
for all `n ≠ 0`, and Lemma B.3, with `E` and `D` replaced by the identity and `M = 0`, makes `ψ` a
rescaling of the units. So `dim K(θ) = d_model (d_model − 1)/2 + 1 + s`."

This file is the twin, for a ReGLU block, of `OneBlock/ResidualRMSZeroRescale.lean` (ReLU and
ReLU² blocks, `ε = 0`) and, for `ε = 0`, of `OneBlock/ResidualRMSReGLU.lean` (a ReGLU block,
`ε > 0`). As there, the case `ε = 0` of part (iii) gives the zero derivative only at the inputs
`w` at which `w E` and `g(w)` are linearly independent (`OneBlock/ResidualRMSZeroStepsOn.lean`),
and the step to all inputs off the kinks uses that the block turns a dense set of the rows at
which some gate is active (`TurnsActiveRowsGated`): at a row where no gate is active the
derivative of the block along any direction is zero; elsewhere the derivative is continuous off
the kinks of the gates and vanishes on a dense set. The condition holds at almost every parameter
(`OneBlock/ResidualRMSZeroReGLUGeneric.lean`).

Here, at one parameter under the conditions of the proof (`OneBlockGenericReGLURMS`, the two
conditions on turned rows): the flat directions at the paper's inputs (no normalized row
vanishes, no gate at its kink) are a rotation and a scaling of both hidden states plus a rescaling
of the values and a rescaling of the gates of the hidden units; the value of Lean's `funDim`; a
finite batch of the paper's inputs on which the Jacobian has this rank. No width of the block is
asked.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ}

/-- **A gated block turns a dense set of the rows at which some gate is active:** every row `v`
with no gate at its kink (no entry of the gate columns of `v W_read` is zero) and with some
active gate (`σ` of such an entry is not zero) is a limit of rows `u` such that `u` and the
output of the block at `u` are linearly independent. The output at `u` is
`gatedBlock σ W_gate W_value W_write u`, with `W_gate` and `W_value` the gate columns and the
value columns of `W_read`. -/
def TurnsActiveRowsGated
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) : Prop :=
  ∀ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) →
    (∃ i, σ ((v ᵥ* θ.read 0) (Sum.inl i)) ≠ 0) →
    v ∈ closure {u : d → ℝ | LinearIndependent ℝ ![u, gatedBlock σ
      ((θ.read 0).submatrix id Sum.inl) ((θ.read 0).submatrix id Sum.inr) (θ.write 0) u]}

/-- **Proof of Theorem B.1 (iv) of the skips paper, "The residual network", for a ReGLU block:**
let `ε = 0` and `d ≥ 2`; under the conditions `OneBlockGenericReGLURMS`, if the block turns a
dense set of the rows with an active gate and turns some row off the kinks of the gates, then a
direction that is flat at every input at which no normalized row vanishes and no gate sits at its
kink is the direction of a rotation and of a scaling shared by `h_0` and `h_1`, plus a rescaling
of the values and a rescaling of the gates of the hidden units. -/
theorem flatOn_noKinkGate_le_reglu_residual_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d) (hturn : TurnsActiveRowsGated θ)
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v])
    (η : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.gated relu (rmsNorm 0) hid) 1 θ
      (residualZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ ∩ noKinkGateRMS θ)) :
    ∃ (Y : Matrix d d ℝ) (c : ℝ) (α β : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
      η = cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c) + rescaleDir θ α
        + rescaleDirGate 1 θ β := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the residual network, for a ReGLU block, at one
parameter:** under the conditions of `flatOn_noKinkGate_le_reglu_residual_rmsNorm_zero`,
`funDim = P − (d(d−1)/2 + 1) − s`, with `s` twice the number of hidden units. -/
theorem funDim_reglu_oneBlock_residual_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d) (hturn : TurnsActiveRowsGated θ)
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v]) :
    funDim (Arch.gated relu (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the residual network, in the paper's own sense, for a
ReGLU block, at one parameter:** under the same conditions, a finite batch of inputs at which no
normalized row vanishes and no gate sits at its kink, on which the Jacobian has the rank
`P − (d(d−1)/2 + 1) − s`. -/
theorem exists_jacobianRank_reglu_oneBlock_residual_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d) (hturn : TurnsActiveRowsGated θ)
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v]) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ residualZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ ∩ noKinkGateRMS θ) ∧
      jacobianRank (Arch.gated relu (rmsNorm 0) hid) 1 X θ
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  sorry

end Skips
