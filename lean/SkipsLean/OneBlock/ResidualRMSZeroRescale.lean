import SkipsLean.OneBlock.ResidualRMSZeroStepsOn
import SkipsLean.OneBlock.ResidualRMSRescale
import SkipsLean.Residual.UpperBoundRescaleRMSNormZero
import SkipsLean.Absorb.Block

/-!
# One residual ReLU or ReLU² block under pre-RMSNorm with `ε = 0`: the functional dimension

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`".

Its proof, "The residual network": "The case `ε = 0` of part (iii), with `A = I`, shows that a
flat direction is the sum of a direction of the rotation and scaling of all hidden states and a
direction `ψ` of the weights of the block along which `B` has derivative zero on the sphere of
radius `√d_model`. This derivative is positively homogeneous of degree `k` in `n`, so it vanishes
for all `n ≠ 0`, and Lemma B.3, with `E` and `D` replaced by the identity and `M = 0`, makes `ψ` a
rescaling of the units. So `dim K(θ) = d_model (d_model − 1)/2 + 1 + s`."

The case `ε = 0` of part (iii) gives the zero derivative only at the inputs `w` at which `w E` and
`g(w)` are linearly independent ("The constant terms then give `μ = c` wherever `w E A` and `g(w)`
are linearly independent"; `OneBlock/ResidualRMSZeroStepsOn.lean`). To pass to all inputs off the
kinks, the proof needs one more condition on the parameters, which the paper does not state: the
block turns a dense set of the rows at which some hidden unit is active (`TurnsActiveRows`). At a
row where no unit is active the derivative of the block along any direction is zero; elsewhere
the derivative is continuous off the kinks and vanishes on a dense set. The condition holds at
almost every parameter for ReLU and ReLU² blocks (`OneBlock/ResidualRMSZeroRescaleGeneric.lean`).

Here, for one MLP block with a positively homogeneous activation (twin of
`OneBlock/ResidualRMSRescale.lean` for `ε > 0`), at one parameter under the conditions of the
proof: the flat directions at the paper's inputs (no normalized row vanishes, no hidden unit at
its kink) are a rotation and a scaling of both hidden states plus a rescaling of the hidden units;
the value of Lean's `funDim`; a finite batch of the paper's inputs on which the Jacobian has this
rank. No width of the block is asked.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **The block turns a dense set of the rows at which some hidden unit is active:** every row
`v` with no hidden unit at its kink (no entry of `v W_read` is zero) and with some active unit
(`σ` of an entry of `v W_read` is not zero) is a limit of rows `u` such that `u` and the output
`σ(u W_read) W_write` of the block at `u` are linearly independent. -/
def TurnsActiveRows (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) : Prop :=
  ∀ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) → (∃ i, σ ((v ᵥ* θ.read 0) i) ≠ 0) →
    v ∈ closure {u : d → ℝ |
      LinearIndependent ℝ ![u, vanillaBlock σ (θ.read 0) (θ.write 0) u]}

/-- **Proof of Theorem B.1 (iv) of the skips paper, "The residual network", for ReLU-type MLP
blocks:** let `ε = 0`, `d ≥ 2`, let `σ` be differentiable off `0` and positively homogeneous of
degree `k`, with Lemma B.3 in the form `UnitsRescale`; under the conditions `OneBlockGenericRMS`,
if the block turns a dense set of the active rows and turns some row off the kinks, then a
direction that is flat at every input at which no normalized row vanishes and no hidden unit sits
at its kink is the direction of a rotation and of a scaling shared by `h_0` and `h_1`, plus a
rescaling of the hidden units. -/
theorem flatOn_noKink_le_mlp_rescale_residual_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d) (hturn : TurnsActiveRows θ)
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v, vanillaBlock σ (θ.read 0) (θ.write 0) v])
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.mlp σ (rmsNorm 0) hid) 1 θ
      (residualZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ)) :
    ∃ (Y : Matrix d d ℝ) (c : ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
      η = cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c) + rescaleDirMlp k θ α := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the residual network, for ReLU-type MLP blocks, at one
parameter:** under the conditions of
`flatOn_noKink_le_mlp_rescale_residual_rmsNorm_zero`, `funDim = P − (d(d−1)/2 + 1) − s`, with `s`
the number of hidden units. -/
theorem funDim_mlp_oneBlock_rescale_residual_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d) (hturn : TurnsActiveRows θ)
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v, vanillaBlock σ (θ.read 0) (θ.write 0) v]) :
    funDim (Arch.mlp σ (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the residual network, in the paper's own sense, for
ReLU-type MLP blocks, at one parameter:** under the same conditions, a finite batch of inputs at
which no normalized row vanishes and no hidden unit sits at its kink, on which the Jacobian has
the rank `P − (d(d−1)/2 + 1) − s`. -/
theorem exists_jacobianRank_mlp_oneBlock_rescale_residual_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d) (hturn : TurnsActiveRows θ)
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v, vanillaBlock σ (θ.read 0) (θ.write 0) v]) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ residualZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp σ (rmsNorm 0) hid) 1 X θ
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

end Skips
