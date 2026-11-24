import SkipsLean.OneBlock.LearnedSkipRMSZeroSteps
import SkipsLean.OneBlock.UnitsRescaleSphere
import SkipsLean.OneBlock.LearnedSkipRMSZeroRescaleBound

/-!
# One ReLU or ReLU² block with a full learned skip under pre-RMSNorm with `ε = 0`: the equality

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. […] For `ε = 0` it exceeds that of the residual
network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and
ReGLU blocks."

Its proof, "The case `ε = 0`": "Steps 3 and 4 run with `Y + c I` in place of `Y` and with
`X_s = c_0 I + X_0`, where `X_0` has trace zero; the scalings, with the derivatives `c_0` at `h_0`
and `c` at `h_1`, join the rotations in `η^rot`; and (17) holds with `X_0` in place of `X_s` on
the sphere. […] For ReLU, ReLU² and ReGLU, both sides of (17) are positively homogeneous, of
degrees `k` and `k + 2`, so `‖n‖² ∂_ψ B(n) = k d_model q(n) B(n)` for all `n ≠ 0`. […] Since
`‖n‖²` has no real linear factor, it divides `q(n)`, so `X_0` is a multiple of `I`, and `X_0 = 0`
because its trace vanishes. Then Step 5 gives equality."

Steps 1 to 3 (`OneBlock/LearnedSkipRMSZeroSteps.lean`) give `D_θ g η = g(x) (Y + c I)` only at
the inputs at which `x E A` and `g(x)` are linearly independent ("The constant terms then give
`μ = c` wherever `w E A` and `g(w)` are linearly independent"). To pass to all inputs off the
kinks the proof needs a condition on the parameters that the paper does not state, as for the
residual network (`TurnsActiveRows`, `OneBlock/ResidualRMSZeroRescale.lean`): the rows `u` at
which `u A` and the output of the block are linearly independent are dense among the rows with an
active unit (`TurnsActiveRowsSkip`). It holds at almost every weights and skip
(`OneBlock/LearnedSkipRMSZeroRescaleGeneric.lean`).

Here, for one MLP block with a positively homogeneous activation and a full learned skip (the twin
for `ε = 0` of `OneBlock/LearnedSkipRescale.lean`, and for a learned skip of
`OneBlock/ResidualRMSZeroRescale.lean`), at one parameter under the conditions of the proof:

* the directions of the weights and the skip that are flat at the paper's inputs (no normalized
  row vanishes, no hidden unit at its kink) are a rotation and a scaling of `h_0`, a rotation and
  a scaling of `h_1`, and a rescaling of the hidden units;
* the value of Lean's `funDimLearned`: `P + d² − (d(d−1) + 2) − s`, with `s` the number of hidden
  units and `P` the number of weights without the skip (the bound "at most" is
  `funDimLearned_add_le_rmsNorm_zero'`, `OneBlock/LearnedSkipRMSZeroRescaleBound.lean`);
* a finite batch of the paper's inputs on which the Jacobian in the weights and the skip has
  this rank.

The step "`X_0` is a multiple of `I`", with Lemma B.3, is the hypothesis `UnitsRescaleSphere`
(`OneBlock/UnitsRescaleSphere.lean`; ReLU and ReLU²). No width of the block is asked. Numeric
check of the values: `learned_skip_zero_relu_check_2026-11-24.py`. Not stated: ReGLU blocks; the
upper triangular skip.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **The block turns a dense set of the active rows, for the skip `S`:** every row `v` with no
hidden unit at its kink (no entry of `v W_read` is zero) and with some active unit (`σ` of an
entry of `v W_read` is not zero) is a limit of rows `u` such that `u S` and the output
`σ(u W_read) W_write` of the block at `u` are linearly independent. For `S = 1` this is
`TurnsActiveRows`. -/
def TurnsActiveRowsSkip (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (S : Matrix d d ℝ) : Prop :=
  ∀ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) → (∃ i, σ ((v ᵥ* θ.read 0) i) ≠ 0) →
    v ∈ closure {u : d → ℝ |
      LinearIndependent ℝ ![u ᵥ* S, vanillaBlock σ (θ.read 0) (θ.write 0) u]}

/-- **Proof of Theorem B.1 (iii) of the skips paper, "The case `ε = 0`", the flat directions for
one MLP block with a positively homogeneous activation and a full learned skip:** under the
conditions `OneBlockGenericRMS`, for `d ≥ 2`, an invertible skip `A = R 0`, a block that turns a
dense set of the active rows and one turned row off the kinks, a direction `(η, η_A)` of the
weights and the skip that is flat at every input at which no normalized row vanishes and no
hidden unit sits at its kink is the sum of the rotations of `h_0` and `h_1` (antisymmetric `X₀`,
`Y`), the scalings of `h_0` and `h_1` (numbers `c₀`, `c₁`) and a rescaling of the hidden units:
`η = (E (X₀ + c₀ I), −X₀ W_read + W_read diag(α), W_write (Y + c₁ I) − k diag(α) W_write, −Y D)`
and `η_A = A (Y + c₁ I) − (X₀ + c₀ I) A`. -/
theorem flatSkipsOn_noKink_le_mlp_rescale_learned_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescaleSphere σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det)
    (hturn : TurnsActiveRowsSkip θ (R 0))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* R 0, vanillaBlock σ (θ.read 0) (θ.write 0) v])
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (ρ : Fin 1 → Matrix d d ℝ)
    (hη : (η, ρ) ∈ flatSkipsOn (Arch.mlp σ (rmsNorm 0) hid)
      (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
      (learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ R ∩ noKinkRMS θ)) :
    ∃ (X₀ Y : Matrix d d ℝ) (c₀ c₁ : ℝ) (α : ∀ ℓ, hid ℓ → ℝ), X₀ᵀ = -X₀ ∧ Yᵀ = -Y ∧
      η = cobDir θ ![X₀, Y] + scaleDir θ ![c₀, c₁] + rescaleDirMlp k θ α ∧
      ρ 0 = R 0 * (Y + c₁ • 1) - (X₀ + c₀ • 1) * R 0 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", for one MLP block with a
positively homogeneous activation and a full learned skip, at one parameter:** under the
conditions of the proof, `funDimLearned = P + d² − (d(d−1) + 2) − s`, with `s` the number of
hidden units and `P` the number of weights without the skip. -/
theorem funDimLearned_mlp_oneBlock_rescale_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescaleSphere σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det)
    (hturn : TurnsActiveRowsSkip θ (R 0))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* R 0, vanillaBlock σ (θ.read 0) (θ.write 0) v]) :
    funDimLearned (Arch.mlp σ (rmsNorm 0) hid) (θ, R)
        + ((Fintype.card d * (Fintype.card d - 1) + 2) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", in the paper's own
sense, for one MLP block with a positively homogeneous activation and a full learned skip, at
one parameter:** a finite batch of inputs at which no normalized row vanishes and no hidden unit
sits at its kink, on which the Jacobian in the weights and the skip has the rank
`P + d² − (d(d−1) + 2) − s`. -/
theorem exists_jacobianRankSkips_mlp_oneBlock_rescale_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescaleSphere σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det)
    (hturn : TurnsActiveRowsSkip θ (R 0))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* R 0, vanillaBlock σ (θ.read 0) (θ.write 0) v]) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ R ∩ noKinkRMS θ) ∧
      jacobianRankSkips (Arch.mlp σ (rmsNorm 0) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X (θ, R)
          + ((Fintype.card d * (Fintype.card d - 1) + 2) + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  sorry

end Skips
