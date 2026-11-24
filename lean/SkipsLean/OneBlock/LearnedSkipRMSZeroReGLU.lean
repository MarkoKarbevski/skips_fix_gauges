import SkipsLean.OneBlock.LearnedSkipRMSZeroSteps
import SkipsLean.OneBlock.UnitsRescaleSphereReGLU
import SkipsLean.OneBlock.LearnedSkipRMSZeroRescaleBound

/-!
# One ReGLU block with a full learned skip under pre-RMSNorm with `ε = 0`: the equality

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

The twin for a ReGLU block of `OneBlock/LearnedSkipRMSZeroRescale.lean` (ReLU and ReLU² blocks),
and for a learned skip of `OneBlock/ResidualRMSZeroReGLU.lean`. As there, the proof needs a
condition on the parameters that the paper does not state: the rows `u` at which `u A` and the
output of the block are linearly independent are dense among the rows with an active gate
(`TurnsActiveRowsGatedSkip`; at almost every weights and skip:
`OneBlock/LearnedSkipRMSZeroReGLUGeneric.lean`). Here, at one parameter under the conditions of
the proof:

* the directions of the weights and the skip that are flat at the paper's inputs (no normalized
  row vanishes, no gate at its kink) are a rotation and a scaling of `h_0`, a rotation and a
  scaling of `h_1`, a rescaling of the values and a rescaling of the gates of the hidden units;
* the value of Lean's `funDimLearned`: `P + d² − (d(d−1) + 2) − 2 d_hidden` (the bound "at most" is
  `funDimLearned_add_le_rmsNorm_zero'`, `OneBlock/LearnedSkipRMSZeroRescaleBound.lean`);
* a finite batch of the paper's inputs on which the Jacobian in the weights and the skip has
  this rank.

The step "`X_0` is a multiple of `I`", with Lemma B.3, is `reglu_unitsRescaleSphere`
(`OneBlock/UnitsRescaleSphereReGLU.lean`). No width of the block is asked. Numeric check of the
values: `learned_skip_zero_relu_check_2026-11-24.py`. Not stated: the upper triangular skip.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ}

/-- **A gated block turns a dense set of the rows with an active gate, for the skip `S`:** every
row `v` with no gate at its kink and with some active gate is a limit of rows `u` such that `u S`
and the output of the block at `u` are linearly independent. For `S = 1` this is
`TurnsActiveRowsGated`. -/
def TurnsActiveRowsGatedSkip
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (S : Matrix d d ℝ) :
    Prop :=
  ∀ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) →
    (∃ i, σ ((v ᵥ* θ.read 0) (Sum.inl i)) ≠ 0) →
    v ∈ closure {u : d → ℝ | LinearIndependent ℝ ![u ᵥ* S, gatedBlock σ
      ((θ.read 0).submatrix id Sum.inl) ((θ.read 0).submatrix id Sum.inr) (θ.write 0) u]}

/-- **Proof of Theorem B.1 (iii) of the skips paper, "The case `ε = 0`", the flat directions for
one ReGLU block with a full learned skip:** under the conditions `OneBlockGenericReGLURMS`, for
`d ≥ 2`, an invertible skip `A = R 0`, a block that turns a dense set of the rows with an active
gate and one turned row off the kinks of the gates, a direction `(η, η_A)` of the weights and the
skip that is flat at every input at which no normalized row vanishes and no gate sits at its kink
is the sum of the rotations of `h_0` and `h_1` (antisymmetric `X₀`, `Y`), the scalings of `h_0`
and `h_1` (numbers `c₀`, `c₁`), a rescaling of the values and a rescaling of the gates of the
hidden units, with `η_A = A (Y + c₁ I) − (X₀ + c₀ I) A`. -/
theorem flatSkipsOn_noKinkGate_le_reglu_learned_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det)
    (hturn : TurnsActiveRowsGatedSkip θ (R 0))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* R 0, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v])
    (η : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (ρ : Fin 1 → Matrix d d ℝ)
    (hη : (η, ρ) ∈ flatSkipsOn (Arch.gated relu (rmsNorm 0) hid)
      (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
      (learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ R ∩ noKinkGateRMS θ)) :
    ∃ (X₀ Y : Matrix d d ℝ) (c₀ c₁ : ℝ) (α β : ∀ ℓ, hid ℓ → ℝ), X₀ᵀ = -X₀ ∧ Yᵀ = -Y ∧
      η = cobDir θ ![X₀, Y] + scaleDir θ ![c₀, c₁] + rescaleDir θ α + rescaleDirGate 1 θ β ∧
      ρ 0 = R 0 * (Y + c₁ • 1) - (X₀ + c₀ • 1) * R 0 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", for one ReGLU block with
a full learned skip, at one parameter:** under the conditions of the proof,
`funDimLearned = P + d² − (d(d−1) + 2) − 2 d_hidden`, with `P` the number of weights without the
skip. -/
theorem funDimLearned_reglu_oneBlock_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det)
    (hturn : TurnsActiveRowsGatedSkip θ (R 0))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* R 0, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v]) :
    funDimLearned (Arch.gated relu (rmsNorm 0) hid) (θ, R)
        + ((Fintype.card d * (Fintype.card d - 1) + 2) + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", in the paper's own
sense, for one ReGLU block with a full learned skip, at one parameter:** a finite batch of inputs
at which no normalized row vanishes and no gate sits at its kink, on which the Jacobian in the
weights and the skip has the rank `P + d² − (d(d−1) + 2) − 2 d_hidden`. -/
theorem exists_jacobianRankSkips_reglu_oneBlock_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det)
    (hturn : TurnsActiveRowsGatedSkip θ (R 0))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* R 0, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v]) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ R ∩ noKinkGateRMS θ) ∧
      jacobianRankSkips (Arch.gated relu (rmsNorm 0) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X (θ, R)
          + ((Fintype.card d * (Fintype.card d - 1) + 2) + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  sorry

end Skips
