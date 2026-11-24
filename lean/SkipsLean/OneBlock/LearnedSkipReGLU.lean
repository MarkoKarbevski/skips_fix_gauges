import SkipsLean.OneBlock.LearnedSkipGain
import SkipsLean.OneBlock.ResidualRMSReGLU
import SkipsLean.Symmetry.InsideBlocksKinds
import SkipsLean.Dimension.UpperBoundTransformerRescale
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-!
# One ReGLU block with a full learned skip under pre-RMSNorm

Paper (skips paper): Theorem 4.6 (ii): "A learned skip raises it by exactly
`d_model (d_model + 1)/2` more than an identity skip." Theorem B.1 (iii): "Let the network be
pre-RMSNorm without biases, with a learned skip `A`, full or upper triangular. For generic
parameters and `ε > 0`, its functional dimension exceeds that of the residual network of part (ii)
by exactly `d_model (d_model + 1)/2`, and it satisfies the equality condition." Its proof, Step 4,
after equation (17), `∂_ψ B(n) = q(n) 𝐃B(n) n`: "For ReLU, ReLU² and ReGLU, `B(λn) = λ^k B(n)` for
`λ > 0`, with `k = 1` or `2`, so the right side of (17) is `k q(n) B(n)`. Replacing `n` by `λn`
with `0 < λ ≤ 1` multiplies the left side by `λ^k` and the right side by `λ^{k+2}`, so both vanish,
and `q = 0` wherever `B ≠ 0`." For ReGLU `k = 2` and `s = 2 d_hidden`: one rescaling of the gate
and one of the value for each hidden unit.

Stated here, as in `OneBlock/ResidualRMSReGLU.lean` (the same block with the identity skip) and
`OneBlock/LearnedSkipRescale.lean` (ReLU and ReLU² blocks with a learned skip), for a block of any
width with at least one hidden unit:

* Step 4: `NoSymmetricPart` at the inputs `noKinkGateRMS θ` with no gate at its kink, under the
  conditions `OneBlockGenericReGLURMS`.
* At one parameter, with an invertible skip: the functional dimension is that of the residual
  network at the same weights plus `d (d + 1)/2`; it is `P + d² − d (d − 1) − 2 d_hidden` (the
  equality condition: `P + d²` parameters, symmetries of dimension `d (d − 1) + 2 d_hidden`); and a
  batch of inputs of `noKinkGateRMS θ` has a Jacobian of this rank.
* For `d_in, d_out ≥ d ≥ 2`: the same at almost every `(θ, A)`.

The route is that of `OneBlock/LearnedSkipRescale.lean`, with Lemma B.3 for ReGLU as in
`flatOn_noKinkGateRMS_le_reglu_residual_rmsNorm` and the residual value
`funDim_reglu_oneBlock_residual_rmsNorm`. Numeric check:
`learned_skip_relu_attention_check_2026-11-24.py`. Not stated here: the upper triangular skip;
`ε = 0`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)] {ε : ℝ}

/-- **Proof of Theorem B.1 (iii), Step 4, for a ReGLU block:** for a block with at least one
hidden unit and `ε > 0`, under the conditions `OneBlockGenericReGLURMS`, equation (17) at the
inputs with no gate at its kink forces `X_s = 0`. -/
theorem noSymmetricPart_reglu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) :
    NoSymmetricPart (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) ε θ
      (noKinkGateRMS θ) := by
  sorry

/-- **Theorem 4.6 (ii), "A learned skip raises it by exactly `d (d + 1)/2` more than an identity
skip", for a ReGLU block, at one parameter:** under the conditions `OneBlockGenericReGLURMS`, for
an invertible skip `A = R 0`, the network with the full learned skip has at `(θ, A)` the functional
dimension of the residual network at `θ` plus `d (d + 1)/2`. -/
theorem funDimLearned_reglu_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (hid 0)]
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det) :
    funDimLearned (Arch.gated relu (rmsNorm ε) hid) (θ, R)
      = funDim (Arch.gated relu (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) for a ReGLU block with a full learned skip, at one parameter:** under the
conditions `OneBlockGenericReGLURMS`, for an invertible skip,
`funDim = P + d² − d (d − 1) − 2 d_hidden`, with `P` the number of weights without the skip. -/
theorem funDimLearned_reglu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det) :
    funDimLearned (Arch.gated relu (rmsNorm ε) hid) (θ, R)
        + (Fintype.card d * (Fintype.card d - 1) + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem B.1 (iii) in the paper's own sense, for a ReGLU block, at one parameter:** a finite
batch of inputs with no gate at its kink on which the Jacobian in the weights and the skip has the
rank `P + d² − d (d − 1) − 2 d_hidden`. -/
theorem exists_jacobianRankSkips_reglu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateRMS θ) ∧
      jacobianRankSkips (Arch.gated relu (rmsNorm ε) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X (θ, R)
          + (Fintype.card d * (Fintype.card d - 1) + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one ReGLU block with a full learned skip,
`ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and a block of any width with at least one hidden unit, at
almost every `(θ, A)` the functional dimension is `P + d² − d (d − 1) − 2 d_hidden`. -/
theorem ae_funDimLearned_reglu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.gated relu (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem B.1 (iii) in the paper's own sense, for one ReGLU block with a full learned skip:**
at almost every `(θ, A)` there is a finite batch of inputs with no gate at its kink on which the
Jacobian in the weights and the skip has the rank `P + d² − d (d − 1) − 2 d_hidden`. -/
theorem ae_exists_jacobianRankSkips_reglu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateRMS p.1) ∧
      jacobianRankSkips (Arch.gated relu (rmsNorm ε) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X p
          + (Fintype.card d * (Fintype.card d - 1) + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem 4.6 (ii) of the skips paper, "A learned skip raises it by exactly `d (d + 1)/2` more
than an identity skip", for one ReGLU block, `ε > 0`:** at almost every `(θ, A)` and almost every
`θ'`, the network with the full learned skip `A` has `d (d + 1)/2` more functional dimension than
the residual network at `θ'`. -/
theorem ae_funDimLearned_reglu_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearned (Arch.gated relu (rmsNorm ε) hid) p
      = funDim (Arch.gated relu (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

end Skips
