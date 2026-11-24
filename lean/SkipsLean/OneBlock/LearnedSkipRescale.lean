import SkipsLean.OneBlock.LearnedSkipGain
import SkipsLean.OneBlock.ResidualRMSRescale
import SkipsLean.Dimension.UpperBoundTransformerRescale
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-!
# One ReLU or ReLU² block with a full learned skip under pre-RMSNorm

Paper (skips paper): Theorem 4.6 (ii): "A learned skip raises it by exactly
`d_model (d_model + 1)/2` more than an identity skip." Theorem B.1 (iii): "Let the network be
pre-RMSNorm without biases, with a learned skip `A`, full or upper triangular. For generic
parameters and `ε > 0`, its functional dimension exceeds that of the residual network of part (ii)
by exactly `d_model (d_model + 1)/2`, and it satisfies the equality condition." Its proof, Step 4,
after equation (17), `∂_ψ B(n) = q(n) 𝐃B(n) n`: "We show that `q = 0`, hence `X_s = 0`. For ReLU,
ReLU² and ReGLU, `B(λn) = λ^k B(n)` for `λ > 0`, with `k = 1` or `2`, so the right side of (17) is
`k q(n) B(n)`. Replacing `n` by `λn` with `0 < λ ≤ 1` multiplies the left side by `λ^k` and the
right side by `λ^{k+2}`, so both vanish, and `q = 0` wherever `B ≠ 0`."

Stated here, as in `OneBlock/ResidualRMSRescale.lean` (the same block with the identity skip), for
an activation that is differentiable away from `0`, positively homogeneous of degree `k ≥ 1`, and
satisfies Lemma B.3 in the form `UnitsRescale`, for a block of any width with at least one hidden
unit (a block with no hidden unit is the zero map, and then every change of basis at `h_0` is
undone by the skip):

* Step 4: `NoSymmetricPart` at the inputs `noKinkRMS θ` with no hidden unit at its kink, under the
  conditions `OneBlockGenericRMS` (they give `B ≠ 0` on an open set, by Lemma B.3).
* At one parameter, with an invertible skip: the functional dimension is that of the residual
  network at the same weights plus `d (d + 1)/2`; it is `P + d² − d (d − 1) − s` with `s` the
  number of hidden units (the equality condition: `P + d²` parameters, symmetries of dimension
  `d (d − 1) + s`); and a batch of inputs of `noKinkRMS θ` has a Jacobian of this rank (the paper's
  functional dimension for these blocks).
* For ReLU and ReLU² blocks, `d_in, d_out ≥ d ≥ 2`: the same at almost every `(θ, A)`.

The route: Steps 1 to 3 (`exists_of_flatSkipsOn_learned_rmsNorm`), Step 4 by homogeneity, Step 5 as
`funDimLearned_eq_funDim_residual_add_of_noSymmetricPart_on` (`OneBlock/LearnedSkipGain.lean`), with
the residual value `funDim_mlp_oneBlock_rescale_residual_rmsNorm`. Numeric check:
`learned_skip_relu_attention_check_2026-11-24.py`. Not stated here: the upper triangular skip;
`ε = 0`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **Proof of Theorem B.1 (iii), Step 4, for ReLU-type MLP blocks:** for an activation that is
positively homogeneous of degree `k ≥ 1`, a block with at least one hidden unit and `ε > 0`, under
the conditions `OneBlockGenericRMS`, equation (17) at the inputs with no hidden unit at its kink
forces `X_s = 0`. -/
theorem noSymmetricPart_mlp_rescale_rmsNorm {k : ℕ} (hk : k ≠ 0) (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0)) [Nonempty (hid 0)]
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) :
    NoSymmetricPart (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) ε θ (noKinkRMS θ) := by
  sorry

/-- **Theorem 4.6 (ii), "A learned skip raises it by exactly `d (d + 1)/2` more than an identity
skip", for ReLU-type MLP blocks, at one parameter:** under the conditions `OneBlockGenericRMS`,
for an invertible skip `A = R 0`, the network with the full learned skip has at `(θ, A)` the
functional dimension of the residual network at `θ` plus `d (d + 1)/2`. -/
theorem funDimLearned_mlp_rescale_rmsNorm_eq_residual_add {k : ℕ} (hk : k ≠ 0) (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0)) [Nonempty (hid 0)]
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det) :
    funDimLearned (Arch.mlp σ (rmsNorm ε) hid) (θ, R)
      = funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) for ReLU-type MLP blocks with a full learned skip, at one parameter:**
under the conditions `OneBlockGenericRMS`, for an invertible skip,
`funDim = P + d² − d (d − 1) − s`, with `s` the number of hidden units and `P` the number of
weights without the skip. -/
theorem funDimLearned_mlp_rescale_rmsNorm {k : ℕ} (hk : k ≠ 0) (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0)) [Nonempty (hid 0)]
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det) :
    funDimLearned (Arch.mlp σ (rmsNorm ε) hid) (θ, R)
        + (Fintype.card d * (Fintype.card d - 1) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem B.1 (iii) in the paper's own sense, for ReLU-type MLP blocks, at one parameter:** a
finite batch of inputs with no hidden unit at its kink on which the Jacobian in the weights and
the skip has the rank `P + d² − d (d − 1) − s`. -/
theorem exists_jacobianRankSkips_mlp_rescale_rmsNorm {k : ℕ} (hk : k ≠ 0) (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0)) [Nonempty (hid 0)]
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkRMS θ) ∧
      jacobianRankSkips (Arch.mlp σ (rmsNorm ε) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X (θ, R)
          + (Fintype.card d * (Fintype.card d - 1) + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one ReLU block with a full learned skip, `ε > 0`:**
for `d_in, d_out ≥ d ≥ 2` and a block of any width with at least one hidden unit, at almost every
`(θ, A)` the functional dimension is `P + d² − d (d − 1) − d_hidden`. -/
theorem ae_funDimLearned_relu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp relu (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem B.1 (iii) in the paper's own sense, for one ReLU block with a full learned skip:**
at almost every `(θ, A)` there is a finite batch of inputs with no hidden unit at its kink on which
the Jacobian in the weights and the skip has the rank `P + d² − d (d − 1) − d_hidden`. -/
theorem ae_exists_jacobianRankSkips_relu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkRMS p.1) ∧
      jacobianRankSkips (Arch.mlp relu (rmsNorm ε) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X p
          + (Fintype.card d * (Fintype.card d - 1) + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem 4.6 (ii) of the skips paper, "A learned skip raises it by exactly `d (d + 1)/2` more
than an identity skip", for one ReLU block, `ε > 0`:** at almost every `(θ, A)` and almost every
`θ'`, the network with the full learned skip `A` has `d (d + 1)/2` more functional dimension than
the residual network at `θ'`. -/
theorem ae_funDimLearned_relu_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearned (Arch.mlp relu (rmsNorm ε) hid) p
      = funDim (Arch.mlp relu (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one ReLU² block with a full learned skip,
`ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and a block of any width with at least one hidden unit, at
almost every `(θ, A)` the functional dimension is `P + d² − d (d − 1) − d_hidden`. -/
theorem ae_funDimLearned_reluSq_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp reluSq (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem B.1 (iii) in the paper's own sense, for one ReLU² block with a full learned skip:**
at almost every `(θ, A)` there is a finite batch of inputs with no hidden unit at its kink on which
the Jacobian in the weights and the skip has the rank `P + d² − d (d − 1) − d_hidden`. -/
theorem ae_exists_jacobianRankSkips_reluSq_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkRMS p.1) ∧
      jacobianRankSkips (Arch.mlp reluSq (rmsNorm ε) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X p
          + (Fintype.card d * (Fintype.card d - 1) + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem 4.6 (ii) of the skips paper, "A learned skip raises it by exactly `d (d + 1)/2` more
than an identity skip", for one ReLU² block, `ε > 0`:** at almost every `(θ, A)` and almost every
`θ'`, the network with the full learned skip `A` has `d (d + 1)/2` more functional dimension than
the residual network at `θ'`. -/
theorem ae_funDimLearned_reluSq_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearned (Arch.mlp reluSq (rmsNorm ε) hid) p
      = funDim (Arch.mlp reluSq (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

end Skips
