import SkipsLean.OneBlock.LearnedSkipGain
import SkipsLean.Residual.DepthAttentionRMSDim
import SkipsLean.Network.AttentionAnalytic
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-!
# One attention block with a full learned skip under pre-RMSNorm

Paper (skips paper): Theorem 4.6 (ii): "A learned skip raises it by exactly
`d_model (d_model + 1)/2` more than an identity skip." Theorem B.1 (iii): "Let the network be
pre-RMSNorm without biases, with a learned skip `A`, full or upper triangular. For generic
parameters and `ε > 0`, its functional dimension exceeds that of the residual network of part (ii)
by exactly `d_model (d_model + 1)/2`, and it satisfies the equality condition." Its proof, Step 4,
after equation (17), `∂_ψ B(n) = q(n) 𝐃B(n) n`: "For attention, `q(n) n` stands for the matrix with
the rows `q(n_t) n_t`, one per token. We show that `q = 0`, hence `X_s = 0`. […] For attention, on
the two-token inputs of Step 2 for attention blocks with `u = t n̂` and `v` fixed, the right side is
`t³ q(n̂) n̂ S + O(t²)` and the left side is `O(t)`." Here `S = ∑_i W_{V,i} W_{O,i}`.

The Lean statement of Step 4 is the paper's (`NoSymmetricPart` at all inputs, for a block with
`S ≠ 0` in which some token sees a token). A shorter proof than the paper's is available: on inputs
whose tokens are all equal to a row `v`, a token that sees some token has the output `v S`, for
all weights, so equation (17) reads `v (X S + ∂_ψ S) = q(v) v S` on the ball, a linear map equal to
a cubic one, and `q(v) v S = 0`. The statement does not ask for two tokens.

Stated here:

* Step 4: `NoSymmetricPart` for an attention block, where `E` has rank `d`, some token sees a
  token and `S ≠ 0`.
* At one parameter, with `E`, `D` of rank `d` and an invertible skip: the functional dimension is
  that of the residual network at the same weights plus `d (d + 1)/2`
  (`funDimLearned_eq_funDim_residual_add_of_noSymmetricPart`).
* For `d_in, d_out ≥ d ≥ 2`, at least one head, heads of width `1 ≤ d_h ≤ d` and a token that sees
  itself and another token (the hypotheses of `ae_funDim_attention_residual_rmsNorm`, the residual
  value): at almost every `(θ, A)` the functional dimension is `P + d² − d (d − 1) − 2 H d_h²`,
  which is `d (d + 1)/2` more than the residual network at almost every `θ'`.

Numeric check: `learned_skip_relu_attention_check_2026-11-24.py`. Not stated here: the upper
triangular skip; `ε = 0`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)] {ε : ℝ}

/-- **Proof of Theorem B.1 (iii), Step 4, for an attention block:** for `ε > 0`, if `E` has rank
`d`, some token sees a token and `S = ∑_i W_{V,i} W_{O,i}` is not `0`, equation (17) at all inputs
forces `X_s = 0`. -/
theorem noSymmetricPart_attention_rmsNorm (hε : 0 < ε)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hsees : ∃ t s, sees t s)
    (hS : ∑ i, headValueModel θ 0 i ≠ 0) :
    NoSymmetricPart (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) ε θ Set.univ := by
  sorry

/-- **Theorem 4.6 (ii), "A learned skip raises it by exactly `d (d + 1)/2` more than an identity
skip", for an attention block, at one parameter:** for `ε > 0`, if `E` and `D` have rank `d`, some
token sees a token, `S = ∑_i W_{V,i} W_{O,i}` is not `0` and the skip `A = R 0` is invertible, the
network with the full learned skip has at `(θ, A)` the functional dimension of the residual network
at `θ` plus `d (d + 1)/2`. -/
theorem funDimLearned_attention_rmsNorm_eq_residual_add (hε : 0 < ε)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hsees : ∃ t s, sees t s) (hS : ∑ i, headValueModel θ 0 i ≠ 0)
    (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det) :
    funDimLearned (Arch.attention sees (rmsNorm ε) H dh) (θ, R)
      = funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one attention block with a full learned skip,
`ε > 0`:** for `d_in, d_out ≥ d ≥ 2`, at least one head, heads of width `1 ≤ d_h ≤ d` and a token
that sees itself and another token, at almost every `(θ, A)` the functional dimension is
`P + d² − d (d − 1) − 2 H d_h²`, with `P` the number of weights without the skip. -/
theorem ae_funDimLearned_attention_rmsNorm (hε : 0 < ε) [Nonempty (H 0)]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.attention sees (rmsNorm ε) H dh) p
        + (Fintype.card d * (Fintype.card d - 1)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
        + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem 4.6 (ii) of the skips paper, "A learned skip raises it by exactly `d (d + 1)/2` more
than an identity skip", for one attention block, `ε > 0`:** at almost every `(θ, A)` and almost
every `θ'`, the network with the full learned skip `A` has `d (d + 1)/2` more functional dimension
than the residual network at `θ'`. -/
theorem ae_funDimLearned_attention_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (H 0)]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearned (Arch.attention sees (rmsNorm ε) H dh) p
      = funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

end Skips
