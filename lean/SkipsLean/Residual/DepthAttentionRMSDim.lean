import SkipsLean.Residual.DepthAttentionRMS
import SkipsLean.Dimension.GenericRank
import SkipsLean.OneBlock.Common
import SkipsLean.Generic.Params

/-!
# Residual networks of attention blocks at any depth under pre-RMSNorm: the dimension

Paper (skips paper): Theorem 4.7 (Equality for residual networks at any depth): "Let the blocks
be analytic, with or without pre-RMSNorm. The residual network satisfies the equality condition:
at generic parameters its functional dimension is `P − dim G − s`. So the skips raise the
functional dimension by at least `L dim G` […]", with `dim G = d_model (d_model − 1)/2` under
pre-RMSNorm; Lemma A.27, second value, at generic parameters.

Here, for attention blocks under pre-RMSNorm with `ε > 0`, heads of width `1 ≤ d_h ≤ d` (any
numbers of heads; `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`), `d_in, d_out ≥ d ≥ 2`, and a mask with a token that
sees itself and another token:

* `ae_smallWritesGenericAttentionRMS`: the conditions of the proof hold at almost every `θ`;
* `ae_eventually_funDim_smallWrites_attention_rmsNorm`: Lemma A.27, second value;
* `ae_funDim_attention_residual_rmsNorm`: Theorem 4.7, `fd = P − d(d−1)/2 − s`;
* `ae_funDim_attention_residual_rmsNorm_ge_add`: the skips raise the functional dimension by at
  least `L d(d−1)/2`, when every block has total width `H d_h ≥ d`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)] {ε : ℝ}

/-- The conditions of Lemma A.27 under pre-RMSNorm for attention blocks hold at generic
parameters, for `d_in, d_out ≥ d ≥ 2` and heads of width `1 ≤ d_h ≤ d`. -/
theorem ae_smallWritesGenericAttentionRMS
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, SmallWritesGenericAttentionRMS θ := by
  sorry

/-- **Lemma A.27 (Small writes), second value, for attention blocks:** under pre-RMSNorm with
`ε > 0`, for generic parameters `θ` and all small `τ ≠ 0`, the residual network has
`fd(θ_τ) = P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_eventually_funDim_smallWrites_attention_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.attention sees (rmsNorm ε) H dh) 1 (θ.smallWrites τ)
          + (Fintype.card d * (Fintype.card d - 1) / 2
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ
            (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for attention blocks under pre-RMSNorm:** with
`d_in, d_out ≥ d ≥ 2`, `ε > 0`, `L` attention blocks with heads of width `1 ≤ d_h ≤ d`, and a
token that sees itself and another token, at almost every parameter the residual network has the
functional dimension `P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_attention_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  sorry

/-- **Theorem 4.7, the gain, for attention blocks under pre-RMSNorm:** if moreover every block
has total width `H d_h ≥ d`, at almost every parameter the skips raise the functional dimension
by at least `L d(d−1)/2`. -/
theorem ae_funDim_attention_residual_rmsNorm_ge_add (hε : 0 < ε)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
        + L * (Fintype.card d * (Fintype.card d - 1) / 2)
      ≤ funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ := by
  sorry

end Skips
