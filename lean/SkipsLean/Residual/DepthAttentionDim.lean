import SkipsLean.Residual.DepthAttentionGeneric
import SkipsLean.Dimension.GenericRank

/-!
# Residual networks of attention blocks at any depth: the functional dimension

Paper (skips paper): Theorem 4.7 (Equality for residual networks at any depth): "Let the blocks
be analytic, with or without pre-RMSNorm. The residual network satisfies the equality condition:
at generic parameters its functional dimension is `P − dim G − s`. So the skips raise the
functional dimension by at least `L dim G` […]." Corollary 4.10 (Attention-only transformers:
Conjecture 2.4 of Henry, 2026): "Without normalization, consider a residual network of `L`
attention blocks at generic parameters, and let `s = 2 L d_model² / H`. (i) With an embedding and
a readout, its functional dimension is `P − d_model² − s`." Lemma A.27, first value, at generic
parameters.

Here, for attention blocks without normalization, heads of width `1 ≤ d_h ≤ d` (any numbers of
heads; `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`), `d_in, d_out ≥ d ≥ 2`, and a mask with a token that sees
itself and another token (two tokens at least; causal or not):

* `ae_eventually_funDim_smallWrites_attention`: Lemma A.27, first value, at almost every `θ`;
* `ae_funDim_attention_residual`: Theorem 4.7 for attention blocks without normalization,
  `fd = P − d² − s` at almost every parameter;
* `ae_funDim_attention_residual_ge_add`: the skips raise the functional dimension by at least
  `L d²`, when every block has total width `H d_h ≥ d`;
* `ae_funDim_attention_residual_of_width`: Corollary 4.10 (i) in the setting of the main text,
  `H` heads of total width `H d_h = d` in every block, with `s = 2 L d² / H`.
Not stated: Corollary 4.10 (ii) (without an embedding and a readout); pre-RMSNorm.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-- **Lemma A.27 (Small writes), first value, for attention blocks:** for generic parameters `θ`
and all small `τ ≠ 0`, the residual network has `fd(θ_τ) = P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_eventually_funDim_smallWrites_attention
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.attention sees id H dh) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ
            (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for attention blocks without normalization:** with
`d_in, d_out ≥ d ≥ 2`, `L` attention blocks with heads of width `1 ≤ d_h ≤ d`, and a token that
sees itself and another token, at almost every parameter the residual network has the functional
dimension `P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_attention_residual
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

/-- **Theorem 4.7, the gain, for attention blocks without normalization:** if moreover every
block has total width `H d_h ≥ d`, at almost every parameter the skips raise the functional
dimension by at least `L d²`. -/
theorem ae_funDim_attention_residual_ge_add
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 0 θ + L * Fintype.card d ^ 2
      ≤ funDim (Arch.attention sees id H dh) 1 θ := by
  sorry

/-- **Corollary 4.10 (i) of the skips paper (attention-only transformers):** without
normalization, with `d_in, d_out ≥ d ≥ 2` and `L` attention blocks of `Hn` heads each, of total
width `H d_h = d`, on a mask with a token that sees itself and another token: at almost every
parameter the residual network has the functional dimension `P − d² − s`, `s = 2 L d² / H`. -/
theorem ae_funDim_attention_residual_of_width (Hn : ℕ)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hHn : ∀ ℓ, Fintype.card (H ℓ) = Hn)
    (hHd : ∀ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) = Fintype.card d)
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2 + 2 * L * Fintype.card d ^ 2 / Hn)
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

end Skips
