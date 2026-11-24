import SkipsLean.Residual.DepthAttentionDim
import SkipsLean.Residual.DepthGated
import SkipsLean.Dimension.UpperBoundTransformer
import SkipsLean.Generic.Sum

/-!
# Residual networks of attention blocks and gated blocks at any depth, without normalization

Paper (skips paper): Lemma A.27 (Small writes): "Let `d_model ≥ 2`, let `E` and `D` have rank
`d_model`, and let each block, in any order and of any width, be an attention block with heads of
width at most `d_model`, causal or not, on sequences of at least two tokens, or an MLP block, with
all MLP blocks tanh, all GELU, all SwiGLU or all GeGLU blocks. […] For all small `τ ≠ 0`, the
residual network has `fd(θ_τ) = P − d_model² − s` (no normalization, no biases)". Theorem 4.7
(Equality for residual networks at any depth): "Let the blocks be analytic, with or without
pre-RMSNorm. The residual network satisfies the equality condition: at generic parameters its
functional dimension is `P − dim G − s`. So the skips raise the functional dimension by at least
`L dim G`".

The proof of Lemma A.27 for attention blocks: "First take an input whose tokens all equal `x`.
Head `i` then gives every token the output `x C_i`, whatever its scores are, so `ψ_{B_i}` does not
enter […]. This is `D_φ G(φ, x) ψ` with `M + ∑_i C_i` in place of `M`, so for a flat `η`
Lemma B.3 gives a rescaling at every unit. The terms of the units then vanish at every input:
they act on each token separately, and they are the derivative along a rescaling, which does not
change the function. Next take an input whose tokens other than the second all equal the first.
[…] So Step 2 for attention blocks in Appendix B gives `ψ_M = 0`, `ψ_{B_i} = 0` and
`ψ_{C_i} = 0` for every head."

Here for `Arch.attentionGated sees σ id H dh hid` (`Network/Transformer.lean`): `L` blocks, block
`ℓ` with the heads `H ℓ` of width `dh ℓ` and the hidden units `hid ℓ` (an attention block if `hid
ℓ` is empty, a gated block if `H ℓ` is empty), without normalization, with a token `t₂` that sees
itself and another token `t₁`; stated for every gate that satisfies the conclusion of Lemma B.3
(`GatedUnitsRescale`) for the hidden units of all blocks together. The conditions on `θ` are those
of the two kinds of block, on the two parts of the parameters: `SmallWritesGenericAttention
θ.sumFst` (`Residual/DepthAttention.lean`) and `SmallWritesGenericGated θ.sumSnd`
(`Residual/DepthGated.lean`). For a block without heads `dh ℓ` is any nonempty type.

* `smallWritesLimit_eq_zero_attentionGated`: the flat directions of `J_0`;
* `eventually_funDim_smallWrites_attentionGated`: `fd(θ_τ) = P − d² − s` for all small `τ ≠ 0`,
  `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}² + ∑_ℓ d_hidden,ℓ`;
* `ae_smallWritesGeneric_attentionGated`: the conditions at generic parameters;
* `ae_funDim_attentionGated_residual`: Theorem 4.7, and `…_ge_add`: the gain of at least `L d²` for
  blocks of total width `H d_h + d_hidden ≥ d`;
* the named kinds: attention with SwiGLU blocks, attention with GeGLU blocks.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ}

/-- **Proof of Lemma A.27, attention blocks and gated blocks without normalization, the flat
directions of `J_0`:** let token `t₂` see itself and another token `t₁`. Under the conditions of
the lemma, a direction `η` with `(J_0 η)(x) = 0` at every input `x` has `η_E = E X` and
`η_D = −X D` for one matrix `X`; in every block the reads and the writes of its heads are those
of the directions of the changes of basis inside the heads, and
it vanishes at the gate columns of the hidden units and rescales every hidden unit (the value
column of unit `i` of block `ℓ` by `−α_{ℓ,i}`, its write row by `α_{ℓ,i}`). -/
theorem smallWritesLimit_eq_zero_attentionGated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hθa : SmallWritesGenericAttention θ.sumFst) (hθm : SmallWritesGenericGated θ.sumSnd)
    (η : Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hη : ∀ x, smallWritesLimit (Arch.attentionGated sees σ id H dh hid) θ η x = 0) :
    ∃ (X : Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η.E = θ.E * X ∧ η.D = -(X * θ.D)
        ∧ (∀ ℓ, η.sumFst.read ℓ = (headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').read ℓ)
        ∧ (∀ ℓ, η.sumFst.write ℓ = (headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').write ℓ)
        ∧ (∀ ℓ (i : hid ℓ) a, η.sumSnd.read ℓ a (Sum.inl i) = 0)
        ∧ (∀ ℓ (i : hid ℓ) a,
          η.sumSnd.read ℓ a (Sum.inr i) = -(α ℓ i) * θ.sumSnd.read ℓ a (Sum.inr i))
        ∧ (∀ ℓ (i : hid ℓ) a, η.sumSnd.write ℓ i a = α ℓ i * θ.sumSnd.write ℓ i a) := by
  sorry

/-- **Lemma A.27 (Small writes), first value, for attention blocks and gated blocks, under the
conditions of its proof:** with a token that sees itself and another token, for all small `τ ≠ 0`
the residual network has `fd(θ_τ) = P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem eventually_funDim_smallWrites_attentionGated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hθa : SmallWritesGenericAttention θ.sumFst) (hθm : SmallWritesGenericGated θ.sumSnd) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.attentionGated sees σ id H dh hid) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2
            + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
        = Module.finrank ℝ
            (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **The conditions of Lemma A.27 hold at generic parameters,** for `d_in, d_out ≥ d ≥ 2`,
heads of width `1 ≤ d_h ≤ d` and blocks of any widths. -/
theorem ae_smallWritesGeneric_attentionGated
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, SmallWritesGenericAttention θ.sumFst ∧ SmallWritesGenericGated θ.sumSnd := by
  sorry

/-- **Theorem 4.7 of the skips paper for attention blocks and gated blocks, without
normalization:** with `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths
and a token that sees itself and another token, at almost every parameter the residual network
has the functional dimension `P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_attentionGated_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ
          (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7, the gain, for attention blocks and gated blocks, without normalization:** if
moreover every block has total width `H d_h + d_hidden ≥ d`, at almost every parameter the skips
raise the functional dimension by at least `L d²`. -/
theorem ae_funDim_attentionGated_residual_ge_add (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 0 θ + L * Fintype.card d ^ 2
      ≤ funDim (Arch.attentionGated sees σ id H dh hid) 1 θ := by
  sorry

/-- **Theorem 4.7 of the skips paper for attention blocks and SwiGLU blocks, without
normalization:** at almost every parameter the residual network has the functional dimension
`P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_attention_swiglu_residual
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees silu id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ
          (Params (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for attention blocks and GeGLU blocks, without
normalization:** at almost every parameter the residual network has the functional dimension
`P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_attention_geglu_residual
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees gelu id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ
          (Params (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid) dIn dOut) := by
  sorry

end Skips
