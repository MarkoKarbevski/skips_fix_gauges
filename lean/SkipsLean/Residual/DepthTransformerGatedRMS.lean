import SkipsLean.Residual.DepthAttentionRMSDim
import SkipsLean.Residual.DepthGatedRMS
import SkipsLean.Dimension.UpperBoundTransformer
import SkipsLean.Generic.Sum

/-!
# Residual networks of attention blocks and gated blocks at any depth, under pre-RMSNorm

Paper (skips paper): Lemma A.27 (Small writes), second value: "let each block, in any order and
of any width, be an attention block […] or an MLP block, with all MLP blocks tanh, all GELU, all
SwiGLU or all GeGLU blocks. […] For all small `τ ≠ 0`, the residual network has
`fd(θ_τ) = P − d_model (d_model − 1)/2 − s` (pre-RMSNorm with `ε > 0`, no biases)". Theorem 4.7:
"Let the blocks be analytic, with or without pre-RMSNorm. The residual network satisfies the
equality condition: at generic parameters its functional dimension is `P − dim G − s`. So the
skips raise the functional dimension by at least `L dim G`".

The proof of Lemma A.27 under pre-RMSNorm: "This is the equation of the proof of Theorem B.1(ii)
with `h_1 = xE` and `D_θ h_1 η = x η_E + D_θ g(n) η`, and its Steps 1 to 5 go through with three
changes. […] In Step 4, the hidden units are handled first, on inputs with equal tokens, as
above. So the flat directions are the `η^Y`, the rescalings of the units and the changes of basis
inside the heads, a space of dimension `d_model (d_model − 1)/2 + s`."

Here for `Arch.attentionGated sees σ (rmsNorm ε) H dh hid` (`Network/Transformer.lean`): `L`
blocks, block `ℓ` with the heads `H ℓ` of width `dh ℓ` and the hidden units `hid ℓ` (an attention
block if `hid ℓ` is empty, a gated block if `H ℓ` is empty), under pre-RMSNorm with `ε > 0`, with
a token `t₂` that sees itself and another token `t₁`; stated for every gate that satisfies the
conclusion of Lemma B.3 (`GatedUnitsRescale`) for the hidden units of all blocks together. The
conditions on `θ` are those of the two kinds of block, on the two parts of the parameters:
`SmallWritesGenericAttentionRMS θ.sumFst` (`Residual/DepthAttentionRMS.lean`) and
`SmallWritesGenericGatedRMS θ.sumSnd` (`Residual/DepthGatedRMS.lean`). For a block without heads
`dh ℓ` is any nonempty type. The twin without normalization:
`Residual/DepthTransformerGated.lean`.

* `smallWritesLimitNorm_eq_zero_attentionGated_rmsNorm`: the flat directions of `J_0`;
* `eventually_funDim_smallWrites_attentionGated_rmsNorm`: `fd(θ_τ) = P − d(d−1)/2 − s` for all small
  `τ ≠ 0`, `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}² + ∑_ℓ d_hidden,ℓ`;
* `ae_smallWritesGeneric_attentionGated_rmsNorm`: the conditions at generic parameters;
* `ae_funDim_attentionGated_residual_rmsNorm`: Theorem 4.7, and `…_ge_add`: the gain of at least
  `L d(d−1)/2` for blocks of total width `H d_h + d_hidden ≥ d`;
* the named kinds: attention with SwiGLU blocks, attention with GeGLU blocks.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **Proof of Lemma A.27, attention blocks and gated blocks under pre-RMSNorm, the flat
directions of `J_0`:** let `ε > 0` and let token `t₂` see itself and another token `t₁`. Under
the conditions of the lemma, a direction `η` with `(J_0 η)(x) = 0` at every input `x` has
`η_E = E Y` and `η_D = −Y D` for one antisymmetric matrix `Y`; in every block the reads and the
writes of its heads are those of the directions of the changes of basis inside the heads, and
it vanishes at the gate columns of the hidden units and rescales every hidden unit (the value
column of unit `i` of block `ℓ` by `−α_{ℓ,i}`, its write row by `α_{ℓ,i}`). -/
theorem smallWritesLimitNorm_eq_zero_attentionGated_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hθa : SmallWritesGenericAttentionRMS θ.sumFst) (hθm : SmallWritesGenericGatedRMS θ.sumSnd)
    (η : Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hη : ∀ x, smallWritesLimitNorm (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) θ η x = 0) :
    ∃ (Y : Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D)
        ∧ (∀ ℓ, η.sumFst.read ℓ = (headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').read ℓ)
        ∧ (∀ ℓ, η.sumFst.write ℓ = (headDirQK θ.sumFst Γ + headDirVO θ.sumFst Γ').write ℓ)
        ∧ (∀ ℓ (i : hid ℓ) a, η.sumSnd.read ℓ a (Sum.inl i) = 0)
        ∧ (∀ ℓ (i : hid ℓ) a,
          η.sumSnd.read ℓ a (Sum.inr i) = -(α ℓ i) * θ.sumSnd.read ℓ a (Sum.inr i))
        ∧ (∀ ℓ (i : hid ℓ) a, η.sumSnd.write ℓ i a = α ℓ i * θ.sumSnd.write ℓ i a) := by
  sorry

/-- **Lemma A.27 (Small writes), second value, for attention blocks and gated blocks, under the
conditions of its proof:** with `ε > 0` and a token that sees itself and another token, for all
small `τ ≠ 0` the residual network has
`fd(θ_τ) = P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem eventually_funDim_smallWrites_attentionGated_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hθa : SmallWritesGenericAttentionRMS θ.sumFst) (hθm : SmallWritesGenericGatedRMS θ.sumSnd) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 (θ.smallWrites τ)
          + (Fintype.card d * (Fintype.card d - 1) / 2
            + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
        = Module.finrank ℝ
            (Params
              (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **The conditions of Lemma A.27 under pre-RMSNorm hold at generic parameters,** for
`d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d` and blocks of any widths. -/
theorem ae_smallWritesGeneric_attentionGated_rmsNorm
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, SmallWritesGenericAttentionRMS θ.sumFst ∧ SmallWritesGenericGatedRMS θ.sumSnd := by
  sorry

/-- **Theorem 4.7 of the skips paper for attention blocks and gated blocks under pre-RMSNorm
(`ε > 0`):** with `d_in, d_out ≥ d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths and a
token that sees itself and another token, at almost every parameter the residual network has the
functional dimension `P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_attentionGated_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ
          (Params
            (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7, the gain, for attention blocks and gated blocks under pre-RMSNorm
(`ε > 0`):** if moreover every block has total width `H d_h + d_hidden ≥ d`, at almost every
parameter the skips raise the functional dimension by at least `L d(d−1)/2`. -/
theorem ae_funDim_attentionGated_residual_rmsNorm_ge_add (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ
        + L * (Fintype.card d * (Fintype.card d - 1) / 2)
      ≤ funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ := by
  sorry

/-- **Theorem 4.7 of the skips paper for attention blocks and SwiGLU blocks under pre-RMSNorm
(`ε > 0`):** at almost every parameter the residual network has the functional dimension
`P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_attention_swiglu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees silu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees silu (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ
          (Params
            (Arch.attentionGated (T := T) (d := d) sees silu (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for attention blocks and GeGLU blocks under pre-RMSNorm
(`ε > 0`):** at almost every parameter the residual network has the functional dimension
`P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_attention_geglu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees gelu (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ
          (Params
            (Arch.attentionGated (T := T) (d := d) sees gelu (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

end Skips
