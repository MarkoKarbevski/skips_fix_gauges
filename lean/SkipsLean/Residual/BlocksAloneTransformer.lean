import SkipsLean.Residual.BlocksAloneGeneral
import SkipsLean.Residual.DepthTransformer
import SkipsLean.Residual.DepthTransformerGated

/-!
# Residual networks of attention blocks and MLP blocks without an embedding and a readout

Paper (skips paper), Lemma A.27: "let each block, in any order and of any width, be an attention
block with heads of width at most `d_model`, causal or not, on sequences of at least two tokens,
or an MLP block, with all MLP blocks tanh, all GELU, all SwiGLU or all GeGLU blocks. […] For all
small `τ ≠ 0`, the residual network has […] `fd(θ_τ) = P − s` (no embedding, readout, biases or
normalization)", where "`s` counts the changes of basis inside the heads and the rescalings of the
values of gated units". Its proof for attention blocks: "So the flat directions form a space of
dimension `d_model² + s`, and of dimension `s` without an embedding and a readout."

Here, for the networks `Arch.attentionMlp sees σ id H dh hid` and
`Arch.attentionGated sees σ id H dh hid` (`Network/Transformer.lean`: block `ℓ` with the heads
`H ℓ` of width `dh ℓ` and the hidden units `hid ℓ`; an attention block if `hid ℓ` is empty, an MLP
block if `H ℓ` is empty), a token that sees itself and another token, `d ≥ 2`, and the network
without an embedding and a readout of `Residual/BlocksAlone.lean`:

* `eventually_funDimBlocks_smallWrites_attentionMlp`, `…_attentionGated`: the fourth value under
  the conditions of the proof of the lemma at `E = D = I`, on the two parts of the parameters;
  `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`, and with gated units `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}² + ∑_ℓ d_hidden,ℓ`;
* `ae_funDimBlocks_attentionMlp_residual`, `ae_funDimBlocks_attentionGated_residual`: `fd = P − s`
  at almost every parameter of the blocks (heads of width `1 ≤ d_h ≤ d`);
* the named kinds: attention with tanh, GELU, SwiGLU and GeGLU blocks.

They follow from the first value at `β.toParams`
(`eventually_funDim_smallWrites_attentionMlp`, `…_attentionGated`) and
`funDimBlocks_add_finrank_eq_of_funDim_toParams` (`Residual/BlocksAloneGeneral.lean`), with `R`
the directions of the changes of basis inside the heads and of the rescalings of the values. The
twins for one kind of block: `Residual/BlocksAloneAttention.lean`, `Residual/BlocksAloneMlp.lean`,
`Residual/BlocksAloneGated.lean`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ}

/-- **Lemma A.27 (Small writes), fourth value, for networks of attention blocks and MLP blocks
with `s = 0` for the hidden units, under the conditions of its proof:** let the network with
`E = D = I` and the blocks of `β` satisfy the conditions of the lemma on its two parts, and let a
token see itself and another token. For all small `τ ≠ 0`, the residual network without an
embedding and a readout has `fd(β_τ) = P − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`, with `P` the number of parameters
of the blocks. -/
theorem eventually_funDimBlocks_smallWrites_attentionMlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (β : BlockParams (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid))
    (hβa : SmallWritesGenericAttention β.toParams.sumFst)
    (hβm : SmallWritesGeneric β.toParams.sumSnd) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimBlocks (Arch.attentionMlp sees σ id H dh hid) 1 (β.smallWrites τ)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
        = Module.finrank ℝ
            (BlockParams (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid)) := by
  sorry

/-- **Lemma A.27, fourth value, at generic parameters, for networks of attention blocks and MLP
blocks with `s = 0` for the hidden units:** without normalization, with `d ≥ 2`, heads of width
`1 ≤ d_h ≤ d`, blocks of any widths and a token that sees itself and another token, at almost
every parameter of the blocks the residual network without an embedding and a readout has the
functional dimension `P − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDimBlocks_attentionMlp_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (BlockParams (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.attentionMlp sees σ id H dh hid) 1 β
        + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
      = Module.finrank ℝ
          (BlockParams (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid)) := by
  sorry

/-- **Lemma A.27 (Small writes), fourth value, for networks of attention blocks and gated blocks,
under the conditions of its proof:** as `eventually_funDimBlocks_smallWrites_attentionMlp`, with
`fd(β_τ) = P − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`: the changes of basis inside the heads and
the rescalings of the values of the gated units. -/
theorem eventually_funDimBlocks_smallWrites_attentionGated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (β : BlockParams (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid))
    (hβa : SmallWritesGenericAttention β.toParams.sumFst)
    (hβm : SmallWritesGenericGated β.toParams.sumSnd) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimBlocks (Arch.attentionGated sees σ id H dh hid) 1 (β.smallWrites τ)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ
            (BlockParams (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid)) := by
  sorry

/-- **Lemma A.27, fourth value, at generic parameters, for networks of attention blocks and gated
blocks:** without normalization, with `d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths
and a token that sees itself and another token, at almost every parameter of the blocks the
residual network without an embedding and a readout has the functional dimension
`P − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDimBlocks_attentionGated_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (BlockParams (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.attentionGated sees σ id H dh hid) 1 β
        + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ
          (BlockParams (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid)) := by
  sorry

/-! ### The four kinds of block -/

/-- **Lemma A.27, fourth value, at generic parameters, for attention blocks with `tanh`
blocks.** -/
theorem ae_funDimBlocks_attention_tanh_residual
    (μ : Measure (BlockParams (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.attentionMlp sees Real.tanh id H dh hid) 1 β
        + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
      = Module.finrank ℝ
          (BlockParams (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid)) :=
  ae_funDimBlocks_attentionMlp_residual hasDerivAt_tanh analyticOnNhd_tanh
    (tanh_unitsRigid _ _ _) μ hd hdh hdh0 t₁ t₂ h12 hs2 hs1

/-- **Lemma A.27, fourth value, at generic parameters, for attention blocks with GELU
blocks.** -/
theorem ae_funDimBlocks_attention_gelu_residual
    (μ : Measure (BlockParams (Arch.attentionMlp (T := T) (d := d) sees gelu id H dh hid)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.attentionMlp sees gelu id H dh hid) 1 β
        + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
      = Module.finrank ℝ
          (BlockParams (Arch.attentionMlp (T := T) (d := d) sees gelu id H dh hid)) :=
  ae_funDimBlocks_attentionMlp_residual hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_unitsRigid _ _ _) μ hd hdh hdh0 t₁ t₂ h12 hs2 hs1

/-- **Lemma A.27, fourth value, at generic parameters, for attention blocks with SwiGLU
blocks.** -/
theorem ae_funDimBlocks_attention_swiglu_residual
    (μ : Measure (BlockParams (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.attentionGated sees silu id H dh hid) 1 β
        + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ
          (BlockParams (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid)) :=
  ae_funDimBlocks_attentionGated_residual hasDerivAt_silu analyticOnNhd_silu
    (silu_gatedUnitsRescale _ _ _) μ hd hdh hdh0 t₁ t₂ h12 hs2 hs1

/-- **Lemma A.27, fourth value, at generic parameters, for attention blocks with GeGLU
blocks.** -/
theorem ae_funDimBlocks_attention_geglu_residual
    (μ : Measure (BlockParams (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.attentionGated sees gelu id H dh hid) 1 β
        + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ
          (BlockParams (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid)) :=
  ae_funDimBlocks_attentionGated_residual hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_gatedUnitsRescale _ _ _) μ hd hdh hdh0 t₁ t₂ h12 hs2 hs1

end Skips
