import SkipsLean.Residual.BlocksAloneGeneral
import SkipsLean.Residual.DepthGated

/-!
# Residual networks of gated blocks without an embedding and a readout

Paper (skips paper), Lemma A.27, fourth value: "`fd(θ_τ) = P − s` (no embedding, readout, biases
or normalization)", for SwiGLU and GeGLU blocks, where `s` is the number of hidden units ("`s`
counts the changes of basis inside the heads and the rescalings of the values of gated units").
Its proof: "Without an embedding and a readout, `M = I` is fixed, so `ψ_M = 0` for every
direction, and the flat directions are the rescalings alone, of dimension `s`."

Here, for `Arch.gated σ id hid` with a gate activation that has the conclusion of Lemma B.3 for
gated units (`GatedUnitsRescale`; SiLU and GELU), blocks of any widths, `d ≥ 2`, and the network
without an embedding and a readout of `Residual/BlocksAlone.lean`:

* `eventually_funDimBlocks_smallWrites_gated`: the fourth value under the conditions of the proof
  of the lemma, at `E = D = I` (`SmallWritesGenericGated β.toParams`);
* `ae_funDimBlocks_gated_residual`: `fd = P − s` at almost every parameter of the blocks;
* `ae_funDimBlocks_swiglu_residual`, `ae_funDimBlocks_geglu_residual`: the two kinds of block.

The twins: `Residual/BlocksAloneMlp.lean` (tanh and GELU blocks),
`Residual/BlocksAloneAttention.lean` (attention blocks). Numeric check:
`blocks_alone_mlp_check_2026-11-25.py`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **Lemma A.27 (Small writes), fourth value, for gated blocks, under the conditions of its
proof:** let the network with `E = D = I` and the blocks of `β` satisfy the conditions of the
lemma. For all small `τ ≠ 0`, the residual network without an embedding and a readout has
`fd(β_τ) = P − s`, with `P` the number of parameters of the blocks and `s` the number of hidden
units. -/
theorem eventually_funDimBlocks_smallWrites_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (β : BlockParams (Arch.gated (T := T) (d := d) σ id hid))
    (hβ : SmallWritesGenericGated β.toParams) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimBlocks (Arch.gated σ id hid) 1 (β.smallWrites τ) + ∑ ℓ, Fintype.card (hid ℓ)
        = Module.finrank ℝ (BlockParams (Arch.gated (T := T) (d := d) σ id hid)) := by
  sorry

/-- **Lemma A.27, fourth value, at generic parameters, for gated blocks:** without normalization,
with `d ≥ 2` and `L` blocks of any widths, at almost every parameter of the blocks the residual
network without an embedding and a readout has the functional dimension `P − s`, with `P` the
number of parameters of the blocks and `s` the number of hidden units. -/
theorem ae_funDimBlocks_gated_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (BlockParams (Arch.gated (T := T) (d := d) σ id hid))) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.gated σ id hid) 1 β + ∑ ℓ, Fintype.card (hid ℓ)
      = Module.finrank ℝ (BlockParams (Arch.gated (T := T) (d := d) σ id hid)) := by
  sorry

/-- **Lemma A.27, fourth value, at generic parameters, for SwiGLU blocks.** -/
theorem ae_funDimBlocks_swiglu_residual
    (μ : Measure (BlockParams (Arch.gated (T := T) (d := d) silu id hid)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.gated silu id hid) 1 β + ∑ ℓ, Fintype.card (hid ℓ)
      = Module.finrank ℝ (BlockParams (Arch.gated (T := T) (d := d) silu id hid)) :=
  ae_funDimBlocks_gated_residual hasDerivAt_silu analyticOnNhd_silu
    (silu_gatedUnitsRescale _ _ _) μ hd

/-- **Lemma A.27, fourth value, at generic parameters, for GeGLU blocks.** -/
theorem ae_funDimBlocks_geglu_residual
    (μ : Measure (BlockParams (Arch.gated (T := T) (d := d) gelu id hid)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.gated gelu id hid) 1 β + ∑ ℓ, Fintype.card (hid ℓ)
      = Module.finrank ℝ (BlockParams (Arch.gated (T := T) (d := d) gelu id hid)) :=
  ae_funDimBlocks_gated_residual hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_gatedUnitsRescale _ _ _) μ hd

end Skips
