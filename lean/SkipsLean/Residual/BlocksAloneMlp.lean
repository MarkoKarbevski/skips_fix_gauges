import SkipsLean.Residual.BlocksAloneGeneral
import SkipsLean.Residual.DepthMlp

/-!
# Residual networks of MLP blocks without an embedding and a readout

Paper (skips paper), Lemma A.27, fourth value: "`fd(θ_τ) = P − s` (no embedding, readout, biases
or normalization)", for tanh and GELU blocks, where `s = 0`. The proof of Theorem A.28 (i) and
(ii) uses it in this form: "a network of GELU blocks without an embedding and a readout has
functional dimension `P`."

Here, for `Arch.mlp σ id hid` with an activation that has the conclusion of Lemma B.3 with `s = 0`
(`UnitsRigid`; tanh and GELU), blocks of any widths, `d ≥ 2`, and the network without an embedding
and a readout of `Residual/BlocksAlone.lean`:

* `eventually_funDimBlocks_smallWrites_mlp`: the fourth value under the conditions of the proof of
  the lemma, at `E = D = I` (`SmallWritesGeneric β.toParams`): `fd(β_τ) = P` for all small
  `τ ≠ 0`, with `P` the number of parameters of the blocks;
* `ae_funDimBlocks_mlp_residual`: `fd = P` at almost every parameter of the blocks (as Theorem 4.7
  follows from the first value: the outputs are real-analytic in the parameters);
* `ae_funDimBlocks_tanh_residual`, `ae_funDimBlocks_gelu_residual`: the two kinds of block.

The twin for attention blocks is `Residual/BlocksAloneAttention.lean` (Corollary 4.10 (ii)), for
gated blocks `Residual/BlocksAloneGated.lean`. Numeric check:
`blocks_alone_mlp_check_2026-11-25.py`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **Lemma A.27 (Small writes), fourth value, for MLP blocks with `s = 0`, under the conditions
of its proof:** let the network with `E = D = I` and the blocks of `β` satisfy the conditions of
the lemma. For all small `τ ≠ 0`, the residual network without an embedding and a readout has
`fd(β_τ) = P`, the number of parameters of the blocks. -/
theorem eventually_funDimBlocks_smallWrites_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (β : BlockParams (Arch.mlp (T := T) (d := d) σ id hid))
    (hβ : SmallWritesGeneric β.toParams) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimBlocks (Arch.mlp σ id hid) 1 (β.smallWrites τ)
        = Module.finrank ℝ (BlockParams (Arch.mlp (T := T) (d := d) σ id hid)) := by
  -- `(β_τ).toParams` is `(β.toParams)_τ`, and `fd + d² = P` there (first value)
  filter_upwards [eventually_funDim_smallWrites_mlp hσ hσa hU β.toParams hβ] with τ hτ
  -- no symmetry inside the blocks: `R = 0`
  have h := funDimBlocks_add_finrank_eq_of_funDim_toParams
    (A := Arch.mlp (T := T) (d := d) σ id hid) rfl
    (fun ℓ => differentiable_f_mlp (fun z => (hσ z).differentiableAt) ℓ) (β.smallWrites τ) ⊥
    (fun η hη => by
      rw [(Submodule.mem_bot ℝ).1 hη, map_zero]
      exact Submodule.zero_mem _)
    (by
      rw [finrank_bot, add_zero]
      exact hτ)
  rwa [finrank_bot, add_zero] at h

/-- **Lemma A.27, fourth value, at generic parameters, for MLP blocks with `s = 0`** ("a network
of GELU blocks without an embedding and a readout has functional dimension `P`"): without
normalization, with `d ≥ 2` and `L` blocks of any widths, at almost every parameter of the blocks
the residual network without an embedding and a readout has the functional dimension `P`, the
number of parameters of the blocks. -/
theorem ae_funDimBlocks_mlp_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (BlockParams (Arch.mlp (T := T) (d := d) σ id hid))) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.mlp σ id hid) 1 β
      = Module.finrank ℝ (BlockParams (Arch.mlp (T := T) (d := d) σ id hid)) := by
  sorry

/-- **Lemma A.27, fourth value, at generic parameters, for `tanh` blocks.** -/
theorem ae_funDimBlocks_tanh_residual
    (μ : Measure (BlockParams (Arch.mlp (T := T) (d := d) Real.tanh id hid)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.mlp Real.tanh id hid) 1 β
      = Module.finrank ℝ (BlockParams (Arch.mlp (T := T) (d := d) Real.tanh id hid)) :=
  ae_funDimBlocks_mlp_residual hasDerivAt_tanh analyticOnNhd_tanh (tanh_unitsRigid _ _ _) μ hd

/-- **Lemma A.27, fourth value, at generic parameters, for GELU blocks** ("a network of GELU
blocks without an embedding and a readout has functional dimension `P`"). -/
theorem ae_funDimBlocks_gelu_residual
    (μ : Measure (BlockParams (Arch.mlp (T := T) (d := d) gelu id hid)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.mlp gelu id hid) 1 β
      = Module.finrank ℝ (BlockParams (Arch.mlp (T := T) (d := d) gelu id hid)) :=
  ae_funDimBlocks_mlp_residual hasDerivAt_gelu analyticOnNhd_gelu (gelu_unitsRigid _ _ _) μ hd

end Skips
