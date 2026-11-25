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

omit [Fintype T] [Nonempty T] in
/-- Helper: if a network `θ` with `d_in = d_out = d` satisfies the conditions of Lemma A.27, so
does the network with `E = D = I` and the blocks `(E W_read^ℓ, W_write^ℓ D)` of `θ`: `E = D = I`
have rank `d`, the rows of `(W_write^ℓ D) I` and the columns of `I (E W_read^ℓ)` are those of
`θ`. -/
private theorem smallWritesGeneric_blocksOf_bam
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) d d) (hθ : SmallWritesGeneric θ) :
    SmallWritesGeneric (BlockParams.toParams
      (⟨0, fun ℓ => θ.E * θ.read ℓ, fun ℓ => θ.write ℓ * θ.D, 0⟩ :
        BlockParams (Arch.mlp (T := T) (d := d) σ id hid))) where
  rank_E := by
    show (1 : Matrix d d ℝ).rank = _
    exact Matrix.rank_one
  rank_D := by
    show (1 : Matrix d d ℝ).rank = _
    exact Matrix.rank_one
  row_ne_zero ℓ i := by
    show (θ.write ℓ * θ.D * (1 : Matrix d d ℝ)) i ≠ 0
    rw [Matrix.mul_one]
    exact hθ.row_ne_zero ℓ i
  col_ne_zero ℓ i := by
    show ((1 : Matrix d d ℝ) * (θ.E * θ.read ℓ))ᵀ i ≠ 0
    rw [Matrix.one_mul]
    exact hθ.col_ne_zero ℓ i
  col_not_collinear p q hpq r := by
    show ((1 : Matrix d d ℝ) * (θ.E * θ.read p.1))ᵀ p.2
      ≠ r • ((1 : Matrix d d ℝ) * (θ.E * θ.read q.1))ᵀ q.2
    rw [Matrix.one_mul, Matrix.one_mul]
    exact hθ.col_not_collinear p q hpq r

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
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ id hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp hσa ℓ
  -- one network `θ₀` with `d_in = d_out = d` and the conditions of Lemma A.27
  obtain ⟨θ₀, hθ₀⟩ := (ae_smallWritesGeneric
    (Measure.addHaar : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) d d))
    hd le_rfl le_rfl).exists
  -- the blocks `β₀ = (E W_read, W_write D)` and one small `τ ≠ 0`: `fd(β₀_τ) = P`
  obtain ⟨τ, hτ⟩ := (eventually_funDimBlocks_smallWrites_mlp hσ hσa hU
    (⟨0, fun ℓ => θ₀.E * θ₀.read ℓ, fun ℓ => θ₀.write ℓ * θ₀.D, 0⟩ :
      BlockParams (Arch.mlp (T := T) (d := d) σ id hid))
    (smallWritesGeneric_blocksOf_bam θ₀ hθ₀)).exists
  -- `≥`: at almost every `β`, `fd(β) ≥ fd(β₀_τ)` (the outputs are analytic)
  filter_upwards [ae_funDimBlocks_ge (Arch.mlp σ id hid) 1 hf analyticOnNhd_id μ
    ((⟨0, fun ℓ => θ₀.E * θ₀.read ℓ, fun ℓ => θ₀.write ℓ * θ₀.D, 0⟩ :
      BlockParams (Arch.mlp (T := T) (d := d) σ id hid)).smallWrites τ)] with β h1
  -- `≤`: `fd(β) ≤ P`, on a batch that attains it
  obtain ⟨m, Y, hY⟩ := exists_jacobianRankBlocks_eq_funDimBlocks (S := 1) β
  have hup := jacobianRankBlocks_le_finrank (S := 1) Y β
  omega

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
