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

/-- Helper (as `valueRescaleLin` of `Residual/UpperBoundSymmetries.lean`): `α ↦ rescaleDir θ α` is
linear. -/
private noncomputable def rescaleDirLin_bgt {dIn dOut : Type*} {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  toFun := rescaleDir θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext a j
      cases j with
      | inl i => simp [rescaleDir]
      | inr i =>
        simp only [rescaleDir, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply,
          Sum.elim_inr]
        ring
    · intro ℓ
      ext i a
      simp [rescaleDir, add_mul]
    · simp [rescaleDir]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext a j
      cases j <;> simp [rescaleDir, mul_assoc]
    · intro ℓ
      ext i a
      simp [rescaleDir, mul_assoc]
    · simp [rescaleDir]

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper (as `valueRescaleLin_injective`): if no value column of a read vanishes,
`α ↦ rescaleDir θ α` is injective: the value column `e_i` moves by `-α_i e_i`. -/
private theorem rescaleDirLin_injective_bgt {dIn dOut : Type*}
    {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0) :
    Function.Injective (rescaleDirLin_bgt θ) := by
  intro α α' h
  have h' : rescaleDir θ α = rescaleDir θ α' := h
  funext ℓ i
  -- an entry `a` with `e_i a ≠ 0`
  obtain ⟨a, ha⟩ := Function.ne_iff.mp (hv ℓ i)
  have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h') a) (Sum.inr i)
  change -(α ℓ i) * θ.read ℓ a (Sum.inr i) = -(α' ℓ i) * θ.read ℓ a (Sum.inr i) at hr
  exact neg_inj.mp (mul_right_cancel₀ ha hr)

/-- Helper: the numbers of the rescalings of the hidden units form a space of dimension `s`, the
number of hidden units. -/
private theorem finrank_hidFun_bgt :
    Module.finrank ℝ (∀ ℓ, hid ℓ → ℝ) = ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]

omit [Nonempty T] in
/-- Helper: the rescalings at the blocks, `R(β) = {rescaleDir β α}`, are flat for the residual
network at `β.toParams`: `blockDir A (rescaleDir β α) = rescaleDir β.toParams α`. -/
private theorem rescaleDir_mem_flat_bgt
    (β : BlockParams (Arch.gated (T := T) (d := d) σ id hid)) :
    ∀ η ∈ LinearMap.range (rescaleDirLin_bgt β),
      blockDir _ η ∈ flat (Arch.gated σ id hid) 1 β.toParams := by
  rintro _ ⟨α, rfl⟩
  exact rescaleDir_mem_flat' β.toParams 1 α

omit [Fintype T] [Nonempty T] in
/-- Helper: if a network `θ` with `d_in = d_out = d` satisfies the conditions of Lemma A.27, so
does the network with `E = D = I` and the blocks `(E W_read^ℓ, W_write^ℓ D)` of `θ`: `E = D = I`
have rank `d`, the rows of `(W_write^ℓ D) I` and the columns of `I (E W_read^ℓ)` are those of
`θ`. -/
private theorem smallWritesGenericGated_blocksOf_bgt
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) d d) (hθ : SmallWritesGenericGated θ) :
    SmallWritesGenericGated (BlockParams.toParams
      (⟨0, fun ℓ => θ.E * θ.read ℓ, fun ℓ => θ.write ℓ * θ.D, 0⟩ :
        BlockParams (Arch.gated (T := T) (d := d) σ id hid))) where
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
  gate_ne_zero ℓ i := by
    show ((1 : Matrix d d ℝ) * (θ.E * θ.read ℓ))ᵀ (Sum.inl i) ≠ 0
    rw [Matrix.one_mul]
    exact hθ.gate_ne_zero ℓ i
  gate_not_collinear p q hpq r := by
    show ((1 : Matrix d d ℝ) * (θ.E * θ.read p.1))ᵀ (Sum.inl p.2)
      ≠ r • ((1 : Matrix d d ℝ) * (θ.E * θ.read q.1))ᵀ (Sum.inl q.2)
    rw [Matrix.one_mul, Matrix.one_mul]
    exact hθ.gate_not_collinear p q hpq r
  value_ne_zero ℓ i := by
    show ((1 : Matrix d d ℝ) * (θ.E * θ.read ℓ))ᵀ (Sum.inr i) ≠ 0
    rw [Matrix.one_mul]
    exact hθ.value_ne_zero ℓ i

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
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  -- `(β_τ).toParams` is `(β.toParams)_τ`, and `fd + d² + s = P` there (first value)
  filter_upwards [eventually_funDim_smallWrites_gated hσ hσa hU β.toParams hβ] with τ hτ
  -- the value columns of `β_τ` (those of `β`, the columns of `I W_read^ℓ`) are nonzero, so the
  -- rescalings at `β_τ` form a space `R` of dimension `s`
  have hv : ∀ ℓ i, (fun a => (β.smallWrites τ).read ℓ a (Sum.inr i)) ≠ 0 := fun ℓ i h0 => by
    apply hβ.value_ne_zero ℓ i
    show ((1 : Matrix d d ℝ) * β.read ℓ)ᵀ (Sum.inr i) = 0
    rw [Matrix.one_mul]
    exact h0
  have hdim : Module.finrank ℝ (LinearMap.range (rescaleDirLin_bgt (β.smallWrites τ)))
      = ∑ ℓ, Fintype.card (hid ℓ) := by
    rw [LinearMap.finrank_range_of_inj (rescaleDirLin_injective_bgt _ hv), finrank_hidFun_bgt]
  -- the fourth value from the first, with `R` the rescalings
  have h := funDimBlocks_add_finrank_eq_of_funDim_toParams
    (A := Arch.gated (T := T) (d := d) σ id hid) rfl (fun ℓ => differentiable_f_gated hσd ℓ)
    (β.smallWrites τ) _ (rescaleDir_mem_flat_bgt (β.smallWrites τ)) (by rw [hdim]; exact hτ)
  rwa [hdim] at h

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
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  -- one network `θ₀` with `d_in = d_out = d` and the conditions of Lemma A.27
  obtain ⟨θ₀, hθ₀⟩ := (ae_smallWritesGenericGated
    (Measure.addHaar : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) d d))
    hd le_rfl le_rfl).exists
  -- the blocks `β₀ = (E W_read, W_write D)` and one small `τ ≠ 0`: `fd(β₀_τ) = P - s`
  obtain ⟨τ, hτ⟩ := (eventually_funDimBlocks_smallWrites_gated hσ hσa hU
    (⟨0, fun ℓ => θ₀.E * θ₀.read ℓ, fun ℓ => θ₀.write ℓ * θ₀.D, 0⟩ :
      BlockParams (Arch.gated (T := T) (d := d) σ id hid))
    (smallWritesGenericGated_blocksOf_bgt θ₀ hθ₀)).exists
  -- `≥`: at almost every `β`, `fd(β) ≥ fd(β₀_τ)` (the outputs are analytic); and no value column
  -- of a read of `β` is zero
  filter_upwards [ae_funDimBlocks_ge (Arch.gated σ id hid) 1
    (fun ℓ => analyticOnNhd_f_gated hσa ℓ) analyticOnNhd_id μ
    ((⟨0, fun ℓ => θ₀.E * θ₀.read ℓ, fun ℓ => θ₀.write ℓ * θ₀.D, 0⟩ :
      BlockParams (Arch.gated (T := T) (d := d) σ id hid)).smallWrites τ),
    ae_value_ne_zero μ] with β h1 h2
  -- `≤`: the rescalings at `β`, of dimension `s`, are in the kernel on a batch attaining `fd(β)`
  obtain ⟨m, Y, hY⟩ := exists_jacobianRankBlocks_eq_funDimBlocks (S := 1) β
  have hup := jacobianRankBlocks_add_finrank_le (A := Arch.gated (T := T) (d := d) σ id hid) rfl
    (fun ℓ => differentiable_f_gated hσd ℓ) β _ (rescaleDir_mem_flat_bgt β) Y
  rw [LinearMap.finrank_range_of_inj (rescaleDirLin_injective_bgt β h2), finrank_hidFun_bgt]
    at hup
  omega

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
