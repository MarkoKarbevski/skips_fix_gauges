import SkipsLean.Symmetry.InsideBlocksRMSNormZero
import SkipsLean.Dimension.UpperBoundTransformerRescale
import SkipsLean.Dimension.UpperBoundHomogeneousRMSNormZero

/-!
# The upper bounds under pre-RMSNorm with `ε = 0`, with the symmetries inside the blocks

Paper (skips paper), Theorem 4.2 (Upper bounds): "Let `G` be the group of changes of basis of one
hidden state, and `s` the dimension of the symmetries inside the blocks, the same with and without
skips. With or without pre-RMSNorm, at generic parameters, the functional dimension is at most
`P − (L + 1) dim G − s` without skips and at most `P − dim G − s` with identity skips." It is a
special case of Theorem A.17 (ii): "If in both networks the symmetries act locally freely at
generic parameters, the functional dimension at these parameters is at most
`P − (L + 1) dim G − s` without skips and `P − dim G − s` with them." Appendix A: "`G` is
`GL(d_model)` without normalization, `O(d_model)` under RMSNorm with `ε > 0`, and `CO(d_model)`,
the positive multiples of orthogonal matrices, under RMSNorm with `ε = 0`." So for `ε = 0`,
`dim G = d(d−1)/2 + 1`.

The library has these bounds for `ε = 0` for networks of MLP blocks without `s`
(`Dimension/UpperBoundRMSNormZero.lean`, `Dimension/UpperBoundResidualRMSNormZero.lean`), for
skipless gated blocks with the rescalings of the values (`Dimension/UpperBoundRMSNormZero.lean`)
and for residual ReLU, ReLU² and ReGLU blocks (`Residual/UpperBoundRescaleRMSNormZero.lean`). Here
the other kinds of network, each the twin for `ε = 0` of a statement for any `ε` that counts the
orthogonal changes of basis only (`Dimension/UpperBoundAttention.lean`,
`Residual/UpperBoundSymmetries.lean`, `Dimension/UpperBoundTransformer.lean`,
`Dimension/UpperBoundTransformerRescale.lean`), from the general bounds of
`Symmetry/InsideBlocksRMSNormZero.lean`:

* attention blocks, without skips and with identity skips, `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`;
* gated blocks with identity skips, `s = ∑_ℓ d_hidden,ℓ` (the rescalings of the values: SwiGLU,
  GeGLU);
* attention blocks and MLP blocks; attention blocks and gated blocks; attention blocks and MLP
  blocks with a positively homogeneous activation (ReLU, ReLU²); attention blocks and gated blocks
  with a positively homogeneous gate (ReGLU): without skips and with identity skips;
* skipless networks of ReLU, ReLU² or ReGLU blocks with `CO(d)` at every hidden state: the bound
  of Theorem A.17 (ii) as written, a consequence of the stronger bound of
  `Dimension/UpperBoundHomogeneousRMSNormZero.lean` (all of `GL(d)` at `h_0, …, h_{L−1}`).

At one parameter under the rank conditions of Lemma A.18 and at almost every parameter. The
functional dimension is Lean's `funDim` (all inputs; a zero row is normalized to `0`). Every
statement asks `d ≥ 1` (`[Nonempty d]`): the scaling of a hidden state is a direction only then.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

/-! ### Attention blocks -/

/-- **Theorem A.17 (ii) of the skips paper without skips for attention blocks, under pre-RMSNorm
with `ε = 0`, under the conditions of Lemma A.18:** `fd ≤ P − (L + 1) (d(d−1)/2 + 1) − 2 ∑_ℓ H_ℓ
d_{h,ℓ}²`. -/
theorem funDim_add_le_skipless_attention_rmsNorm_zero [Nonempty d]
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attention sees (rmsNorm 0) H dh) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut) := by
  -- `V`: the changes of basis inside the heads
  obtain ⟨V, hV', hrw, hdim⟩ := attn_part_ubt θ hQ hV
  have h := funDim_add_le_skipless_of_insideBlocks_rmsNorm_zero θ rfl V hV' hrw hE hw
  rwa [hdim] at h

/-- **Theorem A.17 (ii) of the skips paper with identity skips, for attention blocks, under
pre-RMSNorm with `ε = 0`:** `fd ≤ P − (d(d−1)/2 + 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_residual_attention_rmsNorm_zero [Nonempty d]
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attention sees (rmsNorm 0) H dh) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut) := by
  -- `V`: the changes of basis inside the heads
  obtain ⟨V, hV', -, hdim⟩ := attn_part_ubt θ hQ hV
  have h := funDim_add_le_residual_of_insideBlocks_rmsNorm_zero θ rfl V hV' hE
  rwa [hdim] at h

/-- **Theorem A.17 (ii) of the skips paper without skips for attention blocks at generic
parameters, under pre-RMSNorm with `ε = 0`.** -/
theorem ae_funDim_add_le_skipless_attention_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm 0) H dh) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut) := by
  classical
  -- the writes have `H_ℓ d_{h,ℓ} ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d
      ≤ Fintype.card ((Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh).w ℓ) :=
    fun ℓ => by
      show Fintype.card d ≤ Fintype.card (H ℓ × dh ℓ)
      rw [Fintype.card_prod]
      exact hH ℓ
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_uba μ hdh] with θ h1 h2
  exact funDim_add_le_skipless_attention_rmsNorm_zero θ h1.1 h1.2 h2.1 h2.2

/-- **Theorem A.17 (ii) of the skips paper with identity skips, for attention blocks at generic
parameters, under pre-RMSNorm with `ε = 0`.** -/
theorem ae_funDim_add_le_residual_attention_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm 0) H dh) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut) := by
  classical
  filter_upwards [ae_rank_E_ubt μ hdIn, ae_rank_QV_uba μ hdh] with θ h1 h2
  exact funDim_add_le_residual_attention_rmsNorm_zero θ h1 h2.1 h2.2

/-! ### Gated blocks with identity skips: the rescalings of the values -/

/-- **Theorem A.17 (ii) of the skips paper with identity skips for gated blocks, under pre-RMSNorm
with `ε = 0`:** `fd ≤ P − (d(d−1)/2 + 1) − s`. -/
theorem funDim_add_le_residual_gated_rmsNorm_zero [Nonempty d]
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  -- `V`: the rescalings of the values of the hidden units
  obtain ⟨V, hV', -, hdim⟩ := gated_part_ubt θ hv
  have h := funDim_add_le_residual_of_insideBlocks_rmsNorm_zero θ rfl V hV' hE
  rwa [hdim] at h

/-- Theorem A.17 (ii) of the skips paper with identity skips for gated blocks at generic parameters
(`d_in ≥ d`), under pre-RMSNorm with `ε = 0`. -/
theorem ae_funDim_add_le_residual_gated_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_ubt μ hdIn, ae_value_ne_zero μ] with θ h1 h2
  exact funDim_add_le_residual_gated_rmsNorm_zero θ h1 h2

/-! ### Attention blocks and MLP blocks -/

/-- **Theorem A.17 (ii) of the skips paper without skips for attention blocks and MLP blocks, under
pre-RMSNorm with `ε = 0`, under the conditions of Lemma A.18:** `fd ≤ P − (L + 1) (d(d−1)/2 + 1) −
2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_skipless_attentionMlp_rmsNorm_zero [Nonempty d]
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attentionMlp sees σ (rmsNorm 0) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut) := by
  -- `V_A`: the changes of basis inside the heads; `V_B = 0` for the MLP part
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubt θ.sumFst hQ hV
  have h := funDim_add_le_skipless_sum_of_insideBlocks_rmsNorm_zero θ rfl VA ⊥ hVA bot_le hrwA
    (fun η hη _ _ => by rw [(Submodule.mem_bot ℝ).1 hη]; rfl) hE hw
  rwa [hdimA, finrank_bot, add_zero] at h

/-- **Theorem A.17 (ii) of the skips paper with identity skips for attention blocks and MLP blocks,
under pre-RMSNorm with `ε = 0`, under the conditions of Lemma A.18:** `fd ≤ P − (d(d−1)/2 + 1) − 2
∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_residual_attentionMlp_rmsNorm_zero [Nonempty d]
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attentionMlp sees σ (rmsNorm 0) H dh hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut) := by
  -- `V_A`: the changes of basis inside the heads; `V_B = 0` for the MLP part
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubt θ.sumFst hQ hV
  have h := funDim_add_le_residual_sum_of_insideBlocks_rmsNorm_zero θ rfl VA ⊥ hVA bot_le hE
  rwa [hdimA, finrank_bot, add_zero] at h

/-- **Theorem A.17 (ii) of the skips paper without skips for attention blocks and MLP blocks, under
pre-RMSNorm with `ε = 0`, at generic parameters:** `fd ≤ P − (L + 1) (d(d−1)/2 + 1) − 2 ∑_ℓ H_ℓ
d_{h,ℓ}²`. -/
theorem ae_funDim_add_le_skipless_attentionMlp_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm 0) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut) := by
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  -- the pointwise bound holds wherever the rank conditions of Lemma A.18 hold
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubt μ hdh] with θ h1 h2
  exact funDim_add_le_skipless_attentionMlp_rmsNorm_zero θ h1.1 h1.2 h2.1 h2.2

/-- **Theorem A.17 (ii) of the skips paper with identity skips for attention blocks and MLP blocks,
under pre-RMSNorm with `ε = 0`, at generic parameters:** `fd ≤ P − (d(d−1)/2 + 1) − 2 ∑_ℓ H_ℓ
d_{h,ℓ}²`. -/
theorem ae_funDim_add_le_residual_attentionMlp_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm 0) H dh hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut) := by
  -- the pointwise bound holds wherever the rank conditions of Lemma A.18 hold
  filter_upwards [ae_rank_E_ubt μ hdIn, ae_rank_QV_ubt μ hdh] with θ h1 h2
  exact funDim_add_le_residual_attentionMlp_rmsNorm_zero θ h1 h2.1 h2.2

/-! ### Attention blocks and gated blocks -/

/-- **Theorem A.17 (ii) of the skips paper without skips for attention blocks and gated blocks,
under pre-RMSNorm with `ε = 0`, under the conditions of Lemma A.18:** `fd ≤ P − (L + 1) (d(d−1)/2 +
1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_skipless_attentionGated_rmsNorm_zero [Nonempty d]
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ (rmsNorm 0) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
        (Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut) := by
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the values
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubt θ.sumFst hQ hV
  obtain ⟨VB, hVB, hrwB, hdimB⟩ := gated_part_ubt θ.sumSnd hv
  have h := funDim_add_le_skipless_sum_of_insideBlocks_rmsNorm_zero θ rfl VA VB hVA hVB hrwA
    hrwB hE hw
  rwa [hdimA, hdimB] at h

/-- **Theorem A.17 (ii) of the skips paper with identity skips for attention blocks and gated
blocks, under pre-RMSNorm with `ε = 0`, under the conditions of Lemma A.18:** `fd ≤ P − (d(d−1)/2 +
1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_residual_attentionGated_rmsNorm_zero [Nonempty d]
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ (rmsNorm 0) H dh hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
        (Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut) := by
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the values
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubt θ.sumFst hQ hV
  obtain ⟨VB, hVB, hrwB, hdimB⟩ := gated_part_ubt θ.sumSnd hv
  have h := funDim_add_le_residual_sum_of_insideBlocks_rmsNorm_zero θ rfl VA VB hVA hVB hE
  rwa [hdimA, hdimB] at h

/-- **Theorem A.17 (ii) of the skips paper without skips for attention blocks and gated blocks,
under pre-RMSNorm with `ε = 0`, at generic parameters:** `fd ≤ P − (L + 1) (d(d−1)/2 + 1) − 2 ∑_ℓ
H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attentionGated_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm 0) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
        (Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut) := by
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  -- the pointwise bound holds wherever the rank conditions of Lemma A.18 hold
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubt μ hdh, ae_value_ne_zero_ubt μ]
    with θ h1 h2 h3
  exact funDim_add_le_skipless_attentionGated_rmsNorm_zero θ h1.1 h1.2 h2.1 h2.2 h3

/-- **Theorem A.17 (ii) of the skips paper with identity skips for attention blocks and gated
blocks, under pre-RMSNorm with `ε = 0`, at generic parameters:** `fd ≤ P − (d(d−1)/2 + 1) − 2 ∑_ℓ
H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attentionGated_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm 0) H dh hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
        (Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut) := by
  -- the pointwise bound holds wherever the rank conditions of Lemma A.18 hold
  filter_upwards [ae_rank_E_ubt μ hdIn, ae_rank_QV_ubt μ hdh, ae_value_ne_zero_ubt μ]
    with θ h1 h2 h3
  exact funDim_add_le_residual_attentionGated_rmsNorm_zero θ h1 h2.1 h2.2 h3

/-! ### Attention blocks and MLP blocks with a positively homogeneous activation -/

/-- **Theorem A.17 (ii) of the skips paper without skips for attention blocks and MLP blocks with a
positively homogeneous activation, under pre-RMSNorm with `ε = 0`, under the conditions of Lemma
A.18:** `fd ≤ P − (L + 1) (d(d−1)/2 + 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_skipless_attentionMlp_rescale_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hc : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a i) ≠ 0) :
    funDim (Arch.attentionMlp sees σ (rmsNorm 0) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut) := by
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the hidden units
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubr θ.sumFst hQ hV
  obtain ⟨VB, hVB, hrwB, hdimB⟩ := mlp_part_ubr hσ θ.sumSnd hc
  have h := funDim_add_le_skipless_sum_of_insideBlocks_rmsNorm_zero θ rfl VA VB hVA hVB hrwA
    hrwB hE hw
  rwa [hdimA, hdimB] at h

/-- **Theorem A.17 (ii) of the skips paper with identity skips for attention blocks and MLP blocks
with a positively homogeneous activation, under pre-RMSNorm with `ε = 0`, under the conditions of
Lemma A.18:** `fd ≤ P − (d(d−1)/2 + 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_residual_attentionMlp_rescale_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hc : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a i) ≠ 0) :
    funDim (Arch.attentionMlp sees σ (rmsNorm 0) H dh hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut) := by
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the hidden units
  obtain ⟨VA, hVA, -, hdimA⟩ := attn_part_ubr θ.sumFst hQ hV
  obtain ⟨VB, hVB, -, hdimB⟩ := mlp_part_ubr hσ θ.sumSnd hc
  have h := funDim_add_le_residual_sum_of_insideBlocks_rmsNorm_zero θ rfl VA VB hVA hVB hE
  rwa [hdimA, hdimB] at h

/-- **Theorem A.17 (ii) of the skips paper without skips for attention blocks and MLP blocks with a
positively homogeneous activation, under pre-RMSNorm with `ε = 0`, at generic parameters:** `fd ≤ P
− (L + 1) (d(d−1)/2 + 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attentionMlp_rescale_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm 0) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut) := by
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  -- the pointwise bound holds wherever the rank conditions of Lemma A.18 hold and no read
  -- column of a hidden unit vanishes
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3
  exact funDim_add_le_skipless_attentionMlp_rescale_rmsNorm_zero hσ θ h1.1 h1.2 h2.1 h2.2 h3

/-- **Theorem A.17 (ii) of the skips paper with identity skips for attention blocks and MLP blocks
with a positively homogeneous activation, under pre-RMSNorm with `ε = 0`, at generic parameters:**
`fd ≤ P − (d(d−1)/2 + 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attentionMlp_rescale_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm 0) H dh hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut) := by
  -- the pointwise bound holds wherever the rank conditions of Lemma A.18 hold and no read
  -- column of a hidden unit vanishes
  filter_upwards [ae_rank_E_ubr μ hdIn, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3
  exact funDim_add_le_residual_attentionMlp_rescale_rmsNorm_zero hσ θ h1 h2.1 h2.2 h3

/-! ### Attention blocks and ReLU blocks -/

/-- **Theorem A.17 (ii) of the skips paper without skips for attention blocks and ReLU blocks,
under pre-RMSNorm with `ε = 0`, at generic parameters:** `fd ≤ P − (L + 1) (d(d−1)/2 + 1) − 2 ∑_ℓ
H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attention_relu_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees relu (rmsNorm 0) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees relu (rmsNorm 0) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees relu (rmsNorm 0) H dh hid) dIn dOut) := by
  exact ae_funDim_add_le_skipless_attentionMlp_rescale_rmsNorm_zero relu_homogeneous μ hdIn hdh hW

/-- **Theorem A.17 (ii) of the skips paper with identity skips for attention blocks and ReLU
blocks, under pre-RMSNorm with `ε = 0`, at generic parameters:** `fd ≤ P − (d(d−1)/2 + 1) − 2 ∑_ℓ
H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attention_relu_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees relu (rmsNorm 0) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees relu (rmsNorm 0) H dh hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees relu (rmsNorm 0) H dh hid) dIn dOut) := by
  exact ae_funDim_add_le_residual_attentionMlp_rescale_rmsNorm_zero relu_homogeneous μ hdIn hdh

/-! ### Attention blocks and ReLU² blocks -/

/-- **Theorem A.17 (ii) of the skips paper without skips for attention blocks and ReLU² blocks,
under pre-RMSNorm with `ε = 0`, at generic parameters:** `fd ≤ P − (L + 1) (d(d−1)/2 + 1) − 2 ∑_ℓ
H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attention_reluSq_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees reluSq (rmsNorm 0) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees reluSq (rmsNorm 0) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees reluSq (rmsNorm 0) H dh hid) dIn dOut) := by
  exact ae_funDim_add_le_skipless_attentionMlp_rescale_rmsNorm_zero reluSq_homogeneous μ hdIn hdh hW

/-- **Theorem A.17 (ii) of the skips paper with identity skips for attention blocks and ReLU²
blocks, under pre-RMSNorm with `ε = 0`, at generic parameters:** `fd ≤ P − (d(d−1)/2 + 1) − 2 ∑_ℓ
H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attention_reluSq_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees reluSq (rmsNorm 0) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees reluSq (rmsNorm 0) H dh hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees reluSq (rmsNorm 0) H dh hid) dIn dOut) := by
  exact ae_funDim_add_le_residual_attentionMlp_rescale_rmsNorm_zero reluSq_homogeneous μ hdIn hdh

/-! ### Attention blocks and gated blocks with a positively homogeneous gate -/

/-- **Theorem A.17 (ii) of the skips paper without skips for attention blocks and gated blocks with
a positively homogeneous gate, under pre-RMSNorm with `ε = 0`, under the conditions of Lemma
A.18:** `fd ≤ P − (L + 1) (d(d−1)/2 + 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_skipless_attentionGated_rescale_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ (rmsNorm 0) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut) := by
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the values and gates
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubr θ.sumFst hQ hV
  obtain ⟨VB, hVB, hrwB, hdimB⟩ := gate_part_ubr hσ θ.sumSnd hv hg
  have h := funDim_add_le_skipless_sum_of_insideBlocks_rmsNorm_zero θ rfl VA VB hVA hVB hrwA
    hrwB hE hw
  rwa [hdimA, hdimB] at h

/-- **Theorem A.17 (ii) of the skips paper with identity skips for attention blocks and gated
blocks with a positively homogeneous gate, under pre-RMSNorm with `ε = 0`, under the conditions of
Lemma A.18:** `fd ≤ P − (d(d−1)/2 + 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_residual_attentionGated_rescale_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ (rmsNorm 0) H dh hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut) := by
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the values and gates
  obtain ⟨VA, hVA, -, hdimA⟩ := attn_part_ubr θ.sumFst hQ hV
  obtain ⟨VB, hVB, -, hdimB⟩ := gate_part_ubr hσ θ.sumSnd hv hg
  have h := funDim_add_le_residual_sum_of_insideBlocks_rmsNorm_zero θ rfl VA VB hVA hVB hE
  rwa [hdimA, hdimB] at h

/-- **Theorem A.17 (ii) of the skips paper without skips for attention blocks and gated blocks with
a positively homogeneous gate, under pre-RMSNorm with `ε = 0`, at generic parameters:** `fd ≤ P −
(L + 1) (d(d−1)/2 + 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attentionGated_rescale_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm 0) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut) := by
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  -- the pointwise bound holds wherever the rank conditions of Lemma A.18 hold and no read
  -- column of a hidden unit vanishes
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3
  exact funDim_add_le_skipless_attentionGated_rescale_rmsNorm_zero hσ θ h1.1 h1.2 h2.1 h2.2
    (fun ℓ i => h3 ℓ (Sum.inr i)) (fun ℓ i => h3 ℓ (Sum.inl i))

/-- **Theorem A.17 (ii) of the skips paper with identity skips for attention blocks and gated
blocks with a positively homogeneous gate, under pre-RMSNorm with `ε = 0`, at generic parameters:**
`fd ≤ P − (d(d−1)/2 + 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attentionGated_rescale_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm 0) H dh hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm 0) H dh hid) dIn dOut) := by
  -- the pointwise bound holds wherever the rank conditions of Lemma A.18 hold and no read
  -- column of a hidden unit vanishes
  filter_upwards [ae_rank_E_ubr μ hdIn, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3
  exact funDim_add_le_residual_attentionGated_rescale_rmsNorm_zero hσ θ h1 h2.1 h2.2
    (fun ℓ i => h3 ℓ (Sum.inr i)) (fun ℓ i => h3 ℓ (Sum.inl i))

/-! ### Attention blocks and ReGLU blocks -/

/-- **Theorem A.17 (ii) of the skips paper without skips for attention blocks and ReGLU blocks,
under pre-RMSNorm with `ε = 0`, at generic parameters:** `fd ≤ P − (L + 1) (d(d−1)/2 + 1) − 2 ∑_ℓ
H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attention_reglu_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees relu (rmsNorm 0) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees relu (rmsNorm 0) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees relu (rmsNorm 0) H dh hid) dIn dOut) := by
  exact ae_funDim_add_le_skipless_attentionGated_rescale_rmsNorm_zero relu_homogeneous μ hdIn hdh hW

/-- **Theorem A.17 (ii) of the skips paper with identity skips for attention blocks and ReGLU
blocks, under pre-RMSNorm with `ε = 0`, at generic parameters:** `fd ≤ P − (d(d−1)/2 + 1) − 2 ∑_ℓ
H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attention_reglu_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees relu (rmsNorm 0) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees relu (rmsNorm 0) H dh hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees relu (rmsNorm 0) H dh hid) dIn dOut) := by
  exact ae_funDim_add_le_residual_attentionGated_rescale_rmsNorm_zero relu_homogeneous μ hdIn hdh

/-! ### Skipless ReLU, ReLU² and ReGLU blocks: the bound of Theorem A.17 (ii) as written -/

/-- Helper: `n(n−1)/2 + 1 ≤ n²` for `n ≥ 1` (`dim CO(d) ≤ dim GL(d)`). -/
private theorem co_le_sq_usz (n : ℕ) (hn : 1 ≤ n) : n * (n - 1) / 2 + 1 ≤ n ^ 2 := by
  have h1 : n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ _
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h2 : (1 + m) * (1 + m - 1) = (1 + m) * m := by rw [Nat.add_sub_cancel_left]
  nlinarith [h1, h2]

/-- Helper: `(L + 1) (q + 1) ≤ L n² + (q + 1)` for `q = n(n−1)/2`, `n ≥ 1`. -/
private theorem co_count_le_usz (L n : ℕ) (hn : 1 ≤ n) :
    (L + 1) * (n * (n - 1) / 2 + 1) ≤ L * n ^ 2 + (n * (n - 1) / 2 + 1) := by
  have h := Nat.mul_le_mul_left L (co_le_sq_usz n hn)
  linarith [h, Nat.succ_mul L (n * (n - 1) / 2 + 1)]

/-- **Theorem A.17 (ii) of the skips paper without skips for `ε = 0`, for MLP blocks with a
positively homogeneous activation, under the conditions of Lemma A.18:** `fd ≤ P − (L + 1)
(d(d−1)/2 + 1) − ∑_ℓ d_hidden,ℓ`. A consequence of the stronger bound
`funDim_add_le_skipless_mlp_rescale_rmsNorm_zero`. -/
theorem funDim_add_le_skipless_mlp_rescale_rmsNorm_zero_co [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ (rmsNorm 0) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  have h := funDim_add_le_skipless_mlp_rescale_rmsNorm_zero hσ θ hE hw hc
  have h2 := co_count_le_usz L (Fintype.card d) Fintype.card_pos
  omega

/-- **Theorem A.17 (ii) of the skips paper without skips for `ε = 0`, for gated blocks with a
positively homogeneous gate, under the conditions of Lemma A.18:** `fd ≤ P − (L + 1)
(d(d−1)/2 + 1) − 2 ∑_ℓ d_hidden,ℓ`. A consequence of the stronger bound
`funDim_add_le_skipless_gated_gate_rmsNorm_zero`. -/
theorem funDim_add_le_skipless_gated_gate_rmsNorm_zero_co [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm 0) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  have h := funDim_add_le_skipless_gated_gate_rmsNorm_zero hσ θ hE hw hv hg
  have h2 := co_count_le_usz L (Fintype.card d) Fintype.card_pos
  omega

/-- **Theorem A.17 (ii) of the skips paper without skips for `ε = 0`, for ReLU blocks of width at
least `d` at generic parameters** (`d_in ≥ d`):
`fd ≤ P − (L + 1) (d(d−1)/2 + 1) − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_relu_rmsNorm_zero_co [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_funDim_add_le_skipless_relu_rmsNorm_zero μ hdIn hhid] with θ h
  have h2 := co_count_le_usz L (Fintype.card d) Fintype.card_pos
  omega

/-- **The same for ReLU² blocks.** -/
theorem ae_funDim_add_le_skipless_reluSq_rmsNorm_zero_co [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_funDim_add_le_skipless_reluSq_rmsNorm_zero μ hdIn hhid] with θ h
  have h2 := co_count_le_usz L (Fintype.card d) Fintype.card_pos
  omega

/-- **The same for ReGLU blocks,** `s = 2 ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_reglu_rmsNorm_zero_co [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm 0) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_funDim_add_le_skipless_reglu_rmsNorm_zero μ hdIn hhid] with θ h
  have h2 := co_count_le_usz L (Fintype.card d) Fintype.card_pos
  omega

end Skips
