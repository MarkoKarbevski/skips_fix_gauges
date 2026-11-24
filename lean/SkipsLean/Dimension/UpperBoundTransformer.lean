import SkipsLean.Symmetry.InsideBlocksSum
import SkipsLean.Symmetry.InsideBlocksKinds
import SkipsLean.Network.Transformer
import SkipsLean.Dimension.UpperBoundAttention
import SkipsLean.Generic.Gated

/-!
# The upper bounds for networks of attention blocks and MLP blocks

Papers. Skips paper, Theorem 4.2 (Upper bounds): "Let `G` be the group of changes of basis of one
hidden state, and `s` the dimension of the symmetries inside the blocks, the same with and without
skips. With or without pre-RMSNorm, at generic parameters, the functional dimension is at most
`P − (L + 1) dim G − s` without skips and at most `P − dim G − s` with identity skips." Dimension
paper, Theorem 4.3 and Lemma B.1. Section 2 of the skips paper: "A transformer layer has two
blocks, its attention and MLP sub-layers".

Here for the networks of `Network/Transformer.lean`, whose blocks are attention blocks and MLP
blocks (`Arch.attentionMlp`), or attention blocks and gated blocks (`Arch.attentionGated`), in any
order (a block may also have heads and hidden units side by side):

* attention and MLP blocks, any activation `σ`: `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`, the changes of basis
  inside the heads (for tanh and GELU blocks the hidden units add nothing to `s`; for ReLU and
  ReLU² blocks the rescalings of the hidden units are not counted here, so the bound is not the
  paper's for them);
* attention and gated blocks, any gate activation `σ`:
  `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}² + ∑_ℓ d_hidden,ℓ`, with the rescalings of the values of the gated units
  (for a ReGLU block the rescalings of the gates are not counted here).

At one parameter under the rank conditions of Lemma B.1 (stated on the two parts
`θ.sumFst`, `θ.sumSnd` of the parameters, `Symmetry/InsideBlocksSum.lean`), and at almost every
parameter: `d_in ≥ d`, heads of width `d_h ≤ d`, and, without skips, blocks of total width
`H d_h + d_hidden ≥ d`. Under pre-RMSNorm (any `ε`) `dim G = d(d−1)/2`. The twins for networks
of one kind of block: `Dimension/UpperBoundAttention.lean`, `Generic/Params.lean`,
`Generic/Gated.lean`, `Residual/UpperBoundSymmetries.lean`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}


/-! ### Attention blocks and MLP blocks -/

/-- **Theorem 4.3 of the dimension paper for attention blocks and MLP blocks, without
normalization, under the conditions of Lemma B.1:**
`fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_skipless_attentionMlp
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attentionMlp sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and MLP blocks, under pre-RMSNorm,
under the conditions of Lemma B.1:**
`fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_skipless_attentionMlp_rmsNorm (ε : ℝ)
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and MLP blocks,
without normalization, under the conditions of Lemma B.1:**
`fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_residual_attentionMlp
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and MLP blocks,
under pre-RMSNorm, under the conditions of Lemma B.1:**
`fd ≤ P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_residual_attentionMlp_rmsNorm (ε : ℝ)
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and MLP blocks, without
normalization, at generic parameters:**
`fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_add_le_skipless_attentionMlp
    (μ : Measure (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and MLP blocks, under pre-RMSNorm,
at generic parameters:**
`fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_add_le_skipless_attentionMlp_rmsNorm (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and MLP blocks,
without normalization, at generic parameters:**
`fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_add_le_residual_attentionMlp
    (μ : Measure (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and MLP blocks,
under pre-RMSNorm, at generic parameters:**
`fd ≤ P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_add_le_residual_attentionMlp_rmsNorm (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry


/-! ### Attention blocks and gated blocks -/

/-- **Theorem 4.3 of the dimension paper for attention blocks and gated blocks, without
normalization, under the conditions of Lemma B.1:**
`fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_skipless_attentionGated
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
          (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and gated blocks, under pre-RMSNorm,
under the conditions of Lemma B.1:**
`fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_skipless_attentionGated_rmsNorm (ε : ℝ)
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
        (Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and gated blocks,
without normalization, under the conditions of Lemma B.1:**
`fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_residual_attentionGated
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
          (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and gated blocks,
under pre-RMSNorm, under the conditions of Lemma B.1:**
`fd ≤ P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_residual_attentionGated_rmsNorm (ε : ℝ)
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
        (Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and gated blocks, without
normalization, at generic parameters:**
`fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attentionGated [Nonempty d]
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
          (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and gated blocks, under pre-RMSNorm,
at generic parameters:**
`fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attentionGated_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
        (Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and gated blocks,
without normalization, at generic parameters:**
`fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attentionGated [Nonempty d]
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
          (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and gated blocks,
under pre-RMSNorm, at generic parameters:**
`fd ≤ P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attentionGated_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
        (Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

end Skips
