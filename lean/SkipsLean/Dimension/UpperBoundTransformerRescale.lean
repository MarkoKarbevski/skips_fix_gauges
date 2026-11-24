import SkipsLean.Dimension.UpperBoundTransformer
import SkipsLean.Dimension.RescalingMlp
import SkipsLean.Dimension.RescalingGate

/-!
# The upper bounds for networks of attention blocks and ReLU, ReLU² or ReGLU blocks

Papers. Skips paper, Section 4.1: the symmetries inside the blocks are "the rescaling of a hidden
unit of a ReLU or ReLU² block, the rescaling of the value of a hidden unit of a gated block, and
the changes of basis inside an attention head"; Theorem 4.2 (Upper bounds): "at generic
parameters, the functional dimension is at most `P − (L + 1) dim G − s` without skips and at most
`P − dim G − s` with identity skips." Dimension paper, Theorem 4.3 and Appendix B ("ReGLU, in
addition": the rescaling of the gate of a hidden unit).

`Dimension/UpperBoundTransformer.lean` has these bounds for networks of attention blocks and MLP
blocks or gated blocks, with the changes of basis inside the heads and the rescalings of the
values of gated units. Here the rescalings of positively homogeneous units are added:

* the rescalings of the hidden units of an MLP block whose activation is positively homogeneous
  of degree `k` (ReLU: `k = 1`; ReLU²: `k = 2`) and of the gates of a gated block whose gate is
  (ReGLU: the gate ReLU) are symmetries inside the blocks (`Symmetry/InsideBlocks.lean`);
* attention blocks and MLP blocks with such an activation:
  `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}² + ∑_ℓ d_hidden,ℓ`; named for ReLU and ReLU²;
* attention blocks and gated blocks with such a gate:
  `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}² + 2 ∑_ℓ d_hidden,ℓ`; named for ReGLU.

At one parameter under the rank conditions of Lemma B.1 and with no vanishing column of the
reads of the hidden units, and at almost every parameter (`d_in ≥ d ≥ 1`, `d_h ≤ d`; without
skips, blocks of total width `H d_h + d_hidden ≥ d`). Under pre-RMSNorm (any `ε`)
`dim G = d(d−1)/2`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ}

/-! ### The rescalings are symmetries inside the blocks -/

/-- **The rescalings of the hidden units of an MLP block with a positively homogeneous
activation are symmetries inside the blocks** (ReLU, ReLU²). -/
theorem insideBlocks_rescaleDirMlp {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) :
    InsideBlocks (Arch.mlp σ χ hid) θ (rescaleDirMlp k θ α) := by
  sorry

/-- **The rescalings of the gates of a gated block with a positively homogeneous gate are
symmetries inside the blocks** (ReGLU). -/
theorem insideBlocks_rescaleDirGate {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (β : ∀ ℓ, hid ℓ → ℝ) :
    InsideBlocks (Arch.gated σ χ hid) θ (rescaleDirGate k θ β) := by
  sorry


/-! ### Attention blocks and MLP blocks with a positively homogeneous activation -/

/-- **Theorem 4.3 of the dimension paper for attention blocks and MLP blocks with a positively
homogeneous activation, without normalization, under the conditions of Lemma B.1:** `fd ≤ P − (L +
1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_skipless_attentionMlp_rescale {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hc : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a i) ≠ 0) :
    funDim (Arch.attentionMlp sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and MLP blocks with a positively
homogeneous activation, under pre-RMSNorm, under the conditions of Lemma B.1:** `fd ≤ P − (L + 1)
d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_skipless_attentionMlp_rescale_rmsNorm (ε : ℝ) {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hc : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a i) ≠ 0) :
    funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and MLP blocks with
a positively homogeneous activation, without normalization, under the conditions of Lemma B.1:**
`fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_residual_attentionMlp_rescale {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hc : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a i) ≠ 0) :
    funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and MLP blocks with
a positively homogeneous activation, under pre-RMSNorm, under the conditions of Lemma B.1:** `fd ≤
P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_residual_attentionMlp_rescale_rmsNorm (ε : ℝ) {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hc : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a i) ≠ 0) :
    funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and MLP blocks with a positively
homogeneous activation, without normalization, at generic parameters:** `fd ≤ P − (L + 1) d² − 2
∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attentionMlp_rescale [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and MLP blocks with a positively
homogeneous activation, under pre-RMSNorm, at generic parameters:** `fd ≤ P − (L + 1) d(d−1)/2 − 2
∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attentionMlp_rescale_rmsNorm [Nonempty d] (ε : ℝ) {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and MLP blocks with
a positively homogeneous activation, without normalization, at generic parameters:** `fd ≤ P − d²
− 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attentionMlp_rescale [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and MLP blocks with
a positively homogeneous activation, under pre-RMSNorm, at generic parameters:** `fd ≤ P −
d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attentionMlp_rescale_rmsNorm [Nonempty d] (ε : ℝ) {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry


/-! ### Attention blocks and ReLU blocks -/

/-- **Theorem 4.3 of the dimension paper for attention blocks and ReLU blocks, without
normalization, at generic parameters:** `fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attention_relu [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees relu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees relu id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees relu id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and ReLU blocks, under pre-RMSNorm,
at generic parameters:** `fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attention_relu_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees relu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees relu (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees relu (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and ReLU blocks,
without normalization, at generic parameters:** `fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attention_relu [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees relu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees relu id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees relu id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and ReLU blocks,
under pre-RMSNorm, at generic parameters:** `fd ≤ P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attention_relu_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees relu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees relu (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees relu (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry


/-! ### Attention blocks and ReLU² blocks -/

/-- **Theorem 4.3 of the dimension paper for attention blocks and ReLU² blocks, without
normalization, at generic parameters:** `fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attention_reluSq [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees reluSq id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees reluSq id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees reluSq id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and ReLU² blocks, under pre-RMSNorm,
at generic parameters:** `fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attention_reluSq_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees reluSq (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees reluSq (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees reluSq (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and ReLU² blocks,
without normalization, at generic parameters:** `fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attention_reluSq [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees reluSq id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees reluSq id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees reluSq id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and ReLU² blocks,
under pre-RMSNorm, at generic parameters:** `fd ≤ P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attention_reluSq_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees reluSq (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees reluSq (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees reluSq (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry


/-! ### Attention blocks and gated blocks with a positively homogeneous gate -/

/-- **Theorem 4.3 of the dimension paper for attention blocks and gated blocks with a positively
homogeneous gate, without normalization, under the conditions of Lemma B.1:** `fd ≤ P − (L + 1) d²
− 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_skipless_attentionGated_rescale {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and gated blocks with a positively
homogeneous gate, under pre-RMSNorm, under the conditions of Lemma B.1:** `fd ≤ P − (L + 1)
d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_skipless_attentionGated_rescale_rmsNorm (ε : ℝ) {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and gated blocks
with a positively homogeneous gate, without normalization, under the conditions of Lemma B.1:**
`fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_residual_attentionGated_rescale {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and gated blocks
with a positively homogeneous gate, under pre-RMSNorm, under the conditions of Lemma B.1:** `fd ≤
P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_residual_attentionGated_rescale_rmsNorm (ε : ℝ) {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and gated blocks with a positively
homogeneous gate, without normalization, at generic parameters:** `fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ
d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attentionGated_rescale [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and gated blocks with a positively
homogeneous gate, under pre-RMSNorm, at generic parameters:** `fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ
H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attentionGated_rescale_rmsNorm [Nonempty d] (ε : ℝ) {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and gated blocks
with a positively homogeneous gate, without normalization, at generic parameters:** `fd ≤ P − d² −
2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attentionGated_rescale [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and gated blocks
with a positively homogeneous gate, under pre-RMSNorm, at generic parameters:** `fd ≤ P − d(d−1)/2
− 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attentionGated_rescale_rmsNorm [Nonempty d] (ε : ℝ) {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry


/-! ### Attention blocks and ReGLU blocks -/

/-- **Theorem 4.3 of the dimension paper for attention blocks and ReGLU blocks, without
normalization, at generic parameters:** `fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attention_reglu [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees relu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees relu id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees relu id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and ReGLU blocks, under pre-RMSNorm,
at generic parameters:** `fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attention_reglu_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees relu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees relu (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees relu (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and ReGLU blocks,
without normalization, at generic parameters:** `fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attention_reglu [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees relu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees relu id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees relu id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and ReGLU blocks,
under pre-RMSNorm, at generic parameters:** `fd ≤ P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attention_reglu_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees relu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees relu (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees relu (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

end Skips
