import SkipsLean.Symmetry.AttentionHeads
import SkipsLean.Dimension.UpperBoundRMSNorm
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.Generic.Params

/-!
# The upper bounds for networks of attention blocks

Paper (dimension paper): Theorem 4.3 (Upper bound): "Without normalization or under
pre-RMSNorm, at generic parameters, the functional dimension of a network of `L` blocks is at
most `P − (L + 1) dim 𝒢 − s`", for attention blocks: `s = 2 H d_h²` per block (Appendix B), with
Lemma B.1 for "attention blocks whose heads have width `d_h ≤ d_model` and total width
`H d_h ≥ d_model`", `d_in ≥ d_model`. Paper (skips paper): Theorem 4.2 (Upper bounds), with
identity skips: `P − dim 𝒢 − s`.

Stated here for `Arch.attention` (`Network/Attention.lean`), any mask, with
`s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`, as the bounds for the other kinds of block
(`Dimension/RescalingGate.lean`, `Residual/UpperBoundSymmetries.lean`): at one parameter under
the rank conditions of Lemma B.1, and at almost every parameter. Without skips: `E` and the
writes of rank `d`, the query and value matrices of every head of rank `d_h`; generic for
`d_in ≥ d`, `d_h ≤ d`, `H d_h ≥ d`. With identity skips the writes are not needed, and neither is
`H d_h ≥ d`. Under pre-RMSNorm (any `ε`) the changes of basis of the hidden states are the
antisymmetric directions, `dim 𝒢 = d(d−1)/2`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-- **Theorem 4.3 for attention blocks, without normalization, under the conditions of
Lemma B.1:** `fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_skipless_attention
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attention sees id H dh) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

/-- **Theorem 4.3 for attention blocks, under pre-RMSNorm, under the conditions of Lemma B.1:**
`fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_skipless_attention_rmsNorm (ε : ℝ)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips, for attention blocks, without
normalization:** if `E` has rank `d` and the query and value matrices of every head have rank
`d_h`, `fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_residual_attention
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips, for attention blocks, under
pre-RMSNorm:** `fd ≤ P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_residual_attention_rmsNorm (ε : ℝ)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  sorry

/-- **Theorem 4.3 for attention blocks at generic parameters, without normalization:** for
`d_in ≥ d`, heads of width `d_h ≤ d` and total width `H d_h ≥ d` in every block. -/
theorem ae_funDim_add_le_skipless_attention
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

/-- **Theorem 4.3 for attention blocks at generic parameters, under pre-RMSNorm.** -/
theorem ae_funDim_add_le_skipless_attention_rmsNorm (ε : ℝ)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips, for attention blocks at generic
parameters, without normalization:** for `d_in ≥ d` and heads of width `d_h ≤ d`. -/
theorem ae_funDim_add_le_residual_attention
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips, for attention blocks at generic
parameters, under pre-RMSNorm.** -/
theorem ae_funDim_add_le_residual_attention_rmsNorm (ε : ℝ)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  sorry

end Skips
