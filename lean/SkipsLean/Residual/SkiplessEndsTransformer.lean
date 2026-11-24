import SkipsLean.Residual.SkiplessEndsAttention
import SkipsLean.Dimension.UpperBoundTransformer

/-!
# Skipless transformers: the changes of basis at the two ends and the symmetries inside the blocks

Paper (skips paper): proof of Theorem A.28 (ii). "In a skipless network of the same widths, with
embedding `E′` and readout `D′`, the changes of basis at `h_0` and `h_L`, those inside the heads
and the rescalings have orbits of dimension `2 d_model² + s` at generic parameters, where `E′`
and `D′` have rank `d_model` and the queries and values of every head have full column rank."
Under pre-RMSNorm: "the orthogonal changes of basis at `h_0` and `h_L`, which commute with the
normalization, have orbits of dimension `d_model (d_model − 1) + s` in the skipless network". The
proof of Lemma A.26 uses the bound at every parameter ("the rank is lower semicontinuous, so the
bound holds at every `η`").

Stated once for any architecture and any space `V` of directions spanned by directions of
symmetries inside the blocks (`Symmetry/InsideBlocks.lean`): a skipless network of `L ≥ 1` blocks
whose `E` and `D` have rank `d` has `fd ≤ P − 2 d² − dim V` (no condition on the writes: the
hidden states in between are not used). Then, for the networks of `Network/Transformer.lean`
(attention blocks and MLP blocks, or attention blocks and gated blocks, in any order, of any
widths), the bound on the rank of the Jacobian on every batch at EVERY parameter, with
`s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²` (and `+ ∑_ℓ d_hidden,ℓ` for gated blocks). The twins for networks of one
kind of block: `Residual/SkiplessEnds.lean`, `Residual/SkiplessEndsAttention.lean`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **Proof of Theorem A.28 (ii) of the skips paper, "the changes of basis at `h_0` and `h_L`"
and the symmetries inside the blocks, without normalization, for any architecture:** for a
skipless network of `L ≥ 1` blocks whose `E` and `D` have rank `d`, and a space `V` of directions
spanned by directions of symmetries inside the blocks, `fd ≤ P − 2 d² − dim V`. -/
theorem funDim_add_le_skipless_ends_of_insideBlocks {A : Arch T d L} (hA : A.χ = id)
    (hL : 0 < L) (θ : Params A dIn dOut) (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) :
    funDim A 0 θ + (2 * Fintype.card d ^ 2 + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **The same under pre-RMSNorm** (any `ε`), with the orthogonal changes of basis at `h_0` and
`h_L`: `fd ≤ P − d (d − 1) − dim V`. -/
theorem funDim_add_le_skipless_ends_of_insideBlocks_rmsNorm {A : Arch T d L} (ε : ℝ)
    (hA : A.χ = rmsNorm ε) (hL : 0 < L) (θ : Params A dIn dOut)
    (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) :
    funDim A 0 θ + (Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **The bound at every parameter, on every batch, for a skipless network of attention blocks and
MLP blocks, without normalization:** for a real-analytic activation, `d_in, d_out ≥ d`, `L ≥ 1`
and heads of width `d_h ≤ d`, the Jacobian of the outputs on a batch has rank at most `P − 2 d² −
2 ∑_ℓ H_ℓ d_{h,ℓ}²` at every parameter. -/
theorem jacobianRank_add_le_skipless_ends_attentionMlp
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank (Arch.attentionMlp sees σ id H dh hid) 0 X θ
        + (2 * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **The bound at every parameter, on every batch, for a skipless network of attention blocks and
MLP blocks, under pre-RMSNorm with `ε > 0`:** for a real-analytic activation, `d_in, d_out ≥ d`,
`L ≥ 1` and heads of width `d_h ≤ d`, the Jacobian of the outputs on a batch has rank at most `P −
d (d − 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}²` at every parameter. -/
theorem jacobianRank_add_le_skipless_ends_attentionMlp_rmsNorm (hε : 0 < ε)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 X θ
        + (Fintype.card d * (Fintype.card d - 1)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **The bound at every parameter, on every batch, for a skipless network of attention blocks and
gated blocks, without normalization:** for a real-analytic gate, `d_in, d_out ≥ d` `≥ 1`, `L ≥ 1`
and heads of width `d_h ≤ d`, the Jacobian of the outputs on a batch has rank at most `P − 2 d² −
2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ` at every parameter. -/
theorem jacobianRank_add_le_skipless_ends_attentionGated [Nonempty d]
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank (Arch.attentionGated sees σ id H dh hid) 0 X θ
        + (2 * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **The bound at every parameter, on every batch, for a skipless network of attention blocks and
gated blocks, under pre-RMSNorm with `ε > 0`:** for a real-analytic gate, `d_in, d_out ≥ d` `≥ 1`,
`L ≥ 1` and heads of width `d_h ≤ d`, the Jacobian of the outputs on a batch has rank at most `P −
d (d − 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ` at every parameter. -/
theorem jacobianRank_add_le_skipless_ends_attentionGated_rmsNorm [Nonempty d] (hε : 0 < ε)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 X θ
        + (Fintype.card d * (Fintype.card d - 1)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

end Skips
