import SkipsLean.Residual.SkiplessEnds
import SkipsLean.Dimension.UpperBoundAttention
import SkipsLean.Network.AttentionAnalytic

/-!
# Skipless networks of attention blocks: the changes of basis at the two ends and inside the heads

Paper (skips paper): proof of Theorem A.28 (i) and (ii). "In a skipless network of the same
widths, with embedding `E′` and readout `D′`, the changes of basis at `h_0` and `h_L`, those inside
the heads and the rescalings have orbits of dimension `2 d_model² + s` at generic parameters, where
`E′` and `D′` have rank `d_model` and the queries and values of every head have full column rank."
And: "Under pre-RMSNorm with `ε > 0` […] the orthogonal changes of basis at `h_0` and `h_L`, which
commute with the normalization, have orbits of dimension `d_model (d_model − 1) + s` in the
skipless network". The proof of Lemma A.26 then uses the bound at every parameter ("the rank is
lower semicontinuous, so the bound holds at every `η`").

Here, for `Arch.attention sees χ H dh` (any mask), `L ≥ 1` blocks whose heads have any numbers and
widths, with `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²` (the changes of basis between queries and keys and between
values and outputs, `Symmetry/AttentionHeads.lean`). The total width `H d_h` of a block may be
smaller than `d`: the changes of basis at the hidden states in between are not used.

* `funDim_add_le_skipless_ends_attention`, `…_rmsNorm`: the bound on the functional dimension at a
  parameter whose `E` and `D` have rank `d` and whose query and value matrices have rank `d_h`.
* `jacobianRank_add_le_skipless_ends_attention`, `…_rmsNorm`: the same bound for the rank of the
  Jacobian on every batch at EVERY parameter, for heads of width `d_h ≤ d` and `d_in, d_out ≥ d`.

The twin statements for MLP and gated blocks are in `Residual/SkiplessEnds.lean`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-- **Proof of Theorem A.28 (ii) of the skips paper, "the changes of basis at `h_0` and `h_L`,
those inside the heads", for attention blocks without normalization:** for a skipless network of
`L ≥ 1` attention blocks whose `E` and `D` have rank `d` and whose query and value matrices have
rank `d_h`, the functional dimension is at most `P − 2 d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_skipless_ends_attention
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) (hL : 0 < L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attention sees id H dh) 0 θ
        + (2 * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

/-- **The same bound at every parameter, on every batch, for attention blocks without
normalization:** for `d_in, d_out ≥ d`, `L ≥ 1` and heads of width `d_h ≤ d`, the Jacobian of the
outputs of a skipless network of attention blocks on a batch has rank at most
`P − 2 d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²` at every parameter. -/
theorem jacobianRank_add_le_skipless_ends_attention (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank (Arch.attention sees id H dh) 0 X θ
        + (2 * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

/-- **For attention blocks under pre-RMSNorm with `ε > 0`, "the orthogonal changes of basis at
`h_0` and `h_L`" and the changes of basis inside the heads:** for a skipless network of `L ≥ 1`
attention blocks whose `E` and `D` have rank `d` and whose query and value matrices have rank
`d_h`, the functional dimension is at most `P − d (d − 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_skipless_ends_attention_rmsNorm {ε : ℝ} (hε : 0 < ε)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) (hL : 0 < L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
        + (Fintype.card d * (Fintype.card d - 1)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  sorry

/-- **The same bound at every parameter, on every batch, for attention blocks under pre-RMSNorm
with `ε > 0`:** the Jacobian of the outputs of a skipless network of attention blocks on a batch
has rank at most `P − d (d − 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}²` at every parameter. -/
theorem jacobianRank_add_le_skipless_ends_attention_rmsNorm {ε : ℝ} (hε : 0 < ε) (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank (Arch.attention sees (rmsNorm ε) H dh) 0 X θ
        + (Fintype.card d * (Fintype.card d - 1)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  sorry

end Skips
