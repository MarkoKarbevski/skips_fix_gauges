import SkipsLean.Dimension.UpperBoundRMSNorm
import SkipsLean.Residual.UpperBoundSymmetries

/-!
# Symmetries inside the blocks, for any kind of block, and the upper bounds they give

Papers. Skips paper, Section 4.1: "the symmetries inside the blocks […] change only the read and
the write of one block and leave the map of that block unchanged: the rescaling of a hidden unit
of a ReLU or ReLU² block, the rescaling of the value of a hidden unit of a gated block, and the
changes of basis inside an attention head […]. Let `s` be the total dimension of the symmetries
inside the blocks, summed over the blocks […]. They preserve the function with skips and without
them, so `s` is the same number for both networks." Theorem 4.2 (Upper bounds): "at generic
parameters, the functional dimension is at most `P − (L + 1) dim G − s` without skips and at most
`P − dim G − s` with identity skips." Dimension paper: Theorem 4.3 and Lemma B.1.

The library has these bounds kind by kind (`Dimension/Rescaling.lean`, `RescalingMlp.lean`,
`RescalingGate.lean`, `UpperBoundAttention.lean`, `Residual/UpperBoundSymmetries.lean`). Here they
are stated once, for any architecture, so that they also serve networks with two kinds of block
(`Network/Sum.lean`, `Symmetry/InsideBlocksSum.lean`):

* `InsideBlocks A θ η`: `η` is the velocity at `θ` of a curve of parameters that keeps `E`, `D`
  and the map `n ↦ f_ℓ(n W_read^ℓ) W_write^ℓ` of every block.
* `InsideBlocks.mem_flat`: such a direction is flat, for every stream (with or without skips)
  and every `χ`; its `E` and `D` components are `0`.
* The bounds for a space `V` of directions spanned by such directions: without skips
  `fd ≤ P − (L + 1) dim G − dim V`, if `E` and the writes have rank `d` and a direction of `V`
  whose read of a block is `0` has the write of that block `0` (the directions of Lemma B.1);
  with identity skips `fd ≤ P − dim G − dim V`, if `E` has rank `d`. Without normalization
  `dim G = d²`; under pre-RMSNorm (any `ε`) the changes of basis are the antisymmetric
  directions, `dim G = d(d−1)/2`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **A direction of a symmetry inside the blocks:** `η` is the velocity at `τ = 0` of a curve
`γ` of parameters through `θ` along which, near `τ = 0`, the embedding and the readout stay those
of `θ` and every block keeps its map `n ↦ f_ℓ(n W_read^ℓ) W_write^ℓ`. -/
def InsideBlocks (A : Arch T d L) (θ η : Params A dIn dOut) : Prop :=
  ∃ γ : ℝ → Params A dIn dOut, γ 0 = θ ∧ HasDerivAt γ η 0 ∧
    ∀ᶠ τ in 𝓝 (0 : ℝ), (γ τ).E = θ.E ∧ (γ τ).D = θ.D ∧
      ∀ ℓ (n : Matrix T d ℝ),
        A.f ℓ (n * (γ τ).read ℓ) * (γ τ).write ℓ = A.f ℓ (n * θ.read ℓ) * θ.write ℓ

variable {A : Arch T d L} {θ η : Params A dIn dOut}

/-- **A symmetry inside the blocks preserves the function with skips and without them:** its
direction is flat for every stream and every `χ`. -/
theorem InsideBlocks.mem_flat (h : InsideBlocks A θ η) (S : Fin L → Matrix d d ℝ) :
    η ∈ flat A S θ := by
  sorry

omit [Fintype T] [DecidableEq d] in
/-- A direction of a symmetry inside the blocks does not move the embedding. -/
theorem InsideBlocks.E_eq_zero (h : InsideBlocks A θ η) : η.E = 0 := by
  sorry

omit [Fintype T] [DecidableEq d] in
/-- A direction of a symmetry inside the blocks does not move the readout. -/
theorem InsideBlocks.D_eq_zero (h : InsideBlocks A θ η) : η.D = 0 := by
  sorry

variable (θ)

/-- **Theorem 4.3 of the dimension paper for any symmetries inside the blocks, without
normalization, under the conditions of Lemma B.1:** let `V` be a space of directions spanned by
directions of symmetries inside the blocks, in which a direction whose read of block `ℓ` is `0`
has the write of block `ℓ` `0`. If `E` and the writes have rank `d`,
`fd ≤ P − (L + 1) d² − dim V`. -/
theorem funDim_add_le_skipless_of_insideBlocks (hA : A.χ = id)
    (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
    (hrw : ∀ η ∈ V, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim A 0 θ + ((L + 1) * Fintype.card d ^ 2 + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **The same under pre-RMSNorm** (any `ε`):
`fd ≤ P − (L + 1) d(d−1)/2 − dim V`. -/
theorem funDim_add_le_skipless_of_insideBlocks_rmsNorm (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
    (hrw : ∀ η ∈ V, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim A 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips, for any symmetries inside the blocks,
without normalization:** if `E` has rank `d`, `fd ≤ P − d² − dim V`. -/
theorem funDim_add_le_residual_of_insideBlocks (hA : A.χ = id)
    (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
    (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + (Fintype.card d ^ 2 + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **The same under pre-RMSNorm** (any `ε`): `fd ≤ P − d(d−1)/2 − dim V`. -/
theorem funDim_add_le_residual_of_insideBlocks_rmsNorm (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
    (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + (Fintype.card d * (Fintype.card d - 1) / 2 + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end Skips
