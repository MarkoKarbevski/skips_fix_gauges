import SkipsLean.Symmetry.InsideBlocksSum
import SkipsLean.Residual.UpperBoundRescaleRMSNormZero

/-!
# The upper bounds for any symmetries inside the blocks, under pre-RMSNorm with `ε = 0`

Paper (skips paper), Theorem 4.2 (Upper bounds): "Let `G` be the group of changes of basis of one
hidden state, and `s` the dimension of the symmetries inside the blocks, the same with and without
skips. With or without pre-RMSNorm, at generic parameters, the functional dimension is at most
`P − (L + 1) dim G − s` without skips and at most `P − dim G − s` with identity skips." It is a
special case of Theorem A.17 (ii). Appendix A: "`G` is `GL(d_model)` without normalization,
`O(d_model)` under RMSNorm with `ε > 0`, and `CO(d_model)`, the positive multiples of orthogonal
matrices, under RMSNorm with `ε = 0`." So for `ε = 0`, `dim G = d(d−1)/2 + 1`.

`Symmetry/InsideBlocks.lean` and `Symmetry/InsideBlocksSum.lean` have these bounds for any space
`V` of directions of symmetries inside the blocks, without normalization and under pre-RMSNorm for
any `ε` with the orthogonal changes of basis only (`d(d−1)/2` for each). Here their twins for
`ε = 0`, with the scaling of each hidden state as one more flat direction
(`scaleDir`, `Dimension/UpperBoundRMSNormZero.lean`): `(L + 1) (d(d−1)/2 + 1)` without skips and
`d(d−1)/2 + 1` with identity skips, for one architecture and for the sum of two.

The functional dimension is Lean's `funDim` (all inputs; a zero row is normalized to `0`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

section One

variable {A : Arch T d L} (θ : Params A dIn dOut)

omit [DecidableEq d] in
/-- Helper (the private `span_le_flat_ibl` of `Symmetry/InsideBlocks.lean`): the directions
spanned by directions of symmetries inside the blocks are flat, for every stream. -/
private theorem span_le_flat_ibz (S : Fin L → Matrix d d ℝ) :
    Submodule.span ℝ {η | InsideBlocks A θ η} ≤ flat A S θ :=
  Submodule.span_le.2 fun _ hη => InsideBlocks.mem_flat hη S

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `E_eq_zero_of_mem_span_ibl` of `Symmetry/InsideBlocks.lean`): the
directions spanned by directions of symmetries inside the blocks have `E` component `0`. -/
private theorem E_eq_zero_of_mem_span_ibz {v : Params A dIn dOut}
    (hv : v ∈ Submodule.span ℝ {η | InsideBlocks A θ η}) : v.E = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact InsideBlocks.E_eq_zero hx
  | zero => rfl
  | add x y _ _ hx hy => rw [Params.add_E, hx, hy, add_zero]
  | smul a x _ hx => rw [Params.smul_E, hx, smul_zero]

/-- **Theorem 4.2 of the skips paper without skips, for any symmetries inside the blocks, under
pre-RMSNorm with `ε = 0`, under the conditions of Lemma A.18:** let `V` be a space of directions
spanned by directions of symmetries inside the blocks, in which a direction whose read of block
`ℓ` is `0` has the write of block `ℓ` `0`. If `E` and the writes have rank `d ≥ 1`,
`fd ≤ P − (L + 1) (d(d−1)/2 + 1) − dim V`. -/
theorem funDim_add_le_skipless_of_insideBlocks_rmsNorm_zero [Nonempty d] (hA : A.χ = rmsNorm 0)
    (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
    (hrw : ∀ η ∈ V, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim A 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips, for any symmetries inside the blocks,
under pre-RMSNorm with `ε = 0`:** if `E` has rank `d ≥ 1`, `fd ≤ P − (d(d−1)/2 + 1) − dim V`. -/
theorem funDim_add_le_residual_of_insideBlocks_rmsNorm_zero [Nonempty d] (hA : A.χ = rmsNorm 0)
    (V : Submodule ℝ (Params A dIn dOut))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A θ η})
    (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) :=
  -- the rotation and the scaling of all hidden states, and the directions of `V`
  funDim_add_le_of_coScale_add_urz θ hA hE V.subtype V.injective_subtype
    (fun v => E_eq_zero_of_mem_span_ibz θ (hV v.2)) (fun v => span_le_flat_ibz θ 1 (hV v.2))

end One

section Sum

variable {A B : Arch T d L} (θ : Params (A.sum B) dIn dOut)

/-- **The bound without skips for a network with two kinds of block, under pre-RMSNorm with
`ε = 0`:** let `V_A` and `V_B` be spaces of directions spanned by directions of symmetries inside
the blocks of the two parts, in each of which a direction whose read of block `ℓ` is `0` has the
write of block `ℓ` `0`. If `E` and the writes of the sum have rank `d ≥ 1`,
`fd ≤ P − (L + 1) (d(d−1)/2 + 1) − dim V_A − dim V_B`. -/
theorem funDim_add_le_skipless_sum_of_insideBlocks_rmsNorm_zero [Nonempty d]
    (hA : A.χ = rmsNorm 0)
    (VA : Submodule ℝ (Params A dIn dOut)) (VB : Submodule ℝ (Params B dIn dOut))
    (hVA : VA ≤ Submodule.span ℝ {η | InsideBlocks A θ.sumFst η})
    (hVB : VB ≤ Submodule.span ℝ {η | InsideBlocks B θ.sumSnd η})
    (hrwA : ∀ η ∈ VA, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hrwB : ∀ η ∈ VB, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim (A.sum B) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (Module.finrank ℝ VA + Module.finrank ℝ VB))
      ≤ Module.finrank ℝ (Params (A.sum B) dIn dOut) := by
  -- the bound for one architecture, for the lifts of `V_A` and `V_B` to the sum
  have h := funDim_add_le_skipless_of_insideBlocks_rmsNorm_zero θ hA _
    (sup_le_span_ibl θ VA VB hVA hVB) (write_eq_zero_of_read_ibl VA VB hrwA hrwB) hE hw
  rwa [finrank_sup_ibl θ VA VB hVA] at h

/-- **The bound with identity skips for a network with two kinds of block, under pre-RMSNorm with
`ε = 0`:** if `E` has rank `d ≥ 1`, `fd ≤ P − (d(d−1)/2 + 1) − dim V_A − dim V_B`. -/
theorem funDim_add_le_residual_sum_of_insideBlocks_rmsNorm_zero [Nonempty d]
    (hA : A.χ = rmsNorm 0)
    (VA : Submodule ℝ (Params A dIn dOut)) (VB : Submodule ℝ (Params B dIn dOut))
    (hVA : VA ≤ Submodule.span ℝ {η | InsideBlocks A θ.sumFst η})
    (hVB : VB ≤ Submodule.span ℝ {η | InsideBlocks B θ.sumSnd η})
    (hE : θ.E.rank = Fintype.card d) :
    funDim (A.sum B) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + (Module.finrank ℝ VA + Module.finrank ℝ VB))
      ≤ Module.finrank ℝ (Params (A.sum B) dIn dOut) := by
  -- the bound for one architecture, for the lifts of `V_A` and `V_B` to the sum
  have h := funDim_add_le_residual_of_insideBlocks_rmsNorm_zero θ hA _
    (sup_le_span_ibl θ VA VB hVA hVB) hE
  rwa [finrank_sup_ibl θ VA VB hVA] at h

end Sum

end Skips
