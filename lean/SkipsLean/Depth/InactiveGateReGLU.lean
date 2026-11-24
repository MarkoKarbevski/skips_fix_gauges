import SkipsLean.Depth.InactiveGateOpen
import SkipsLean.Generic.Gated

/-!
# Proposition E.1 for ReGLU blocks

Paper (dimension paper): Appendix E, Proposition E.1.

"Proposition E.1 (Inactive hidden units). Consider networks of `L ≥ 2` ReLU, ReLU² or ReGLU blocks
without normalization, each with more than `d_model` hidden units. There is a nonempty open set of
weights on which a hidden unit of block 2 is inactive at every input. At almost every point of this
set the functional dimension is at most `P − (L+1) d_model² − s − (2 d_model − 1)`, and at most
`P − (L+1) d_model² − s − (3 d_model − 2)` for ReGLU blocks. So these networks do not satisfy the
equality condition."

Stated here, for networks of ReGLU blocks `Fin (L + 1)` (at least two blocks when `L ≥ 1`), a block
`ℓ.succ` after the first and a hidden unit `j` of it:

* `exists_isOpen_gateInactive_reglu_bound`: a nonempty open set of weights on which the gate of
  the hidden unit is closed at every input, and at almost every point of it
  `fd ≤ P − (L+2) d² − s − (3d − 2)`, where `s` is twice the number of hidden units (the network
  has `L + 2` hidden states). Lean asks at least `d` hidden units in every block and more than `d`
  in the block of the inactive unit.
* `not_ae_funDim_add_eq_reglu_skipless`: "So these networks do not satisfy the equality
  condition": it is not the case that `fd = P − (L+2) d² − s` at almost every parameter.

The open set is from `Depth/InactiveGateOpen.lean`, the bound at one parameter from
`Depth/InactiveGate.lean`. ReLU and ReLU² blocks are in `Depth/InactiveUnitRelu.lean`. Lean's
`funDim` takes the Jacobian at all inputs, so it is at least the paper's functional dimension.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin (L + 1) → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)]

/-- Helper: a matrix with `d` columns and an invertible `d × d` submatrix of rows has rank `d`
(copied from `Generic/Params.lean`). -/
private theorem rank_eq_of_isUnit_det_submatrix_igr {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- **Proposition E.1 for ReGLU blocks:** for `d_in ≥ d ≥ 1`, at least `d` hidden units in every
block and more than `d` in block `ℓ.succ`, there is a nonempty open set of weights on which the
gate of hidden unit `j` of block `ℓ.succ` is closed at every input, and at almost every point of
this set `fd ≤ P − (L+2) d² − s − (3d − 2)`, with `s` twice the number of hidden units. -/
theorem exists_isOpen_gateInactive_reglu_bound [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ)
    (hj : Fintype.card d < Fintype.card (hid ℓ.succ)) :
    ∃ U : Set (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, GateInactive θ ℓ.succ j) ∧
      ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.gated relu id hid) 0 θ
          + ((L + 2) * Fintype.card d ^ 2 + 2 * ∑ m, Fintype.card (hid m)
            + (3 * Fintype.card d - 2))
        ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- the open set on which the gate of the hidden unit is closed at every input
  obtain ⟨U, hU, hUne, hUin⟩ :=
    exists_isOpen_gateInactive_reglu (T := T) (dIn := dIn) (dOut := dOut) ℓ j (hhid ℓ.castSucc)
  refine ⟨U, hU, hUne, hUin, ?_⟩
  -- `d` rows of the write of block `ℓ.succ` other than the row of `j`
  have hcard : Fintype.card d ≤ Fintype.card {i : hid ℓ.succ // i ≠ j} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    omega
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hcard
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_value_ne_zero μ, ae_gate_ne_zero μ,
    ae_isUnit_det_submatrix μ] with θ h1 h2 h3 h4 hθU
  -- the write without the row of `j` has rank `d`
  have hwj : ((θ.write ℓ.succ).submatrix (fun i : {i : hid ℓ.succ // i ≠ j} => (i : hid ℓ.succ))
      id).rank = Fintype.card d := by
    refine rank_eq_of_isUnit_det_submatrix_igr _ ρ ?_
    have := h4.2.2.2 ℓ.succ (ρ.trans (Function.Embedding.subtype _))
    simpa [Matrix.submatrix_submatrix] using this
  -- the gate is closed at every input at all parameters near `θ`
  have hθ : ∀ᶠ θ' in 𝓝 θ, GateInactive θ' ℓ.succ j :=
    Filter.mem_of_superset (hU.mem_nhds hθU) hUin
  have := funDim_add_le_of_eventually_gateInactive relu_homogeneous
    (fun z hz => max_eq_right hz) θ ℓ.succ j hθ h1.1 h1.2 hwj h2 h3
  simpa [add_assoc] using this

/-- **Proposition E.1, "So these networks do not satisfy the equality condition", for ReGLU
blocks:** for at least two blocks (`L ≥ 1`), `d_in ≥ d ≥ 1` and more than `d` hidden units in every
block, it is not the case that `fd = P − (L+2) d² − s` at almost every parameter, with `s` twice
the number of hidden units. -/
theorem not_ae_funDim_add_eq_reglu_skipless [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ m, Fintype.card d < Fintype.card (hid m)) :
    ¬ ∀ᵐ θ ∂μ, funDim (Arch.gated relu id hid) 0 θ
        + ((L + 2) * Fintype.card d ^ 2 + 2 * ∑ m, Fintype.card (hid m))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  intro hae
  -- block `ℓ.succ` with `ℓ = 0` and one of its hidden units
  let ℓ : Fin L := ⟨0, hL⟩
  have hpos : 0 < Fintype.card (hid ℓ.succ) := (Nat.zero_le _).trans_lt (hhid ℓ.succ)
  obtain ⟨j⟩ : Nonempty (hid ℓ.succ) := Fintype.card_pos_iff.1 hpos
  obtain ⟨U, hU, hUne, -, hbound⟩ := exists_isOpen_gateInactive_reglu_bound μ hdIn
    (fun m => (hhid m).le) ℓ j (hhid ℓ.succ)
  -- `d ≥ 1`, so `3d − 2 ≥ 1`
  have hd : 0 < Fintype.card d := Fintype.card_pos
  -- the equality and the bound cannot both hold on `U`, so `U` is null
  have hnull : μ U = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hae, hbound] with θ heq hle hθU
    have := hle hθU
    omega
  exact (hU.measure_pos μ hUne).ne' hnull

end Skips
