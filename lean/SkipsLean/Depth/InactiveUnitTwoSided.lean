import SkipsLean.Depth.InactiveUnitRelu
import SkipsLean.Dimension.UpperBoundTwoSided
import SkipsLean.Symmetry.LocallyFreeReadoutGeneric

/-!
# Dead units without skips, for blocks with at least `d` hidden units

Paper (skips paper), Proposition A.35 (Dead units without skips): "Consider skipless networks of
`L ≥ 2` ReLU, ReLU² or ReGLU blocks without normalization. There is a nonempty open set of
weights on which a unit of block 2 is dead. On it the functional dimension is at most
`P − (L + 1) d_model² − s − (2 d_model − 1)`, and at most
`P − (L + 1) d_model² − s − (3 d_model − 2)` for ReGLU, so the equality condition fails there."
The Scope of the main text has `d_hidden ≥ d_model` and `d_in, d_out ≥ d_model`.

`Depth/InactiveUnit.lean` and `Depth/InactiveUnitRelu.lean` have the proposition as the dimension
paper states it (Proposition E.1: "each with more than `d_model` hidden units"; "At almost every
point of this set"): they ask more than `d` hidden units in the block of the dead unit, because
the network without the dead unit must have writes of rank `d`. Here the proposition for ReLU and
ReLU² blocks with **at least `d` hidden units in every block**, for `d_in, d_out ≥ d ≥ 1`: the
block of the dead unit may have exactly `d` hidden units. The bound uses the locally free action
from both ends (`Dimension/UpperBoundTwoSided.lean`): nothing is asked of the write of the block
of the dead unit.

* `funDim_add_le_of_eventually_unitInactive_of_rank_E_D`: the bound at one parameter, the twin
  of `funDim_add_le_of_eventually_unitInactive`.
* `exists_isOpen_unitInactive_relu_of_le`, `exists_isOpen_unitInactive_reluSq_of_le`: the
  nonempty open set (the same set `negReadSet`) and the bound at almost every point of it.
* `not_ae_funDim_add_eq_relu_skipless_of_le`, `not_ae_funDim_add_eq_reluSq_skipless_of_le`: "so
  the equality condition fails there".

As in the twins, the network has the blocks `Fin (L + 1)` in the last four statements (at least
two blocks when `L ≥ 1`), Lean's `funDim` is at least the paper's functional dimension, and the
bound is at almost every point of the open set. Not stated: the bound at every point of the open
set; ReGLU blocks with exactly `d` hidden units in the block of the dead unit.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ}

/-- **Proposition A.35, the bound, at one parameter (ReLU and ReLU² blocks), with the conditions
from both ends.** Let `σ` be positively homogeneous of degree `k ≠ 0` and vanish on `z ≤ 0`, and
let hidden unit `j` of block `m` be inactive at every input at all parameters near `θ`. If `E`
and `D` have rank `d`, the writes of the blocks before `m` and the reads of the blocks after `m`
have rank `d`, no read column of a block up to `m` and no write row of a block after `m`
vanishes, then `fd(θ) ≤ P − (L+1) d² − s − (2d − 1)`, with `s` the number of hidden units. -/
theorem funDim_add_le_of_eventually_unitInactive_of_rank_E_D {L : ℕ} {hid : Fin L → Type}
    [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)] {k : ℕ} (hk : k ≠ 0)
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hθ : ∀ᶠ θ' in 𝓝 θ, UnitInactive θ' m j)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hr : ∀ ℓ, m < ℓ → (θ.read ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a i) ≠ 0)
    (ha : ∀ ℓ, m < ℓ → ∀ i, (fun a => θ.write ℓ i a) ≠ 0) :
    funDim (Arch.mlp σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) + (2 * Fintype.card d - 1))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

variable {L : ℕ} {hid : Fin (L + 1) → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)]

/-- **Proposition A.35 for ReLU blocks with at least `d` hidden units:** for `d_in, d_out ≥ d ≥ 1`
and at least `d` hidden units in every block, there is a nonempty open set of weights on which
hidden unit `j` of block `ℓ.succ` is inactive at every input, and at almost every point of this
set `fd ≤ P − (L+2) d² − s − (2d − 1)`, with `s` the number of hidden units. -/
theorem exists_isOpen_unitInactive_relu_of_le [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, UnitInactive θ ℓ.succ j) ∧
      ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp relu id hid) 0 θ
          + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m) + (2 * Fintype.card d - 1))
        ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Proposition A.35 for ReLU² blocks with at least `d` hidden units:** the same as for ReLU
blocks. -/
theorem exists_isOpen_unitInactive_reluSq_of_le [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, UnitInactive θ ℓ.succ j) ∧
      ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp reluSq id hid) 0 θ
          + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m) + (2 * Fintype.card d - 1))
        ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  sorry

/-- **Proposition A.35, "so the equality condition fails there", for ReLU blocks with at least
`d` hidden units:** for at least two blocks (`L ≥ 1`) and `d_in, d_out ≥ d ≥ 1`, it is not the
case that `fd = P − (L+2) d² − s` at almost every parameter. -/
theorem not_ae_funDim_add_eq_relu_skipless_of_le [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) :
    ¬ ∀ᵐ θ ∂μ, funDim (Arch.mlp relu id hid) 0 θ
        + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **The same for ReLU² blocks with at least `d` hidden units.** -/
theorem not_ae_funDim_add_eq_reluSq_skipless_of_le [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) :
    ¬ ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq id hid) 0 θ
        + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  sorry

end Skips
