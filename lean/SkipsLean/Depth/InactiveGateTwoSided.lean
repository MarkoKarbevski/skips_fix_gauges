import SkipsLean.Depth.InactiveGateReGLU
import SkipsLean.Dimension.UpperBoundTwoSidedGated
import SkipsLean.Symmetry.LocallyFreeReadoutGeneric

/-!
# Dead units without skips, ReGLU blocks with at least `d` hidden units

Paper (skips paper), Proposition A.35 (Dead units without skips): "Consider skipless networks of
`L ≥ 2` ReLU, ReLU² or ReGLU blocks without normalization. There is a nonempty open set of
weights on which a unit of block 2 is dead. On it the functional dimension is at most
`P − (L + 1) d_model² − s − (2 d_model − 1)`, and at most
`P − (L + 1) d_model² − s − (3 d_model − 2)` for ReGLU, so the equality condition fails there."

`Depth/InactiveGate.lean` and `Depth/InactiveGateReGLU.lean` have the proposition for ReGLU
blocks as the dimension paper states it (Proposition E.1, more than `d_model` hidden units in the
block of the dead unit). Here the twins for **at least `d` hidden units in every block** and
`d_in, d_out ≥ d ≥ 1`, as `Depth/InactiveUnitTwoSided.lean` for ReLU and ReLU² blocks: the bound
uses the locally free action from both ends (`Dimension/UpperBoundTwoSidedGated.lean`), and asks
nothing of the write of the block of the dead unit. For the blocks after it the gate and value
columns of the read are asked in general position, which holds at generic parameters.

As in the twins, the last two statements are for networks with the blocks `Fin (L + 1)`, Lean's
`funDim` is at least the paper's functional dimension, and the bound is at almost every point of
the open set. Not stated: the bound at every point of the open set.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ}

/-- **Proposition A.35, the bound, at one parameter (ReGLU blocks), with the conditions from
both ends.** Let the gate activation be positively homogeneous of degree `k` and vanish on
`z ≤ 0`, and let the gate of hidden unit `j` of block `m` be closed at every input at all
parameters near `θ`. If `E` and `D` have rank `d`, the writes of the blocks before `m` have rank
`d`, no gate column and no value column of a read of a block up to `m` vanishes, and for every
block after `m` no write row vanishes and the gate and value columns of its read are in general
position, then `fd(θ) ≤ P − (L+1) d² − s − (3d − 2)`, with `s` twice the number of hidden
units. -/
theorem funDim_add_le_of_eventually_gateInactive_of_rank_E_D {L : ℕ} {hid : Fin L → Type}
    [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hθ : ∀ᶠ θ' in 𝓝 θ, GateInactive θ' m j)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0)
    (ha : ∀ ℓ, m < ℓ → ∀ i, (fun a => θ.write ℓ i a) ≠ 0)
    (hgp : ∀ ℓ, m < ℓ → ∀ S : Finset (hid ℓ ⊕ hid ℓ), S.card ≤ Fintype.card d →
      LinearIndependent ℝ fun j : S => (θ.read ℓ)ᵀ j)
    (hcard : ∀ ℓ, m < ℓ → Fintype.card d < Fintype.card (hid ℓ ⊕ hid ℓ)) :
    funDim (Arch.gated σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ)
          + (3 * Fintype.card d - 2))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

variable {L : ℕ} {hid : Fin (L + 1) → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)]

/-- **Proposition A.35 for ReGLU blocks with at least `d` hidden units:** for
`d_in, d_out ≥ d ≥ 1` and at least `d` hidden units in every block, there is a nonempty open set
of weights on which the gate of hidden unit `j` of block `ℓ.succ` is closed at every input, and
at almost every point of this set `fd ≤ P − (L+2) d² − s − (3d − 2)`, with `s` twice the number
of hidden units. -/
theorem exists_isOpen_gateInactive_reglu_bound_of_le [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ) :
    ∃ U : Set (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, GateInactive θ ℓ.succ j) ∧
      ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.gated relu id hid) 0 θ
          + ((L + 2) * Fintype.card d ^ 2 + 2 * ∑ m, Fintype.card (hid m)
            + (3 * Fintype.card d - 2))
        ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Proposition A.35, "so the equality condition fails there", for ReGLU blocks with at least
`d` hidden units:** for at least two blocks (`L ≥ 1`) and `d_in, d_out ≥ d ≥ 1`, it is not the
case that `fd = P − (L+2) d² − s` at almost every parameter, with `s` twice the number of hidden
units. -/
theorem not_ae_funDim_add_eq_reglu_skipless_of_le [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) :
    ¬ ∀ᵐ θ ∂μ, funDim (Arch.gated relu id hid) 0 θ
        + ((L + 2) * Fintype.card d ^ 2 + 2 * ∑ m, Fintype.card (hid m))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

end Skips
