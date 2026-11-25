import SkipsLean.Depth.InactiveUnitTwoSided
import SkipsLean.Depth.InactiveGateTwoSided
import SkipsLean.Residual.SmallWritesOn

/-!
# Dead units without skips: the bound at every point of the open set

Paper (skips paper), Proposition A.35 (Dead units without skips): "There is a nonempty open set
of weights on which a unit of block 2 is dead. On it the functional dimension is at most
`P − (L + 1) d_model² − s − (2 d_model − 1)`, and at most
`P − (L + 1) d_model² − s − (3 d_model − 2)` for ReGLU, so the equality condition fails there."

`Depth/InactiveUnitTwoSided.lean` and `Depth/InactiveGateTwoSided.lean` have the bound at almost
every point of the open set (as Proposition E.1 of the dimension paper states it), where the
rank conditions hold. Here "On it": the bound **at every point of the open set**, by the lower
semicontinuity of the rank of the Jacobian on a batch
(`eventually_jacobianRank_ge_of_contDiffOn`, `Residual/SmallWritesOn.lean`): near a point `θ`
the rank on a batch does not drop, and every neighbourhood of `θ` has points at which the bound
holds.

* `jacobianRank_add_le_of_ae_of_contDiffOn`: the general step, for blocks without normalization
  whose fixed maps are continuously differentiable on open sets `V ℓ`: if `fd + k ≤ P` at almost
  every point of an open set `U`, then at every `θ ∈ U` the rank on every batch whose
  pre-activations at `θ` lie in the `V ℓ` is at most `P − k`.
  `funDim_add_le_of_ae_of_contDiff`: for blocks that are continuously differentiable everywhere,
  `fd + k ≤ P` at every point of `U`.
* ReLU blocks: the bound for the rank on every batch on which no pre-activation vanishes (the
  batches of the paper's functional dimension for these blocks).
* ReLU² blocks: the block is continuously differentiable, and the bound is for Lean's `funDim`.
* ReGLU blocks: the bound for the rank on every batch on which no gate pre-activation vanishes.

The widths are those of the twins: at least `d` hidden units in every block,
`d_in, d_out ≥ d ≥ 1`; the networks have the blocks `Fin (L + 1)`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **From almost every point to every point of an open set, on batches in the domain of
smoothness.** Blocks without normalization, any stream matrices, `f_ℓ` continuously
differentiable on the open set `V ℓ`. If `fd + k ≤ P` at almost every point of an open set `U`,
then at every `θ ∈ U` and on every batch whose pre-activations at `θ` lie in the `V ℓ`, the rank
of the Jacobian is at most `P − k`. -/
theorem jacobianRank_add_le_of_ae_of_contDiffOn {L : ℕ} {A : Arch T d L} (hA : A.χ = id)
    (S : Fin L → Matrix d d ℝ) (V : ∀ ℓ, Set (Matrix T (A.r ℓ) ℝ)) (hVo : ∀ ℓ, IsOpen (V ℓ))
    (hf : ∀ ℓ, ContDiffOn ℝ 1 (A.f ℓ) (V ℓ))
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {U : Set (Params A dIn dOut)} (hU : IsOpen U) (k : ℕ)
    (hae : ∀ᵐ θ ∂μ, θ ∈ U → funDim A S θ + k ≤ Module.finrank ℝ (Params A dIn dOut))
    {θ : Params A dIn dOut} (hθ : θ ∈ U) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i ℓ, hidden A S θ (X i) ℓ.castSucc * θ.read ℓ ∈ V ℓ) :
    jacobianRank A S X θ + k ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **From almost every point to every point of an open set, for blocks that are continuously
differentiable.** Blocks without normalization, any stream matrices, `f_ℓ` continuously
differentiable. If `fd + k ≤ P` at almost every point of an open set `U`, then at every point
of `U`. -/
theorem funDim_add_le_of_ae_of_contDiff {L : ℕ} {A : Arch T d L} (hA : A.χ = id)
    (S : Fin L → Matrix d d ℝ) (hf : ∀ ℓ, ContDiff ℝ 1 (A.f ℓ))
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {U : Set (Params A dIn dOut)} (hU : IsOpen U) (k : ℕ)
    (hae : ∀ᵐ θ ∂μ, θ ∈ U → funDim A S θ + k ≤ Module.finrank ℝ (Params A dIn dOut))
    {θ : Params A dIn dOut} (hθ : θ ∈ U) :
    funDim A S θ + k ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

variable {L : ℕ} {hid : Fin (L + 1) → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)]

/-- **Proposition A.35, "On it", for ReLU blocks:** for `d_in, d_out ≥ d ≥ 1` and at least `d`
hidden units in every block, there is a nonempty open set of weights at every point `θ` of which
hidden unit `j` of block `ℓ.succ` is inactive at every input, and on every batch on which no
pre-activation vanishes at `θ` the rank of the Jacobian is at most
`P − (L+2) d² − s − (2d − 1)`. -/
theorem exists_isOpen_unitInactive_relu_forall [Nonempty d]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ ∀ θ ∈ U, UnitInactive θ ℓ.succ j ∧
        ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
          (∀ (i : Fin n) (m : Fin (L + 1)) (t : T) (u : hid m),
            (hidden (Arch.mlp relu id hid) 0 θ (X i) m.castSucc * θ.read m) t u ≠ 0) →
          jacobianRank (Arch.mlp relu id hid) 0 X θ
              + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m)
                + (2 * Fintype.card d - 1))
            ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Proposition A.35, "On it", for ReLU² blocks:** for `d_in, d_out ≥ d ≥ 1` and at least `d`
hidden units in every block, there is a nonempty open set of weights at every point of which
hidden unit `j` of block `ℓ.succ` is inactive at every input and
`fd ≤ P − (L+2) d² − s − (2d − 1)`. -/
theorem exists_isOpen_unitInactive_reluSq_forall [Nonempty d]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ ∀ θ ∈ U, UnitInactive θ ℓ.succ j ∧
        funDim (Arch.mlp reluSq id hid) 0 θ
            + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m)
              + (2 * Fintype.card d - 1))
          ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  sorry

/-- **Proposition A.35, "On it", for ReGLU blocks:** for `d_in, d_out ≥ d ≥ 1` and at least `d`
hidden units in every block, there is a nonempty open set of weights at every point `θ` of which
the gate of hidden unit `j` of block `ℓ.succ` is closed at every input, and on every batch on
which no pre-activation of a gate vanishes at `θ` the rank of the Jacobian is at most
`P − (L+2) d² − s − (3d − 2)`, with `s` twice the number of hidden units. -/
theorem exists_isOpen_gateInactive_reglu_forall [Nonempty d]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ) :
    ∃ U : Set (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ ∀ θ ∈ U, GateInactive θ ℓ.succ j ∧
        ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
          (∀ (i : Fin n) (m : Fin (L + 1)) (t : T) (u : hid m),
            (hidden (Arch.gated relu id hid) 0 θ (X i) m.castSucc * θ.read m) t (Sum.inl u)
              ≠ 0) →
          jacobianRank (Arch.gated relu id hid) 0 X θ
              + ((L + 2) * Fintype.card d ^ 2 + 2 * ∑ m, Fintype.card (hid m)
                + (3 * Fintype.card d - 2))
            ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

end Skips
