import SkipsLean.Residual.DeadUnits
import SkipsLean.Residual.FoldingOpen
import SkipsLean.Dimension.RescalingMlp
import SkipsLean.Generic.Params

/-!
# On the open set of Proposition A.33 (i) the count of the symmetries is missed

Paper (skips paper): the sentence after the proof of Proposition A.33: "So on the open set of
Proposition A.33(i) the residual network has functional dimension below `P − d_model² − s`. For
ReLU networks, the bound of Theorem 4.2 is therefore attained on one open set of weights
(Lemma A.30) and missed on another."

Stated here by putting Proposition A.33 (i) (`Residual/FoldingOpen.lean`) and (ii)
(`Residual/DeadUnits.lean`) together: for `d_in ≥ d ≥ 1` and at least `d` units in block
`ℓ.castSucc`, a nonempty open set of weights of the residual ReLU network on which block
`ℓ.castSucc` folds and unit `j` of block `ℓ.succ` is dead, and at almost every point of which
`fd ≤ P − d² − s − (2d − 1)`. As for Proposition E.1 of the dimension paper, the bound is stated
at almost every point of the open set (where `E` has rank `d` and no read column vanishes); the
paper says "on the open set".
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin (L + 1) → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **The sentence after Proposition A.33:** for `d_in ≥ d ≥ 1` and at least `d` units in block
`ℓ.castSucc`, there is a nonempty open set of weights of the residual ReLU network on which
block `ℓ.castSucc` folds and unit `j` of block `ℓ.succ` is dead, and at almost every point of it
the functional dimension is at most `P − d² − s − (2d − 1)`, below `P − d² − s`. -/
theorem exists_isOpen_folds_funDim_add_le_relu [Nonempty d]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (ℓ : Fin L) (j : hid ℓ.succ)
    (hq : Fintype.card d ≤ Fintype.card (hid ℓ.castSucc)) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, Folds θ ℓ.castSucc ∧ UnitInactiveRes θ ℓ.succ j) ∧
      ∀ (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
        [μ.IsAddHaarMeasure], ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp relu id hid) 1 θ
          + (Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m) + (2 * Fintype.card d - 1))
        ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  classical
  -- the open set of Proposition A.33 (i)
  obtain ⟨U, hU, hUne, hUin⟩ :=
    exists_isOpen_folds_unitInactiveRes_relu (T := T) (dIn := dIn) (dOut := dOut) ℓ j hq
  refine ⟨U, hU, hUne, hUin, fun μ _ => ?_⟩
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  -- at almost every `θ`: `E` has rank `d` and no read column vanishes
  filter_upwards [ae_isUnit_det_submatrix μ, ae_read_col_ne_zero μ] with θ h1 h2 hθU
  have hE : θ.E.rank = Fintype.card d :=
    le_antisymm (Matrix.rank_le_card_width θ.E)
      ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (h1.2.2.1 ρ))).symm.le.trans
        (Matrix.rank_submatrix_le θ.E ρ id))
  -- Proposition A.33 (ii) with the one dead unit `(ℓ.succ, j)`, dead at all parameters of `U`
  have h := funDim_add_le_residual_of_eventually_unitInactive relu_homogeneous
    (fun _ hz => max_eq_right hz) θ ({⟨ℓ.succ, j⟩} : Finset (Σ m, hid m))
    (fun p hp => by
      rw [Finset.mem_singleton] at hp
      subst hp
      exact Filter.mem_of_superset (hU.mem_nhds hθU) fun θ' h' => (hUin θ' h').2)
    hE h2
  simpa using h

end Skips
