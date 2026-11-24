import SkipsLean.Residual.Folding

/-!
# An open set of weights on which a block folds and the next block has a dead unit

Paper (skips paper): Appendix A.8, Proposition A.33 (i) and its proof.

"(i) There is a nonempty open set of weights on which block 1 folds and block 2 has a dead unit."

"(i) Let block 1 hold the `d_model` units of the example above, with `W_read = −I` and
`W_write = 2I`. Give its other units zero writes. Let a unit of block 2 have a read `r` whose
entries are all negative. Then `Φ_1(h) r < 0` for every `h ≠ 0`, since `Φ_1(h)` is a nonzero vector
with no negative entry. By compactness of the unit sphere, `max_{‖h‖=1} Φ_1(h) r < 0` persists
under small changes of all the weights. Since the perturbed `Φ_1` is still positively homogeneous,
`Φ_1(h) r < 0` then holds for every `h ≠ 0`. As `h_1(x) = Φ_1(xE)` and `Φ_1(0) = 0`, the unit is
active at no input, so it is dead. And `Φ_1` misses the half-space `{h : hr > 0}`, so it is not
onto, and block 1 folds by Proposition A.32 (i)."

Stated here, for a residual network of ReLU blocks `Fin (L + 1)` without normalization, a block
`ℓ.succ` after the first and a unit `j` of it (the paper's blocks 1 and 2 are `ℓ.castSucc` and
`ℓ.succ`): if block `ℓ.castSucc` has at least `d` units, there is a nonempty open set of weights on
which block `ℓ.castSucc` folds and unit `j` of block `ℓ.succ` is dead.

The statement does not take invariance of domain as a hypothesis: that the block folds at every
parameter of the open set can be shown directly (near the example, `Φ` is close to the identity
around a row with positive entries and close to a reflection around its mirror image, and both
images contain a common ball).
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin (L + 1) → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)]

/-- **Proposition A.33 (i) of the skips paper:** for `d ≥ 1` and at least `d` units in block
`ℓ.castSucc`, there is a nonempty open set of weights of the residual ReLU network on which block
`ℓ.castSucc` folds and unit `j` of the next block `ℓ.succ` is dead. -/
theorem exists_isOpen_folds_unitInactiveRes_relu [Nonempty d] (ℓ : Fin L) (j : hid ℓ.succ)
    (hq : Fintype.card d ≤ Fintype.card (hid ℓ.castSucc)) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ ∀ θ ∈ U, Folds θ ℓ.castSucc ∧ UnitInactiveRes θ ℓ.succ j := by
  sorry

end Skips
