import SkipsLean.Literature.InvarianceOfDomain
import SkipsLean.Activations.ReLU
import SkipsLean.Network.Blocks
import SkipsLean.Dimension.Space

/-!
# ReLU blocks with a skip: folding, and blocks that do not fold

Paper (skips paper): Appendix A.8, "ReLU blocks: folding and dead units", Definition A.31 and
Proposition A.32.

"Unit `i` of block `ℓ` has the read `r_i`, column `i` of `W_read^ℓ`, and the write `r̂_i`, row `i`
of `W_write^ℓ`. Its pre-activation at the input `x` is the number `z_i(x) = h_{ℓ−1}(x) r_i`, and
the unit adds `ReLU(z_i(x)) r̂_i` to the output of the block. The unit is active at `x` if
`z_i(x) > 0`. […] A unit is dead if it is active at no input."

"Definition A.31 (Folding). Let `Φ_ℓ(h) = h + B_ℓ(h)` be the map of `ℝ^{1×d_model}` computed by
residual block `ℓ`. The block folds if `Φ_ℓ` is not injective: two different hidden states give the
same next hidden state."

"Proposition A.32 (Blocks that do not fold keep units alive). Consider a residual network of ReLU
blocks without normalization. (i) If block `ℓ` does not fold, `Φ_ℓ` is a homeomorphism of
`ℝ^{1×d_model}`. (ii) If no block folds, every unit with a nonzero read is active on a nonempty
open set of inputs and inactive on another. In particular, no unit with a nonzero read is dead.
(iii) A block with `‖W_read‖ ‖W_write‖ < 1`, in spectral norm, does not fold."

In this section of the paper "inputs range over all of `ℝ^{1×d_in}`, and `E` has rank `d_model`".

Stated here:

* `blockMapRes θ ℓ` is `Φ_ℓ` on a row; `Folds θ ℓ` is Definition A.31; `UnitInactiveRes θ m j`
  says that unit `j` of block `m` reads a number `≤ 0` at every token of every input (a dead
  unit); `hidden_succ_eq_blockMapRes` says that a row of the next hidden state is `Φ_ℓ` of the row.
* (i) under invariance of domain (`Literature/InvarianceOfDomain.lean`; a hypothesis).
* (ii) under invariance of domain, for `E` of rank `d`: for a unit with a nonzero read and a
  token `t`, the inputs at which it is active at `t` contain a nonempty open set, and so do those
  at which its pre-activation is negative; so it is not dead (if there is a token).
* (iii) with the spectral norms as Lipschitz constants in the Euclidean norm: if
  `‖v W_read‖₂ ≤ a ‖v‖₂` for all rows `v`, `‖u W_write‖₂ ≤ b ‖u‖₂` for all rows `u`, and
  `a b < 1`, the block does not fold. No invariance of domain is used. (The spectral norm of a
  matrix is the least such constant.)
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- The map `Φ_ℓ(h) = h + B_ℓ(h) = h + σ(h W_read^ℓ) W_write^ℓ` of residual block `ℓ` without
normalization, on one row `h`. -/
def blockMapRes (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (ℓ : Fin L)
    (h : d → ℝ) : d → ℝ :=
  h + (fun i => σ ((h ᵥ* θ.read ℓ) i)) ᵥ* θ.write ℓ

/-- **Definition A.31 (Folding):** residual block `ℓ` folds if `Φ_ℓ` is not injective. -/
def Folds (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (ℓ : Fin L) : Prop :=
  ¬ Function.Injective (blockMapRes θ ℓ)

/-- Unit `j` of block `m` of a residual network of MLP blocks without normalization is dead at
`θ`: it reads a number `≤ 0` at every token of every input. -/
def UnitInactiveRes (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L)
    (j : hid m) : Prop :=
  ∀ (x : Matrix T dIn ℝ) (t : T),
    (hidden (Arch.mlp σ id hid) 1 θ x m.castSucc * θ.read m) t j ≤ 0

/-- A row of the hidden state after residual block `ℓ` is `Φ_ℓ` of the row before it. -/
theorem hidden_succ_eq_blockMapRes
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (x : Matrix T dIn ℝ) (ℓ : Fin L)
    (t : T) :
    hidden (Arch.mlp σ id hid) 1 θ x ℓ.succ t
      = blockMapRes θ ℓ (hidden (Arch.mlp σ id hid) 1 θ x ℓ.castSucc t) := by
  sorry

/-- **Proposition A.32 (i), under invariance of domain:** if residual ReLU block `ℓ` does not
fold, `Φ_ℓ` is a homeomorphism of `ℝ^{1×d}`. -/
theorem exists_homeomorph_blockMapRes_of_not_folds (hinv : InvarianceOfDomain d)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (ℓ : Fin L)
    (hℓ : ¬ Folds θ ℓ) :
    ∃ e : (d → ℝ) ≃ₜ (d → ℝ), ∀ h, e h = blockMapRes θ ℓ h := by
  sorry

/-- **Proposition A.32 (ii), under invariance of domain:** let `E` have rank `d` and let no block
of a residual ReLU network fold. For a unit `j` of block `m` with a nonzero read and a token `t`,
there is a nonempty open set of inputs at which the unit is active at `t`, and one at which its
pre-activation at `t` is negative. -/
theorem exists_isOpen_active_of_not_folds (hinv : InvarianceOfDomain d)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hfold : ∀ ℓ, ¬ Folds θ ℓ) (m : Fin L) (j : hid m)
    (hr : (fun a => θ.read m a j) ≠ 0) (t : T) :
    (∃ U : Set (Matrix T dIn ℝ), IsOpen U ∧ U.Nonempty ∧
        ∀ x ∈ U, 0 < (hidden (Arch.mlp relu id hid) 1 θ x m.castSucc * θ.read m) t j) ∧
      ∃ U : Set (Matrix T dIn ℝ), IsOpen U ∧ U.Nonempty ∧
        ∀ x ∈ U, (hidden (Arch.mlp relu id hid) 1 θ x m.castSucc * θ.read m) t j < 0 := by
  sorry

/-- **Proposition A.32 (ii), "In particular, no unit with a nonzero read is dead"** (with at
least one token). -/
theorem not_unitInactiveRes_of_not_folds [Nonempty T] (hinv : InvarianceOfDomain d)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hfold : ∀ ℓ, ¬ Folds θ ℓ) (m : Fin L) (j : hid m)
    (hr : (fun a => θ.read m a j) ≠ 0) : ¬ UnitInactiveRes θ m j := by
  sorry

/-- **Proposition A.32 (iii):** a residual ReLU block with `‖W_read‖ ‖W_write‖ < 1` in spectral
norm does not fold. The spectral norms enter as Lipschitz constants `a`, `b` in the Euclidean
norm. -/
theorem not_folds_of_norm_mul_norm_lt_one
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (ℓ : Fin L) {a b : ℝ}
    (ha : ∀ v : d → ℝ,
      Real.sqrt ((v ᵥ* θ.read ℓ) ⬝ᵥ (v ᵥ* θ.read ℓ)) ≤ a * Real.sqrt (v ⬝ᵥ v))
    (hb : ∀ u : hid ℓ → ℝ,
      Real.sqrt ((u ᵥ* θ.write ℓ) ⬝ᵥ (u ᵥ* θ.write ℓ)) ≤ b * Real.sqrt (u ⬝ᵥ u))
    (hab : a * b < 1) : ¬ Folds θ ℓ := by
  sorry

end Skips
