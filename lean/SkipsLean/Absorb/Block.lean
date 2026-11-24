import SkipsLean.Activations.ReLU
import SkipsLean.Activations.Gaussian
import SkipsLean.Network.Blocks

/-!
# One block and a linear term: mirror units and flipped reads

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Section 2 ("Blocks", "Absorbing a linear
term", equation (2)), Section 3.1 (the two constructions before Theorem 3.1), and
Proposition A.11 (i).

A vanilla block with the read `W_read` and the write `W_write` computes `B(x) = σ(x W_read) W_write`
on a row `x`; a gated block with the read `[W_g | W_v]` computes `(σ(x W_g) ⊙ x W_v) W_write`.
The question of the paper is whether a block of the same kind computes `x M + B(x)`.

ReLU and GELU satisfy `σ(z) - σ(-z) = z` (equation (3)). Two constructions follow.
* *With more units* (Proposition A.11 (i), the first half of Theorem 3.1 (ii)): a unit and its
  mirror image add up to a linear term of rank one, so `d` new units add any `x M` when the read has
  rank `d`.
* *At the same width* (the "if" of Theorem 3.1 (i)): flipping the reads of the units of a set `S`
  changes the block by `- x W_read[:,S] W_write[S,:]`.

The statements are for rectangular weights (`p` inputs, `q` outputs), as Corollary A.9 of the paper,
and for activations with `σ(z) - σ(-z) = c z`, as Proposition 5.4. A width is an index type.
-/

namespace Skips

open Matrix

variable {p q m : Type*} [Fintype p] [Fintype m]

/-- A vanilla block on a row, equation (1) of the paper: `B(x) = σ(x W_read) W_write`. -/
def vanillaBlock (σ : ℝ → ℝ) (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ) (x : p → ℝ) : q → ℝ :=
  (fun i => σ ((x ᵥ* Wr) i)) ᵥ* Ww

/-- A gated block on a row: unit `i` multiplies `σ((x W_g)_i)` by its value `(x W_v)_i`. -/
def gatedBlock (σ : ℝ → ℝ) (Wg Wv : Matrix p m ℝ) (Ww : Matrix m q ℝ) (x : p → ℝ) : q → ℝ :=
  (fun i => σ ((x ᵥ* Wg) i) * (x ᵥ* Wv) i) ᵥ* Ww

/-- On a hidden state `h` a vanilla block acts on each token (row) separately. -/
theorem map_mul_mul_row {T : Type*} (σ : ℝ → ℝ) (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ)
    (h : Matrix T p ℝ) (t : T) :
    ((h * Wr).map σ * Ww) t = vanillaBlock σ Wr Ww (h t) := by
  -- both sides at `o` are `∑ i, σ (∑ a, h t a * Wr a i) * Ww i o`
  funext o
  simp only [vanillaBlock, Matrix.mul_apply, Matrix.map_apply, Matrix.vecMul, dotProduct]

/-- The read with the columns of the units in `S` multiplied by `-1`. -/
def flipCols [DecidableEq m] (S : Finset m) (Wr : Matrix p m ℝ) : Matrix p m ℝ :=
  Matrix.of fun i j => if j ∈ S then -Wr i j else Wr i j

/-- `W_read[:,S] W_write[S,:] = W_read Π_S W_write`, with `Π_S` the diagonal projector on the units
of `S` (Appendix A, "Setting"). -/
def subProd [DecidableEq m] (S : Finset m) (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ) :
    Matrix p q ℝ :=
  Wr * Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0) * Ww

/-- ReLU satisfies equation (3): `σ(z) - σ(-z) = z`. (For GELU: `gelu_sub_gelu_neg`.) -/
theorem relu_sub_relu_neg (z : ℝ) : relu z - relu (-z) = z := by
  simp only [relu]
  rcases le_total z 0 with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
  · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring

variable {σ : ℝ → ℝ} {c : ℝ}

/-- **Flipping reads** (Section 3.1, "At the same width"): if `σ(z) - σ(-z) = c z`, flipping the
reads of the units in `S` changes the block by `- c x W_read[:,S] W_write[S,:]`. -/
theorem vanillaBlock_flipCols [DecidableEq m] (hσ : ∀ z, σ z - σ (-z) = c * z) (S : Finset m)
    (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ) (x : p → ℝ) :
    vanillaBlock σ (flipCols S Wr) Ww x
      = vanillaBlock σ Wr Ww x - c • (x ᵥ* subProd S Wr Ww) := by
  sorry

/-- **Theorem 3.1 (i), "if"** (for every `M`): if `σ(z) - σ(-z) = z` and a set `S` of units has
`W_read[:,S] W_write[S,:] = -M`, the block with the reads of `S` flipped, of the same width,
computes `x M + B(x)`. -/
theorem vanillaBlock_flipCols_of_subProd [DecidableEq m] (hσ : ∀ z, σ z - σ (-z) = z)
    (S : Finset m) (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ) (M : Matrix p q ℝ)
    (hS : subProd S Wr Ww = -M) (x : p → ℝ) :
    x ᵥ* M + vanillaBlock σ Wr Ww x = vanillaBlock σ (flipCols S Wr) Ww x := by
  sorry

/-- **Proposition A.11 (i)** (the first half of Theorem 3.1 (ii)), "With more units": if
`σ(z) - σ(-z) = c z` with `c ≠ 0` and the read has rank `p` (the number of its rows; `d` in the
paper), then for every `M` a block with `p` more hidden units computes `x M + B(x)`. The new block
keeps the reads of the old units; it mirrors `p` units whose reads form an invertible matrix. (The
paper states it for `c = 1` and invertible `M`; the construction does not use that `M` is
invertible.) -/
theorem exists_vanillaBlock_add_linear [DecidableEq p] (hσ : ∀ z, σ z - σ (-z) = c * z)
    (hc : c ≠ 0) (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ) (hr : Wr.rank = Fintype.card p)
    (M : Matrix p q ℝ) :
    ∃ (Wr' : Matrix p (m ⊕ p) ℝ) (Ww' : Matrix (m ⊕ p) q ℝ),
      (∀ i j, Wr' i (Sum.inl j) = Wr i j) ∧
      ∀ x : p → ℝ, x ᵥ* M + vanillaBlock σ Wr Ww x = vanillaBlock σ Wr' Ww' x := by
  sorry

end Skips
