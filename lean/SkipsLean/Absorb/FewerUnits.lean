import SkipsLean.Absorb.SameWidth

/-!
# Fewer than `d` more units do not suffice

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Proposition A.11 (ii), which is the second
half of Theorem 3.1 (ii).

Let `σ` be ReLU or GELU and let `M` be an invertible `d × d` matrix. For generic weights
`θ = (W_read, W_write)` of a block of width `m`, no block of width less than `m + d` computes
`x M + B_θ(x)`. The proof of the paper excludes the weights for which the block is degenerate or
`M + W_read[:,S] W_write[S,:]` is singular for some set `S` of units; outside them, every unit of
the absorbing block is matched to a class of collinear reads, and every class that holds reads of
both signs costs one more unit and adds a term of rank at most one.

With `exists_vanillaBlock_add_linear` (Proposition A.11 (i)): for almost every block the linear term
`x M`, and so the skip `M = I`, is worth exactly `d` units.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {d m : Type*} [Fintype d] [DecidableEq d] [Fintype m] [DecidableEq m]

/-- **Proposition A.11 (ii) for ReLU, under the conditions of its proof.** Let the block be
nondegenerate and let `M + W_read[:,S] W_write[S,:]` be invertible for every set `S` of hidden
units. Then no ReLU block with fewer than `m + d` hidden units computes `x M + B(x)`. -/
theorem exists_ne_of_relu_card_lt (hd : 2 ≤ Fintype.card d) (Wr : Matrix d m ℝ)
    (Ww : Matrix m d ℝ) (hnd : Nondegenerate Wr Ww) (M : Matrix d d ℝ)
    (hdet : ∀ S : Finset m, IsUnit (M + subProd S Wr Ww).det)
    {m' : Type*} [Fintype m'] (hm' : Fintype.card m' < Fintype.card m + Fintype.card d)
    (Wr' : Matrix d m' ℝ) (Ww' : Matrix m' d ℝ) :
    ∃ x : d → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x ≠ vanillaBlock relu Wr' Ww' x := by
  sorry

/-- **Proposition A.11 (ii) for GELU, under the same conditions** (from the case of ReLU by the
reduction along rays, `relu_absorb_of_gelu_absorb`). -/
theorem exists_ne_of_gelu_card_lt (hd : 2 ≤ Fintype.card d) (Wr : Matrix d m ℝ)
    (Ww : Matrix m d ℝ) (hnd : Nondegenerate Wr Ww) (M : Matrix d d ℝ)
    (hdet : ∀ S : Finset m, IsUnit (M + subProd S Wr Ww).det)
    {m' : Type*} [Fintype m'] (hm' : Fintype.card m' < Fintype.card m + Fintype.card d)
    (Wr' : Matrix d m' ℝ) (Ww' : Matrix m' d ℝ) :
    ∃ x : d → ℝ, x ᵥ* M + vanillaBlock gelu Wr Ww x ≠ vanillaBlock gelu Wr' Ww' x := by
  sorry

/-- For an invertible `M`, at generic weights `M + W_read[:,S] W_write[S,:]` is invertible for every
set `S` of hidden units: its determinant is a polynomial in the weights that equals `det M ≠ 0` when
the writes vanish. -/
theorem ae_forall_isUnit_det_add_subProd (M : Matrix d d ℝ) (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × Matrix m d ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ∀ S : Finset m, IsUnit (M + subProd S W.1 W.2).det := by
  sorry

/-- **Theorem 3.1 (ii), second half, for ReLU** (Proposition A.11 (ii)): let `M` be invertible. For
generic `θ = (W_read, W_write)` no ReLU block with fewer than `d` more hidden units computes
`x M + B_θ(x)`. -/
theorem ae_not_relu_absorb_of_card_lt (hd : 2 ≤ Fintype.card d) (M : Matrix d d ℝ)
    (hM : IsUnit M.det) (μ : Measure (Matrix d m ℝ × Matrix m d ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
      ∀ (Wr' : Matrix d m' ℝ) (Ww' : Matrix m' d ℝ),
        ∃ x : d → ℝ, x ᵥ* M + vanillaBlock relu W.1 W.2 x ≠ vanillaBlock relu Wr' Ww' x := by
  sorry

/-- **Theorem 3.1 (ii), second half, for GELU.** -/
theorem ae_not_gelu_absorb_of_card_lt (hd : 2 ≤ Fintype.card d) (M : Matrix d d ℝ)
    (hM : IsUnit M.det) (μ : Measure (Matrix d m ℝ × Matrix m d ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
      ∀ (Wr' : Matrix d m' ℝ) (Ww' : Matrix m' d ℝ),
        ∃ x : d → ℝ, x ᵥ* M + vanillaBlock gelu W.1 W.2 x ≠ vanillaBlock gelu Wr' Ww' x := by
  sorry

end Skips
