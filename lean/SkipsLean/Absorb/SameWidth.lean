import SkipsLean.Absorb.Block
import SkipsLean.OneBlock.Mlp

/-!
# Absorption at the same width: only by flipped reads

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Theorem 3.1 (i) and Proposition 3.2, with
Theorem A.4, Corollary A.9 and the reduction of GELU to ReLU along rays (proof of Theorem 4.5).

Let `σ` be ReLU or GELU and let the block `B(x) = σ(x W_read) W_write` be nondegenerate: the columns
of `W_read` are nonzero and pairwise non-collinear, and the rows of `W_write` are nonzero. A block of
the same width computes `x M + B(x)` if and only if some set `S` of hidden units has
`W_read[:,S] W_write[S,:] = -M` (Corollary A.9; the "if" is `vanillaBlock_flipCols_of_subProd`).
For `M ≠ 0` this holds only on a set of weights of measure zero.

The paper proves the "only if" for ReLU through the kinks of `|x w_i|` (Theorem A.4) and for GELU
through ridge functions (Theorem A.7). Here the case of GELU is obtained from the case of ReLU by
the paper's reduction along rays: `|GELU(t y)/t - ReLU(y)| ≤ κ/t`, so a GELU block equation implies
the ReLU block equation with the same weights.

Weights are rectangular (`p` inputs, `q` outputs), as in Corollary A.9. "Generic" refers to an
additive Haar measure on the pairs `(W_read, W_write)`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {p q m : Type*} [Fintype p] [Fintype m]

/-- A block is **nondegenerate** if the columns of `W_read` are nonzero and pairwise non-collinear
(no one of them is a scalar multiple of another) and the rows of `W_write` are nonzero. -/
structure Nondegenerate (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ) : Prop where
  col_ne_zero : ∀ i, Wrᵀ i ≠ 0
  col_not_collinear : ∀ i j, i ≠ j → ∀ r : ℝ, Wrᵀ i ≠ r • Wrᵀ j
  row_ne_zero : ∀ i, Ww i ≠ 0

/-! ### GELU and ReLU along rays -/

/-- `GELU(y) - ReLU(y) = -|y| Φ(-|y|)` (proof of Theorem 4.5). -/
theorem gelu_sub_relu (y : ℝ) : gelu y - relu y = -(|y| * gaussCdf (-|y|)) := by
  sorry

/-- `|GELU(y) - ReLU(y)|` is bounded. (The paper's bound is `κ < 0.17`; any bound serves.) -/
theorem abs_gelu_sub_relu_le (y : ℝ) : |gelu y - relu y| ≤ 1 := by
  sorry

/-- **GELU to ReLU along rays** (proof of Theorem 4.5, for one block): if a GELU block absorbs
`x M` into a GELU block, of any width, then the ReLU blocks with the same weights satisfy the same
equation. (Evaluate at `t x`, divide by `t`, and let `t → ∞`.) -/
theorem relu_absorb_of_gelu_absorb {m' : Type*} [Fintype m'] (Wr : Matrix p m ℝ)
    (Ww : Matrix m q ℝ) (Wr' : Matrix p m' ℝ) (Ww' : Matrix m' q ℝ) (M : Matrix p q ℝ)
    (h : ∀ x : p → ℝ, x ᵥ* M + vanillaBlock gelu Wr Ww x = vanillaBlock gelu Wr' Ww' x) :
    ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x := by
  sorry

/-! ### Corollary A.9 and Theorem 3.1 (i) -/

variable [DecidableEq m]

/-- **Corollary A.9 / Theorem A.4, "only if", for ReLU.** Let `p ≥ 2` and let the block be
nondegenerate. If a ReLU block of the same width computes `x M + B(x)`, then some set `S` of hidden
units has `W_read[:,S] W_write[S,:] = -M`. -/
theorem exists_subProd_eq_neg_of_relu_absorb (hp : 2 ≤ Fintype.card p) (Wr : Matrix p m ℝ)
    (Ww : Matrix m q ℝ) (hnd : Nondegenerate Wr Ww) (M : Matrix p q ℝ) (Wr' : Matrix p m ℝ)
    (Ww' : Matrix m q ℝ)
    (h : ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x) :
    ∃ S : Finset m, subProd S Wr Ww = -M := by
  sorry

/-- **Corollary A.9, "only if", for GELU.** -/
theorem exists_subProd_eq_neg_of_gelu_absorb (hp : 2 ≤ Fintype.card p) (Wr : Matrix p m ℝ)
    (Ww : Matrix m q ℝ) (hnd : Nondegenerate Wr Ww) (M : Matrix p q ℝ) (Wr' : Matrix p m ℝ)
    (Ww' : Matrix m q ℝ)
    (h : ∀ x : p → ℝ, x ᵥ* M + vanillaBlock gelu Wr Ww x = vanillaBlock gelu Wr' Ww' x) :
    ∃ S : Finset m, subProd S Wr Ww = -M := by
  sorry

/-- **Theorem 3.1 (i), first sentence, for ReLU** (Corollary A.9): a nondegenerate block absorbs
`x M` at the same width if and only if some set `S` of hidden units has
`W_read[:,S] W_write[S,:] = -M`. -/
theorem relu_absorb_same_width_iff (hp : 2 ≤ Fintype.card p) (Wr : Matrix p m ℝ)
    (Ww : Matrix m q ℝ) (hnd : Nondegenerate Wr Ww) (M : Matrix p q ℝ) :
    (∃ (Wr' : Matrix p m ℝ) (Ww' : Matrix m q ℝ),
        ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x)
      ↔ ∃ S : Finset m, subProd S Wr Ww = -M := by
  sorry

/-- **Theorem 3.1 (i), first sentence, for GELU.** -/
theorem gelu_absorb_same_width_iff (hp : 2 ≤ Fintype.card p) (Wr : Matrix p m ℝ)
    (Ww : Matrix m q ℝ) (hnd : Nondegenerate Wr Ww) (M : Matrix p q ℝ) :
    (∃ (Wr' : Matrix p m ℝ) (Ww' : Matrix m q ℝ),
        ∀ x : p → ℝ, x ᵥ* M + vanillaBlock gelu Wr Ww x = vanillaBlock gelu Wr' Ww' x)
      ↔ ∃ S : Finset m, subProd S Wr Ww = -M := by
  sorry

variable [Fintype q]

/-- Generic blocks are nondegenerate (`p ≥ 2` inputs, at least one output). -/
theorem ae_nondegenerate (hp : 2 ≤ Fintype.card p) [Nonempty q]
    (μ : Measure (Matrix p m ℝ × Matrix m q ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, Nondegenerate W.1 W.2 := by
  sorry

/-- For `M ≠ 0` the condition `W_read[:,S] W_write[S,:] = -M` fails for every `S` at generic
weights: it is polynomial in the weights and fails when the writes vanish. -/
theorem ae_forall_subProd_ne_neg (M : Matrix p q ℝ) (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × Matrix m q ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ∀ S : Finset m, subProd S W.1 W.2 ≠ -M := by
  sorry

/-- **Theorem 3.1 (i), second sentence, for ReLU:** fix `M ≠ 0`. For generic `θ = (W_read, W_write)`
no ReLU block of the same width computes `x M + B_θ(x)`. -/
theorem ae_not_relu_absorb_same_width (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ) (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × Matrix m q ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ¬ ∃ (Wr' : Matrix p m ℝ) (Ww' : Matrix m q ℝ),
      ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu W.1 W.2 x = vanillaBlock relu Wr' Ww' x := by
  sorry

/-- **Theorem 3.1 (i), second sentence, for GELU.** -/
theorem ae_not_gelu_absorb_same_width (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ) (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × Matrix m q ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ¬ ∃ (Wr' : Matrix p m ℝ) (Ww' : Matrix m q ℝ),
      ∀ x : p → ℝ, x ᵥ* M + vanillaBlock gelu W.1 W.2 x = vanillaBlock gelu Wr' Ww' x := by
  sorry

/-! ### Proposition 3.2: networks of one block -/

section OneBlock

variable {T dIn dOut : Type*} {d : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Proposition 3.2 for ReLU:** for almost every choice of weights, a residual network of one
ReLU block equals no skipless network of one ReLU block of the same width (with its own model
dimension, embedding, read, write and readout). Scope of the paper: `d_in, d_out, d_hidden ≥ d ≥ 2`. -/
theorem ae_ne_skipless_oneBlock_relu [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∀ (d' : Type) [Fintype d']
      (θ' : Params (Arch.mlp (T := T) (d := d') relu id hid) dIn dOut),
      ∃ X : Matrix T dIn ℝ,
        eval (Arch.mlp relu id hid) 1 θ X ≠ eval (Arch.mlp relu id hid) 0 θ' X := by
  sorry

/-- **Proposition 3.2 for GELU.** -/
theorem ae_ne_skipless_oneBlock_gelu [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∀ (d' : Type) [Fintype d']
      (θ' : Params (Arch.mlp (T := T) (d := d') gelu id hid) dIn dOut),
      ∃ X : Matrix T dIn ℝ,
        eval (Arch.mlp gelu id hid) 1 θ X ≠ eval (Arch.mlp gelu id hid) 0 θ' X := by
  sorry

end OneBlock

end Skips
