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
  rcases le_total 0 y with hy | hy
  · -- `y ≥ 0`: `y Φ(y) - y = -y (1 - Φ(y)) = -y Φ(-y)`
    rw [abs_of_nonneg hy, gaussCdf_neg, gelu, relu, max_eq_left hy]
    ring
  · -- `y ≤ 0`: `y Φ(y) - 0 = -|y| Φ(-|y|)`, with `|y| = -y`
    rw [abs_of_nonpos hy, neg_neg, gelu, relu, max_eq_right hy]
    ring

/-- `φ(u) ≤ 1`: `e^{-u²/2} ≤ 1 ≤ √(2π)`. -/
private theorem gaussPdf_le_one (u : ℝ) : gaussPdf u ≤ 1 := by
  have h1 : Real.exp (-u ^ 2 / 2) ≤ 1 :=
    Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg u)) two_pos.le)
  have h2 : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  rw [gaussPdf, div_le_one (by linarith)]
  linarith

/-- `|GELU(y) - ReLU(y)|` is bounded. (The paper's bound is `κ < 0.17`; any bound serves.) -/
theorem abs_gelu_sub_relu_le (y : ℝ) : |gelu y - relu y| ≤ 1 := by
  rw [gelu_sub_relu, abs_neg]
  rcases (abs_nonneg y).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul, abs_zero]
    exact zero_le_one
  · -- `u Φ(-u) = u (1 - Φ(u)) ≤ φ(u) ≤ 1` for `u = |y| > 0`
    rw [abs_of_pos (mul_pos hpos (gaussCdf_pos _)), gaussCdf_neg]
    calc |y| * (1 - gaussCdf |y|) ≤ |y| * (gaussPdf |y| / |y|) :=
          mul_le_mul_of_nonneg_left (one_sub_gaussCdf_le hpos) hpos.le
      _ = gaussPdf |y| := by field_simp
      _ ≤ 1 := gaussPdf_le_one _

/-- An output coordinate of a vanilla block. -/
private theorem vanillaBlock_apply {k : Type*} [Fintype k] (σ : ℝ → ℝ) (W : Matrix p k ℝ)
    (V : Matrix k q ℝ) (z : p → ℝ) (o : q) :
    vanillaBlock σ W V z o = ∑ i, σ ((z ᵥ* W) i) * V i o := rfl

/-- ReLU is positively homogeneous: `ReLU(t y) = t ReLU(y)` for `t > 0`. -/
private theorem relu_mul_of_pos {t : ℝ} (ht : 0 < t) (y : ℝ) : relu (t * y) = t * relu y := by
  rw [relu, relu, mul_max_of_nonneg _ _ ht.le, mul_zero]

/-- `|∑ᵢ (GELU(t yᵢ) - t ReLU(yᵢ)) wᵢ| ≤ ∑ᵢ |wᵢ|` for `t > 0`. -/
private theorem abs_sum_gelu_sub_le {ι : Type*} [Fintype ι] {t : ℝ} (ht : 0 < t) (y w : ι → ℝ) :
    |∑ i, (gelu (t * y i) - t * relu (y i)) * w i| ≤ ∑ i, |w i| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, ← relu_mul_of_pos ht]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_gelu_sub_relu_le _)

/-- **GELU to ReLU along rays** (proof of Theorem 4.5, for one block): if a GELU block absorbs
`x M` into a GELU block, of any width, then the ReLU blocks with the same weights satisfy the same
equation. (Evaluate at `t x`, divide by `t`, and let `t → ∞`.) -/
theorem relu_absorb_of_gelu_absorb {m' : Type*} [Fintype m'] (Wr : Matrix p m ℝ)
    (Ww : Matrix m q ℝ) (Wr' : Matrix p m' ℝ) (Ww' : Matrix m' q ℝ) (M : Matrix p q ℝ)
    (h : ∀ x : p → ℝ, x ᵥ* M + vanillaBlock gelu Wr Ww x = vanillaBlock gelu Wr' Ww' x) :
    ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x := by
  intro x
  funext o
  -- the GELU equation at `t x`, coordinate `o`
  have hG : ∀ t : ℝ, t * (x ᵥ* M) o + ∑ i, gelu (t * (x ᵥ* Wr) i) * Ww i o
      = ∑ j, gelu (t * (x ᵥ* Wr') j) * Ww' j o := by
    intro t
    have h1 := congrFun (h (t • x)) o
    simpa only [Pi.add_apply, vanillaBlock_apply, Matrix.smul_vecMul, Pi.smul_apply,
      smul_eq_mul] using h1
  -- the defect `D` of the ReLU equation at `o` has `|t D| ≤ C` for all `t > 0`
  obtain ⟨D, hD⟩ : ∃ D, D = (x ᵥ* M) o + ∑ i, relu ((x ᵥ* Wr) i) * Ww i o
      - ∑ j, relu ((x ᵥ* Wr') j) * Ww' j o := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = ∑ i, |Ww i o| + ∑ j, |Ww' j o| := ⟨_, rfl⟩
  have hbound : ∀ t : ℝ, 0 < t → |t * D| ≤ C := by
    intro t ht
    -- `t D = ∑ⱼ (GELU(t y'ⱼ) - t ReLU(y'ⱼ)) ŵ'ⱼ - ∑ᵢ (GELU(t yᵢ) - t ReLU(yᵢ)) ŵᵢ`
    have e : t * D = ∑ j, (gelu (t * (x ᵥ* Wr') j) - t * relu ((x ᵥ* Wr') j)) * Ww' j o
        - ∑ i, (gelu (t * (x ᵥ* Wr) i) - t * relu ((x ᵥ* Wr) i)) * Ww i o := by
      simp only [sub_mul, Finset.sum_sub_distrib, hD, mul_add, mul_sub, Finset.mul_sum,
        mul_assoc]
      linarith [hG t]
    rw [e, hC]
    refine (abs_sub _ _).trans ?_
    linarith [abs_sum_gelu_sub_le ht (fun j => (x ᵥ* Wr') j) (fun j => Ww' j o),
      abs_sum_gelu_sub_le ht (fun i => (x ᵥ* Wr) i) (fun i => Ww i o)]
  -- hence `D = 0`: else `t = (C + 1)/|D|` gives `|t D| = C + 1`
  have hD0 : D = 0 := by
    by_contra hne
    have hC0 : 0 ≤ C := hC ▸ add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have hDpos : 0 < |D| := abs_pos.2 hne
    have ht : 0 < (C + 1) / |D| := div_pos (by linarith) hDpos
    have h1 := hbound _ ht
    rw [abs_mul, abs_of_pos ht, div_mul_cancel₀ _ hDpos.ne'] at h1
    linarith
  rw [Pi.add_apply, vanillaBlock_apply, vanillaBlock_apply]
  linarith

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
