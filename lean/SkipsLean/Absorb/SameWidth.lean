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
    ∃ S : Finset m, subProd S Wr Ww = -M :=
  -- the ReLU blocks with the same weights satisfy the same equation
  exists_subProd_eq_neg_of_relu_absorb hp Wr Ww hnd M Wr' Ww'
    (relu_absorb_of_gelu_absorb Wr Ww Wr' Ww' M h)

/-- **Theorem 3.1 (i), first sentence, for ReLU** (Corollary A.9): a nondegenerate block absorbs
`x M` at the same width if and only if some set `S` of hidden units has
`W_read[:,S] W_write[S,:] = -M`. -/
theorem relu_absorb_same_width_iff (hp : 2 ≤ Fintype.card p) (Wr : Matrix p m ℝ)
    (Ww : Matrix m q ℝ) (hnd : Nondegenerate Wr Ww) (M : Matrix p q ℝ) :
    (∃ (Wr' : Matrix p m ℝ) (Ww' : Matrix m q ℝ),
        ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x)
      ↔ ∃ S : Finset m, subProd S Wr Ww = -M := by
  constructor
  · rintro ⟨Wr', Ww', h⟩
    exact exists_subProd_eq_neg_of_relu_absorb hp Wr Ww hnd M Wr' Ww' h
  · -- flip the reads of the units of `S`
    rintro ⟨S, hS⟩
    exact ⟨flipCols S Wr, Ww, vanillaBlock_flipCols_of_subProd relu_sub_relu_neg S Wr Ww M hS⟩

/-- **Theorem 3.1 (i), first sentence, for GELU.** -/
theorem gelu_absorb_same_width_iff (hp : 2 ≤ Fintype.card p) (Wr : Matrix p m ℝ)
    (Ww : Matrix m q ℝ) (hnd : Nondegenerate Wr Ww) (M : Matrix p q ℝ) :
    (∃ (Wr' : Matrix p m ℝ) (Ww' : Matrix m q ℝ),
        ∀ x : p → ℝ, x ᵥ* M + vanillaBlock gelu Wr Ww x = vanillaBlock gelu Wr' Ww' x)
      ↔ ∃ S : Finset m, subProd S Wr Ww = -M := by
  constructor
  · rintro ⟨Wr', Ww', h⟩
    exact exists_subProd_eq_neg_of_gelu_absorb hp Wr Ww hnd M Wr' Ww' h
  · -- flip the reads of the units of `S`
    rintro ⟨S, hS⟩
    exact ⟨flipCols S Wr, Ww, vanillaBlock_flipCols_of_subProd gelu_sub_gelu_neg S Wr Ww M hS⟩

variable [Fintype q]

/-- An entry of a product of two matrix-valued functions whose entries are analytic is
analytic. -/
private theorem analyticOnNhd_mul_entry {P a b c : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [Fintype b] {F : P → Matrix a b ℝ} {G : P → Matrix b c ℝ}
    (hF : ∀ i j, AnalyticOnNhd ℝ (fun y => F y i j) Set.univ)
    (hG : ∀ i j, AnalyticOnNhd ℝ (fun y => G y i j) Set.univ) (i : a) (j : c) :
    AnalyticOnNhd ℝ (fun y => (F y * G y) i j) Set.univ := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticOnNhd_fun_sum _ fun k _ => (hF i k).mul (hG k j)

omit [DecidableEq m] in
/-- An entry of the read is an analytic (linear) function of the weights. -/
private theorem analyticOnNhd_fst_apply (a : p) (i : m) :
    AnalyticOnNhd ℝ (fun W : Matrix p m ℝ × Matrix m q ℝ => W.1 a i) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ a i).comp
    (LinearMap.fst ℝ (Matrix p m ℝ) (Matrix m q ℝ)))

omit [DecidableEq m] in
/-- An entry of the write is an analytic (linear) function of the weights. -/
private theorem analyticOnNhd_snd_apply (i : m) (o : q) :
    AnalyticOnNhd ℝ (fun W : Matrix p m ℝ × Matrix m q ℝ => W.2 i o) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ i o).comp
    (LinearMap.snd ℝ (Matrix p m ℝ) (Matrix m q ℝ)))

omit [DecidableEq m] in
/-- An analytic function of the weights `(W_read, W_write)` that is not identically zero is nonzero
at generic weights. The Borel structure of the product is given explicitly: the measure sees the
topology of `Matrix`, the analytic function the one of the norm, and they agree only by
definition. -/
private theorem ae_ne_zero_of_analytic_prod
    (μ : Measure (Matrix p m ℝ × Matrix m q ℝ)) [μ.IsAddHaarMeasure]
    {g : Matrix p m ℝ × Matrix m q ℝ → ℝ} (hg : AnalyticOnNhd ℝ g Set.univ)
    (hne : ∃ y, g y ≠ 0) : ∀ᵐ W ∂μ, g W ≠ 0 := by
  have h1 : SecondCountableTopology (Matrix p m ℝ) :=
    inferInstanceAs (SecondCountableTopology (p → m → ℝ))
  have hB : BorelSpace (Matrix p m ℝ × Matrix m q ℝ) := Prod.borelSpace
  exact @ae_ne_zero_of_analytic _ _ _ _ _ hB μ ‹_› _ hg hne

/-- Generic blocks are nondegenerate (`p ≥ 2` inputs, at least one output). -/
theorem ae_nondegenerate (hp : 2 ≤ Fintype.card p) [Nonempty q]
    (μ : Measure (Matrix p m ℝ × Matrix m q ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, Nondegenerate W.1 W.2 := by
  classical
  obtain ⟨a₁, a₂, ha⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card p by omega)
  obtain ⟨o₀⟩ := ‹Nonempty q›
  -- the columns of the read are nonzero: their entries at `a₁` are
  have h1 : ∀ᵐ W ∂μ, ∀ i : m, W.1 a₁ i ≠ 0 := by
    refine ae_all_iff.2 fun i => ?_
    exact ae_ne_zero_of_analytic_prod μ (analyticOnNhd_fst_apply a₁ i)
      ⟨(Matrix.of fun _ _ => 1, 0), one_ne_zero⟩
  -- the rows of the write are nonzero: their entries at `o₀` are
  have h2 : ∀ᵐ W ∂μ, ∀ i : m, W.2 i o₀ ≠ 0 := by
    refine ae_all_iff.2 fun i => ?_
    exact ae_ne_zero_of_analytic_prod μ (analyticOnNhd_snd_apply i o₀)
      ⟨(0, Matrix.of fun _ _ => 1), one_ne_zero⟩
  -- two columns of the read are not collinear: a `2 × 2` minor does not vanish
  have h3 : ∀ᵐ W ∂μ, ∀ i j : m, i ≠ j →
      W.1 a₁ i * W.1 a₂ j - W.1 a₁ j * W.1 a₂ i ≠ 0 := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hij h
    · -- the read with the entries `(a₁, i)` and `(a₂, j)` equal to `1`, the others `0`
      let R : Matrix p m ℝ := Matrix.of fun a k =>
        if a = a₁ ∧ k = i then 1 else if a = a₂ ∧ k = j then 1 else 0
      have hR : R a₁ i * R a₂ j - R a₁ j * R a₂ i ≠ 0 := by
        simp only [R, Matrix.of_apply, ha, ha.symm, hij, Ne.symm hij, and_self, and_true,
          and_false, ↓reduceIte]
        norm_num
      have hg : AnalyticOnNhd ℝ (fun W : Matrix p m ℝ × Matrix m q ℝ =>
          W.1 a₁ i * W.1 a₂ j - W.1 a₁ j * W.1 a₂ i) Set.univ :=
        ((analyticOnNhd_fst_apply a₁ i).mul (analyticOnNhd_fst_apply a₂ j)).sub
          ((analyticOnNhd_fst_apply a₁ j).mul (analyticOnNhd_fst_apply a₂ i))
      exact (ae_ne_zero_of_analytic_prod μ hg ⟨(R, 0), hR⟩).mono fun _ h _ => h
  filter_upwards [h1, h2, h3] with W h1 h2 h3
  refine ⟨fun i hi => h1 i (congrFun hi a₁), fun i j hij r hr => ?_,
    fun i hi => h2 i (congrFun hi o₀)⟩
  -- if `w_i = r w_j`, the minor of the columns `i`, `j` vanishes
  have e1 : W.1 a₁ i = r * W.1 a₁ j := congrFun hr a₁
  have e2 : W.1 a₂ i = r * W.1 a₂ j := congrFun hr a₂
  apply h3 i j hij
  rw [e1, e2]
  ring

/-- For `M ≠ 0` the condition `W_read[:,S] W_write[S,:] = -M` fails for every `S` at generic
weights: it is polynomial in the weights and fails when the writes vanish. -/
theorem ae_forall_subProd_ne_neg (M : Matrix p q ℝ) (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × Matrix m q ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ∀ S : Finset m, subProd S W.1 W.2 ≠ -M := by
  -- an entry `(a, o)` with `M a o ≠ 0`
  obtain ⟨a, o, hao⟩ : ∃ a o, M a o ≠ 0 := by
    by_contra hc
    exact hM (Matrix.ext fun a o => by_contra fun h => hc ⟨a, o, h⟩)
  refine ae_all_iff.2 fun S => ?_
  -- `W ↦ (W_read Π_S W_write) a o + M a o` is a polynomial, equal to `M a o ≠ 0` at `W = 0`
  have hg : AnalyticOnNhd ℝ (fun W : Matrix p m ℝ × Matrix m q ℝ =>
      subProd S W.1 W.2 a o + M a o) Set.univ := by
    refine AnalyticOnNhd.add ?_ analyticOnNhd_const
    have h1 : ∀ a k, AnalyticOnNhd ℝ (fun W : Matrix p m ℝ × Matrix m q ℝ =>
        (W.1 * Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0)) a k) Set.univ :=
      analyticOnNhd_mul_entry (F := fun W : Matrix p m ℝ × Matrix m q ℝ => W.1)
        (G := fun _ => Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0))
        (fun a i => analyticOnNhd_fst_apply a i) (fun _ _ => analyticOnNhd_const)
    exact analyticOnNhd_mul_entry (F := fun W : Matrix p m ℝ × Matrix m q ℝ =>
        W.1 * Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0))
      (G := fun W => W.2) h1 (fun i o => analyticOnNhd_snd_apply i o) a o
  have h0 : subProd S (0 : Matrix p m ℝ × Matrix m q ℝ).1 (0 : Matrix p m ℝ × Matrix m q ℝ).2 a o
      + M a o ≠ 0 := by
    simpa only [subProd, Prod.fst_zero, Prod.snd_zero, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.zero_apply, zero_add] using hao
  filter_upwards [ae_ne_zero_of_analytic_prod μ hg ⟨0, h0⟩] with W hW hS
  apply hW
  rw [hS, Matrix.neg_apply, neg_add_cancel]

/-- **Theorem 3.1 (i), second sentence, for ReLU:** fix `M ≠ 0`. For generic `θ = (W_read, W_write)`
no ReLU block of the same width computes `x M + B_θ(x)`. -/
theorem ae_not_relu_absorb_same_width (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ) (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × Matrix m q ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ¬ ∃ (Wr' : Matrix p m ℝ) (Ww' : Matrix m q ℝ),
      ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu W.1 W.2 x = vanillaBlock relu Wr' Ww' x := by
  -- `q` is nonempty, since `M ≠ 0`
  have : Nonempty q := by
    by_contra hq
    exact hM (Matrix.ext fun _ o => (hq ⟨o⟩).elim)
  filter_upwards [ae_nondegenerate hp μ, ae_forall_subProd_ne_neg M hM μ] with W hnd hS
  rintro ⟨Wr', Ww', h⟩
  obtain ⟨S, hS'⟩ := exists_subProd_eq_neg_of_relu_absorb hp W.1 W.2 hnd M Wr' Ww' h
  exact hS S hS'

/-- **Theorem 3.1 (i), second sentence, for GELU.** -/
theorem ae_not_gelu_absorb_same_width (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ) (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × Matrix m q ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ¬ ∃ (Wr' : Matrix p m ℝ) (Ww' : Matrix m q ℝ),
      ∀ x : p → ℝ, x ᵥ* M + vanillaBlock gelu W.1 W.2 x = vanillaBlock gelu Wr' Ww' x := by
  -- `q` is nonempty, since `M ≠ 0`
  have : Nonempty q := by
    by_contra hq
    exact hM (Matrix.ext fun _ o => (hq ⟨o⟩).elim)
  filter_upwards [ae_nondegenerate hp μ, ae_forall_subProd_ne_neg M hM μ] with W hnd hS
  rintro ⟨Wr', Ww', h⟩
  obtain ⟨S, hS'⟩ := exists_subProd_eq_neg_of_gelu_absorb hp W.1 W.2 hnd M Wr' Ww' h
  exact hS S hS'

/-! ### Proposition 3.2: networks of one block -/

section OneBlock

variable {T dIn dOut : Type*} {d : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

omit [Fintype T] [Fintype dOut] in
/-- A row of a residual network of one MLP block: `x E D + σ(x E W_read) W_write D`. -/
private theorem eval_residual_row (σ : ℝ → ℝ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (X : Matrix T dIn ℝ) (t : T) :
    eval (Arch.mlp σ id hid) 1 θ X t
      = X t ᵥ* (θ.E * θ.D) + vanillaBlock σ (θ.E * θ.read 0) (θ.write 0 * θ.D) (X t) := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.mlp (T := T) (d := d) σ id hid).χ = id := rfl
  have hf : (Arch.mlp (T := T) (d := d) σ id hid).f 0 = fun M => M.map σ := rfl
  -- `h_1 = h_0 + σ(h_0 W_read) W_write` with `h_0 = X E`
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hχ, hf]
  simp only [id_eq, Pi.one_apply, Matrix.mul_one]
  have e : (X * θ.E + (X * θ.E * θ.read 0).map σ * θ.write 0) * θ.D
      = X * (θ.E * θ.D) + (X * (θ.E * θ.read 0)).map σ * (θ.write 0 * θ.D) := by
    rw [Matrix.add_mul, Matrix.mul_assoc X θ.E θ.D, Matrix.mul_assoc X θ.E (θ.read 0),
      Matrix.mul_assoc]
  rw [e]
  exact congrArg₂ (· + ·) (Matrix.mul_apply_eq_vecMul X _ t)
    (map_mul_mul_row σ (θ.E * θ.read 0) (θ.write 0 * θ.D) X t)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dOut] in
/-- A row of a skipless network of one MLP block: `σ(x E' W_read') W_write' D'`. -/
private theorem eval_skipless_row (σ : ℝ → ℝ) {d' : Type*} [Fintype d']
    (θ' : Params (Arch.mlp (T := T) (d := d') σ id hid) dIn dOut) (X : Matrix T dIn ℝ) (t : T) :
    eval (Arch.mlp σ id hid) 0 θ' X t
      = vanillaBlock σ (θ'.E * θ'.read 0) (θ'.write 0 * θ'.D) (X t) := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.mlp (T := T) (d := d') σ id hid).χ = id := rfl
  have hf : (Arch.mlp (T := T) (d := d') σ id hid).f 0 = fun M => M.map σ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hχ, hf]
  simp only [Pi.zero_apply, Matrix.mul_zero, zero_add, id_eq]
  rw [Matrix.mul_assoc X θ'.E (θ'.read 0), Matrix.mul_assoc _ (θ'.write 0) θ'.D]
  exact map_mul_mul_row σ _ _ X t

omit [Fintype T] [DecidableEq d] in
/-- At generic parameters of one MLP block, `E W_read[:,S] W_write[S,:] D ≠ -E D` for every set
`S` of units, if `E D` can be nonzero: an entry of the difference is a polynomial in the weights,
equal to `(E D)_{a o} ≠ 0` when the write vanishes. -/
private theorem ae_subProd_ne_neg_oneBlock {σ : ℝ → ℝ} [DecidableEq (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ S : Finset (hid 0),
      subProd S (θ.E * θ.read 0) (θ.write 0 * θ.D) ≠ -(θ.E * θ.D) := by
  obtain ⟨a⟩ : Nonempty dIn := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨o⟩ : Nonempty dOut := Fintype.card_pos_iff.1 (by omega)
  refine ae_all_iff.2 fun S => ?_
  -- the entry `(a, o)` of `E W_read Π_S W_write D + E D` is a polynomial in the parameters
  have hg : AnalyticOnNhd ℝ (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
      subProd S (θ.E * θ.read 0) (θ.write 0 * θ.D) a o + (θ.E * θ.D) a o) Set.univ := by
    have hED : AnalyticOnNhd ℝ (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        (θ.E * θ.D) a o) Set.univ :=
      analyticOnNhd_mul_apply (Params.linE (A := Arch.mlp (T := T) (d := d) σ id hid) (dIn := dIn) (dOut := dOut))
        Params.linD a o
    refine AnalyticOnNhd.add ?_ hED
    have h1 : ∀ a k, AnalyticOnNhd ℝ
        (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
          (θ.E * θ.read 0 * Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0)) a k)
        Set.univ :=
      analyticOnNhd_mul_entry
        (F := fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => θ.E * θ.read 0)
        (G := fun _ => Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0))
        (fun a i => analyticOnNhd_E_mul_read (A := Arch.mlp (T := T) (d := d) σ id hid) (dOut := dOut) 0 a i)
        (fun _ _ => analyticOnNhd_const)
    exact analyticOnNhd_mul_entry
      (F := fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        θ.E * θ.read 0 * Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0))
      (G := fun θ => θ.write 0 * θ.D) h1
      (fun i o => analyticOnNhd_write_mul_D (A := Arch.mlp (T := T) (d := d) σ id hid) (dIn := dIn) 0 i o) a o
  -- at the parameters with `W_write = 0` and `E`, `D` of ones it is `card d ≠ 0`
  let θ₀ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => 0, fun _ => 0, Matrix.of fun _ _ => 1⟩
  have h0 : subProd S (θ₀.E * θ₀.read 0) (θ₀.write 0 * θ₀.D) a o + (θ₀.E * θ₀.D) a o ≠ 0 := by
    simp only [θ₀, subProd, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_apply, zero_add]
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact sum_one_mul_one_ne_zero hd
  filter_upwards [ae_ne_zero_of_analytic μ hg ⟨θ₀, h0⟩] with θ hθ hS
  exact hθ (by rw [hS, Matrix.neg_apply, neg_add_cancel])

/-- Proposition 3.2 for an activation for which Corollary A.9 holds. -/
private theorem ae_ne_skipless_oneBlock_of {σ : ℝ → ℝ} [Nonempty T] [DecidableEq (hid 0)]
    (hσ : ∀ (Wr : Matrix dIn (hid 0) ℝ) (Ww : Matrix (hid 0) dOut ℝ), Nondegenerate Wr Ww →
      ∀ (M : Matrix dIn dOut ℝ) (Wr' : Matrix dIn (hid 0) ℝ) (Ww' : Matrix (hid 0) dOut ℝ),
        (∀ x : dIn → ℝ, x ᵥ* M + vanillaBlock σ Wr Ww x = vanillaBlock σ Wr' Ww' x) →
        ∃ S : Finset (hid 0), subProd S Wr Ww = -M)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∀ (d' : Type) [Fintype d']
      (θ' : Params (Arch.mlp (T := T) (d := d') σ id hid) dIn dOut),
      ∃ X : Matrix T dIn ℝ,
        eval (Arch.mlp σ id hid) 1 θ X ≠ eval (Arch.mlp σ id hid) 0 θ' X := by
  filter_upwards [ae_oneBlockGeneric μ hd hdIn hdOut hhid,
    ae_subProd_ne_neg_oneBlock μ hd hdIn hdOut] with θ hθ hS
  intro d' _ θ'
  by_contra hall
  have heq : ∀ X : Matrix T dIn ℝ,
      eval (Arch.mlp σ id hid) 1 θ X = eval (Arch.mlp σ id hid) 0 θ' X :=
    fun X => by_contra fun hne => hall ⟨X, hne⟩
  -- on an input whose rows all equal `x`, the networks are the blocks of Corollary A.9, with the
  -- reads `E W_read`, the writes `W_write D` and `M = E D`
  have hrow : ∀ x : dIn → ℝ, x ᵥ* (θ.E * θ.D)
      + vanillaBlock σ (θ.E * θ.read 0) (θ.write 0 * θ.D) x
      = vanillaBlock σ (θ'.E * θ'.read 0) (θ'.write 0 * θ'.D) x := by
    intro x
    have h := congrFun (heq (Matrix.of fun _ => x)) (Classical.arbitrary T)
    rwa [eval_residual_row, eval_skipless_row] at h
  obtain ⟨S, hS'⟩ := hσ _ _ ⟨hθ.col_ne_zero, hθ.col_not_collinear, hθ.row_ne_zero⟩ _ _ _ hrow
  exact hS S hS'

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
  classical
  -- Corollary A.9 with `p = d_in` (`d_in ≥ d ≥ 2`)
  exact ae_ne_skipless_oneBlock_of (fun Wr Ww hnd M Wr' Ww' h =>
    exists_subProd_eq_neg_of_relu_absorb (by omega) Wr Ww hnd M Wr' Ww' h) μ hd hdIn hdOut hhid

/-- **Proposition 3.2 for GELU.** -/
theorem ae_ne_skipless_oneBlock_gelu [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∀ (d' : Type) [Fintype d']
      (θ' : Params (Arch.mlp (T := T) (d := d') gelu id hid) dIn dOut),
      ∃ X : Matrix T dIn ℝ,
        eval (Arch.mlp gelu id hid) 1 θ X ≠ eval (Arch.mlp gelu id hid) 0 θ' X := by
  classical
  -- Corollary A.9 with `p = d_in` (`d_in ≥ d ≥ 2`)
  exact ae_ne_skipless_oneBlock_of (fun Wr Ww hnd M Wr' Ww' h =>
    exists_subProd_eq_neg_of_gelu_absorb (by omega) Wr Ww hnd M Wr' Ww' h) μ hd hdIn hdOut hhid

end OneBlock

end Skips
