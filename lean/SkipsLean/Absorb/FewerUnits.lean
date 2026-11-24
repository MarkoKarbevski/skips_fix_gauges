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
  by_contra hcon
  push Not at hcon
  -- the ReLU blocks with the same weights would satisfy the same equation
  obtain ⟨x, hx⟩ := exists_ne_of_relu_card_lt hd Wr Ww hnd M hdet hm' Wr' Ww'
  exact hx (relu_absorb_of_gelu_absorb Wr Ww Wr' Ww' M hcon x)

/-- An entry of a product of two matrix-valued functions whose entries are analytic is
analytic. (A copy of the private helper `analyticOnNhd_mul_entry` of `SameWidth.lean`.) -/
private theorem analyticOnNhd_mul_entry' {P a b c : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [Fintype b] {F : P → Matrix a b ℝ} {G : P → Matrix b c ℝ}
    (hF : ∀ i j, AnalyticOnNhd ℝ (fun y => F y i j) Set.univ)
    (hG : ∀ i j, AnalyticOnNhd ℝ (fun y => G y i j) Set.univ) (i : a) (j : c) :
    AnalyticOnNhd ℝ (fun y => (F y * G y) i j) Set.univ := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticOnNhd_fun_sum _ fun k _ => (hF i k).mul (hG k j)

/-- An entry of the read is an analytic (linear) function of the weights. -/
private theorem analyticOnNhd_fst_apply' {p q k : Type*} [Fintype p] [Fintype q] [Fintype k]
    (a : p) (i : k) :
    AnalyticOnNhd ℝ (fun W : Matrix p k ℝ × Matrix k q ℝ => W.1 a i) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ a i).comp
    (LinearMap.fst ℝ (Matrix p k ℝ) (Matrix k q ℝ)))

/-- An entry of the write is an analytic (linear) function of the weights. -/
private theorem analyticOnNhd_snd_apply' {p q k : Type*} [Fintype p] [Fintype q] [Fintype k]
    (i : k) (o : q) :
    AnalyticOnNhd ℝ (fun W : Matrix p k ℝ × Matrix k q ℝ => W.2 i o) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ i o).comp
    (LinearMap.snd ℝ (Matrix p k ℝ) (Matrix k q ℝ)))

/-- An analytic function of the weights `(W_read, W_write)` that is not identically zero is nonzero
at generic weights. The Borel structure of the product is given explicitly, as in
`ae_ne_zero_of_analytic_prod` of `SameWidth.lean`: the measure sees the topology of `Matrix`, the
analytic function the one of the norm. -/
private theorem ae_ne_zero_of_analytic_pair {p q k : Type*} [Fintype p] [Fintype q] [Fintype k]
    (μ : Measure (Matrix p k ℝ × Matrix k q ℝ)) [μ.IsAddHaarMeasure]
    {g : Matrix p k ℝ × Matrix k q ℝ → ℝ} (hg : AnalyticOnNhd ℝ g Set.univ)
    (hne : ∃ y, g y ≠ 0) : ∀ᵐ W ∂μ, g W ≠ 0 := by
  have h1 : SecondCountableTopology (Matrix p k ℝ) :=
    inferInstanceAs (SecondCountableTopology (p → k → ℝ))
  have hB : BorelSpace (Matrix p k ℝ × Matrix k q ℝ) := Prod.borelSpace
  exact @ae_ne_zero_of_analytic _ _ _ _ _ hB μ ‹_› _ hg hne

/-- For an invertible `M`, at generic weights `M + W_read[:,S] W_write[S,:]` is invertible for every
set `S` of hidden units: its determinant is a polynomial in the weights that equals `det M ≠ 0` when
the writes vanish. -/
theorem ae_forall_isUnit_det_add_subProd (M : Matrix d d ℝ) (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × Matrix m d ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ∀ S : Finset m, IsUnit (M + subProd S W.1 W.2).det := by
  refine ae_all_iff.2 fun S => ?_
  -- the entries of `M + W_read Π_S W_write` are polynomials in the weights
  have he : ∀ a o, AnalyticOnNhd ℝ (fun W : Matrix d m ℝ × Matrix m d ℝ =>
      (M + subProd S W.1 W.2) a o) Set.univ := by
    intro a o
    simp only [Matrix.add_apply]
    refine analyticOnNhd_const.add ?_
    have h1 : ∀ a k, AnalyticOnNhd ℝ (fun W : Matrix d m ℝ × Matrix m d ℝ =>
        (W.1 * Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0)) a k) Set.univ :=
      analyticOnNhd_mul_entry' (F := fun W : Matrix d m ℝ × Matrix m d ℝ => W.1)
        (G := fun _ => Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0))
        (fun a i => analyticOnNhd_fst_apply' a i) (fun _ _ => analyticOnNhd_const)
    exact analyticOnNhd_mul_entry' (F := fun W : Matrix d m ℝ × Matrix m d ℝ =>
        W.1 * Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0))
      (G := fun W => W.2) h1 (fun i o => analyticOnNhd_snd_apply' i o) a o
  -- so is its determinant, a signed sum of products of entries
  have hg : AnalyticOnNhd ℝ (fun W : Matrix d m ℝ × Matrix m d ℝ =>
      (M + subProd S W.1 W.2).det) Set.univ := by
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => he (σ i) i)
  -- at `W = 0` it is `det M ≠ 0`
  have h0 : (M + subProd S (0 : Matrix d m ℝ × Matrix m d ℝ).1
      (0 : Matrix d m ℝ × Matrix m d ℝ).2).det ≠ 0 := by
    simpa only [subProd, Prod.fst_zero, Prod.snd_zero, Matrix.zero_mul, Matrix.mul_zero,
      add_zero] using hM.ne_zero
  filter_upwards [ae_ne_zero_of_analytic_pair μ hg ⟨0, h0⟩] with W hW
  -- in `ℝ`, a unit is a nonzero number
  exact isUnit_iff_ne_zero.2 hW

/-- **Theorem 3.1 (ii), second half, for ReLU** (Proposition A.11 (ii)): let `M` be invertible. For
generic `θ = (W_read, W_write)` no ReLU block with fewer than `d` more hidden units computes
`x M + B_θ(x)`. -/
theorem ae_not_relu_absorb_of_card_lt (hd : 2 ≤ Fintype.card d) (M : Matrix d d ℝ)
    (hM : IsUnit M.det) (μ : Measure (Matrix d m ℝ × Matrix m d ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
      ∀ (Wr' : Matrix d m' ℝ) (Ww' : Matrix m' d ℝ),
        ∃ x : d → ℝ, x ᵥ* M + vanillaBlock relu W.1 W.2 x ≠ vanillaBlock relu Wr' Ww' x := by
  -- generic blocks are nondegenerate (`d ≥ 2`, and `d` outputs) and every `M + W_read Π_S W_write`
  -- is invertible
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  filter_upwards [ae_nondegenerate hd μ, ae_forall_isUnit_det_add_subProd M hM μ]
    with W hnd hdet
  intro m' _ hm' Wr' Ww'
  exact exists_ne_of_relu_card_lt hd W.1 W.2 hnd M hdet hm' Wr' Ww'

/-- **Theorem 3.1 (ii), second half, for GELU.** -/
theorem ae_not_gelu_absorb_of_card_lt (hd : 2 ≤ Fintype.card d) (M : Matrix d d ℝ)
    (hM : IsUnit M.det) (μ : Measure (Matrix d m ℝ × Matrix m d ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
      ∀ (Wr' : Matrix d m' ℝ) (Ww' : Matrix m' d ℝ),
        ∃ x : d → ℝ, x ᵥ* M + vanillaBlock gelu W.1 W.2 x ≠ vanillaBlock gelu Wr' Ww' x := by
  -- as for ReLU, with the case of GELU of Proposition A.11 (ii)
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  filter_upwards [ae_nondegenerate hd μ, ae_forall_isUnit_det_add_subProd M hM μ]
    with W hnd hdet
  intro m' _ hm' Wr' Ww'
  exact exists_ne_of_gelu_card_lt hd W.1 W.2 hnd M hdet hm' Wr' Ww'

end Skips
