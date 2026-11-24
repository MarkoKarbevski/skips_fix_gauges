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

/-- ReLU satisfies `σ(z) + σ(-z) = |z|`: the even part of ReLU is `|z|/2`. (A copy of the private
helper `relu_add_relu_neg` of `SameWidth.lean`.) -/
private theorem relu_add_relu_neg' (z : ℝ) : relu z + relu (-z) = |z| := by
  simp only [relu]
  rcases le_total z 0 with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h), abs_of_nonpos h]; ring
  · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h), abs_of_nonneg h]; ring

/-- **Fewer conditions than unknowns.** If there are fewer vectors `u k` than coordinates, some row
`x ≠ 0` has `x ⬝ᵥ u k = 0` for every `k`: the `card n` rows `a ↦ (u k a)_k` of `ℝ^ι` are linearly
dependent. -/
theorem exists_ne_zero_forall_dotProduct_eq_zero {n ι : Type*} [Fintype n] [Fintype ι]
    (u : ι → n → ℝ) (h : Fintype.card ι < Fintype.card n) :
    ∃ x : n → ℝ, x ≠ 0 ∧ ∀ k, x ⬝ᵥ u k = 0 := by
  have hli : ¬ LinearIndependent ℝ (fun a : n => fun k : ι => u k a) := fun hli => by
    have h1 := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at h1
    omega
  -- a vanishing combination `∑ₐ g_a (u k a)_k = 0` with `g ≠ 0`; take `x = g`
  obtain ⟨g, hg, a, ha⟩ := Fintype.not_linearIndependent_iff.1 hli
  refine ⟨g, fun h0 => ha (congrFun h0 a), fun k => ?_⟩
  have h1 := congrFun hg k
  simpa only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h1

/-- **Proposition A.11 (ii) for ReLU, under the conditions of its proof.** Let the block be
nondegenerate and let `M + W_read[:,S] W_write[S,:]` be invertible for every set `S` of hidden
units. Then no ReLU block with fewer than `m + d` hidden units computes `x M + B(x)`. (The paper
assumes `d ≥ 2`; the proof does not use it.) -/
theorem exists_ne_of_relu_card_lt (Wr : Matrix d m ℝ)
    (Ww : Matrix m d ℝ) (hnd : Nondegenerate Wr Ww) (M : Matrix d d ℝ)
    (hdet : ∀ S : Finset m, IsUnit (M + subProd S Wr Ww).det)
    {m' : Type*} [Fintype m'] (hm' : Fintype.card m' < Fintype.card m + Fintype.card d)
    (Wr' : Matrix d m' ℝ) (Ww' : Matrix m' d ℝ) :
    ∃ x : d → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x ≠ vanillaBlock relu Wr' Ww' x := by
  -- Route (a shortcut of the paper's count of mixed classes): by (★) every unit `i` has a unit
  -- `f i` of the new block that reads `ρ_i w_i`, `ρ_i ≠ 0`, and `f` is injective. The other units,
  -- fewer than `d`, are invisible to some row `x ≠ 0`. For that `x` no unit `i` with `x w_i ≠ 0`
  -- has a second unit on its hyperplane, so `ŵ_i = |ρ_i| ŵ'_{f i}`, and the odd part at `x` gives
  -- `x (M + W_read[:,S] W_write[S,:]) = 0` with `S = {i | ρ_i < 0}`: the matrix is singular.
  classical
  by_contra hcon
  push Not at hcon
  -- the equation at `x` and at `-x`, at the output coordinate `o`
  have hpre : ∀ (x : d → ℝ) (o : d), (x ᵥ* M) o + ∑ k, relu (x ⬝ᵥ Wrᵀ k) * Ww k o
      = ∑ j, relu (x ⬝ᵥ Wr'ᵀ j) * Ww' j o := fun x o => congrFun (hcon x) o
  have hpm : ∀ (x : d → ℝ) (o : d), -(x ᵥ* M) o + ∑ k, relu (-(x ⬝ᵥ Wrᵀ k)) * Ww k o
      = ∑ j, relu (-(x ⬝ᵥ Wr'ᵀ j)) * Ww' j o := by
    intro x o
    have h2 := hpre (-x) o
    simp only [Matrix.neg_vecMul, Pi.neg_apply, neg_dotProduct] at h2
    exact h2
  -- the even part: `|x W_read| W_write = |x W_read'| W_write'`
  have hEven : ∀ x : d → ℝ,
      (fun k => |(x ᵥ* Wr) k|) ᵥ* Ww = (fun j => |(x ᵥ* Wr') j|) ᵥ* Ww' := by
    intro x
    funext o
    show ∑ k, |x ⬝ᵥ Wrᵀ k| * Ww k o = ∑ j, |x ⬝ᵥ Wr'ᵀ j| * Ww' j o
    simp only [← relu_add_relu_neg', add_mul, Finset.sum_add_distrib]
    linarith [hpre x o, hpm x o]
  -- the odd part: `x W_read W_write + 2 x M = x W_read' W_write'`
  have hOdd : ∀ (x : d → ℝ) (o : d), 2 * (x ᵥ* M) o + ∑ k, (x ⬝ᵥ Wrᵀ k) * Ww k o
      = ∑ j, (x ⬝ᵥ Wr'ᵀ j) * Ww' j o := by
    intro x o
    have e1 : ∑ k, (x ⬝ᵥ Wrᵀ k) * Ww k o
        = ∑ k, relu (x ⬝ᵥ Wrᵀ k) * Ww k o - ∑ k, relu (-(x ⬝ᵥ Wrᵀ k)) * Ww k o := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [← sub_mul, relu_sub_relu_neg]
    have e2 : ∑ j, (x ⬝ᵥ Wr'ᵀ j) * Ww' j o
        = ∑ j, relu (x ⬝ᵥ Wr'ᵀ j) * Ww' j o - ∑ j, relu (-(x ⬝ᵥ Wr'ᵀ j)) * Ww' j o := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [← sub_mul, relu_sub_relu_neg]
    linarith [hpre x o, hpm x o]
  -- (★) at unit `i`, with `J` the units `j` whose `w'_j` is a multiple `r_j w_i` (zero included)
  have hJr : ∀ i, ∃ (J : Finset m') (r : m' → ℝ), (∀ j ∈ J, Wr'ᵀ j = r j • Wrᵀ i) ∧
      (∀ j ∉ J, ∀ t : ℝ, Wr'ᵀ j ≠ t • Wrᵀ i) := by
    intro i
    have hr : ∀ j, ∃ t : ℝ, (∃ t' : ℝ, Wr'ᵀ j = t' • Wrᵀ i) → Wr'ᵀ j = t • Wrᵀ i := fun j => by
      by_cases hj : ∃ t' : ℝ, Wr'ᵀ j = t' • Wrᵀ i
      · obtain ⟨t', ht'⟩ := hj
        exact ⟨t', fun _ => ht'⟩
      · exact ⟨0, fun h' => absurd h' hj⟩
    choose r hr using hr
    exact ⟨Finset.univ.filter (fun j => ∃ t' : ℝ, Wr'ᵀ j = t' • Wrᵀ i), r,
      fun j hj => hr j (Finset.mem_filter.1 hj).2,
      fun j hj t ht => hj (Finset.mem_filter.2 ⟨Finset.mem_univ _, t, ht⟩)⟩
  have hstar : ∀ i (J : Finset m') (r : m' → ℝ), (∀ j ∈ J, Wr'ᵀ j = r j • Wrᵀ i) →
      (∀ j ∉ J, ∀ t : ℝ, Wr'ᵀ j ≠ t • Wrᵀ i) → Ww i = ∑ j ∈ J, |r j| • Ww' j :=
    fun i J r hJ hJc => write_eq_sum_of_abs_eq Wr Ww Wr' Ww' hEven i (hnd.col_ne_zero i)
      (fun k hk t => hnd.col_not_collinear k i hk t) J r hJ hJc
  -- since `ŵ_i ≠ 0`, some unit `f i` reads a nonzero multiple `ρ_i w_i` of `w_i`
  have hex : ∀ i, ∃ j, ∃ ρ : ℝ, ρ ≠ 0 ∧ Wr'ᵀ j = ρ • Wrᵀ i := by
    intro i
    obtain ⟨J, r, hJ, hJc⟩ := hJr i
    have hne : ∑ j ∈ J, |r j| • Ww' j ≠ 0 := hstar i J r hJ hJc ▸ hnd.row_ne_zero i
    obtain ⟨j, hj, hj0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact ⟨j, r j, fun h0 => hj0 (by rw [h0, abs_zero, zero_smul]), hJ j hj⟩
  choose f ρ hρ hf using hex
  -- two columns of the read that are collinear are the same column
  have hsame : ∀ a b (r₁ r₂ : ℝ), r₁ ≠ 0 → r₁ • Wrᵀ a = r₂ • Wrᵀ b → a = b := by
    intro a b r₁ r₂ h1 h12
    by_contra hab
    apply hnd.col_not_collinear a b hab (r₁⁻¹ * r₂)
    rw [mul_smul, ← h12, smul_smul, inv_mul_cancel₀ h1, one_smul]
  -- so the units `f i` are distinct
  have hinj : Function.Injective f := by
    intro a b hab
    exact hsame a b (ρ a) (ρ b) (hρ a) (by rw [← hf a, ← hf b, hab])
  -- the other units `E` of the new block: fewer than `d`, as `m' < m + d`
  obtain ⟨E, hE⟩ : ∃ E : Finset m', E = (Finset.univ.image f)ᶜ := ⟨_, rfl⟩
  -- (`d` is nonempty without `hd`: else `hm'` makes `m` nonempty, and a column of the read, a
  -- vector with no coordinates, would be `0`)
  have hd0 : 0 < Fintype.card d := by
    by_contra h0
    have : IsEmpty d := Fintype.card_eq_zero_iff.1 (by omega)
    obtain ⟨i⟩ : Nonempty m := Fintype.card_pos_iff.1 (by omega)
    exact hnd.col_ne_zero i (funext fun a => isEmptyElim a)
  have hEcard : Fintype.card E < Fintype.card d := by
    rw [Fintype.card_coe, hE, Finset.card_compl, Finset.card_image_of_injective _ hinj,
      Finset.card_univ]
    omega
  -- a row `x ≠ 0` that none of them sees
  obtain ⟨x, hx0, hxE⟩ := exists_ne_zero_forall_dotProduct_eq_zero (fun k : E => Wr'ᵀ k.1) hEcard
  have hxE' : ∀ j, j ∉ Finset.univ.image f → x ⬝ᵥ Wr'ᵀ j = 0 := fun j hj =>
    hxE ⟨j, by rw [hE, Finset.mem_compl]; exact hj⟩
  -- if `x w_i ≠ 0`, no other unit reads a nonzero multiple of `w_i`, so `ŵ_i = |ρ_i| ŵ'_{f i}`
  have hw : ∀ i, x ⬝ᵥ Wrᵀ i ≠ 0 → Ww i = |ρ i| • Ww' (f i) := by
    intro i hxi
    obtain ⟨J, r, hJ, hJc⟩ := hJr i
    have hfi : f i ∈ J := by
      by_contra hn
      exact hJc (f i) hn (ρ i) (hf i)
    have hr : r (f i) = ρ i :=
      smul_left_injective ℝ (hnd.col_ne_zero i) ((hJ (f i) hfi).symm.trans (hf i))
    rw [hstar i J r hJ hJc, Finset.sum_eq_single_of_mem (f i) hfi, hr]
    intro j hj hne
    have hr0 : r j = 0 := by
      by_contra h0
      by_cases hjf : j ∈ Finset.univ.image f
      · -- `j = f i'` with `ρ_{i'} w_{i'} = r_j w_i`, so `i' = i`
        obtain ⟨i', -, rfl⟩ := Finset.mem_image.1 hjf
        exact hne (congrArg f
          (hsame i' i (ρ i') (r (f i')) (hρ i') ((hf i').symm.trans (hJ _ hj))))
      · -- `x w'_j = r_j (x w_i) ≠ 0`, but `x` does not see `j`
        have h1 := hxE' j hjf
        rw [hJ j hj, dotProduct_smul, smul_eq_mul] at h1
        exact mul_ne_zero h0 hxi h1
    rw [hr0, abs_zero, zero_smul]
  -- `S`: the units whose read changes sign. Then `x (M + W_read[:,S] W_write[S,:]) = 0`
  obtain ⟨S, hS⟩ : ∃ S : Finset m, S = Finset.univ.filter (fun i => ρ i < 0) := ⟨_, rfl⟩
  have hmemS : ∀ i, i ∈ S ↔ ρ i < 0 := fun i => by
    rw [hS, Finset.mem_filter]
    exact and_iff_right (Finset.mem_univ i)
  have hker : x ᵥ* (M + subProd S Wr Ww) = 0 := by
    funext o
    have hO := hOdd x o
    -- reindex the new units by `f`; the others do not see `x`
    have hre : ∑ j, (x ⬝ᵥ Wr'ᵀ j) * Ww' j o = ∑ i, (x ⬝ᵥ Wr'ᵀ (f i)) * Ww' (f i) o := by
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f)),
        Finset.sum_image (fun a _ b _ hab => hinj hab)]
      intro j _ hj
      rw [hxE' j hj, zero_mul]
    -- unit `f i` contributes `±` the term of unit `i`, with `-` exactly for `i ∈ S`
    have hterm : ∀ i, (x ⬝ᵥ Wr'ᵀ (f i)) * Ww' (f i) o - (x ⬝ᵥ Wrᵀ i) * Ww i o
        = -2 * ((x ⬝ᵥ Wrᵀ i) * (if i ∈ S then 1 else 0) * Ww i o) := by
      intro i
      rw [hf i, dotProduct_smul, smul_eq_mul]
      by_cases hxi : x ⬝ᵥ Wrᵀ i = 0
      · rw [hxi]; ring
      · have e2 : Ww i o = |ρ i| * Ww' (f i) o := congrFun (hw i hxi) o
        rw [e2]
        rcases lt_or_gt_of_ne (hρ i) with hneg | hpos
        · simp only [abs_of_neg hneg, (hmemS i).2 hneg, ↓reduceIte]; ring
        · simp only [abs_of_pos hpos, (hmemS i).not.2 (not_lt.2 hpos.le), ↓reduceIte]; ring
    have hsum : ∑ i, (x ⬝ᵥ Wr'ᵀ (f i)) * Ww' (f i) o - ∑ i, (x ⬝ᵥ Wrᵀ i) * Ww i o
        = -2 * ∑ i, (x ⬝ᵥ Wrᵀ i) * (if i ∈ S then 1 else 0) * Ww i o := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => hterm i
    have hsp : (x ᵥ* subProd S Wr Ww) o
        = ∑ i, (x ⬝ᵥ Wrᵀ i) * (if i ∈ S then 1 else 0) * Ww i o := by
      rw [subProd, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
      show ∑ i, ((x ᵥ* Wr) ᵥ* Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0)) i
        * Ww i o = _
      simp only [Matrix.vecMul_diagonal]
      rfl
    rw [Matrix.vecMul_add, Pi.add_apply, hsp, Pi.zero_apply]
    linarith
  -- a nonzero row in the left kernel: the determinant vanishes, against `hdet S`
  exact (hdet S).ne_zero (Matrix.exists_vecMul_eq_zero_iff.1 ⟨x, hx0, hker⟩)

/-- **Proposition A.11 (ii) for GELU, under the same conditions** (from the case of ReLU by the
reduction along rays, `relu_absorb_of_gelu_absorb`). -/
theorem exists_ne_of_gelu_card_lt (Wr : Matrix d m ℝ)
    (Ww : Matrix m d ℝ) (hnd : Nondegenerate Wr Ww) (M : Matrix d d ℝ)
    (hdet : ∀ S : Finset m, IsUnit (M + subProd S Wr Ww).det)
    {m' : Type*} [Fintype m'] (hm' : Fintype.card m' < Fintype.card m + Fintype.card d)
    (Wr' : Matrix d m' ℝ) (Ww' : Matrix m' d ℝ) :
    ∃ x : d → ℝ, x ᵥ* M + vanillaBlock gelu Wr Ww x ≠ vanillaBlock gelu Wr' Ww' x := by
  by_contra hcon
  push Not at hcon
  -- the ReLU blocks with the same weights would satisfy the same equation
  obtain ⟨x, hx⟩ := exists_ne_of_relu_card_lt Wr Ww hnd M hdet hm' Wr' Ww'
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
  exact exists_ne_of_relu_card_lt W.1 W.2 hnd M hdet hm' Wr' Ww'

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
  exact exists_ne_of_gelu_card_lt W.1 W.2 hnd M hdet hm' Wr' Ww'

end Skips
