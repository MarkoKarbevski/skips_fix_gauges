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
  -- the flipped read: unit `i ∈ S` reads `-(x w_i)`
  have hy : ∀ i, (x ᵥ* flipCols S Wr) i = if i ∈ S then -(x ᵥ* Wr) i else (x ᵥ* Wr) i := by
    intro i
    by_cases hi : i ∈ S
    · simp only [flipCols, Matrix.vecMul, dotProduct, Matrix.of_apply, hi, ↓reduceIte, mul_neg,
        Finset.sum_neg_distrib]
    · simp only [flipCols, Matrix.vecMul, dotProduct, Matrix.of_apply, hi, ↓reduceIte]
  -- `x W_read[:,S] W_write[S,:]` keeps the units of `S` in the read
  have hsub : x ᵥ* subProd S Wr Ww = (fun i => if i ∈ S then (x ᵥ* Wr) i else 0) ᵥ* Ww := by
    have hd : (x ᵥ* Wr) ᵥ* Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0)
        = fun i => if i ∈ S then (x ᵥ* Wr) i else 0 := by
      funext i
      rw [Matrix.vecMul_diagonal]
      by_cases hi : i ∈ S <;> simp only [hi, ↓reduceIte, mul_one, mul_zero]
    rw [subProd, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hd]
  unfold vanillaBlock
  rw [hsub, ← Matrix.smul_vecMul, ← Matrix.sub_vecMul]
  congr 1
  funext i
  -- `σ(-y) = σ(y) - c y`
  have h1 := hσ ((x ᵥ* Wr) i)
  by_cases hi : i ∈ S
  · simp only [hy, hi, ↓reduceIte, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · simp only [hy, hi, ↓reduceIte, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_zero, sub_zero]

/-- **Theorem 3.1 (i), "if"** (for every `M`): if `σ(z) - σ(-z) = z` and a set `S` of units has
`W_read[:,S] W_write[S,:] = -M`, the block with the reads of `S` flipped, of the same width,
computes `x M + B(x)`. -/
theorem vanillaBlock_flipCols_of_subProd [DecidableEq m] (hσ : ∀ z, σ z - σ (-z) = z)
    (S : Finset m) (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ) (M : Matrix p q ℝ)
    (hS : subProd S Wr Ww = -M) (x : p → ℝ) :
    x ᵥ* M + vanillaBlock σ Wr Ww x = vanillaBlock σ (flipCols S Wr) Ww x := by
  -- `c = 1`, and `x W_read[:,S] W_write[S,:] = x (-M) = -(x M)`
  have h := vanillaBlock_flipCols (c := 1) (fun z => by rw [hσ z, one_mul]) S Wr Ww x
  rw [h, hS, Matrix.vecMul_neg, one_smul]
  abel

/-- A matrix with `d` rows and rank `d` has `d` columns that form an invertible matrix: a maximal
linearly independent family of columns spans the column space, so it has `d` members. -/
private theorem exists_isUnit_det_submatrix [DecidableEq p] (Wr : Matrix p m ℝ)
    (hr : Wr.rank = Fintype.card p) : ∃ e : p → m, IsUnit (Wr.submatrix id e).det := by
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' ℝ (fun j => Wr.col j)
  have : Finite κ := hli.finite
  have := Fintype.ofFinite κ
  -- the family has `finrank (span of the columns) = rank = card p` members
  have hcard : Fintype.card κ = Fintype.card p := by
    have h := finrank_span_eq_card hli
    rw [hsp] at h
    have h2 := Wr.rank_eq_finrank_span_cols
    have h3 : Set.range (fun j => Wr.col j) = Set.range Wr.col := rfl
    rw [h3, ← h2] at h
    omega
  let f : p ≃ κ := Fintype.equivOfCardEq hcard.symm
  refine ⟨a ∘ f, ?_⟩
  have hK : LinearIndependent ℝ (Wr.submatrix id (a ∘ f)).col := hli.comp f f.injective
  exact (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_col_iff_isUnit.1 hK)

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
  classical
  -- `p` columns of the read form an invertible matrix `K`
  obtain ⟨e, he⟩ := exists_isUnit_det_submatrix Wr hr
  obtain ⟨K, hK⟩ : ∃ K : Matrix p p ℝ, K = Wr.submatrix id e := ⟨_, rfl⟩
  have hKu : IsUnit K.det := hK ▸ he
  -- `N` is the matrix of the rows `b_k`, with `c K N = M`
  obtain ⟨N, hN⟩ : ∃ N : Matrix p q ℝ, N = c⁻¹ • (K⁻¹ * M) := ⟨_, rfl⟩
  have hKN : M = c • (K * N) := by
    rw [hN, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu, Matrix.one_mul,
      smul_smul, mul_inv_cancel₀ hc, one_smul]
  -- the new read: the old units, then the mirror units with the columns `-w_{e k}`
  obtain ⟨Wr', hWr1, hWr2⟩ : ∃ W : Matrix p (m ⊕ p) ℝ,
      (∀ i j, W i (Sum.inl j) = Wr i j) ∧ (∀ i k, W i (Sum.inr k) = -Wr i (e k)) :=
    ⟨Matrix.of fun i s => Sum.elim (fun j => Wr i j) (fun k => -Wr i (e k)) s,
      fun _ _ => rfl, fun _ _ => rfl⟩
  -- the new write: `b_k` is added to the row of unit `e k`; the mirror unit `k` has the row `-b_k`
  obtain ⟨Ww', hWw1, hWw2⟩ : ∃ W : Matrix (m ⊕ p) q ℝ,
      (∀ j o, W (Sum.inl j) o = Ww j o + ∑ k, if e k = j then N k o else 0) ∧
      (∀ k o, W (Sum.inr k) o = -N k o) :=
    ⟨Matrix.of fun s o => Sum.elim (fun j => Ww j o + ∑ k, if e k = j then N k o else 0)
      (fun k => -N k o) s, fun _ _ => rfl, fun _ _ => rfl⟩
  refine ⟨Wr', Ww', hWr1, fun x => ?_⟩
  -- the pre-activations of the new units
  have hyl : ∀ j, (x ᵥ* Wr') (Sum.inl j) = (x ᵥ* Wr) j := fun j => by
    simp only [Matrix.vecMul, dotProduct, hWr1]
  have hyr : ∀ k, (x ᵥ* Wr') (Sum.inr k) = -(x ᵥ* Wr) (e k) := fun k => by
    simp only [Matrix.vecMul, dotProduct, hWr2, mul_neg, Finset.sum_neg_distrib]
  have hout : ∀ (f : m → ℝ) (W : Matrix m q ℝ) (o : q), (f ᵥ* W) o = ∑ i, f i * W i o :=
    fun _ _ _ => rfl
  funext o
  simp only [Pi.add_apply, vanillaBlock]
  rw [hout, show ∀ (f : m ⊕ p → ℝ) (W : Matrix (m ⊕ p) q ℝ) (o : q),
    (f ᵥ* W) o = ∑ i, f i * W i o from fun _ _ _ => rfl, Fintype.sum_sum_type]
  simp only [hyl, hyr, hWw1, hWw2]
  -- the units `e k` give `σ(y_{e k}) N_k`
  have h1 : ∑ j, σ ((x ᵥ* Wr) j) * (Ww j o + ∑ k, if e k = j then N k o else 0)
      = ∑ j, σ ((x ᵥ* Wr) j) * Ww j o + ∑ k, σ ((x ᵥ* Wr) (e k)) * N k o := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  -- `x M = c (x K) N`
  have h2 : (x ᵥ* M) o = ∑ k, c * (x ᵥ* Wr) (e k) * N k o := by
    have hxK : ∀ k, (x ᵥ* K) k = (x ᵥ* Wr) (e k) := fun k => by
      simp only [hK, Matrix.vecMul, dotProduct, Matrix.submatrix_apply, id]
    rw [hKN, Matrix.vecMul_smul, ← Matrix.vecMul_vecMul, Pi.smul_apply, smul_eq_mul]
    rw [show ∀ (f : p → ℝ) (W : Matrix p q ℝ) (o : q), (f ᵥ* W) o = ∑ i, f i * W i o from
      fun _ _ _ => rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hxK k]; ring
  -- `σ(y) N + σ(-y) (-N) = c y N`
  have h3 : ∑ k, σ ((x ᵥ* Wr) (e k)) * N k o + ∑ k, σ (-(x ᵥ* Wr) (e k)) * -N k o
      = ∑ k, c * (x ᵥ* Wr) (e k) * N k o := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    linear_combination (N k o) * hσ ((x ᵥ* Wr) (e k))
  rw [h1, h2, ← h3]
  ring

end Skips
