import SkipsLean.Residual.OneChangeOfBasis
import Mathlib.Analysis.Matrix.Order

/-!
# Triangular or symmetric skips under pre-RMSNorm

Paper (skips paper), Theorem A.12 (i): "Triangular or symmetric skips. Let `Q_0 = I`, and for
`ℓ = 1, …, L` let `Q_{ℓ−1}ᵀ A_ℓ = R_ℓ Q_ℓᵀ` be an RQ factorization, with `R_ℓ` upper triangular
with positive diagonal and `Q_ℓ` orthogonal. The network with the skips `R_ℓ`, the reads
`Q_{ℓ−1}ᵀ W_read^ℓ`, the writes `W_write^ℓ Q_ℓ` and the readout `Q_Lᵀ D` computes the same
function. So does the network built in the same way from the polar decompositions
`Q_{ℓ−1}ᵀ A_ℓ = S_ℓ Q_ℓᵀ`, with `S_ℓ` symmetric positive definite in place of `R_ℓ`."

The theorem is about "pre-RMSNorm networks with `ε ≥ 0`, and the network with learned skips of (2)
with `χ = N_ε`, whose skips `A_ℓ` are invertible in (i) and (ii)".

Its proof: "With `Q_0 = I` and the `Q_ℓ` of the statement, the skip `A_ℓ` becomes
`Q_{ℓ−1}ᵀ A_ℓ Q_ℓ = R_ℓ`; the RQ factorization of the invertible matrix `Q_{ℓ−1}ᵀ A_ℓ` exists, and
is unique. The same computation with the polar decompositions gives `Q_{ℓ−1}ᵀ A_ℓ Q_ℓ = S_ℓ`:
every invertible matrix `X` is `X = S Qᵀ` with `S = (X Xᵀ)^{1/2}` symmetric positive definite and
`Qᵀ = S⁻¹ X` orthogonal, uniquely. The readout absorbs the last factor, `D ↦ Q_Lᵀ D`."

Here:

* the two factorizations of one invertible matrix, with their uniqueness;
* the two networks. The skips after the change are `cobSkip S Q ℓ = Q_{ℓ−1}⁻¹ A_ℓ Q_ℓ`
  (`Symmetry/ChangeOfBasis.lean`), and the parameters are `θ.cob Q Q`: the embedding `E Q_0`, the
  reads `Q_{ℓ−1}⁻¹ W_read^ℓ`, the writes `W_write^ℓ Q_ℓ`, the readout `Q_L⁻¹ D`; for an orthogonal
  `Q` the inverse is the transpose. The statement holds for every real `ε` (`rmsNorm ε` is a total
  function).

`Matrix.PosDef` is Mathlib's notion: Hermitian (for real matrices: symmetric) with
`0 < x ⬝ᵥ (M *ᵥ x)` for every `x ≠ 0`. `BlockTriangular id` is "upper triangular" (entries below
the diagonal vanish), as in `exists_cob_learned_upperTriangular` of
`Residual/OneChangeOfBasis.lean`, which is the first network below without "positive diagonal" and
for skips that need not be invertible.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn]
variable {A : Arch T d L}

/-! ### One invertible matrix -/

omit [Fintype d] [DecidableEq d] in
/-- A real positive semidefinite matrix is symmetric. -/
private theorem transpose_eq_of_posSemidef_lsp {S : Matrix d d ℝ} (hS : S.PosSemidef) :
    Sᵀ = S := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact hS.isHermitian

open scoped MatrixOrder in
/-- A positive semidefinite square root. -/
private theorem exists_sqrt_lsp {P : Matrix d d ℝ} (hP : P.PosSemidef) :
    ∃ S : Matrix d d ℝ, S.PosSemidef ∧ S * S = P :=
  ⟨CFC.sqrt P, nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P), CFC.sqrt_mul_sqrt_self P hP.nonneg⟩

open scoped MatrixOrder in
/-- The positive semidefinite square root is unique. -/
private theorem eq_of_mul_self_eq_lsp {S S' : Matrix d d ℝ} (hS : S.PosSemidef)
    (hS' : S'.PosSemidef) (h : S * S = S' * S') : S = S' :=
  (CFC.mul_self_eq_mul_self_iff S S' hS.nonneg hS'.nonneg).mp h

/-- **The polar decomposition** ("every invertible matrix `X` is `X = S Qᵀ` with
`S = (X Xᵀ)^{1/2}` symmetric positive definite and `Qᵀ = S⁻¹ X` orthogonal"). -/
theorem exists_posDef_mul_orthogonal_transpose (X : Matrix d d ℝ) (hX : IsUnit X.det) :
    ∃ S Q : Matrix d d ℝ, S.PosDef ∧ Q ∈ Matrix.orthogonalGroup d ℝ ∧ X = S * Qᵀ := by
  -- `P = X Xᵀ` is positive semidefinite; `S = P^{1/2}`
  have hP : (X * Xᵀ).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose X
  obtain ⟨S, hS0, hSS⟩ := exists_sqrt_lsp hP
  have hST : Sᵀ = S := transpose_eq_of_posSemidef_lsp hS0
  -- `det S ≠ 0`, so `S` is positive definite
  have hdet : S.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hSS
    rw [det_mul, det_mul, det_transpose, h0, zero_mul] at h1
    exact hX.ne_zero (mul_self_eq_zero.mp h1.symm)
  have hSu : IsUnit S := (Matrix.isUnit_iff_isUnit_det S).mpr (Ne.isUnit hdet)
  have hSinv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hSu)
  have hinvS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hSu)
  -- `Q = Xᵀ S⁻¹`, so `Qᵀ = S⁻¹ X`
  have hQT : (Xᵀ * S⁻¹)ᵀ = S⁻¹ * X := by
    rw [transpose_mul, transpose_nonsing_inv, hST, transpose_transpose]
  refine ⟨S, Xᵀ * S⁻¹, (hS0.posDef_iff_det_ne_zero).mpr hdet, ?_, ?_⟩
  · -- `Qᵀ Q = S⁻¹ X Xᵀ S⁻¹ = S⁻¹ S S S⁻¹ = 1`
    rw [Matrix.mem_orthogonalGroup_iff', hQT]
    calc S⁻¹ * X * (Xᵀ * S⁻¹) = S⁻¹ * (X * Xᵀ) * S⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hSS, ← Matrix.mul_assoc, hinvS, Matrix.one_mul, hSinv]
  · -- `S Qᵀ = S S⁻¹ X = X`
    rw [hQT, ← Matrix.mul_assoc, hSinv, Matrix.one_mul]

/-- **The polar decomposition is unique** ("uniquely"). -/
theorem posDef_mul_orthogonal_transpose_unique {S S' Q Q' : Matrix d d ℝ} (hS : S.PosDef)
    (hS' : S'.PosDef) (hQ : Q ∈ Matrix.orthogonalGroup d ℝ)
    (hQ' : Q' ∈ Matrix.orthogonalGroup d ℝ) (h : S * Qᵀ = S' * Q'ᵀ) : S = S' ∧ Q = Q' := by
  have hST : Sᵀ = S := transpose_eq_of_posSemidef_lsp hS.posSemidef
  have hST' : S'ᵀ = S' := transpose_eq_of_posSemidef_lsp hS'.posSemidef
  -- `S S = (S Qᵀ)(S Qᵀ)ᵀ = S' S'`
  have key : ∀ {S Q : Matrix d d ℝ}, Sᵀ = S → Q ∈ Matrix.orthogonalGroup d ℝ →
      (S * Qᵀ) * (S * Qᵀ)ᵀ = S * S := by
    intro S Q hST hQ
    rw [transpose_mul, transpose_transpose, hST, Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ,
      (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hQ, Matrix.one_mul]
  have hSS : S = S' := by
    refine eq_of_mul_self_eq_lsp hS.posSemidef hS'.posSemidef ?_
    rw [← key hST hQ, ← key hST' hQ', h]
  subst hSS
  refine ⟨rfl, ?_⟩
  -- `S` is invertible, so `Qᵀ = Q'ᵀ`
  have hT : Qᵀ = Q'ᵀ := hS.isUnit.mul_left_cancel h
  rw [← transpose_transpose Q, hT, transpose_transpose]

/-- **The RQ factorization with positive diagonal** of an invertible matrix ("the RQ
factorization of the invertible matrix `Q_{ℓ−1}ᵀ A_ℓ` exists"): `X = R Qᵀ` with `R` upper
triangular with positive diagonal and `Q` orthogonal. -/
theorem exists_upperTriangular_pos_mul_orthogonal_transpose [LinearOrder d] (X : Matrix d d ℝ)
    (hX : IsUnit X.det) :
    ∃ R Q : Matrix d d ℝ, R.BlockTriangular id ∧ (∀ i, 0 < R i i) ∧
      Q ∈ Matrix.orthogonalGroup d ℝ ∧ X = R * Qᵀ := by
  -- an RQ factorization `X Q₀ = R₀`, with `R₀` upper triangular
  obtain ⟨Q₀, hQ₀, htri⟩ := exists_orthogonal_mul_upperTriangular X
  -- `det R₀ = det X det Q₀ ≠ 0`, so no diagonal entry of `R₀` vanishes
  have hdet : (X * Q₀).det ≠ 0 := by
    rw [det_mul]
    exact mul_ne_zero hX.ne_zero
      (Matrix.det_ne_zero_of_right_inverse ((Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ₀))
  have hdiag : ∀ i, (X * Q₀) i i ≠ 0 :=
    (IsUpperTriangular.det_ne_zero_iff (M := X * Q₀) htri).mp hdet
  -- the signs `s i = ± 1` of the diagonal of `R₀`, and `D = diagonal s`
  let s : d → ℝ := fun i => if 0 < (X * Q₀) i i then 1 else -1
  have hss : ∀ i, s i * s i = 1 := fun i => by
    simp only [s]; split_ifs <;> norm_num
  have hDD : diagonal s * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext hss)
  have hDT : (diagonal s)ᵀ = diagonal s := diagonal_transpose s
  refine ⟨X * Q₀ * diagonal s, Q₀ * diagonal s, htri.mul (blockTriangular_diagonal s),
    fun i => ?_, ?_, ?_⟩
  · -- `R i i = |R₀ i i| > 0`
    rw [mul_diagonal]
    have h := hdiag i
    simp only [s]
    split_ifs with hp
    · rw [mul_one]; exact hp
    · rw [mul_neg_one, neg_pos]; exact lt_of_le_of_ne (not_lt.mp hp) h
  · -- `Q = Q₀ D` is orthogonal
    refine Submonoid.mul_mem _ hQ₀ ?_
    rw [Matrix.mem_orthogonalGroup_iff, hDT, hDD]
  · -- `R Qᵀ = R₀ D D Q₀ᵀ = X Q₀ Q₀ᵀ = X`
    rw [transpose_mul, hDT, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s), hDD,
      Matrix.one_mul, Matrix.mul_assoc, (Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ₀,
      Matrix.mul_one]

/-- One half of the uniqueness of RQ: if `R = R' N` with `R`, `R'` upper triangular and `R'` with
positive diagonal, then `N` is upper triangular. -/
private theorem upperTriangular_of_mul_lsp [LinearOrder d] {R R' N : Matrix d d ℝ}
    (hR : R.BlockTriangular id) (hR' : R'.BlockTriangular id) (hRp' : ∀ i, 0 < R' i i)
    (h : R = R' * N) : N.BlockTriangular id := by
  -- `det R' = ∏ R' i i ≠ 0`
  have hdet : R'.det ≠ 0 :=
    (IsUpperTriangular.det_ne_zero_iff (M := R') hR').mpr fun i => (hRp' i).ne'
  let : Invertible R' := invertibleOfIsUnitDet R' (Ne.isUnit hdet)
  -- `N = R'⁻¹ R`
  have hN : N = R'⁻¹ * R := by
    rw [h, ← Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.one_mul]
  rw [hN]
  exact (blockTriangular_inv_of_blockTriangular hR').mul hR

/-- **The RQ factorization with positive diagonal is unique** ("and is unique"). -/
theorem upperTriangular_pos_mul_orthogonal_transpose_unique [LinearOrder d]
    {R R' Q Q' : Matrix d d ℝ} (hR : R.BlockTriangular id) (hRp : ∀ i, 0 < R i i)
    (hR' : R'.BlockTriangular id) (hRp' : ∀ i, 0 < R' i i)
    (hQ : Q ∈ Matrix.orthogonalGroup d ℝ) (hQ' : Q' ∈ Matrix.orthogonalGroup d ℝ)
    (h : R * Qᵀ = R' * Q'ᵀ) : R = R' ∧ Q = Q' := by
  have hQQ := (Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ
  have hQQ' := (Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ'
  -- `N = Q'ᵀ Q`, with `R = R' N` and `R' = R Nᵀ`
  set N := Q'ᵀ * Q with hNdef
  have h1 : R = R' * N := by
    rw [hNdef, ← Matrix.mul_assoc, ← h, Matrix.mul_assoc,
      (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hQ, Matrix.mul_one]
  have h2 : R' = R * Nᵀ := by
    rw [hNdef, transpose_mul, transpose_transpose, ← Matrix.mul_assoc, h, Matrix.mul_assoc,
      (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hQ', Matrix.mul_one]
  -- `N` and `Nᵀ` are upper triangular, so `N` is diagonal
  have hNu : N.BlockTriangular id := upperTriangular_of_mul_lsp hR hR' hRp' h1
  have hNl : Nᵀ.BlockTriangular id := upperTriangular_of_mul_lsp hR' hR hRp h2
  have hoff : ∀ i j, i ≠ j → N i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact hNl hlt
    · exact hNu hlt
  -- `R i i = R' i i N i i`, so `N i i > 0`
  have hdpos : ∀ i, 0 < N i i := by
    intro i
    have e : R i i = R' i i * N i i := by
      rw [h1, Matrix.mul_apply, Finset.sum_eq_single i]
      · intro k _ hki
        rw [hoff k i hki, mul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    have := hRp i
    rw [e] at this
    exact pos_of_mul_pos_right this (hRp' i).le
  -- `N Nᵀ = 1`, so `(N i i)² = 1` and `N i i = 1`
  have hNN : N * Nᵀ = 1 := by
    rw [hNdef, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Q,
      hQQ, Matrix.one_mul, (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hQ']
  have hd1 : ∀ i, N i i = 1 := by
    intro i
    have e := congrFun (congrFun hNN i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, transpose_apply, one_apply_eq] at e
    · nlinarith [hdpos i]
    · intro k _ hki
      rw [transpose_apply, hoff i k (Ne.symm hki), zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hN1 : N = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [hd1, one_apply_eq]
    · rw [hoff i j hij, one_apply_ne hij]
  refine ⟨by rw [h1, hN1, Matrix.mul_one], ?_⟩
  -- `Q = Q' Q'ᵀ Q = Q' N = Q'`
  calc Q = Q' * N := by rw [hNdef, ← Matrix.mul_assoc, hQQ', Matrix.one_mul]
    _ = Q' := by rw [hN1, Matrix.mul_one]

/-! ### The two networks -/

/-- **Theorem A.12 (i), triangular skips.** Under pre-RMSNorm, for invertible learned skips `A_ℓ`
(the stream matrices `S ℓ`), there are orthogonal `Q_0 = I, Q_1, …, Q_L` such that every
`R_ℓ = Q_{ℓ−1}ᵀ A_ℓ Q_ℓ` is upper triangular with positive diagonal, and the network with the skips
`R_ℓ`, the reads `Q_{ℓ−1}ᵀ W_read^ℓ`, the writes `W_write^ℓ Q_ℓ` and the readout `Q_Lᵀ D` computes
the same function. -/
theorem exists_cob_learned_upperTriangular_pos [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (S : Fin L → Matrix d d ℝ) (hS : ∀ ℓ, IsUnit (S ℓ).det) (θ : Params A dIn dOut) :
    ∃ Q : Fin (L + 1) → GL d ℝ, Q 0 = 1 ∧
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
      (∀ ℓ, (cobSkip S Q ℓ).BlockTriangular id ∧ ∀ i, 0 < cobSkip S Q ℓ i i) ∧
      ∀ x : Matrix T dIn ℝ, eval A (cobSkip S Q) (θ.cob Q Q) x = eval A S θ x := by
  sorry

/-- **Theorem A.12 (i), symmetric skips.** Under pre-RMSNorm, for invertible learned skips `A_ℓ`
(the stream matrices `S ℓ`), there are orthogonal `Q_0 = I, Q_1, …, Q_L` such that every
`S_ℓ = Q_{ℓ−1}ᵀ A_ℓ Q_ℓ` is symmetric positive definite, and the network with the skips `S_ℓ`, the
reads `Q_{ℓ−1}ᵀ W_read^ℓ`, the writes `W_write^ℓ Q_ℓ` and the readout `Q_Lᵀ D` computes the same
function. -/
theorem exists_cob_learned_posDef (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (S : Fin L → Matrix d d ℝ) (hS : ∀ ℓ, IsUnit (S ℓ).det) (θ : Params A dIn dOut) :
    ∃ Q : Fin (L + 1) → GL d ℝ, Q 0 = 1 ∧
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
      (∀ ℓ, (cobSkip S Q ℓ).PosDef) ∧
      ∀ x : Matrix T dIn ℝ, eval A (cobSkip S Q) (θ.cob Q Q) x = eval A S θ x := by
  sorry

end Skips
