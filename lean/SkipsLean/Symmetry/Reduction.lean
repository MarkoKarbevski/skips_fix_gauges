import SkipsLean.Symmetry.Normalized

/-!
# The exact reduction

Paper: Proposition 3.3 and the paragraph after it (rows of a write), Appendix A.2.

A choice of `d` columns of a read is a map `c : d → r` into the column indices, and the chosen
columns form the square matrix `W.submatrix id c`. A choice of `d` rows of a write is a map
`ρ : d → w`, and the chosen rows form `W.submatrix ρ id`.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn]
variable {A : Arch T d L}

omit [DecidableEq d] in
/-- The chosen columns `c` of a product `M N` are `M` times the chosen columns of `N`. -/
private theorem submatrix_id_mul {r : Type*} (M : Matrix d d ℝ) (N : Matrix d r ℝ) (c : d → r) :
    (M * N).submatrix id c = M * N.submatrix id c := by
  rw [Matrix.submatrix_mul M N id id c Function.bijective_id, Matrix.submatrix_id_id]

omit [DecidableEq d] in
/-- The chosen rows `ρ` of a product `M N` are the chosen rows of `M` times `N`. -/
private theorem submatrix_mul_id {w : Type*} (M : Matrix w d ℝ) (N : Matrix d d ℝ) (ρ : d → w) :
    (M * N).submatrix ρ id = M.submatrix ρ id * N := by
  rw [Matrix.submatrix_mul M N ρ id id Function.bijective_id, Matrix.submatrix_id_id]

variable (θ : Params A dIn dOut)

/-- **Proposition 3.3 (i), at all hidden states at once.** Without normalization, if the chosen
columns of every read and of the readout form invertible matrices, changes of basis at the `L + 1`
hidden states preserve the function and turn all of these submatrices into the identity. -/
theorem exists_cob_reads_eq_one (hA : A.χ = id)
    (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut)
    (hc : ∀ ℓ, IsUnit ((θ.read ℓ).submatrix id (c ℓ)).det)
    (hcD : IsUnit (θ.D.submatrix id cD).det) :
    ∃ G : Fin (L + 1) → GL d ℝ,
      (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cob G G) x = eval A 0 θ x) ∧
      (∀ ℓ, ((θ.cob G G).read ℓ).submatrix id (c ℓ) = 1) ∧
      (θ.cob G G).D.submatrix id cD = 1 := by
  -- The chosen columns `W₁^ℓ` of every read and `D₁` of the readout are invertible.
  have hU : ∀ ℓ, ∃ u : GL d ℝ, (u : Matrix d d ℝ) = (θ.read ℓ).submatrix id (c ℓ) :=
    fun ℓ => (Matrix.isUnit_iff_isUnit_det _).mpr (hc ℓ)
  choose U hU using hU
  obtain ⟨UD, hUD⟩ : ∃ u : GL d ℝ, (u : Matrix d d ℝ) = θ.D.submatrix id cD :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hcD
  -- `G_{ℓ-1} = W₁^ℓ` at the hidden state read by block `ℓ`, and `G_L = D₁` at the last one.
  obtain ⟨G, hG, hGL⟩ : ∃ G : Fin (L + 1) → GL d ℝ,
      (∀ ℓ, G ℓ.castSucc = U ℓ) ∧ G (Fin.last L) = UD :=
    ⟨Fin.lastCases (motive := fun _ => GL d ℝ) UD U, fun ℓ => Fin.lastCases_castSucc ℓ,
      Fin.lastCases_last⟩
  -- Without normalization the changes of basis preserve the function (Proposition 3.2).
  refine ⟨G, fun x => eval_cob_skipless θ G x hA, fun ℓ => ?_, ?_⟩
  · -- The chosen columns of the new read are `(W₁^ℓ)⁻¹ W₁^ℓ = 1`.
    change ((↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ).submatrix id (c ℓ) = 1
    rw [submatrix_id_mul, hG ℓ, ← hU ℓ, Units.inv_mul]
  · -- The chosen columns of the new readout are `D₁⁻¹ D₁ = 1`.
    change ((↑(G (Fin.last L))⁻¹ : Matrix d d ℝ) * θ.D).submatrix id cD = 1
    rw [submatrix_id_mul, hGL, ← hUD, Units.inv_mul]

/-- The rows of the writes (the paragraph after Proposition 3.3, and Example A.2): if the chosen
rows of the embedding and of every write form invertible matrices, changes of basis at the `L + 1`
hidden states preserve the function and turn all of these submatrices into the identity. -/
theorem exists_cob_writes_eq_one (hA : A.χ = id)
    (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ)
    (hρE : IsUnit (θ.E.submatrix ρE id).det)
    (hρ : ∀ ℓ, IsUnit ((θ.write ℓ).submatrix (ρ ℓ) id).det) :
    ∃ G : Fin (L + 1) → GL d ℝ,
      (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cob G G) x = eval A 0 θ x) ∧
      (θ.cob G G).E.submatrix ρE id = 1 ∧
      (∀ ℓ, ((θ.cob G G).write ℓ).submatrix (ρ ℓ) id = 1) := by
  -- The chosen rows `E₁` of the embedding and `W₁^ℓ` of every write are invertible.
  obtain ⟨UE, hUE⟩ : ∃ u : GL d ℝ, (u : Matrix d d ℝ) = θ.E.submatrix ρE id :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hρE
  have hU : ∀ ℓ, ∃ u : GL d ℝ, (u : Matrix d d ℝ) = (θ.write ℓ).submatrix (ρ ℓ) id :=
    fun ℓ => (Matrix.isUnit_iff_isUnit_det _).mpr (hρ ℓ)
  choose U hU using hU
  -- `G_0 = E₁⁻¹`, and `G_ℓ = (W₁^ℓ)⁻¹` at the hidden state written by block `ℓ`.
  obtain ⟨G, hG0, hG⟩ : ∃ G : Fin (L + 1) → GL d ℝ,
      G 0 = UE⁻¹ ∧ ∀ ℓ, G ℓ.succ = (U ℓ)⁻¹ :=
    ⟨Fin.cases (motive := fun _ => GL d ℝ) UE⁻¹ (fun ℓ => (U ℓ)⁻¹), Fin.cases_zero,
      fun ℓ => Fin.cases_succ ℓ⟩
  -- Without normalization the changes of basis preserve the function (Proposition 3.2).
  refine ⟨G, fun x => eval_cob_skipless θ G x hA, ?_, fun ℓ => ?_⟩
  · -- The chosen rows of the new embedding are `E₁ E₁⁻¹ = 1`.
    change (θ.E * (G 0 : Matrix d d ℝ)).submatrix ρE id = 1
    rw [submatrix_mul_id, hG0, ← hUE, Units.mul_inv]
  · -- The chosen rows of the new write are `W₁^ℓ (W₁^ℓ)⁻¹ = 1`.
    change (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)).submatrix (ρ ℓ) id = 1
    rw [submatrix_mul_id, hG ℓ, ← hU ℓ, Units.mul_inv]

/-- QR factorization of a square real matrix, in the form used by Proposition 3.3 (ii): there is
an orthogonal `Q` such that `Qᵀ W` is upper triangular. -/
theorem exists_orthogonal_transpose_mul_upperTriangular [LinearOrder d] (W : Matrix d d ℝ) :
    ∃ Q : Matrix d d ℝ, Q ∈ Matrix.orthogonalGroup d ℝ ∧ (Qᵀ * W).BlockTriangular id := by
  -- A finite linear order has finite intervals `Iic a`, as Gram–Schmidt needs.
  let _ : LocallyFiniteOrderBot d :=
    LocallyFiniteOrderBot.ofIic d (fun a => Finset.univ.filter (· ≤ a)) (by simp)
  -- The columns `f i` of `W`, as vectors of `ℝ^d`.
  let f : d → EuclideanSpace ℝ d := fun i => WithLp.toLp 2 (fun k => W k i)
  -- Gram–Schmidt on the columns: an orthonormal basis `b` with `⟪b j, f i⟫ = 0` for `i < j`.
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis (𝕜 := ℝ)
    (finrank_euclideanSpace (𝕜 := ℝ) (ι := d)) f
  -- `Q` is the matrix with the columns `b j`.
  refine ⟨Matrix.of fun k j => b j k, ?_, ?_⟩
  · -- `(Qᵀ Q) i j = ⟪b i, b j⟫ = δ_ij`, since `b` is orthonormal.
    rw [Matrix.mem_orthogonalGroup_iff' d ℝ]
    ext i j
    have h := orthonormal_iff_ite.mp b.orthonormal i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [← h]
    simp only [dotProduct, Pi.star_apply, star_trivial, mul_comm]
  · -- `(Qᵀ W) j i = ⟪b j, f i⟫ = 0` for `i < j`.
    intro j i hij
    have h := InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular (𝕜 := ℝ)
      (finrank_euclideanSpace (𝕜 := ℝ) (ι := d)) f hij
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [← h]
    simp only [mul_comm, dotProduct, id_eq, Pi.star_apply, star_trivial, b, f]

/-- The QR factorization with `Q` as an element of `GL d ℝ`: `Q⁻¹ W = Qᵀ W` is upper
triangular. -/
private theorem exists_orthogonal_inv_mul_upperTriangular [LinearOrder d] (W : Matrix d d ℝ) :
    ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
      ((↑Q⁻¹ : Matrix d d ℝ) * W).BlockTriangular id := by
  obtain ⟨Q, hQ, htri⟩ := exists_orthogonal_transpose_mul_upperTriangular W
  -- `Q` is invertible, with inverse `Qᵀ`.
  let Q' : GL d ℝ :=
    ⟨Q, Qᵀ, (Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ, (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hQ⟩
  have hQ' : (Q' : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := hQ
  refine ⟨Q', hQ', ?_⟩
  rw [coe_inv_of_mem_orthogonalGroup Q' hQ']
  exact htri

/-- **Proposition 3.3 (ii), at all hidden states at once.** Under pre-RMSNorm, orthogonal changes
of basis at the `L + 1` hidden states preserve the function and turn the chosen columns of every
read and of the readout into upper triangular matrices. No invertibility is needed. -/
theorem exists_cob_reads_upperTriangular [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut) :
    ∃ Q : Fin (L + 1) → GL d ℝ,
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
      (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cob Q Q) x = eval A 0 θ x) ∧
      (∀ ℓ, (((θ.cob Q Q).read ℓ).submatrix id (c ℓ)).BlockTriangular id) ∧
      ((θ.cob Q Q).D.submatrix id cD).BlockTriangular id := by
  -- QR factorization of the chosen columns of every read and of the readout.
  have hR : ∀ ℓ, ∃ P : GL d ℝ, (P : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
      ((↑P⁻¹ : Matrix d d ℝ) * (θ.read ℓ).submatrix id (c ℓ)).BlockTriangular id :=
    fun ℓ => exists_orthogonal_inv_mul_upperTriangular _
  choose R hR htri using hR
  obtain ⟨RD, hRD, htriD⟩ := exists_orthogonal_inv_mul_upperTriangular (θ.D.submatrix id cD)
  -- `Q_{ℓ-1} = R_ℓ` at the hidden state read by block `ℓ`, and `Q_L = R_D` at the last one.
  obtain ⟨Q, hQc, hQL⟩ : ∃ Q : Fin (L + 1) → GL d ℝ,
      (∀ ℓ, Q ℓ.castSucc = R ℓ) ∧ Q (Fin.last L) = RD :=
    ⟨Fin.lastCases (motive := fun _ => GL d ℝ) RD R, fun ℓ => Fin.lastCases_castSucc ℓ,
      Fin.lastCases_last⟩
  -- Every `Q_ℓ` is orthogonal.
  have hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
    intro ℓ
    induction ℓ using Fin.lastCases with
    | last => rw [hQL]; exact hRD
    | cast ℓ => rw [hQc ℓ]; exact hR ℓ
  -- Under pre-RMSNorm orthogonal changes of basis preserve the function (Proposition 3.2).
  refine ⟨Q, hQ, fun x => eval_cob_rmsNorm θ x ε hA Q hQ, fun ℓ => ?_, ?_⟩
  · -- The chosen columns of the new read are `R_ℓ⁻¹ W₁^ℓ`, upper triangular.
    change (((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ).submatrix id (c ℓ)).BlockTriangular id
    rw [submatrix_id_mul, hQc ℓ]
    exact htri ℓ
  · -- The chosen columns of the new readout are `R_D⁻¹ D₁`, upper triangular.
    change (((↑(Q (Fin.last L))⁻¹ : Matrix d d ℝ) * θ.D).submatrix id cD).BlockTriangular id
    rw [submatrix_id_mul, hQL]
    exact htriD

/-- The number of entries that an upper triangular `n × n` matrix fixes: the pairs `(i, j)` below
the diagonal, `n (n - 1) / 2`. -/
theorem card_below_diagonal (n : ℕ) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.2 < p.1).card = n * (n - 1) / 2 := by
  calc (Finset.univ.filter fun p : Fin n × Fin n => p.2 < p.1).card
      -- Count row by row: in row `i` the entries `j < i`.
      = ∑ i : Fin n, ∑ j : Fin n, if j < i then 1 else 0 := by
        rw [Finset.card_filter, Fintype.sum_prod_type]
    -- Row `i` has `i` entries below the diagonal.
    _ = ∑ i : Fin n, (i : ℕ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.card_filter, Finset.filter_gt_eq_Iio, Fin.card_Iio]
    -- `0 + 1 + ⋯ + (n - 1) = n (n - 1) / 2`.
    _ = ∑ i ∈ Finset.range n, i := Fin.sum_univ_eq_sum_range (fun i => i) n
    _ = n * (n - 1) / 2 := Finset.sum_range_id n

/-- The count for the ViT-B of Ji et al. (Appendix A.3): `25 · 767 · 766 / 2 = 7,344,025`. -/
theorem vitB_count : 25 * (767 * 766 / 2) = 7344025 := by
  norm_num

end Skips
