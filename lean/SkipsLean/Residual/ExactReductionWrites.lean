import SkipsLean.Residual.LearnedSkips

/-!
# Exact reduction: the rows of a write or of the embedding

Paper (skips paper), Appendix A.3: "Let `W_1` be an invertible `d_model × d_model` submatrix
formed by `d_model` columns of a matrix that reads `h_ℓ`, or by `d_model` rows of a matrix that
writes it." Proposition A.9 (Exact reduction without skips): "(i) In a skipless network or a
network of mixed blocks, the map `W ↦ W G` on the matrices that write `h_ℓ` and `W ↦ G⁻¹ W` on
those that read it turns `W_1` into the identity for `G = W_1` if `W_1` is part of a read, and for
`G = W_1⁻¹` if it is part of a write. Under RMSNorm with `ε > 0`, `G = Q` from a QR factorization
`W_1 = Q T`, or `W_1ᵀ = Q T` for a write, turns `W_1` into a triangular matrix. […] (ii) In a
residual network, the same map with one `G` at all hidden states preserves the function and turns
one such submatrix, in any read or write of the network, into the identity or a triangular
matrix."

The library has (ii) for the columns of a read and of the readout
(`exists_cob_residual_read_eq_one`, `exists_cob_residual_D_eq_one`,
`exists_cob_residual_read_upperTriangular`, `exists_cob_residual_D_upperTriangular`,
`Residual/LearnedSkips.lean`) and (i) for all reads at once and, without normalization, for all
writes at once (`Symmetry/Reduction.lean`). Here:

* (ii) for the rows of a write and of the embedding (the embedding writes `h_0`), without
  normalization (the identity) and under pre-RMSNorm (a triangular matrix: with `W_1ᵀ = Q T`,
  `W_1 Q = Tᵀ` is lower triangular, stated as "its transpose is upper triangular");
* (i) under pre-RMSNorm for the rows of the embedding and of all writes at once.

The statements under pre-RMSNorm hold for every real `ε` (`rmsNorm ε` is a total function), and
need no invertibility of `W_1`. Networks of mixed blocks: `Residual/ExactReductionMixed.lean`;
the count of the removed parameters: `Residual/ExactReductionCount.lean`.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn]
variable {A : Arch T d L}
variable (θ : Params A dIn dOut)

omit [DecidableEq d] in
/-- The chosen rows `ρ` of a product `M N` are the chosen rows of `M` times `N` (a copy of the
private `submatrix_mul_id` of `Symmetry/Reduction.lean`). -/
private theorem submatrix_mul_id_erw {w : Type*} (M : Matrix w d ℝ) (N : Matrix d d ℝ)
    (ρ : d → w) : (M * N).submatrix ρ id = M.submatrix ρ id * N := by
  rw [Matrix.submatrix_mul M N ρ id id Function.bijective_id, Matrix.submatrix_id_id]

/-- QR factorization of `Wᵀ`, with `Q` as an element of `GL d ℝ`: an orthogonal `Q` with `W Q`
lower triangular, that is `(W Q)ᵀ = Qᵀ Wᵀ` upper triangular. -/
private theorem exists_orthogonal_mul_lowerTriangular_erw [LinearOrder d] (W : Matrix d d ℝ) :
    ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
      ((W * (Q : Matrix d d ℝ))ᵀ).BlockTriangular id := by
  -- QR factorization of `Wᵀ`: an orthogonal `Q` with `Qᵀ Wᵀ` upper triangular.
  obtain ⟨Q, hQ, htri⟩ := exists_orthogonal_transpose_mul_upperTriangular Wᵀ
  -- `Q` is invertible, with inverse `Qᵀ`.
  let Q' : GL d ℝ :=
    ⟨Q, Qᵀ, (Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ, (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hQ⟩
  refine ⟨Q', hQ, ?_⟩
  -- `(W Q)ᵀ = Qᵀ Wᵀ`.
  change ((W * Q)ᵀ).BlockTriangular id
  rw [Matrix.transpose_mul]
  exact htri

/-- **Proposition A.9 (ii), without normalization, for the rows of a write.** In a residual
network, if `d` rows of the write of block `ℓ` form an invertible matrix, the same change of basis
at all hidden states preserves the function and turns these rows into the identity. -/
theorem exists_cob_residual_write_eq_one (hA : A.χ = id) (ℓ : Fin L) (ρ : d → A.w ℓ)
    (hρ : IsUnit ((θ.write ℓ).submatrix ρ id).det) :
    ∃ G : GL d ℝ,
      (∀ x : Matrix T dIn ℝ, eval A 1 (θ.cob (fun _ => G) (fun _ => G)) x = eval A 1 θ x) ∧
      ((θ.cob (fun _ => G) (fun _ => G)).write ℓ).submatrix ρ id = 1 := by
  -- The chosen rows `W₁` are invertible; `G = W₁⁻¹`.
  obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr hρ
  -- One change of basis at all hidden states preserves the function of a residual network.
  refine ⟨U⁻¹, fun x => eval_cob_residual (θ := θ) (x := x) hA U⁻¹, ?_⟩
  -- The chosen rows of the new write are `W₁ W₁⁻¹ = I`.
  change (θ.write ℓ * (↑U⁻¹ : Matrix d d ℝ)).submatrix ρ id = 1
  rw [submatrix_mul_id_erw, ← hU, Units.mul_inv]

/-- **Proposition A.9 (ii), without normalization, for the rows of the embedding.** -/
theorem exists_cob_residual_E_eq_one (hA : A.χ = id) (ρE : d → dIn)
    (hρE : IsUnit (θ.E.submatrix ρE id).det) :
    ∃ G : GL d ℝ,
      (∀ x : Matrix T dIn ℝ, eval A 1 (θ.cob (fun _ => G) (fun _ => G)) x = eval A 1 θ x) ∧
      (θ.cob (fun _ => G) (fun _ => G)).E.submatrix ρE id = 1 := by
  -- The chosen rows `E₁` are invertible; `G = E₁⁻¹`.
  obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr hρE
  -- One change of basis at all hidden states preserves the function of a residual network.
  refine ⟨U⁻¹, fun x => eval_cob_residual (θ := θ) (x := x) hA U⁻¹, ?_⟩
  -- The chosen rows of the new embedding are `E₁ E₁⁻¹ = I`.
  change (θ.E * (↑U⁻¹ : Matrix d d ℝ)).submatrix ρE id = 1
  rw [submatrix_mul_id_erw, ← hU, Units.mul_inv]

/-- **Proposition A.9 (ii), under pre-RMSNorm, for the rows of a write.** One orthogonal change
of basis at all hidden states preserves the function of a residual network and turns the chosen
rows of the write of block `ℓ` into a lower triangular matrix (its transpose is upper
triangular). -/
theorem exists_cob_residual_write_lowerTriangular [LinearOrder d] (ε : ℝ)
    (hA : A.χ = rmsNorm ε) (ℓ : Fin L) (ρ : d → A.w ℓ) :
    ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
      (∀ x : Matrix T dIn ℝ, eval A 1 (θ.cob (fun _ => Q) (fun _ => Q)) x = eval A 1 θ x) ∧
      ((((θ.cob (fun _ => Q) (fun _ => Q)).write ℓ).submatrix ρ id)ᵀ).BlockTriangular id := by
  -- QR factorization of `W₁ᵀ`: an orthogonal `Q` with `(W₁ Q)ᵀ` upper triangular.
  obtain ⟨Q, hQ, htri⟩ :=
    exists_orthogonal_mul_lowerTriangular_erw ((θ.write ℓ).submatrix ρ id)
  -- The same orthogonal change of basis at all hidden states preserves the function.
  refine ⟨Q, hQ, fun x => eval_cob_residual_rmsNorm θ x ε hA Q hQ, ?_⟩
  -- The chosen rows of the new write are `W₁ Q`.
  change (((θ.write ℓ * (Q : Matrix d d ℝ)).submatrix ρ id)ᵀ).BlockTriangular id
  rw [submatrix_mul_id_erw]
  exact htri

/-- **Proposition A.9 (ii), under pre-RMSNorm, for the rows of the embedding.** -/
theorem exists_cob_residual_E_lowerTriangular [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (ρE : d → dIn) :
    ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
      (∀ x : Matrix T dIn ℝ, eval A 1 (θ.cob (fun _ => Q) (fun _ => Q)) x = eval A 1 θ x) ∧
      (((θ.cob (fun _ => Q) (fun _ => Q)).E.submatrix ρE id)ᵀ).BlockTriangular id := by
  -- QR factorization of `E₁ᵀ`: an orthogonal `Q` with `(E₁ Q)ᵀ` upper triangular.
  obtain ⟨Q, hQ, htri⟩ := exists_orthogonal_mul_lowerTriangular_erw (θ.E.submatrix ρE id)
  -- The same orthogonal change of basis at all hidden states preserves the function.
  refine ⟨Q, hQ, fun x => eval_cob_residual_rmsNorm θ x ε hA Q hQ, ?_⟩
  -- The chosen rows of the new embedding are `E₁ Q`.
  change (((θ.E * (Q : Matrix d d ℝ)).submatrix ρE id)ᵀ).BlockTriangular id
  rw [submatrix_mul_id_erw]
  exact htri

/-- **Proposition A.9 (i), under pre-RMSNorm, for the rows of the embedding and of all writes at
once.** In a skipless network, orthogonal changes of basis at the `L + 1` hidden states preserve
the function and turn the chosen rows of the embedding and of every write into lower triangular
matrices (their transposes are upper triangular). No invertibility is needed. -/
theorem exists_cob_writes_lowerTriangular [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ) :
    ∃ Q : Fin (L + 1) → GL d ℝ,
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
      (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cob Q Q) x = eval A 0 θ x) ∧
      (((θ.cob Q Q).E.submatrix ρE id)ᵀ).BlockTriangular id ∧
      ∀ ℓ, ((((θ.cob Q Q).write ℓ).submatrix (ρ ℓ) id)ᵀ).BlockTriangular id := by
  -- QR factorization of the transposed chosen rows of the embedding and of every write.
  obtain ⟨PE, hPE, htriE⟩ := exists_orthogonal_mul_lowerTriangular_erw (θ.E.submatrix ρE id)
  have hP : ∀ ℓ, ∃ P : GL d ℝ, (P : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
      (((θ.write ℓ).submatrix (ρ ℓ) id * (P : Matrix d d ℝ))ᵀ).BlockTriangular id :=
    fun ℓ => exists_orthogonal_mul_lowerTriangular_erw _
  choose P hP htri using hP
  -- `Q_0 = P_E` at the hidden state written by the embedding, `Q_{ℓ+1} = P_ℓ` at the one written
  -- by block `ℓ`.
  obtain ⟨Q, hQ0, hQs⟩ : ∃ Q : Fin (L + 1) → GL d ℝ, Q 0 = PE ∧ ∀ ℓ, Q ℓ.succ = P ℓ :=
    ⟨Fin.cases (motive := fun _ => GL d ℝ) PE P, Fin.cases_zero, fun ℓ => Fin.cases_succ ℓ⟩
  -- Every `Q_ℓ` is orthogonal.
  have hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
    intro ℓ
    induction ℓ using Fin.cases with
    | zero => rw [hQ0]; exact hPE
    | succ ℓ => rw [hQs ℓ]; exact hP ℓ
  -- Under pre-RMSNorm orthogonal changes of basis preserve the function (Proposition 3.2).
  refine ⟨Q, hQ, fun x => eval_cob_rmsNorm θ x ε hA Q hQ, ?_, fun ℓ => ?_⟩
  · -- The chosen rows of the new embedding are `E₁ P_E`.
    change (((θ.E * (Q 0 : Matrix d d ℝ)).submatrix ρE id)ᵀ).BlockTriangular id
    rw [submatrix_mul_id_erw, hQ0]
    exact htriE
  · -- The chosen rows of the new write are `W₁^ℓ P_ℓ`.
    change (((θ.write ℓ * (Q ℓ.succ : Matrix d d ℝ)).submatrix (ρ ℓ) id)ᵀ).BlockTriangular id
    rw [submatrix_mul_id_erw, hQs ℓ]
    exact htri ℓ

end Skips
