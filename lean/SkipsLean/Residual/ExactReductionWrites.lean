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
need no invertibility of `W_1`. Not stated: networks of mixed blocks; the count of the removed
parameters.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn]
variable {A : Arch T d L}
variable (θ : Params A dIn dOut)

/-- **Proposition A.9 (ii), without normalization, for the rows of a write.** In a residual
network, if `d` rows of the write of block `ℓ` form an invertible matrix, the same change of basis
at all hidden states preserves the function and turns these rows into the identity. -/
theorem exists_cob_residual_write_eq_one (hA : A.χ = id) (ℓ : Fin L) (ρ : d → A.w ℓ)
    (hρ : IsUnit ((θ.write ℓ).submatrix ρ id).det) :
    ∃ G : GL d ℝ,
      (∀ x : Matrix T dIn ℝ, eval A 1 (θ.cob (fun _ => G) (fun _ => G)) x = eval A 1 θ x) ∧
      ((θ.cob (fun _ => G) (fun _ => G)).write ℓ).submatrix ρ id = 1 := by
  sorry

/-- **Proposition A.9 (ii), without normalization, for the rows of the embedding.** -/
theorem exists_cob_residual_E_eq_one (hA : A.χ = id) (ρE : d → dIn)
    (hρE : IsUnit (θ.E.submatrix ρE id).det) :
    ∃ G : GL d ℝ,
      (∀ x : Matrix T dIn ℝ, eval A 1 (θ.cob (fun _ => G) (fun _ => G)) x = eval A 1 θ x) ∧
      (θ.cob (fun _ => G) (fun _ => G)).E.submatrix ρE id = 1 := by
  sorry

/-- **Proposition A.9 (ii), under pre-RMSNorm, for the rows of a write.** One orthogonal change
of basis at all hidden states preserves the function of a residual network and turns the chosen
rows of the write of block `ℓ` into a lower triangular matrix (its transpose is upper
triangular). -/
theorem exists_cob_residual_write_lowerTriangular [LinearOrder d] (ε : ℝ)
    (hA : A.χ = rmsNorm ε) (ℓ : Fin L) (ρ : d → A.w ℓ) :
    ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
      (∀ x : Matrix T dIn ℝ, eval A 1 (θ.cob (fun _ => Q) (fun _ => Q)) x = eval A 1 θ x) ∧
      ((((θ.cob (fun _ => Q) (fun _ => Q)).write ℓ).submatrix ρ id)ᵀ).BlockTriangular id := by
  sorry

/-- **Proposition A.9 (ii), under pre-RMSNorm, for the rows of the embedding.** -/
theorem exists_cob_residual_E_lowerTriangular [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (ρE : d → dIn) :
    ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
      (∀ x : Matrix T dIn ℝ, eval A 1 (θ.cob (fun _ => Q) (fun _ => Q)) x = eval A 1 θ x) ∧
      (((θ.cob (fun _ => Q) (fun _ => Q)).E.submatrix ρE id)ᵀ).BlockTriangular id := by
  sorry

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
  sorry

end Skips
