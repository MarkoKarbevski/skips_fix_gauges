import SkipsLean.Residual.ExactReductionMixed
import SkipsLean.Residual.ExactReductionCount

/-!
# Exact reduction without skips: a read or a write at each hidden state

Paper (skips paper), Proposition A.9 (i): "In a skipless network or a network of mixed blocks,
the map `W ↦ W G` on the matrices that write `h_ℓ` and `W ↦ G^{-1} W` on those that read it turns
`W_1` into the identity for `G = W_1` if `W_1` is part of a read, and for `G = W_1^{-1}` if it is
part of a write. Under RMSNorm with `ε > 0`, `G = Q` from a QR factorization `W_1 = Q T`, or
`W_1^⊤ = Q T` for a write, turns `W_1` into a triangular matrix. Done at every hidden state, this
removes `d_model²`, respectively `d_model (d_model − 1)/2`, parameters per hidden state without
changing the function." Its proof: "The change of basis at `h_ℓ` touches only the writes into
`h_ℓ` and the reads of `h_ℓ`, and a matrix is touched on each side by one hidden state only
(Proposition A.1(iii)), so the reductions at all hidden states can be made together, one submatrix
per hidden state."

`Symmetry/Reduction.lean`, `Residual/ExactReductionWrites.lean`, `Residual/ExactReductionMixed.lean`
and `Residual/ExactReductionCount.lean` have the reduction and the count with the `L + 1`
submatrices all in reads (the reads of the blocks and the readout) or all in writes (the embedding
and the writes of the blocks). Here "one submatrix per hidden state" with a free choice at each
hidden state `h_k`, `k = 0, …, L`: `d` columns of the matrix that reads `h_k` (the read of block
`k + 1`, or the readout for `k = L`; `Params.readSub`), or `d` rows of the matrix that writes
`h_k` (the embedding for `k = 0`, or the write of block `k`; `Params.writeSub`). The choice is
`s : Fin (L + 1) → Bool`, `true` for a read.

* `exists_cob_eq_one_of_choice`, `exists_cob_triangular_of_choice`: the reduction for skipless
  networks, without normalization and under pre-RMSNorm; for networks of mixed blocks
  `exists_cob_mixed_eq_one_of_choice`, `exists_cob_mixed_triangular_of_choice`.
* `finrank_span_choice_eq_zero`, `finrank_span_choice_triangular`: the count,
  `P − (L + 1) d²` and `P − (L + 1) d(d − 1)/2`, for any architecture.
-/

namespace Skips

open Matrix

section General

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]
variable {A : Arch T d L}

/-- The chosen `d` columns of the matrix that reads the hidden state `h_k`: of the read of block
`k + 1`, or of the readout for `k = L`. -/
def Params.readSub (θ : Params A dIn dOut) (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut)
    (k : Fin (L + 1)) : Matrix d d ℝ :=
  Fin.lastCases (motive := fun _ => Matrix d d ℝ) (θ.D.submatrix id cD)
    (fun ℓ => (θ.read ℓ).submatrix id (c ℓ)) k

/-- The chosen `d` rows of the matrix that writes the hidden state `h_k`: of the embedding for
`k = 0`, or of the write of block `k`. -/
def Params.writeSub (θ : Params A dIn dOut) (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ)
    (k : Fin (L + 1)) : Matrix d d ℝ :=
  Fin.cases (motive := fun _ => Matrix d d ℝ) (θ.E.submatrix ρE id)
    (fun ℓ => (θ.write ℓ).submatrix (ρ ℓ) id) k

variable (θ : Params A dIn dOut)

/-- **Proposition A.9 (i), without normalization, one submatrix per hidden state:** at each
hidden state choose `d` columns of the matrix that reads it or `d` rows of the matrix that writes
it. If the chosen submatrices are invertible, changes of basis at the `L + 1` hidden states
preserve the function and turn all of them into the identity. -/
theorem exists_cob_eq_one_of_choice (hA : A.χ = id)
    (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut) (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ)
    (s : Fin (L + 1) → Bool)
    (h : ∀ k, IsUnit (if s k then θ.readSub c cD k else θ.writeSub ρE ρ k).det) :
    ∃ G : Fin (L + 1) → GL d ℝ,
      (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cob G G) x = eval A 0 θ x) ∧
      ∀ k, (if s k then (θ.cob G G).readSub c cD k else (θ.cob G G).writeSub ρE ρ k) = 1 := by
  sorry

/-- **Proposition A.9 (i), under pre-RMSNorm, one submatrix per hidden state:** orthogonal
changes of basis at the `L + 1` hidden states preserve the function and turn the chosen
submatrix at each hidden state into a triangular matrix: upper triangular for columns of a read,
lower triangular for rows of a write. No invertibility is needed. -/
theorem exists_cob_triangular_of_choice [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut) (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ)
    (s : Fin (L + 1) → Bool) :
    ∃ Q : Fin (L + 1) → GL d ℝ,
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
      (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cob Q Q) x = eval A 0 θ x) ∧
      ∀ k, if s k then ((θ.cob Q Q).readSub c cD k).BlockTriangular id
        else (((θ.cob Q Q).writeSub ρE ρ k)ᵀ).BlockTriangular id := by
  sorry

/-- **Proposition A.9 (i), "this removes `d_model²` […] parameters per hidden state", one
submatrix per hidden state:** the parameters whose chosen submatrices all vanish (the directions
of the family in which these `L + 1` submatrices are the identity) have dimension
`P − (L + 1) d²`, if the chosen columns, or rows, are pairwise different. -/
theorem finrank_span_choice_eq_zero (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut)
    (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ) (s : Fin (L + 1) → Bool)
    (hc : ∀ ℓ : Fin L, s ℓ.castSucc = true → Function.Injective (c ℓ))
    (hcD : s (Fin.last L) = true → Function.Injective cD)
    (hρE : s 0 = false → Function.Injective ρE)
    (hρ : ∀ ℓ : Fin L, s ℓ.succ = false → Function.Injective (ρ ℓ)) :
    Module.finrank ℝ (Submodule.span ℝ {η : Params A dIn dOut |
        ∀ k, (if s k then η.readSub c cD k else η.writeSub ρE ρ k) = 0})
      + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **Proposition A.9 (i), "respectively `d_model (d_model − 1)/2`, parameters per hidden
state", one submatrix per hidden state:** the parameters whose chosen submatrices are triangular
(upper for columns of a read, lower for rows of a write) have dimension
`P − (L + 1) d(d − 1)/2`, if the chosen columns, or rows, are pairwise different. -/
theorem finrank_span_choice_triangular [LinearOrder d] (c : ∀ ℓ : Fin L, d → A.r ℓ)
    (cD : d → dOut) (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ) (s : Fin (L + 1) → Bool)
    (hc : ∀ ℓ : Fin L, s ℓ.castSucc = true → Function.Injective (c ℓ))
    (hcD : s (Fin.last L) = true → Function.Injective cD)
    (hρE : s 0 = false → Function.Injective ρE)
    (hρ : ∀ ℓ : Fin L, s ℓ.succ = false → Function.Injective (ρ ℓ)) :
    Module.finrank ℝ (Submodule.span ℝ {θ : Params A dIn dOut |
        ∀ k, if s k then (θ.readSub c cD k).BlockTriangular id
          else ((θ.writeSub ρE ρ k)ᵀ).BlockTriangular id})
      + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end General

section Mixed

variable {T : Type*} {d : Type} {dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {A : Arch T d L} (θ : Params A.mixed dIn dOut)

/-- **Proposition A.9 (i) for networks of mixed blocks, without normalization, one submatrix per
hidden state:** columns of a read `[U_ℓ | W_read^ℓ]` or of the readout, or rows of the embedding
or of a write (which stacks `V_ℓ` on `W_write^ℓ`). -/
theorem exists_cob_mixed_eq_one_of_choice (hA : A.χ = id)
    (c : ∀ ℓ : Fin L, d → d ⊕ A.r ℓ) (cD : d → dOut) (ρE : d → dIn)
    (ρ : ∀ ℓ : Fin L, d → d ⊕ A.w ℓ) (s : Fin (L + 1) → Bool)
    (h : ∀ k, IsUnit (if s k then θ.readSub c cD k else θ.writeSub ρE ρ k).det) :
    ∃ G : Fin (L + 1) → GL d ℝ,
      (∀ x : Matrix T dIn ℝ, evalMixed A (θ.cob G G) x = evalMixed A θ x) ∧
      ∀ k, (if s k then (θ.cob G G).readSub c cD k else (θ.cob G G).writeSub ρE ρ k) = 1 := by
  -- without normalization the network of mixed blocks is the skipless network of `A.mixed`
  obtain ⟨G, hG, h1⟩ :=
    exists_cob_eq_one_of_choice (A := A.mixed) (θ := θ) hA c cD ρE ρ s h
  refine ⟨G, fun x => ?_, h1⟩
  rw [evalMixed_eq_eval hA, evalMixed_eq_eval hA]
  exact hG x

/-- **Proposition A.9 (i) for networks of mixed blocks, under pre-RMSNorm, one submatrix per
hidden state.** -/
theorem exists_cob_mixed_triangular_of_choice [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (c : ∀ ℓ : Fin L, d → d ⊕ A.r ℓ) (cD : d → dOut) (ρE : d → dIn)
    (ρ : ∀ ℓ : Fin L, d → d ⊕ A.w ℓ) (s : Fin (L + 1) → Bool) :
    ∃ Q : Fin (L + 1) → GL d ℝ,
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
      (∀ x : Matrix T dIn ℝ, evalMixed A (θ.cob Q Q) x = evalMixed A θ x) ∧
      ∀ k, if s k then ((θ.cob Q Q).readSub c cD k).BlockTriangular id
        else (((θ.cob Q Q).writeSub ρE ρ k)ᵀ).BlockTriangular id := by
  -- the matrices `Q_ℓ` of the skipless statement for the architecture `A.mixed`
  obtain ⟨Q, hQ, -, h1⟩ :=
    exists_cob_triangular_of_choice (A := A.mixed) (θ := θ) ε hA c cD ρE ρ s
  refine ⟨Q, hQ, fun x => ?_, h1⟩
  -- they preserve the function of the network of mixed blocks (Proposition A.1 (ii))
  rw [← cobMixed_one_eq_cob]
  exact evalMixed_cobMixed_rmsNorm θ x ε hA Q hQ 1

end Mixed

end Skips
