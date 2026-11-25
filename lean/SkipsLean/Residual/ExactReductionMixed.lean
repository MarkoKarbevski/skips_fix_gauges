import SkipsLean.Symmetry.MixedJunctions
import SkipsLean.Residual.ExactReductionWrites
import SkipsLean.Dimension.Space

/-!
# Exact reduction for networks of mixed blocks

Paper (skips paper), Appendix A.3: "The following proposition is the exact reduction of Karbevski
(2026, Proposition 3.3), stated also for the rows of a write, for networks of mixed blocks and
for residual networks. Let `W_1` be an invertible `d_model × d_model` submatrix formed by
`d_model` columns of a matrix that reads `h_ℓ`, or by `d_model` rows of a matrix that writes it."
Proposition A.9 (i): "In a skipless network or a network of mixed blocks, the map `W ↦ W G` on
the matrices that write `h_ℓ` and `W ↦ G^{-1} W` on those that read it turns `W_1` into the
identity for `G = W_1` if `W_1` is part of a read, and for `G = W_1^{-1}` if it is part of a
write. Under RMSNorm with `ε > 0`, `G = Q` from a QR factorization `W_1 = Q T`, or
`W_1^⊤ = Q T` for a write, turns `W_1` into a triangular matrix."

Here (i) for the networks of mixed blocks of `Network/Mixed.lean`, at all hidden states at once.
In a network of mixed blocks the matrix that reads `h_{ℓ−1}` is `[U_ℓ | W_read^ℓ]` (the readout
`D` for the last hidden state) and the matrix that writes `h_ℓ` stacks `V_ℓ` on `W_write^ℓ` (the
embedding `E` for `h_0`): the read and the write of block `ℓ` of a parameter of `A.mixed`. The
map of the proposition is `θ.cob G G` on these parameters (`cobMixed_one_eq_cob`: it is
`T_{G,1}`); the chosen columns may be columns of `U_ℓ`, of `W_read^ℓ`, or of both.

* `exists_cob_mixed_reads_eq_one`, `exists_cob_mixed_writes_eq_one`: without normalization;
* `exists_cob_mixed_reads_upperTriangular`, `exists_cob_mixed_writes_lowerTriangular`: under
  pre-RMSNorm (any `ε`), with orthogonal `Q_ℓ`; for the rows of a write the result is lower
  triangular, as in the proof ("`W_1 Q = T^⊤`, which is lower triangular").

The proofs are those of the skipless statements for the architecture `A.mixed`
(`Symmetry/Reduction.lean`, `Residual/ExactReductionWrites.lean`), with
`Symmetry/MixedJunctions.lean` for the function of the network of mixed blocks under RMSNorm.
The count of the removed parameters: `Residual/ExactReductionCount.lean`.
-/

namespace Skips

open Matrix

variable {T : Type*} {d : Type} {dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d]
  [Fintype dIn]
variable {A : Arch T d L}

omit [Fintype dIn] in
/-- The map `T_{G,1}` of a network of mixed blocks, with the same `G` for the reads of the
identity units and of the hidden units, is the change of basis `θ.cob G G` of the reads
`[U_ℓ | W_read^ℓ]` and of the writes that stack `V_ℓ` on `W_write^ℓ`. -/
theorem cobMixed_one_eq_cob (θ : Params A.mixed dIn dOut) (G : Fin (L + 1) → GL d ℝ) :
    θ.cobMixed G G 1 = θ.cob G G := by
  apply Params.ext'
  · rfl
  · intro ℓ
    ext a (b | b)
    · simp [Params.cobMixed, Params.mix, Params.cob, Params.mixU, Matrix.mul_apply]
    · simp [Params.cobMixed, Params.mix, Params.cob, Params.unmix, Matrix.mul_apply]
  · intro ℓ
    ext (a | a) b
    · -- the rows of `V_ℓ`: `K_ℓ⁻¹ V_ℓ G_ℓ` with `K_ℓ = 1`
      show ((↑((1 : Fin L → GL d ℝ) ℓ)⁻¹ : Matrix d d ℝ) * θ.mixV ℓ
          * (G ℓ.succ : Matrix d d ℝ)) a b
        = (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) (Sum.inl a) b
      simp [Params.mixV, Matrix.mul_apply]
    · -- the rows of `W_write^ℓ`
      show (θ.unmix.write ℓ * (G ℓ.succ : Matrix d d ℝ)) a b
        = (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) (Sum.inr a) b
      simp [Params.unmix, Matrix.mul_apply]
  · rfl

variable (θ : Params A.mixed dIn dOut)

/-- **Proposition A.9 (i) for networks of mixed blocks, reads, without normalization:** if the
chosen columns of every read `[U_ℓ | W_read^ℓ]` and of the readout form invertible matrices,
changes of basis at the `L + 1` hidden states preserve the function and turn all of these
submatrices into the identity. -/
theorem exists_cob_mixed_reads_eq_one (hA : A.χ = id)
    (c : ∀ ℓ : Fin L, d → d ⊕ A.r ℓ) (cD : d → dOut)
    (hc : ∀ ℓ, IsUnit ((θ.read ℓ).submatrix id (c ℓ)).det)
    (hcD : IsUnit (θ.D.submatrix id cD).det) :
    ∃ G : Fin (L + 1) → GL d ℝ,
      (∀ x : Matrix T dIn ℝ, evalMixed A (θ.cob G G) x = evalMixed A θ x) ∧
      (∀ ℓ, ((θ.cob G G).read ℓ).submatrix id (c ℓ) = 1) ∧
      (θ.cob G G).D.submatrix id cD = 1 := by
  -- without normalization the network of mixed blocks is the skipless network of `A.mixed`
  obtain ⟨G, hG, h1, h2⟩ := exists_cob_reads_eq_one (A := A.mixed) (θ := θ) hA c cD hc hcD
  refine ⟨G, fun x => ?_, h1, h2⟩
  rw [evalMixed_eq_eval hA, evalMixed_eq_eval hA]
  exact hG x

/-- **Proposition A.9 (i) for networks of mixed blocks, writes, without normalization:** if the
chosen rows of the embedding and of every write (which stacks `V_ℓ` on `W_write^ℓ`) form
invertible matrices, changes of basis at the `L + 1` hidden states preserve the function and turn
all of these submatrices into the identity. -/
theorem exists_cob_mixed_writes_eq_one (hA : A.χ = id)
    (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → d ⊕ A.w ℓ)
    (hρE : IsUnit (θ.E.submatrix ρE id).det)
    (hρ : ∀ ℓ, IsUnit ((θ.write ℓ).submatrix (ρ ℓ) id).det) :
    ∃ G : Fin (L + 1) → GL d ℝ,
      (∀ x : Matrix T dIn ℝ, evalMixed A (θ.cob G G) x = evalMixed A θ x) ∧
      (θ.cob G G).E.submatrix ρE id = 1 ∧
      (∀ ℓ, ((θ.cob G G).write ℓ).submatrix (ρ ℓ) id = 1) := by
  obtain ⟨G, hG, h1, h2⟩ := exists_cob_writes_eq_one (A := A.mixed) (θ := θ) hA ρE ρ hρE hρ
  refine ⟨G, fun x => ?_, h1, h2⟩
  rw [evalMixed_eq_eval hA, evalMixed_eq_eval hA]
  exact hG x

/-- **Proposition A.9 (i) for networks of mixed blocks, reads, under pre-RMSNorm:** orthogonal
changes of basis at the `L + 1` hidden states preserve the function and turn the chosen columns
of every read `[U_ℓ | W_read^ℓ]` and of the readout into upper triangular matrices. -/
theorem exists_cob_mixed_reads_upperTriangular [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (c : ∀ ℓ : Fin L, d → d ⊕ A.r ℓ) (cD : d → dOut) :
    ∃ Q : Fin (L + 1) → GL d ℝ,
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
      (∀ x : Matrix T dIn ℝ, evalMixed A (θ.cob Q Q) x = evalMixed A θ x) ∧
      (∀ ℓ, (((θ.cob Q Q).read ℓ).submatrix id (c ℓ)).BlockTriangular id) ∧
      ((θ.cob Q Q).D.submatrix id cD).BlockTriangular id := by
  -- the matrices `Q_ℓ` of the skipless statement for the architecture `A.mixed`
  obtain ⟨Q, hQ, -, h1, h2⟩ :=
    exists_cob_reads_upperTriangular (A := A.mixed) (θ := θ) ε hA c cD
  refine ⟨Q, hQ, fun x => ?_, h1, h2⟩
  -- they preserve the function of the network of mixed blocks (Proposition A.1 (ii))
  rw [← cobMixed_one_eq_cob]
  exact evalMixed_cobMixed_rmsNorm θ x ε hA Q hQ 1

/-- **Proposition A.9 (i) for networks of mixed blocks, writes, under pre-RMSNorm:** orthogonal
changes of basis at the `L + 1` hidden states preserve the function and turn the chosen rows of
the embedding and of every write (which stacks `V_ℓ` on `W_write^ℓ`) into lower triangular
matrices. -/
theorem exists_cob_mixed_writes_lowerTriangular [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → d ⊕ A.w ℓ) :
    ∃ Q : Fin (L + 1) → GL d ℝ,
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
      (∀ x : Matrix T dIn ℝ, evalMixed A (θ.cob Q Q) x = evalMixed A θ x) ∧
      (((θ.cob Q Q).E.submatrix ρE id)ᵀ).BlockTriangular id ∧
      ∀ ℓ, ((((θ.cob Q Q).write ℓ).submatrix (ρ ℓ) id)ᵀ).BlockTriangular id := by
  obtain ⟨Q, hQ, -, h1, h2⟩ :=
    exists_cob_writes_lowerTriangular (A := A.mixed) (θ := θ) ε hA ρE ρ
  refine ⟨Q, hQ, fun x => ?_, h1, h2⟩
  rw [← cobMixed_one_eq_cob]
  exact evalMixed_cobMixed_rmsNorm θ x ε hA Q hQ 1

end Skips
