import SkipsLean.Residual.LearnedSkips
import SkipsLean.Basic.RMSNorm

/-!
# Learned skips in `CO(d)` are absorbed under pre-RMSNorm with `ε = 0`; the forward products

Paper (skips paper), Theorem A.12 (ii): "Orthogonal skips can be absorbed. If every `Π_ℓ` lies in
`G`, write `Π_ℓ = c_ℓ P_ℓ` with `c_ℓ > 0` and `P_ℓ` orthogonal, where `c_ℓ = 1` if `ε > 0`. Then
the network computes the same function as the residual network with the embedding `E`, the reads
`P_{ℓ−1} W_read^ℓ`, the writes `W_write^ℓ Π_ℓ⁻¹` and the readout `P_L D`." Here
`Π_ℓ = A_1 ⋯ A_ℓ` are the forward products of the skips, `Π_0 = I`, and `G` is `O(d_model)` for
`ε > 0` and `CO(d_model)`, the positive multiples of orthogonal matrices, for `ε = 0`.

`Residual/LearnedSkips.lean` has this for orthogonal skips and any `ε` in the form of Theorem 3.2
(ii), with the backward products `Λ_ℓ = A_{ℓ+1} ⋯ A_L` (`skipProd`), where the readout is
unchanged. Here:

* the forward products `skipProdFwd` (`Π_0 = I`, `Π_ℓ = Π_{ℓ−1} A_ℓ`);
* `ε = 0`, skips `A_ℓ = c_ℓ Q_ℓ` with `c_ℓ > 0` and `Q_ℓ` orthogonal (every `Π_ℓ` lies in `CO(d)`
  if and only if every `A_ℓ` does, `CO(d)` being a group): the form with the backward products,
  and the paper's form with the forward products;
* the paper's form with the forward products for orthogonal skips and any `ε` (the case `ε > 0` of
  Theorem A.12 (ii)).

In `θ.cob G K` the embedding and the writes are multiplied by `G` and the reads and the readout
by `K⁻¹`: with `G_ℓ = Π_ℓ⁻¹` and `K_ℓ = P_ℓ⁻¹` these are the paper's embedding `E`, reads
`P_{ℓ−1} W_read^ℓ`, writes `W_write^ℓ Π_ℓ⁻¹` and readout `P_L D`. Not stated: the converse.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn]
variable {A : Arch T d L} (θ : Params A dIn dOut) (x : Matrix T dIn ℝ)

/-- **The forward products of the skips** (Theorem A.12): `Π_0 = I` and `Π_ℓ = Π_{ℓ−1} A_ℓ`, so
`Π_ℓ = A_1 ⋯ A_ℓ`. -/
def skipProdFwd (S : Fin L → GL d ℝ) : Fin (L + 1) → GL d ℝ :=
  Fin.induction (motive := fun _ => GL d ℝ) 1 (fun ℓ P => P * S ℓ)

@[simp] theorem skipProdFwd_zero (S : Fin L → GL d ℝ) : skipProdFwd S 0 = 1 := by
  simp [skipProdFwd]

/-- `Π_ℓ = Π_{ℓ−1} A_ℓ`. -/
@[simp] theorem skipProdFwd_succ (S : Fin L → GL d ℝ) (ℓ : Fin L) :
    skipProdFwd S ℓ.succ = skipProdFwd S ℓ.castSucc * S ℓ := by
  simp [skipProdFwd]

/-- **The embedding is unchanged by the forward change of variables** (`Π_0 = I`). -/
theorem cob_skipProdFwd_E (S : Fin L → GL d ℝ) (K : Fin (L + 1) → GL d ℝ) :
    (θ.cob (fun ℓ => (skipProdFwd S ℓ)⁻¹) K).E = θ.E := by
  sorry

/-- **Theorem A.12 (ii) of the skips paper for `ε = 0`, in the form of Theorem 3.2 (ii):** under
pre-RMSNorm with `ε = 0`, a network with learned skips `A_ℓ = c_ℓ Q_ℓ`, `c_ℓ > 0` and `Q_ℓ`
orthogonal, computes the same function as the residual network with the embedding `E Λ_0`, the
writes `W_write^ℓ Λ_ℓ`, the reads `(Λ^Q_{ℓ−1})⁻¹ W_read^ℓ` and the readout `D`, where `Λ` and
`Λ^Q` are the backward products of the `A_ℓ` and of the `Q_ℓ`. -/
theorem eval_learned_eq_residual_rmsNorm_zero (hA : A.χ = rmsNorm 0) (S Q : Fin L → GL d ℝ)
    (c : Fin L → ℝ) (hc : ∀ ℓ, 0 < c ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hS : ∀ ℓ, (S ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ)) :
    eval A (fun ℓ => (S ℓ : Matrix d d ℝ)) θ x
      = eval A 1 (θ.cob (skipProd S) (skipProd Q)) x := by
  sorry

/-- **Theorem A.12 (ii) of the skips paper for `ε = 0`, first two sentences:** under pre-RMSNorm
with `ε = 0`, a network with learned skips `A_ℓ = c_ℓ Q_ℓ`, `c_ℓ > 0` and `Q_ℓ` orthogonal,
computes the same function as the residual network with the embedding `E`, the reads
`P_{ℓ−1} W_read^ℓ`, the writes `W_write^ℓ Π_ℓ⁻¹` and the readout `P_L D`, where `Π` and `P` are
the forward products of the `A_ℓ` and of the `Q_ℓ` (so `Π_ℓ = (c_1 ⋯ c_ℓ) P_ℓ`). -/
theorem eval_learned_eq_residual_rmsNorm_zero_fwd (hA : A.χ = rmsNorm 0) (S Q : Fin L → GL d ℝ)
    (c : Fin L → ℝ) (hc : ∀ ℓ, 0 < c ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hS : ∀ ℓ, (S ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ)) :
    eval A (fun ℓ => (S ℓ : Matrix d d ℝ)) θ x
      = eval A 1 (θ.cob (fun ℓ => (skipProdFwd S ℓ)⁻¹) (fun ℓ => (skipProdFwd Q ℓ)⁻¹)) x := by
  sorry

/-- **Theorem A.12 (ii) of the skips paper for `ε > 0` (stated for any `ε`), first two
sentences:** under pre-RMSNorm, a network with orthogonal learned skips computes the same
function as the residual network with the embedding `E`, the reads `Π_{ℓ−1} W_read^ℓ`, the writes
`W_write^ℓ Π_ℓ⁻¹` and the readout `Π_L D`, with `Π` the forward products of the skips. -/
theorem eval_learned_eq_residual_rmsNorm_fwd (ε : ℝ) (hA : A.χ = rmsNorm ε) (S : Fin L → GL d ℝ)
    (hS : ∀ ℓ, (S ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) :
    eval A (fun ℓ => (S ℓ : Matrix d d ℝ)) θ x
      = eval A 1 (θ.cob (fun ℓ => (skipProdFwd S ℓ)⁻¹) (fun ℓ => (skipProdFwd S ℓ)⁻¹)) x := by
  sorry

end Skips
