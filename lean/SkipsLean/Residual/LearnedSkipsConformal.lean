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

/-- If every skip is `A_ℓ = c_ℓ Q_ℓ` with `c_ℓ > 0`, every backward product is
`Λ_ℓ = C Λ^Q_ℓ` with `C > 0` (the product of the `c`'s after `ℓ`). -/
private theorem skipProd_smul_lsc (S Q : Fin L → GL d ℝ) (c : Fin L → ℝ) (hc : ∀ ℓ, 0 < c ℓ)
    (hS : ∀ ℓ, (S ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ)) (ℓ : Fin (L + 1)) :
    ∃ C : ℝ, 0 < C ∧ (skipProd S ℓ : Matrix d d ℝ) = C • (skipProd Q ℓ : Matrix d d ℝ) := by
  induction ℓ using Fin.reverseInduction with
  | last =>
    -- `Λ_L = I = 1 • Λ^Q_L`.
    exact ⟨1, one_pos, by rw [skipProd_last, skipProd_last, one_smul]⟩
  | cast i ih =>
    -- `Λ_{i-1} = A_i Λ_i = (c_i C) (Q_i Λ^Q_i)`.
    obtain ⟨C, hC, hΛ⟩ := ih
    refine ⟨c i * C, mul_pos (hc i) hC, ?_⟩
    rw [skipProd_castSucc, skipProd_castSucc, Units.val_mul, Units.val_mul, hS i, hΛ,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- A product of orthogonal matrices is orthogonal: so is every `Λ_ℓ = A_{ℓ+1} ⋯ A_L`. -/
private theorem skipProd_mem_orthogonalGroup_lsc (S : Fin L → GL d ℝ)
    (hS : ∀ ℓ, (S ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) (ℓ : Fin (L + 1)) :
    (skipProd S ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  induction ℓ using Fin.reverseInduction with
  | last =>
    -- `Λ_L = I`.
    rw [skipProd_last, Units.val_one]
    exact one_mem _
  | cast i ih =>
    -- `Λ_{i-1} = A_i Λ_i`.
    rw [skipProd_castSucc, Units.val_mul]
    exact mul_mem (hS i) ih

/-- The skips after the change of basis by `Λ` are the identity: `Λ_{ℓ-1}⁻¹ A_ℓ Λ_ℓ = I`. -/
private theorem cobSkip_skipProd_lsc (S : Fin L → GL d ℝ) :
    cobSkip (fun ℓ => (S ℓ : Matrix d d ℝ)) (skipProd S) = 1 := by
  funext ℓ
  simp only [cobSkip, Pi.one_apply]
  rw [mul_assoc, ← Units.val_mul, ← skipProd_castSucc, Units.inv_mul]

/-- If every skip is `A_ℓ = c_ℓ Q_ℓ` with `c_ℓ > 0`, every forward product is
`Π_ℓ = C P_ℓ` with `C > 0` (the product `c_1 ⋯ c_ℓ`). -/
private theorem skipProdFwd_smul_lsc (S Q : Fin L → GL d ℝ) (c : Fin L → ℝ)
    (hc : ∀ ℓ, 0 < c ℓ) (hS : ∀ ℓ, (S ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ))
    (ℓ : Fin (L + 1)) :
    ∃ C : ℝ, 0 < C ∧ (skipProdFwd S ℓ : Matrix d d ℝ) = C • (skipProdFwd Q ℓ : Matrix d d ℝ) := by
  induction ℓ using Fin.induction with
  | zero =>
    -- `Π_0 = I = 1 • P_0`.
    exact ⟨1, one_pos, by rw [skipProdFwd_zero, skipProdFwd_zero, one_smul]⟩
  | succ i ih =>
    -- `Π_{i+1} = Π_i A_{i+1} = (C c_i) (P_i Q_i)`.
    obtain ⟨C, hC, hP⟩ := ih
    refine ⟨C * c i, mul_pos hC (hc i), ?_⟩
    rw [skipProdFwd_succ, skipProdFwd_succ, Units.val_mul, Units.val_mul, hS i, hP,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- A product of orthogonal matrices is orthogonal: so is every `Π_ℓ = A_1 ⋯ A_ℓ`. -/
private theorem skipProdFwd_mem_orthogonalGroup_lsc (S : Fin L → GL d ℝ)
    (hS : ∀ ℓ, (S ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) (ℓ : Fin (L + 1)) :
    (skipProdFwd S ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  induction ℓ using Fin.induction with
  | zero =>
    -- `Π_0 = I`.
    rw [skipProdFwd_zero, Units.val_one]
    exact one_mem _
  | succ i ih =>
    -- `Π_{i+1} = Π_i A_{i+1}`.
    rw [skipProdFwd_succ, Units.val_mul]
    exact mul_mem ih (hS i)

/-- The inverse of an orthogonal matrix is orthogonal (it is its transpose). -/
private theorem inv_mem_orthogonalGroup_lsc (P : GL d ℝ)
    (hP : (P : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) :
    (↑P⁻¹ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff, coe_inv_of_mem_orthogonalGroup P hP,
    Matrix.transpose_transpose]
  exact (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hP

/-- If `Π = C P` with `C ≠ 0`, then `Π⁻¹ = C⁻¹ P⁻¹`. -/
private theorem coe_inv_eq_smul_lsc (M P : GL d ℝ) {C : ℝ} (hC : C ≠ 0)
    (h : (M : Matrix d d ℝ) = C • (P : Matrix d d ℝ)) :
    (↑M⁻¹ : Matrix d d ℝ) = C⁻¹ • (↑P⁻¹ : Matrix d d ℝ) := by
  -- `Π (C⁻¹ P⁻¹) = (C C⁻¹) (P P⁻¹) = I`.
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [h, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hC, one_smul,
    Units.mul_inv]

/-- The skips after the change of basis by `Π⁻¹` are the identity: `Π_{ℓ-1} A_ℓ Π_ℓ⁻¹ = I`,
since `Π_ℓ = Π_{ℓ-1} A_ℓ`. -/
private theorem cobSkip_skipProdFwd_lsc (S : Fin L → GL d ℝ) :
    cobSkip (fun ℓ => (S ℓ : Matrix d d ℝ)) (fun ℓ => (skipProdFwd S ℓ)⁻¹) = 1 := by
  funext ℓ
  simp only [cobSkip, Pi.one_apply, inv_inv]
  rw [← Units.val_mul, ← Units.val_mul, ← skipProdFwd_succ, mul_inv_cancel, Units.val_one]

/-- **The embedding is unchanged by the forward change of variables** (`Π_0 = I`). -/
theorem cob_skipProdFwd_E (S : Fin L → GL d ℝ) (K : Fin (L + 1) → GL d ℝ) :
    (θ.cob (fun ℓ => (skipProdFwd S ℓ)⁻¹) K).E = θ.E := by
  -- The embedding becomes `E Π_0⁻¹` and `Π_0 = I`.
  change θ.E * (↑(skipProdFwd S 0)⁻¹ : Matrix d d ℝ) = θ.E
  rw [skipProdFwd_zero, inv_one, Units.val_one, Matrix.mul_one]

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
  -- `Λ_ℓ = C Λ^Q_ℓ` with `C > 0` and `Λ^Q_ℓ` orthogonal, so `χ (h Λ_ℓ) = χ (h) Λ^Q_ℓ`.
  have hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (skipProd S ℓ : Matrix d d ℝ))
      = A.χ h * (skipProd Q ℓ : Matrix d d ℝ) := by
    intro ℓ h
    obtain ⟨C, hC, hΛ⟩ := skipProd_smul_lsc S Q c hc hS ℓ
    rw [hA, hΛ]
    exact rmsNorm_zero_mul_smul_orthogonal hC (skipProd_mem_orthogonalGroup_lsc Q hQ ℓ) h
  -- Proposition 3.2 with `G = Λ`, `K = Λ^Q` turns the skips into `Λ_{ℓ-1}⁻¹ A_ℓ Λ_ℓ = I`.
  rw [← eval_cob (M := fun ℓ => (S ℓ : Matrix d d ℝ)) (θ := θ) (G := skipProd S)
    (K := skipProd Q) (x := x) hχ, cobSkip_skipProd_lsc]

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
  -- `Π_ℓ = C P_ℓ` with `C > 0`, so `Π_ℓ⁻¹ = C⁻¹ P_ℓ⁻¹` with `P_ℓ⁻¹` orthogonal, and
  -- `χ (h Π_ℓ⁻¹) = χ (h) P_ℓ⁻¹`.
  have hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (↑(skipProdFwd S ℓ)⁻¹ : Matrix d d ℝ))
      = A.χ h * (↑(skipProdFwd Q ℓ)⁻¹ : Matrix d d ℝ) := by
    intro ℓ h
    obtain ⟨C, hC, hP⟩ := skipProdFwd_smul_lsc S Q c hc hS ℓ
    rw [hA, coe_inv_eq_smul_lsc _ _ hC.ne' hP]
    exact rmsNorm_zero_mul_smul_orthogonal (inv_pos.mpr hC)
      (inv_mem_orthogonalGroup_lsc _ (skipProdFwd_mem_orthogonalGroup_lsc Q hQ ℓ)) h
  -- Proposition 3.2 with `G = Π⁻¹`, `K = P⁻¹` turns the skips into `Π_{ℓ-1} A_ℓ Π_ℓ⁻¹ = I`.
  rw [← eval_cob (M := fun ℓ => (S ℓ : Matrix d d ℝ)) (θ := θ)
    (G := fun ℓ => (skipProdFwd S ℓ)⁻¹) (K := fun ℓ => (skipProdFwd Q ℓ)⁻¹) (x := x) hχ,
    cobSkip_skipProdFwd_lsc]

/-- **Theorem A.12 (ii) of the skips paper for `ε > 0` (stated for any `ε`), first two
sentences:** under pre-RMSNorm, a network with orthogonal learned skips computes the same
function as the residual network with the embedding `E`, the reads `Π_{ℓ−1} W_read^ℓ`, the writes
`W_write^ℓ Π_ℓ⁻¹` and the readout `Π_L D`, with `Π` the forward products of the skips. -/
theorem eval_learned_eq_residual_rmsNorm_fwd (ε : ℝ) (hA : A.χ = rmsNorm ε) (S : Fin L → GL d ℝ)
    (hS : ∀ ℓ, (S ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) :
    eval A (fun ℓ => (S ℓ : Matrix d d ℝ)) θ x
      = eval A 1 (θ.cob (fun ℓ => (skipProdFwd S ℓ)⁻¹) (fun ℓ => (skipProdFwd S ℓ)⁻¹)) x := by
  -- Every `Π_ℓ⁻¹` is orthogonal, so pre-RMSNorm commutes with it (Lemma A.1).
  have hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (↑(skipProdFwd S ℓ)⁻¹ : Matrix d d ℝ))
      = A.χ h * (↑(skipProdFwd S ℓ)⁻¹ : Matrix d d ℝ) := by
    intro ℓ h
    rw [hA]
    exact rmsNorm_mul_orthogonal ε
      (inv_mem_orthogonalGroup_lsc _ (skipProdFwd_mem_orthogonalGroup_lsc S hS ℓ)) h
  -- Proposition 3.2 with `G = K = Π⁻¹` turns the skips into `Π_{ℓ-1} A_ℓ Π_ℓ⁻¹ = I`.
  rw [← eval_cob (M := fun ℓ => (S ℓ : Matrix d d ℝ)) (θ := θ)
    (G := fun ℓ => (skipProdFwd S ℓ)⁻¹) (K := fun ℓ => (skipProdFwd S ℓ)⁻¹) (x := x) hχ,
    cobSkip_skipProdFwd_lsc]

end Skips
