import SkipsLean.Symmetry.ChangeOfBasis

/-!
# Changes of basis under pre-RMSNorm

Paper: Proposition 3.2, the cases of pre-RMSNorm with `ε > 0` (in fact any `ε`) and with `ε = 0`.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn]
variable {A : Arch T d L}

/-- Without skip connections the stream matrices stay zero: `G_{ℓ-1}⁻¹ 0 G_ℓ = 0`. -/
private theorem cobSkip_zero (G : Fin (L + 1) → GL d ℝ) :
    cobSkip (0 : Fin L → Matrix d d ℝ) G = 0 := by
  funext ℓ
  simp only [cobSkip, Pi.zero_apply, Matrix.mul_zero, Matrix.zero_mul]

variable (θ : Params A dIn dOut) (x : Matrix T dIn ℝ)

/-- **Proposition 3.2 under pre-RMSNorm:** one orthogonal matrix per hidden state. The reads are
multiplied by `Q⁻¹ = Qᵀ`. -/
theorem eval_cob_rmsNorm (ε : ℝ) (hA : A.χ = rmsNorm ε) (Q : Fin (L + 1) → GL d ℝ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) :
    eval A 0 (θ.cob Q Q) x = eval A 0 θ x := by
  -- Pre-RMSNorm commutes with every orthogonal `Q_ℓ` (Lemma A.1): `χ (h Q_ℓ) = χ (h) Q_ℓ`.
  have hχ : ∀ ℓ (h : Matrix T d ℝ),
      A.χ (h * (Q ℓ : Matrix d d ℝ)) = A.χ h * (Q ℓ : Matrix d d ℝ) := by
    intro ℓ h
    rw [hA]
    exact rmsNorm_mul_orthogonal ε (hQ ℓ) h
  -- Proposition 3.2 in general form with `G = K = Q`; the zero skips stay `Q⁻¹ 0 Q = 0`.
  have h := eval_cob (M := 0) (θ := θ) (G := Q) (K := Q) (x := x) hχ
  rwa [cobSkip_zero] at h

/-- **Proposition 3.2 for `ε = 0`:** with `G_ℓ = c_ℓ Q_ℓ`, `c_ℓ > 0` and `Q_ℓ` orthogonal, the
writes are multiplied by `G_ℓ` and the reads by `Q_ℓ⁻¹ = Q_ℓᵀ`. -/
theorem eval_cob_rmsNorm_zero (hA : A.χ = rmsNorm 0) (G Q : Fin (L + 1) → GL d ℝ)
    (c : Fin (L + 1) → ℝ) (hc : ∀ ℓ, 0 < c ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ)) :
    eval A 0 (θ.cob G Q) x = eval A 0 θ x := by
  -- RMSNorm with `ε = 0` loses the scale `c_ℓ` (Lemma A.1): `χ (h G_ℓ) = χ (h) Q_ℓ`.
  have hχ : ∀ ℓ (h : Matrix T d ℝ),
      A.χ (h * (G ℓ : Matrix d d ℝ)) = A.χ h * (Q ℓ : Matrix d d ℝ) := by
    intro ℓ h
    rw [hA, hG ℓ]
    exact rmsNorm_zero_mul_smul_orthogonal (hc ℓ) (hQ ℓ) h
  -- Proposition 3.2 in general form with `K = Q`; the zero skips stay `G⁻¹ 0 G = 0`.
  have h := eval_cob (M := 0) (θ := θ) (G := G) (K := Q) (x := x) hχ
  rwa [cobSkip_zero] at h

/-- The inverse of an orthogonal matrix is its transpose, so the reads are multiplied by `Qᵀ`. -/
theorem coe_inv_of_mem_orthogonalGroup (Q : GL d ℝ)
    (hQ : (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) :
    (↑Q⁻¹ : Matrix d d ℝ) = (Q : Matrix d d ℝ)ᵀ := by
  -- `Q Qᵀ = 1`, so `Qᵀ` is the inverse of `Q`.
  exact Units.inv_eq_of_mul_eq_one_right ((Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ)

end Skips
