import SkipsLean.Basic.RMSNorm

/-!
# LayerNorm: the two computations behind its reduction to RMSNorm

Paper (dimension paper): Proposition A.3 and its proof.

LayerNorm is RMSNorm after the projection `Z = I - (1/d) 𝟙𝟙ᵀ` that removes the mean of a row.
Part (i) of the proposition rests on `Z² = Z` and on `hZ` having mean zero. Part (ii) rests on
one identity: for a matrix `U` with orthonormal columns (the paper's `Ū`, with `d - 1` columns
spanning the rows of mean zero),

  `N_ε(y Uᵀ) = sqrt(d/m) · N'(y) Uᵀ`,

where `N'` is RMSNorm of dimension `m` with the constant `ε d / m`.

The statement of Proposition A.3 for whole networks, with gains and biases:
`Network/LayerNorm.lean`.
-/

namespace Skips

open Matrix

variable {d m : Type*} [Fintype d] [DecidableEq d] [Fintype m] [DecidableEq m]

/-- The centering matrix `Z = I - (1/d) 𝟙𝟙ᵀ`. -/
noncomputable def centering (d : Type*) [Fintype d] [DecidableEq d] : Matrix d d ℝ :=
  1 - (Fintype.card d : ℝ)⁻¹ • Matrix.of fun _ _ => (1 : ℝ)

omit [DecidableEq d] in
/-- Helper: `J * J = n • J` for the all-ones matrix `J` (each entry is a sum of `n` ones). -/
private theorem ones_mul_ones :
    (Matrix.of fun _ _ => (1 : ℝ)) * (Matrix.of fun _ _ => (1 : ℝ) : Matrix d d ℝ)
      = (Fintype.card d : ℝ) • (Matrix.of fun _ _ => (1 : ℝ) : Matrix d d ℝ) := by
  ext i j
  simp [Matrix.mul_apply]

/-- `Z² = Z`. -/
theorem centering_mul_centering : centering d * centering d = centering d := by
  rcases isEmpty_or_nonempty d with hd | hd
  · -- no rows: all matrices on `d` are equal
    exact Subsingleton.elim _ _
  · -- `(1 - cJ)² = 1 - 2cJ + c² (nJ) = 1 - cJ` for `c = n⁻¹`, since `c n = 1`
    have hn : (Fintype.card d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    unfold centering
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, ones_mul_ones]
    rw [inv_mul_cancel₀ hn, one_smul, sub_self, smul_zero, sub_zero]

omit [DecidableEq d] in
/-- Helper: `v J` is the constant row with entry `∑ v`. -/
private theorem vecMul_ones (v : d → ℝ) :
    v ᵥ* (Matrix.of fun _ _ => (1 : ℝ) : Matrix d d ℝ) = fun _ => ∑ j, v j := by
  ext i
  simp [Matrix.vecMul, dotProduct]

/-- Helper: `(vZ)_i = v_i - n⁻¹ ∑ v`. -/
private theorem vecMul_centering_apply (v : d → ℝ) (i : d) :
    (v ᵥ* centering d) i = v i - (Fintype.card d : ℝ)⁻¹ * ∑ j, v j := by
  unfold centering
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.vecMul_smul, vecMul_ones]
  simp

/-- The rows `vZ` have mean zero: their entries sum to zero. -/
theorem sum_vecMul_centering (v : d → ℝ) : ∑ i, (v ᵥ* centering d) i = 0 := by
  rcases isEmpty_or_nonempty d with hd | hd
  · -- the empty sum
    exact Finset.sum_of_isEmpty _
  · -- `∑ v - n * (n⁻¹ * ∑ v) = 0`
    have hn : (Fintype.card d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [vecMul_centering_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [mul_inv_cancel_left₀ hn, sub_self]

/-- A row of mean zero is not changed by `Z`. -/
theorem vecMul_centering_of_sum_eq_zero (v : d → ℝ) (hv : ∑ i, v i = 0) :
    v ᵥ* centering d = v := by
  -- `(vZ)_i = v_i - n⁻¹ * 0 = v_i`
  ext i
  rw [vecMul_centering_apply, hv, mul_zero, sub_zero]

/-- **Proposition A.3 (ii), the identity of its proof.** For `U` with orthonormal columns,
`N_ε(y Uᵀ) = sqrt(d/m) · N'(y) Uᵀ`, with `N'` the RMSNorm of dimension `m` and constant `ε d/m`. -/
theorem rmsRow_vecMul_transpose_of_orthonormal (U : Matrix d m ℝ) (hU : Uᵀ * U = 1)
    (hm : 0 < Fintype.card m) (ε : ℝ) (y : m → ℝ) :
    rmsRow ε (y ᵥ* Uᵀ)
      = Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ)) •
          (rmsRow (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ)) y ᵥ* Uᵀ) := by
  rcases isEmpty_or_nonempty d with hd | hd
  · -- no coordinates: both sides are functions on the empty type `d`
    exact Subsingleton.elim _ _
  · have hn : (0 : ℝ) < Fintype.card d := Nat.cast_pos.mpr Fintype.card_pos
    have hk : (0 : ℝ) < Fintype.card m := Nat.cast_pos.mpr hm
    -- `y Uᵀ` has the same squared norm as `y`, because `(y Uᵀ) U = y (Uᵀ U) = y`
    have hww : (y ᵥ* Uᵀ) ⬝ᵥ (y ᵥ* Uᵀ) = y ⬝ᵥ y := by
      have h2 := Matrix.dotProduct_vecMul_transpose U y (y ᵥ* Uᵀ)
      rw [Matrix.vecMul_vecMul, hU, Matrix.vecMul_one] at h2
      exact h2
    -- `s/k + ε n/k = (n/k) (s/n + ε)`, so the square roots differ by the factor `sqrt (n/k)`
    have hs : (y ⬝ᵥ y) / (Fintype.card m : ℝ) + ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ)
        = (Fintype.card d : ℝ) / (Fintype.card m : ℝ)
          * ((y ⬝ᵥ y) / (Fintype.card d : ℝ) + ε) := by
      field_simp
    have hq : Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ)) ≠ 0 :=
      (Real.sqrt_pos.mpr (div_pos hn hk)).ne'
    unfold rmsRow
    rw [hww, hs, Matrix.smul_vecMul, Real.sqrt_mul (div_nonneg hn.le hk.le), smul_smul]
    -- the scalar `sqrt (n/k) * (sqrt (n/k) * sqrt (s/n + ε))⁻¹` is `(sqrt (s/n + ε))⁻¹`
    congr 1
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

end Skips
