import Mathlib

/-!
# RMSNorm on rows

Paper: "On the Functional Dimension of a Family of Analytic Neural Networks", Section 2
(Normalization) and Lemma A.1.

A hidden state is a matrix `h : Matrix T d ℝ` whose rows are the tokens. RMSNorm with the
constant `ε` acts on every row `v` as `v / sqrt (‖v‖² / d_model + ε)`.
-/

namespace Skips

open Matrix

variable {T d : Type*} [Fintype d]

/-- RMSNorm with the constant `ε` on one row `v`: `v / sqrt (‖v‖² / d_model + ε)`.
For `ε = 0` and `v = 0` this is `0` (division by zero is zero in Lean); the paper leaves that
case undefined. -/
noncomputable def rmsRow (ε : ℝ) (v : d → ℝ) : d → ℝ :=
  (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹ • v

/-- RMSNorm on a hidden state: every row (token) is normalized. -/
noncomputable def rmsNorm (ε : ℝ) (h : Matrix T d ℝ) : Matrix T d ℝ :=
  Matrix.of fun t => rmsRow ε (h t)

variable [DecidableEq d]

/-- An orthogonal matrix preserves the squared norm of a row. -/
theorem dotProduct_vecMul_orthogonal {Q : Matrix d d ℝ} (hQ : Q ∈ Matrix.orthogonalGroup d ℝ)
    (v : d → ℝ) : (v ᵥ* Q) ⬝ᵥ (v ᵥ* Q) = v ⬝ᵥ v := by
  -- `Q Qᵀ = 1`, so `(vQ) Qᵀ = v`; the bilinear identity moves `Qᵀ` across the dot product.
  have h1 : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff d ℝ).mp hQ
  have h2 := Matrix.dotProduct_vecMul_transpose Q (v ᵥ* Q) v
  rw [Matrix.vecMul_vecMul, h1, Matrix.vecMul_one] at h2
  exact h2.symm

/-- Lemma A.1, direction "orthogonal ⇒ commutes", on one row: `N_ε(vQ) = N_ε(v)Q`. -/
theorem rmsRow_vecMul_orthogonal (ε : ℝ) {Q : Matrix d d ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup d ℝ) (v : d → ℝ) :
    rmsRow ε (v ᵥ* Q) = rmsRow ε v ᵥ* Q := by
  -- the squared norm is unchanged, and the scalar factor commutes with `· ᵥ* Q`
  unfold rmsRow
  rw [dotProduct_vecMul_orthogonal hQ, Matrix.smul_vecMul]

/-- Lemma A.1, direction "orthogonal ⇒ commutes": `N_ε(hQ) = N_ε(h)Q` for orthogonal `Q`. -/
theorem rmsNorm_mul_orthogonal (ε : ℝ) {Q : Matrix d d ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup d ℝ) (h : Matrix T d ℝ) :
    rmsNorm ε (h * Q) = rmsNorm ε h * Q := by
  -- row `t` of `h * Q` is `(h t) ᵥ* Q` and row `t` of `rmsNorm ε h * Q` is `rmsRow ε (h t) ᵥ* Q`
  ext t j
  have hrow : (h * Q) t = h t ᵥ* Q := rfl
  have hrow' : (rmsNorm ε h * Q) t = rmsRow ε (h t) ᵥ* Q := rfl
  have key : rmsNorm ε (h * Q) t = (rmsNorm ε h * Q) t := by
    rw [hrow']
    show rmsRow ε ((h * Q) t) = _
    rw [hrow, rmsRow_vecMul_orthogonal ε hQ]
  exact congrFun key j

omit [DecidableEq d] in
/-- Helper: `N_0` forgets a positive scale on a row, `N_0(c w) = N_0(w)` for `c > 0`. The case
`w = 0` needs no separate treatment: `(c * s)⁻¹ * c = s⁻¹` also for `s = 0`. -/
private theorem rmsRow_zero_smul {c : ℝ} (hc : 0 < c) (w : d → ℝ) :
    rmsRow 0 (c • w) = rmsRow 0 w := by
  unfold rmsRow
  -- `‖cw‖² / d = c² (‖w‖² / d)`, hence `sqrt (‖cw‖² / d) = c * sqrt (‖w‖² / d)`
  have hs : Real.sqrt ((c • w ⬝ᵥ c • w) / (Fintype.card d : ℝ) + 0)
      = c * Real.sqrt ((w ⬝ᵥ w) / (Fintype.card d : ℝ) + 0) := by
    have : (c • w ⬝ᵥ c • w) / (Fintype.card d : ℝ) + 0
        = c ^ 2 * ((w ⬝ᵥ w) / (Fintype.card d : ℝ) + 0) := by
      rw [smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul, add_zero]
      ring
    rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  -- the factor `c` cancels
  rw [hs, mul_inv, smul_smul]
  congr 1
  rw [mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

/-- Lemma A.1 for `ε = 0`: the scale of a row is lost, `N_0(h·cQ) = N_0(h)Q` for `c > 0`. -/
theorem rmsNorm_zero_mul_smul_orthogonal {c : ℝ} (hc : 0 < c) {Q : Matrix d d ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup d ℝ) (h : Matrix T d ℝ) :
    rmsNorm 0 (h * (c • Q)) = rmsNorm 0 h * Q := by
  -- row `t` of `h * (c • Q)` is `c • ((h t) ᵥ* Q)`; the factor `c` is lost, then use Lemma A.1
  ext t j
  have hrow : (h * (c • Q)) t = c • (h t ᵥ* Q) := by
    rw [show (h * (c • Q)) t = h t ᵥ* (c • Q) from rfl, Matrix.vecMul_smul]
  have hrow' : (rmsNorm 0 h * Q) t = rmsRow 0 (h t) ᵥ* Q := rfl
  have key : rmsNorm 0 (h * (c • Q)) t = (rmsNorm 0 h * Q) t := by
    rw [hrow']
    show rmsRow 0 ((h * (c • Q)) t) = _
    rw [hrow, rmsRow_zero_smul hc, rmsRow_vecMul_orthogonal 0 hQ]
  exact congrFun key j

end Skips
