import SkipsLean.Network.Attention
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Attention networks on short sequences: the polynomial of the construction

Paper (absorb paper), proof of Theorem 4.2 (iii): "Let `z_t = 1/t` for `t = 1, …, T`. We first
choose real numbers `q_1, …, q_L` and `γ'` such that the polynomial
`Q(z) = 1 + q_1 z + ⋯ + q_L z^L` satisfies `Q(z_t) = γ' z_t^{L'}` for `t = 1, …, T`.  (10)
If `T ≤ L`, let `γ' = 1`. The `T × L` matrix with the entries `z_t^k`, `1 ≤ k ≤ L`, has rank `T`
[…]. So the linear equations (10) in `q_1, …, q_L` have a solution. If `T = L + 1 ≤ L'`, (10) is a
system of `L + 1` linear equations in `q_1, …, q_L` and `γ'`. As `L' > L`, the monomials
`z, …, z^L, z^{L'}` are distinct, so a vector in the kernel of its matrix gives a polynomial with
at most `L + 1` nonzero coefficients and the `L + 1` positive roots `z_t`, which is zero by
Descartes' rule. So the matrix is invertible, and there is a solution. Next we realize `Q` by `L`
blocks. As `Q(0) = 1`, the real polynomial `Q` is a product of factors `1 + a z` and
`1 + 2 α z + (α² + β²) z²` with real `a`, `α` and `β`. […] The matrix `U` is diagonalizable with
the eigenvalues `z_t`, so (10) gives `Q(U) = γ' U^{L'}`."

Here the three facts about polynomials that the construction uses, with the tokens `t : Fin n`
(so `z_t = 1/(t + 1)`) and the skipless network of `L' + 1` blocks (the paper's `L'`):

* `exists_polynomial_short`: a real polynomial `Q` of degree at most `L` with `Q(0) = 1` and a
  number `γ ≠ 0` with `Q(z_t) = γ z_t^{L' + 1}` at the `n` points, when `n ≤ L`, or `n = L + 1`
  and `L ≤ L'`. That `γ ≠ 0` is not said in the paper; it holds (in the first case `γ = 1`, in
  the second `Q` has at most `L` roots), and it makes the common function of the two networks
  nonzero.
* `exists_complex_factors`: over `ℂ`, a real polynomial `Q` of degree at most `L` with
  `Q(0) = 1` is a product of `L` factors `1 + c z`. The paper pairs conjugate roots into real
  quadratic factors; one complex factor per block is enough for the construction, since the
  matrices `α Π + β J` of the paper multiply as the complex numbers `α + β i`.
* `aeval_attnWeights_causal_eq_zero`: a real polynomial that vanishes at the `n` points `z_t`
  vanishes at the matrix `U` of the causal mask at zero scores (row `t` of `U` is uniform on the
  tokens `s ≤ t`), which has these `n` distinct eigenvalues.
-/

namespace Skips

open Matrix Polynomial

/-- **Proof of Theorem 4.2 (iii), equation (10):** for `n ≤ L`, or `n = L + 1` and `L ≤ L'`,
there are a real polynomial `Q` of degree at most `L` with `Q(0) = 1` and a number `γ ≠ 0` with
`Q(1/(t+1)) = γ (1/(t+1))^{L'+1}` for the `n` tokens `t`. -/
theorem exists_polynomial_short (n L L' : ℕ) (hn : n ≤ L ∨ (n = L + 1 ∧ L ≤ L')) :
    ∃ (Q : ℝ[X]) (γ : ℝ), Q.natDegree ≤ L ∧ Q.eval 0 = 1 ∧ γ ≠ 0 ∧
      ∀ t : Fin n, Q.eval (((t : ℕ) + 1 : ℝ)⁻¹) = γ * (((t : ℕ) + 1 : ℝ)⁻¹) ^ (L' + 1) := by
  sorry

/-- Helper: `(1 − z/r)(−r) = z − r` for `r ≠ 0`. -/
private theorem factor_eq_ssp {r : ℂ} (hr0 : r ≠ 0) :
    (1 + C (-r⁻¹) * X) * C (-r) = X - C r := by
  have h : C r⁻¹ * C r = (1 : ℂ[X]) := by rw [← C_mul, inv_mul_cancel₀ hr0, C_1]
  simp only [C_neg]
  linear_combination X * h

/-- Helper: over `ℂ`, a polynomial of degree at most `L` with the value `1` at `0` is a product
of `L` factors `1 + c z`, by induction on `L`, splitting off one root `r ≠ 0` at a time. -/
private theorem exists_factors_ssp (L : ℕ) :
    ∀ R : ℂ[X], R.natDegree ≤ L → R.eval 0 = 1 →
      ∃ c : Fin L → ℂ, R = ∏ ℓ, (1 + C (c ℓ) * X) := by
  induction L with
  | zero =>
    intro R hR h0
    refine ⟨Fin.elim0, ?_⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty, eq_C_of_natDegree_le_zero hR,
      coeff_zero_eq_eval_zero, h0, C_1]
  | succ L ih =>
    intro R hR h0
    by_cases hd : R.natDegree = 0
    · -- `R = 1`: all factors `1 + 0 z`
      refine ⟨fun _ => 0, ?_⟩
      simp only [C_0, zero_mul, add_zero, Finset.prod_const_one]
      rw [eq_C_of_natDegree_le_zero hd.le, coeff_zero_eq_eval_zero, h0, C_1]
    -- a root `r` of `R`, `r ≠ 0` since `R(0) = 1`
    have hpos : 0 < R.degree := natDegree_pos_iff_degree_pos.1 (Nat.pos_of_ne_zero hd)
    obtain ⟨r, hr⟩ := Complex.exists_root hpos
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [IsRoot.def, h0] at hr
      exact one_ne_zero hr
    -- `R = (z − r) R₁` with `deg R₁ ≤ L`
    obtain ⟨R₁, hmul⟩ : ∃ R₁, (X - C r) * R₁ = R := ⟨_, mul_divByMonic_eq_iff_isRoot.2 hr⟩
    have hR₁0 : R₁ ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hmul
      rw [← hmul, eval_zero] at h0
      exact zero_ne_one h0
    have hdeg1 : R₁.natDegree ≤ L := by
      have h := natDegree_mul (X_sub_C_ne_zero r) hR₁0
      rw [hmul, natDegree_X_sub_C] at h
      omega
    have h01 : (-r) * R₁.eval 0 = 1 := by
      rw [← h0, ← hmul, eval_mul, eval_sub, eval_X, eval_C, zero_sub]
    -- `R₂ = −r R₁` has `R₂(0) = 1`: induction
    obtain ⟨c, hc⟩ := ih (C (-r) * R₁) ((natDegree_C_mul_le _ _).trans hdeg1)
      (by rw [eval_mul, eval_C, h01])
    refine ⟨Fin.cons (-r⁻¹) c, ?_⟩
    rw [Fin.prod_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    rw [← hc, ← hmul, ← mul_assoc, factor_eq_ssp hr0]

/-- **Proof of Theorem 4.2 (iii), the factors of `Q`:** over the complex numbers, a real
polynomial of degree at most `L` with the value `1` at `0` is a product of `L` factors
`1 + c z`. -/
theorem exists_complex_factors (L : ℕ) (Q : ℝ[X]) (hdeg : Q.natDegree ≤ L)
    (h0 : Q.eval 0 = 1) :
    ∃ c : Fin L → ℂ, Q.map (algebraMap ℝ ℂ) = ∏ ℓ, (1 + C (c ℓ) * X) := by
  -- the complexification of `Q` has degree at most `L` and the value `1` at `0`
  refine exists_factors_ssp L _ (natDegree_map_le.trans hdeg) ?_
  rw [eval_map, eval₂_at_zero, coeff_zero_eq_eval_zero, h0, map_one]

/-- Helper: under the causal mask row `t` of `U` is uniform on the `t + 1` tokens `s ≤ t`. -/
private theorem attnWeights_causal_ssp {n : ℕ} (t s : Fin n) :
    attnWeights (fun t s : Fin n => s ≤ t) 0 t s
      = if s ≤ t then ((t : ℕ) + 1 : ℝ)⁻¹ else 0 := by
  simp only [attnWeights, Matrix.of_apply, Matrix.zero_apply, Real.exp_zero]
  split_ifs with h
  · rw [Finset.sum_boole, Finset.filter_ge_eq_Iic, Fin.card_Iic]
    push_cast
    rw [one_div]
  · rfl

/-- Helper: the characteristic polynomial of `U` is `∏_t (X − 1/(t+1))`, since `U` is lower
triangular with these diagonal entries. -/
private theorem charpoly_causal_ssp (n : ℕ) :
    (attnWeights (fun t s : Fin n => s ≤ t) (0 : Matrix (Fin n) (Fin n) ℝ)).charpoly
      = ∏ t : Fin n, (X - C (((t : ℕ) + 1 : ℝ)⁻¹)) := by
  -- `Uᵀ` is upper triangular with the same diagonal
  rw [← Matrix.charpoly_transpose, Matrix.charpoly_of_isUpperTriangular]
  · refine Finset.prod_congr rfl fun t _ => ?_
    rw [Matrix.transpose_apply, attnWeights_causal_ssp, ite_eq_left le_rfl]
  · intro i j hij
    rw [Matrix.transpose_apply, attnWeights_causal_ssp,
      ite_eq_right (not_le.2 (show j < i from hij))]

/-- Helper: a polynomial that vanishes at the `n` distinct points `1/(t+1)` is a multiple of
`∏_t (X − 1/(t+1))`. -/
private theorem prod_dvd_ssp {n : ℕ} (p : ℝ[X])
    (hp : ∀ t : Fin n, p.eval (((t : ℕ) + 1 : ℝ)⁻¹) = 0) :
    ∏ t : Fin n, (X - C (((t : ℕ) + 1 : ℝ)⁻¹)) ∣ p := by
  have hinj : Function.Injective fun t : Fin n => (((t : ℕ) + 1 : ℝ)⁻¹) := by
    intro x y hxy
    simp only [_root_.inv_inj, add_left_inj, Nat.cast_inj] at hxy
    exact Fin.ext hxy
  -- the factors `X − 1/(t+1)` are pairwise coprime and each divides `p`
  refine Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C hinj).set_pairwise _)
    fun t _ => ?_
  exact dvd_iff_isRoot.2 (hp t)

/-- **Proof of Theorem 4.2 (iii), "`U` is diagonalizable with the eigenvalues `z_t`":** a real
polynomial that vanishes at the points `1/(t+1)`, `t : Fin n`, vanishes at the matrix of the
attention weights of the causal mask at zero scores. -/
theorem aeval_attnWeights_causal_eq_zero (n : ℕ) (p : ℝ[X])
    (hp : ∀ t : Fin n, p.eval (((t : ℕ) + 1 : ℝ)⁻¹) = 0) :
    aeval (attnWeights (fun t s : Fin n => s ≤ t) (0 : Matrix (Fin n) (Fin n) ℝ)) p = 0 := by
  -- the characteristic polynomial of `U` divides `p`, and vanishes at `U` (Cayley–Hamilton)
  obtain ⟨r, hr⟩ := prod_dvd_ssp p hp
  rw [hr, ← charpoly_causal_ssp, map_mul, Matrix.aeval_self_charpoly, zero_mul]

end Skips
