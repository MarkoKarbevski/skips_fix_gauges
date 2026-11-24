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

/-- Helper: a list has fewer sign variations than entries. -/
private theorem signVariations_le_length_ssp (l : List ℝ) :
    l.signVariations ≤ l.length - 1 := by
  unfold List.signVariations
  apply Nat.sub_le_sub_right
  exact (List.destutter_sublist _ _).length_le.trans
    ((List.length_filter_le _ _).trans (List.length_map _).le)

/-- Helper: a polynomial has at most as many sign variations as its degree. -/
private theorem signVariations_le_natDegree_ssp (q : Polynomial ℝ) :
    q.signVariations ≤ q.natDegree := by
  classical
  have h := signVariations_le_length_ssp q.coeffList
  rw [Polynomial.length_coeffList_eq_ite] at h
  unfold Polynomial.signVariations
  split_ifs at h <;> omega

/-- Helper, **the root count**: let `p = q − c z^m`, `deg q ≤ L`, vanish at the `n` points
`1 / (t + 1)`. If `n ≥ L + 2`, or `n = L + 1` and `m ≤ L`, then `p = 0`. If `c = 0` or `m ≤ L`,
`p` has degree `≤ L < n` and `n` roots. Otherwise `m > L`, `n ≥ L + 2`, and by Descartes' rule
of signs `p ≠ 0` would have at most `L + 1` positive roots (dropping its leading term `−c z^m`
leaves `q`, with at most `L` sign variations). -/
private theorem poly_eq_zero_ssp {L n m : ℕ} (q : Polynomial ℝ) (c : ℝ) (hq : q.natDegree ≤ L)
    (hroot : ∀ t : Fin n,
      (q - Polynomial.C c * Polynomial.X ^ m).eval (((t : ℕ) + 1 : ℝ)⁻¹) = 0)
    (hn : L + 2 ≤ n ∨ (n = L + 1 ∧ m ≤ L)) : q - Polynomial.C c * Polynomial.X ^ m = 0 := by
  -- the points `1 / (t + 1)` are distinct
  have hinj : Function.Injective fun t : Fin n => (((t : ℕ) + 1 : ℝ)⁻¹) := by
    intro x y hxy
    simp only [_root_.inv_inj, add_left_inj, Nat.cast_inj] at hxy
    exact Fin.ext hxy
  -- a polynomial of degree `< n` with these `n` roots is `0`
  have hcard : (q - Polynomial.C c * Polynomial.X ^ m).natDegree < n →
      q - Polynomial.C c * Polynomial.X ^ m = 0 := fun h =>
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj hroot
      (by rwa [Fintype.card_fin])
  by_cases hc : c = 0
  · apply hcard
    rw [hc, Polynomial.C_0, zero_mul, sub_zero]
    omega
  by_cases hm : m ≤ L
  · apply hcard
    have := (Polynomial.natDegree_sub_le _ _).trans
      (max_le hq ((Polynomial.natDegree_C_mul_X_pow_le c m).trans hm))
    omega
  -- `m > L`, so `n ≥ L + 2`: Descartes' rule of signs
  have hn2 : L + 2 ≤ n := by omega
  by_contra hp0
  -- `p` has the `n` distinct positive roots `1 / (t + 1)`
  have hroots : n ≤ (q - Polynomial.C c * Polynomial.X ^ m).roots.countP (0 < ·) := by
    classical
    have hS : (Finset.univ.image fun t : Fin n => (((t : ℕ) + 1 : ℝ)⁻¹)).card = n := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    rw [Multiset.countP_eq_card_filter, ← hS]
    refine Multiset.card_le_card ((Multiset.le_iff_subset (Finset.nodup _)).2 fun x hx => ?_)
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_def.2 hx)
    refine Multiset.mem_filter.2 ⟨(Polynomial.mem_roots hp0).2 (hroot t), ?_⟩
    show 0 < (((t : ℕ) + 1 : ℝ)⁻¹)
    positivity
  -- dropping the leading term `−c z^m` leaves `q`
  have hlead : (q - Polynomial.C c * Polynomial.X ^ m).eraseLead = q := by
    rw [sub_eq_add_neg, ← neg_mul, ← Polynomial.C_neg,
      Polynomial.eraseLead_add_of_natDegree_lt_right, Polynomial.eraseLead_C_mul_X_pow, add_zero]
    rw [Polynomial.natDegree_C_mul_X_pow m (-c) (neg_ne_zero.2 hc)]
    omega
  have h1 := Polynomial.roots_countP_pos_le_signVariations (q - Polynomial.C c * Polynomial.X ^ m)
  have h2 := Polynomial.signVariations_le_eraseLead_succ (q - Polynomial.C c * Polynomial.X ^ m)
  have h3 := signVariations_le_natDegree_ssp q
  rw [hlead] at h2
  omega

/-- Helper: `∏_t (1 − (t + 1) z)` vanishes at the points `1/(t+1)`, has the value `1` at `0`
and degree at most `n`. -/
private theorem nodeProd_ssp (n : ℕ) :
    (∀ t : Fin n, (∏ s : Fin n, (1 - C ((s : ℕ) + 1 : ℝ) * X)).eval (((t : ℕ) + 1 : ℝ)⁻¹)
      = 0) ∧
    (∏ s : Fin n, (1 - C ((s : ℕ) + 1 : ℝ) * X)).eval 0 = 1 ∧
    (∏ s : Fin n, (1 - C ((s : ℕ) + 1 : ℝ) * X)).natDegree ≤ n := by
  refine ⟨fun t => ?_, ?_, ?_⟩
  · -- the factor at `t` vanishes
    rw [eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
    have ht : ((t : ℕ) + 1 : ℝ) ≠ 0 := by positivity
    rw [eval_sub, eval_one, eval_mul, eval_C, eval_X, mul_inv_cancel₀ ht, sub_self]
  · rw [eval_prod]
    refine Finset.prod_eq_one fun s _ => ?_
    rw [eval_sub, eval_one, eval_mul, eval_C, eval_X, mul_zero, sub_zero]
  · -- each factor has degree at most `1`
    refine (natDegree_prod_le _ _).trans ?_
    have h1 : ∀ s : Fin n, (1 - C ((s : ℕ) + 1 : ℝ) * X).natDegree ≤ 1 := fun s =>
      (natDegree_sub_le _ _).trans
        (max_le (natDegree_one.le.trans zero_le_one)
          ((natDegree_C_mul_le _ _).trans natDegree_X_le))
    refine (Finset.sum_le_sum fun s _ => h1 s).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- **Proof of Theorem 4.2 (iii), equation (10):** for `n ≤ L`, or `n = L + 1` and `L ≤ L'`,
there are a real polynomial `Q` of degree at most `L` with `Q(0) = 1` and a number `γ ≠ 0` with
`Q(1/(t+1)) = γ (1/(t+1))^{L'+1}` for the `n` tokens `t`. -/
theorem exists_polynomial_short (n L L' : ℕ) (hn : n ≤ L ∨ (n = L + 1 ∧ L ≤ L')) :
    ∃ (Q : ℝ[X]) (γ : ℝ), Q.natDegree ≤ L ∧ Q.eval 0 = 1 ∧ γ ≠ 0 ∧
      ∀ t : Fin n, Q.eval (((t : ℕ) + 1 : ℝ)⁻¹) = γ * (((t : ℕ) + 1 : ℝ)⁻¹) ^ (L' + 1) := by
  -- the nodes `v t = 1/(t+1)` and the interpolant `P` of `v t ^ (L' + 1)`, of degree `< n`
  set v : Fin n → ℝ := fun t => ((t : ℕ) + 1 : ℝ)⁻¹ with hv
  have hinj : Function.Injective v := by
    intro x y hxy
    simp only [hv, _root_.inv_inj, add_left_inj, Nat.cast_inj] at hxy
    exact Fin.ext hxy
  set P := Lagrange.interpolate Finset.univ v (fun t => v t ^ (L' + 1)) with hP
  have hPv : ∀ t, P.eval (v t) = v t ^ (L' + 1) := fun t =>
    Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ t)
  have hPdeg : P.natDegree ≤ n - 1 := by
    have h := Lagrange.degree_interpolate_le (fun t => v t ^ (L' + 1)) hinj.injOn
      (s := Finset.univ)
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact natDegree_le_iff_degree_le.2 h
  rcases hn with hn | ⟨rfl, hL⟩
  · -- `n ≤ L`: correct the value at `0` by a multiple of `∏_t (1 − (t + 1) z)`, `γ = 1`
    obtain ⟨hN, hN0, hNdeg⟩ := nodeProd_ssp n
    refine ⟨P + C (1 - P.eval 0) * ∏ s : Fin n, (1 - C ((s : ℕ) + 1 : ℝ) * X), 1,
      ?_, ?_, one_ne_zero, fun t => ?_⟩
    · exact (natDegree_add_le _ _).trans (max_le (by omega)
        ((natDegree_C_mul_le _ _).trans (hNdeg.trans hn)))
    · rw [eval_add, eval_mul, eval_C, hN0]
      ring
    · rw [eval_add, eval_mul, eval_C, hN t, mul_zero, add_zero, one_mul]
      exact hPv t
  -- `n = L + 1 ≤ L' + 1`: `P(0) ≠ 0`, and `Q = P / P(0)`
  have hP0 : P.eval 0 ≠ 0 := by
    intro h0
    -- `P = z P₁`
    obtain ⟨P₁, hP₁⟩ : X ∣ P := X_dvd_iff.2 (by rw [coeff_zero_eq_eval_zero, h0])
    have hv0 : ∀ t, v t ≠ 0 := fun t => by
      simp only [hv]
      positivity
    by_cases hP₁0 : P₁ = 0
    · -- then `P = 0`, but `P(1) = 1`
      have h := hPv 0
      rw [hP₁, hP₁0, mul_zero, eval_zero] at h
      exact pow_ne_zero _ (hv0 0) h.symm
    have hdeg₁ : P₁.natDegree + 1 ≤ L := by
      have h := natDegree_mul (X_ne_zero (R := ℝ)) hP₁0
      rw [← hP₁, natDegree_X] at h
      omega
    -- `P₁ − z^{L'}` vanishes at the `L + 1` nodes and has degree `≤ L - 1`: it is zero
    have hroot : ∀ t : Fin (L + 1),
        (P₁ - C 1 * X ^ L').eval (((t : ℕ) + 1 : ℝ)⁻¹) = 0 := fun t => by
      have h := hPv t
      rw [hP₁, eval_mul, eval_X, pow_succ', mul_right_inj' (hv0 t)] at h
      rw [eval_sub, eval_mul, eval_C, one_mul, eval_pow, eval_X]
      exact sub_eq_zero.2 h
    have hzero := poly_eq_zero_ssp (L := L - 1) P₁ 1 (by omega) hroot (Or.inl (by omega))
    rw [sub_eq_zero, C_1, one_mul] at hzero
    rw [hzero, natDegree_X_pow] at hdeg₁
    omega
  refine ⟨C (P.eval 0)⁻¹ * P, (P.eval 0)⁻¹, ?_, ?_, inv_ne_zero hP0, fun t => ?_⟩
  · exact (natDegree_C_mul_le _ _).trans (by omega)
  · rw [eval_mul, eval_C, inv_mul_cancel₀ hP0]
  · rw [eval_mul, eval_C]
    exact congrArg _ (hPv t)

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
