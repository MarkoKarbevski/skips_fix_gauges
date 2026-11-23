import Mathlib

/-!
# A flat direction of tanh hidden units vanishes

Paper (dimension paper): Lemma C.3, the case of `tanh`, in the generality in which the paper
states it: with a linear term `x M`, a constant `γ` and biases `β_i`.

The function is `G(φ, x) = x M + γ + ∑_i tanh(z_i) a_i` with `z_i = x c_i + β_i`, where `c_i` is
the read column of hidden unit `i` and `a_i` its write row. A direction
`ψ = (ψ_M, ψ_γ, ψ_{c_i}, ψ_{β_i}, ψ_{a_i})` of these weights is flat if the derivative of `G`
along it vanishes at every input `x`:

  `x ψ_M + ψ_γ + ∑_i [ tanh(z_i) ψ_{a_i} + tanh'(z_i) (x ψ_{c_i} + ψ_{β_i}) a_i ] = 0`,

with `tanh' = 1 - tanh²`. The lemma says that then `ψ = 0`, when every `a_i` is nonzero and the
`c_i` are nonzero and pairwise non-collinear. The proof of the paper follows a ray `x = t n` to
infinity, where the hidden units saturate at pairwise different exponential rates
(Sussmann 1992, Lemma 3.1).
-/

namespace Skips

open Matrix Filter Topology

/-- `tanh z - 1 = -2 e^{-2z} / (1 + e^{-2z})`. -/
private lemma tanh_sub_one_eq (z : ℝ) :
    Real.tanh z - 1 = -2 * Real.exp (-2 * z) / (1 + Real.exp (-2 * z)) := by
  have h1 : Real.exp (-2 * z) = Real.exp (-z) * Real.exp (-z) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp z * Real.exp (-z) = 1 := by rw [← Real.exp_add]; simp
  have hx := Real.exp_pos z
  have hy := Real.exp_pos (-z)
  rw [Real.tanh_eq, h1]
  field_simp
  linear_combination (2 * Real.exp (-z)) * h2

/-- `1 - tanh² z = 4 e^{-2z} / (1 + e^{-2z})²`. -/
private lemma one_sub_tanh_sq_eq (z : ℝ) :
    1 - Real.tanh z ^ 2 = 4 * Real.exp (-2 * z) / (1 + Real.exp (-2 * z)) ^ 2 := by
  have hT : Real.tanh z = 1 + -2 * Real.exp (-2 * z) / (1 + Real.exp (-2 * z)) := by
    rw [← tanh_sub_one_eq]; ring
  have hE : 0 < 1 + Real.exp (-2 * z) := by positivity
  rw [hT]
  field_simp
  ring

/-- `t ^ m e^{μ t} → 0` for `μ < 0`, with `m = 0`. -/
private lemma tendsto_exp_mul_of_neg {μ : ℝ} (hμ : μ < 0) :
    Tendsto (fun t => Real.exp (μ * t)) atTop (𝓝 0) := by
  have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (-μ) (by linarith)
  simpa using this

/-- `t e^{μ t} → 0` for `μ < 0`. -/
private lemma tendsto_mul_exp_mul_of_neg {μ : ℝ} (hμ : μ < 0) :
    Tendsto (fun t => t * Real.exp (μ * t)) atTop (𝓝 0) := by
  have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (-μ) (by linarith)
  simpa using this

/-- For `u > 0`: if `g t e^{(μ - 2u) t} → ℓ`, then `g t e^{μ t} (tanh(t u + b) - 1)` and
`g t e^{μ t} (1 - tanh²(t u + b))` tend to `-2 e^{-2b} ℓ` and `4 e^{-2b} ℓ`. -/
private lemma tanh_limits_pos {u : ℝ} (hu : 0 < u) (b μ ℓ : ℝ) (g : ℝ → ℝ)
    (hg : Tendsto (fun t => g t * Real.exp ((μ - 2 * u) * t)) atTop (𝓝 ℓ)) :
    Tendsto (fun t => g t * Real.exp (μ * t) * (Real.tanh (t * u + b) - 1)) atTop
        (𝓝 (-2 * Real.exp (-2 * b) * ℓ)) ∧
      Tendsto (fun t => g t * Real.exp (μ * t) * (1 - Real.tanh (t * u + b) ^ 2)) atTop
        (𝓝 (4 * Real.exp (-2 * b) * ℓ)) := by
  -- `E t = e^{-2(t u + b)} → 0`
  have hE : Tendsto (fun t => Real.exp (-2 * (t * u + b))) atTop (𝓝 0) := by
    have h := (tendsto_exp_mul_of_neg (μ := -2 * u) (by linarith)).const_mul (Real.exp (-2 * b))
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    rw [← Real.exp_add]; ring_nf
  have h1E : Tendsto (fun t => 1 + Real.exp (-2 * (t * u + b))) atTop (𝓝 1) := by
    simpa using hE.const_add 1
  -- `e^{μ t} E t = e^{-2b} e^{(μ - 2u) t}`
  have key : ∀ t, Real.exp (μ * t) * Real.exp (-2 * (t * u + b))
      = Real.exp (-2 * b) * Real.exp ((μ - 2 * u) * t) := fun t => by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  constructor
  · have h := ((hg.const_mul (-2 * Real.exp (-2 * b)))).div h1E one_ne_zero
    rw [div_one] at h
    refine h.congr fun t => ?_
    rw [Pi.div_apply, tanh_sub_one_eq]
    calc _ = -2 * g t * (Real.exp (-2 * b) * Real.exp ((μ - 2 * u) * t))
          / (1 + Real.exp (-2 * (t * u + b))) := by ring
      _ = _ := by rw [← key t]; ring
  · have h := ((hg.const_mul (4 * Real.exp (-2 * b)))).div (h1E.pow 2) (by norm_num)
    rw [one_pow, div_one] at h
    refine h.congr fun t => ?_
    rw [Pi.div_apply, one_sub_tanh_sq_eq]
    calc _ = 4 * g t * (Real.exp (-2 * b) * Real.exp ((μ - 2 * u) * t))
          / (1 + Real.exp (-2 * (t * u + b))) ^ 2 := by ring
      _ = _ := by rw [← key t]; ring

/-- For `u ≠ 0`: if `g t e^{(μ - 2|u|) t} → 0`, then `g t e^{μ t} (tanh(t u + b) - sign u) → 0`
and `g t e^{μ t} (1 - tanh²(t u + b)) → 0`. The case `u < 0` reduces to `u > 0` as `tanh` is odd. -/
private lemma tanh_limits_zero {u : ℝ} (hu : u ≠ 0) (b μ : ℝ) (g : ℝ → ℝ)
    (hg : Tendsto (fun t => g t * Real.exp ((μ - 2 * |u|) * t)) atTop (𝓝 0)) :
    Tendsto (fun t => g t * Real.exp (μ * t) * (Real.tanh (t * u + b) - Real.sign u)) atTop
        (𝓝 0) ∧
      Tendsto (fun t => g t * Real.exp (μ * t) * (1 - Real.tanh (t * u + b) ^ 2)) atTop
        (𝓝 0) := by
  rcases hu.lt_or_gt with hneg | hpos
  · -- `u < 0`: `tanh (t u + b) = -tanh (t (-u) + (-b))`
    rw [abs_of_neg hneg] at hg
    obtain ⟨h1, h2⟩ := tanh_limits_pos (neg_pos.2 hneg) (-b) μ 0 g hg
    rw [mul_zero] at h1 h2
    have hodd : ∀ t, Real.tanh (t * u + b) = -Real.tanh (t * -u + -b) := fun t => by
      rw [← Real.tanh_neg]; congr 1; ring
    constructor
    · have h1' := h1.neg
      rw [neg_zero] at h1'
      refine h1'.congr fun t => ?_
      rw [Real.sign_of_neg hneg, hodd t]; ring
    · refine h2.congr fun t => ?_
      rw [hodd t]; ring
  · rw [abs_of_pos hpos] at hg
    obtain ⟨h1, h2⟩ := tanh_limits_pos hpos b μ 0 g hg
    rw [mul_zero] at h1 h2
    rw [Real.sign_of_pos hpos]
    exact ⟨h1, h2⟩

/-- Exact rate for `u > 0`: `e^{2ut} (tanh(t u + b) - 1) → -2 e^{-2b}` and
`e^{2ut} (1 - tanh²(t u + b)) → 4 e^{-2b}`. -/
private lemma tanh_limits_exact {u : ℝ} (hu : 0 < u) (b : ℝ) :
    Tendsto (fun t => Real.exp (2 * u * t) * (Real.tanh (t * u + b) - 1)) atTop
        (𝓝 (-2 * Real.exp (-2 * b))) ∧
      Tendsto (fun t => Real.exp (2 * u * t) * (1 - Real.tanh (t * u + b) ^ 2)) atTop
        (𝓝 (4 * Real.exp (-2 * b))) := by
  obtain ⟨h1, h2⟩ := tanh_limits_pos hu b (2 * u) 1 (fun _ => 1)
    (by simp)
  simp only [one_mul, mul_one] at h1 h2
  exact ⟨h1, h2⟩

/-- Decay for `u ≠ 0` and `μ < 2|u|`: `e^{μt} (tanh(t u + b) - sign u)`, `e^{μt} (1 - tanh²)` and
`t e^{μt} (1 - tanh²)` tend to `0`. -/
private lemma tanh_decay {u : ℝ} (hu : u ≠ 0) (b : ℝ) {μ : ℝ} (hμ : μ < 2 * |u|) :
    Tendsto (fun t => Real.exp (μ * t) * (Real.tanh (t * u + b) - Real.sign u)) atTop (𝓝 0) ∧
      Tendsto (fun t => Real.exp (μ * t) * (1 - Real.tanh (t * u + b) ^ 2)) atTop (𝓝 0) ∧
      Tendsto (fun t => t * Real.exp (μ * t) * (1 - Real.tanh (t * u + b) ^ 2)) atTop
        (𝓝 0) := by
  have hneg : μ - 2 * |u| < 0 := by linarith
  obtain ⟨h1, h2⟩ := tanh_limits_zero hu b μ (fun _ => 1)
    (by simpa using tendsto_exp_mul_of_neg hneg)
  obtain ⟨-, h3⟩ := tanh_limits_zero hu b μ id (tendsto_mul_exp_mul_of_neg hneg)
  simp only [one_mul] at h1 h2
  exact ⟨h1, h2, h3⟩

/-- **The ray argument**, in one output coordinate. Along the ray `x = t ν` the identity reads
`t V + C + ∑ᵢ [tanh(t uᵢ + bᵢ) Aᵢ + (1 - tanh²(t uᵢ + bᵢ)) (t wᵢ + pᵢ) aᵢ] = 0`. If `u_j > 0` and
`u_j < |u_i|` for all `i ≠ j`, then `w_j a_j = 0` and `A_j = 2 p_j a_j`. -/
private lemma ray_coeffs {q : Type*} [Fintype q] [DecidableEq q] (u b w p A a : q → ℝ)
    (V C : ℝ) (j : q) (hj : 0 < u j) (hk : ∀ i, i ≠ j → u j < |u i|)
    (hJ : ∀ t : ℝ, t * V + C + ∑ i, (Real.tanh (t * u i + b i) * A i
      + (1 - Real.tanh (t * u i + b i) ^ 2) * (t * w i + p i) * a i) = 0) :
    w j * a j = 0 ∧ A j = 2 * p j * a j := by
  -- every `u i` is nonzero
  have hu0 : ∀ i, u i ≠ 0 := fun i => by
    by_cases hi : i = j
    · subst hi; exact hj.ne'
    · exact abs_pos.1 (hj.trans (hk i hi))
  -- limits along the ray without exponential weight
  have h0 : ∀ i, Tendsto (fun t => Real.tanh (t * u i + b i)) atTop (𝓝 (Real.sign (u i))) ∧
      Tendsto (fun t => 1 - Real.tanh (t * u i + b i) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun t => t * (1 - Real.tanh (t * u i + b i) ^ 2)) atTop (𝓝 0) := fun i => by
    have hpos : (0 : ℝ) < 2 * |u i| := by have := abs_pos.2 (hu0 i); linarith
    obtain ⟨h1, h2, h3⟩ := tanh_decay (hu0 i) (b i) hpos
    simp only [zero_mul, Real.exp_zero, one_mul, mul_one] at h1 h2 h3
    refine ⟨?_, h2, h3⟩
    simpa using h1.add_const (Real.sign (u i))
  -- the part `R t` of the identity without `t V` tends to `K = C + ∑ sign(uᵢ) Aᵢ`
  have hR : Tendsto (fun t => C + ∑ i, (Real.tanh (t * u i + b i) * A i
      + (1 - Real.tanh (t * u i + b i) ^ 2) * (t * w i + p i) * a i)) atTop
      (𝓝 (C + ∑ i, Real.sign (u i) * A i)) := by
    refine tendsto_const_nhds.add (tendsto_finsetSum _ fun i _ => ?_)
    obtain ⟨h1, h2, h3⟩ := h0 i
    have := (h1.mul_const (A i)).add
      (((h3.mul_const (w i)).add (h2.mul_const (p i))).mul_const (a i))
    simp only [zero_mul, add_zero] at this
    refine this.congr fun t => ?_
    ring
  -- (i) divide by `t`: `V = 0`
  have hV : V = 0 := by
    have h1 := tendsto_const_nhds (x := V) |>.add (tendsto_inv_atTop_zero.mul hR)
    rw [zero_mul, add_zero] at h1
    refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_gt_atTop 0] with t ht
    have hR' : C + ∑ i, (Real.tanh (t * u i + b i) * A i
        + (1 - Real.tanh (t * u i + b i) ^ 2) * (t * w i + p i) * a i) = -(t * V) := by
      linear_combination hJ t
    rw [hR']
    field_simp
    ring
  -- (ii) the constant vanishes
  have hK : C + ∑ i, Real.sign (u i) * A i = 0 := by
    refine tendsto_nhds_unique hR (tendsto_const_nhds.congr fun t => ?_)
    have := hJ t
    rw [hV, mul_zero, zero_add] at this
    exact this.symm
  -- so `G t = ∑ᵢ [(tanh - sign uᵢ) Aᵢ + (1 - tanh²) (t wᵢ + pᵢ) aᵢ] = 0`
  have hG : ∀ t, ∑ i, ((Real.tanh (t * u i + b i) - Real.sign (u i)) * A i
      + (1 - Real.tanh (t * u i + b i) ^ 2) * (t * w i + p i) * a i) = 0 := fun t => by
    have h1 := hJ t
    rw [hV, mul_zero, zero_add] at h1
    have h2 : ∑ i, ((Real.tanh (t * u i + b i) - Real.sign (u i)) * A i
        + (1 - Real.tanh (t * u i + b i) ^ 2) * (t * w i + p i) * a i)
        = (C + ∑ i, (Real.tanh (t * u i + b i) * A i
          + (1 - Real.tanh (t * u i + b i) ^ 2) * (t * w i + p i) * a i))
          - (C + ∑ i, Real.sign (u i) * A i) := by
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, h1, hK, sub_zero]
  -- weighted limits, weight `e^{2 u_j t}`: only unit `j` survives
  have hE1 : ∀ i, Tendsto (fun t => Real.exp (2 * u j * t)
      * (Real.tanh (t * u i + b i) - Real.sign (u i))) atTop
      (𝓝 (if i = j then -2 * Real.exp (-2 * b j) else 0)) := fun i => by
    split_ifs with hi
    · subst hi; rw [Real.sign_of_pos hj]; exact (tanh_limits_exact hj (b i)).1
    · exact (tanh_decay (hu0 i) (b i) (by linarith [hk i hi])).1
  have hE2 : ∀ i, Tendsto (fun t => Real.exp (2 * u j * t)
      * (1 - Real.tanh (t * u i + b i) ^ 2)) atTop
      (𝓝 (if i = j then 4 * Real.exp (-2 * b j) else 0)) := fun i => by
    split_ifs with hi
    · subst hi; exact (tanh_limits_exact hj (b i)).2
    · exact (tanh_decay (hu0 i) (b i) (by linarith [hk i hi])).2.1
  -- (iii) weight `e^{2 u_j t} / t`: `w_j a_j = 0`
  have hwa : w j * a j = 0 := by
    have hlim : Tendsto (fun t => ∑ i, Real.exp (2 * u j * t) * t⁻¹
        * ((Real.tanh (t * u i + b i) - Real.sign (u i)) * A i
          + (1 - Real.tanh (t * u i + b i) ^ 2) * (t * w i + p i) * a i)) atTop
        (𝓝 (∑ i, (if i = j then 4 * Real.exp (-2 * b j) else 0) * w i * a i)) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      have := ((tendsto_inv_atTop_zero.mul (hE1 i)).mul_const (A i)).add
        ((((hE2 i).mul_const (w i)).add
          ((tendsto_inv_atTop_zero.mul (hE2 i)).mul_const (p i))).mul_const (a i))
      simp only [zero_mul, zero_add, add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      have ht' := ht.ne'
      field_simp
    have h0' : Tendsto (fun t => ∑ i, Real.exp (2 * u j * t) * t⁻¹
        * ((Real.tanh (t * u i + b i) - Real.sign (u i)) * A i
          + (1 - Real.tanh (t * u i + b i) ^ 2) * (t * w i + p i) * a i)) atTop (𝓝 0) :=
      tendsto_const_nhds.congr fun t => by rw [← Finset.mul_sum, hG t, mul_zero]
    have h := tendsto_nhds_unique hlim h0'
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)] at h
    simp only [ite_true] at h
    have h3 : Real.exp (-2 * b j) * (w j * a j) = 0 := by linear_combination (1 / 4 : ℝ) * h
    exact (mul_eq_zero.1 h3).resolve_left (Real.exp_pos _).ne'
  -- (iv) weight `e^{2 u_j t}`: `-2 e^{-2 b_j} A_j + 4 e^{-2 b_j} p_j a_j = 0`
  have hlim : Tendsto (fun t => ∑ i, Real.exp (2 * u j * t)
      * ((Real.tanh (t * u i + b i) - Real.sign (u i)) * A i
        + (1 - Real.tanh (t * u i + b i) ^ 2) * (t * w i + p i) * a i)) atTop
      (𝓝 (∑ i, ((if i = j then -2 * Real.exp (-2 * b j) else 0) * A i
        + (if i = j then 4 * Real.exp (-2 * b j) else 0) * p i * a i))) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    have hmid : Tendsto (fun t => t * Real.exp (2 * u j * t)
        * (1 - Real.tanh (t * u i + b i) ^ 2) * (w i * a i)) atTop (𝓝 0) := by
      by_cases hi : i = j
      · subst hi; simp only [hwa, mul_zero]; exact tendsto_const_nhds
      · have := (tanh_decay (hu0 i) (b i) (μ := 2 * u j) (by linarith [hk i hi])).2.2.mul_const (w i * a i)
        rwa [zero_mul] at this
    have := ((hE1 i).mul_const (A i)).add (hmid.add (((hE2 i).mul_const (p i)).mul_const (a i)))
    rw [zero_add] at this
    refine this.congr fun t => ?_
    ring
  have h0' : Tendsto (fun t => ∑ i, Real.exp (2 * u j * t)
      * ((Real.tanh (t * u i + b i) - Real.sign (u i)) * A i
        + (1 - Real.tanh (t * u i + b i) ^ 2) * (t * w i + p i) * a i)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun t => by rw [← Finset.mul_sum, hG t, mul_zero]
  have h := tendsto_nhds_unique hlim h0'
  rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)] at h
  simp only [ite_true] at h
  have h3 : Real.exp (-2 * b j) * (A j - 2 * p j * a j) = 0 := by
    linear_combination (-1 / 2 : ℝ) * h
  exact ⟨hwa, sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left (Real.exp_pos _).ne')⟩


/-- **Lemma C.3 for `tanh`.** Rows are indexed by `n` (the coordinates of an input `x`), hidden
units by `q`, and the coordinates of the output by `k`. -/
theorem tanh_units_flat_eq_zero {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψa : q → k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j)
    (h : ∀ x : n → ℝ,
      x ᵥ* ψM + ψγ + ∑ i, (Real.tanh (x ⬝ᵥ c i + β i) • ψa i
        + ((1 - Real.tanh (x ⬝ᵥ c i + β i) ^ 2) * (x ⬝ᵥ ψc i + ψβ i)) • a i) = 0) :
    ψM = 0 ∧ ψγ = 0 ∧ ψc = 0 ∧ ψβ = 0 ∧ ψa = 0 := by
  sorry

end Skips
