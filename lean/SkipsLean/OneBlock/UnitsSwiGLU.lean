import Mathlib

/-!
# A flat direction of SwiGLU hidden units only rescales their values

Paper (dimension paper): Lemma C.3, the case of SwiGLU, with a linear term `x M`, a constant `γ`
and biases, as the paper states it.

A gated hidden unit computes `σ(z_i) w_i a_i` with the gate `z_i = x c_i + β_i` and the value
`w_i = x e_i + β'_i`; for SwiGLU `σ` is SiLU, `σ(z) = z / (1 + e^{-z})`. The function is
`G(φ, x) = x M + γ + ∑_i σ(z_i) w_i a_i`. A direction `ψ` of its weights is flat if the derivative
of `G` along it vanishes at every input `x`:

  `x ψ_M + ψ_γ + ∑_i [ σ(z_i) w_i ψ_{a_i} + σ'(z_i) (x ψ_{c_i} + ψ_{β_i}) w_i a_i
                        + σ(z_i) (x ψ_{e_i} + ψ_{β'_i}) a_i ] = 0`.

The lemma says that then `ψ_M = 0`, `ψ_γ = 0`, `ψ_{c_i} = 0`, `ψ_{β_i} = 0`, and for every unit
there is a number `α_i` with `(ψ_{e_i}, ψ_{β'_i}) = -α_i (e_i, β'_i)` and `ψ_{a_i} = α_i a_i`: the
direction of the rescaling `(e_i, a_i) ↦ (e_i/λ, λ a_i)` of the value of the unit.
-/

namespace Skips

open Matrix

/-- SiLU, the gate of a SwiGLU block: `σ(z) = z / (1 + e^{-z})`. -/
noncomputable def silu (z : ℝ) : ℝ := z / (1 + Real.exp (-z))

/-- The derivative of SiLU: `σ'(z) = (1 + e^{-z} + z e^{-z}) / (1 + e^{-z})²`. -/
noncomputable def siluDeriv (z : ℝ) : ℝ :=
  (1 + Real.exp (-z) + z * Real.exp (-z)) / (1 + Real.exp (-z)) ^ 2

theorem hasDerivAt_silu (z : ℝ) : HasDerivAt silu (siluDeriv z) z := by
  -- quotient rule for `z / (1 + e^{-z})`, with `(1 + e^{-z})' = -e^{-z}`
  have hd : HasDerivAt (fun y => 1 + Real.exp (-y)) (-Real.exp (-z)) z := by
    have := ((hasDerivAt_id z).neg.exp).const_add 1
    simpa using this
  have hpos : (1 + Real.exp (-z)) ≠ 0 := by positivity
  have h := (hasDerivAt_id z).div hd hpos
  convert h using 1
  · rfl
  · simp only [siluDeriv, id]
    ring

open Filter Topology

/-- `σ(-z) = σ(z) - z`. -/
private lemma silu_neg (z : ℝ) : silu (-z) = silu z - z := by
  have hx := Real.exp_pos z
  simp only [silu, neg_neg, Real.exp_neg]
  field_simp
  ring

/-- `σ'(-z) = 1 - σ'(z)`. -/
private lemma siluDeriv_neg (z : ℝ) : siluDeriv (-z) = 1 - siluDeriv z := by
  have hx := Real.exp_pos z
  simp only [siluDeriv, neg_neg, Real.exp_neg]
  field_simp
  ring

/-- `σ(z) - z = -z e^{-z} / (1 + e^{-z})`. -/
private lemma silu_sub_self (z : ℝ) :
    silu z - z = -z * Real.exp (-z) / (1 + Real.exp (-z)) := by
  have hy := Real.exp_pos (-z)
  simp only [silu]
  field_simp
  ring

/-- `σ'(z) - 1 = e^{-z} (z - 1 - e^{-z}) / (1 + e^{-z})²`. -/
private lemma siluDeriv_sub_one (z : ℝ) :
    siluDeriv z - 1 = Real.exp (-z) * (z - 1 - Real.exp (-z)) / (1 + Real.exp (-z)) ^ 2 := by
  have hy := Real.exp_pos (-z)
  simp only [siluDeriv]
  field_simp
  ring


/-- `t^k e^{μ t} → 0` for `μ < 0`. -/
private lemma tendsto_pow_mul_exp_of_neg (k : ℕ) {μ : ℝ} (hμ : μ < 0) :
    Tendsto (fun t : ℝ => t ^ k * Real.exp (μ * t)) atTop (𝓝 0) := by
  have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) (-μ) (by linarith)
  simpa [Real.rpow_natCast] using this

/-- `t^k (α t + β) e^{μ t} → 0` for `μ < 0`. -/
private lemma tendsto_pow_mul_lin_mul_exp_of_neg (k : ℕ) (α β : ℝ) {μ : ℝ} (hμ : μ < 0) :
    Tendsto (fun t : ℝ => t ^ k * (α * t + β) * Real.exp (μ * t)) atTop (𝓝 0) := by
  have := ((tendsto_pow_mul_exp_of_neg (k + 1) hμ).const_mul α).add
    ((tendsto_pow_mul_exp_of_neg k hμ).const_mul β)
  rw [mul_zero, mul_zero, add_zero] at this
  refine this.congr fun t => ?_
  ring

/-- **A cubic that tends to `0` at infinity is zero**: its four coefficients vanish. -/
private lemma cubic_eq_zero {c3 c2 c1 c0 : ℝ}
    (h : Tendsto (fun t => c3 * t ^ 3 + c2 * t ^ 2 + c1 * t + c0) atTop (𝓝 0)) :
    c3 = 0 ∧ c2 = 0 ∧ c1 = 0 ∧ c0 = 0 := by
  have hi : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  -- divide by `t³`: the limit is `c3`
  have h3 : c3 = 0 := by
    have h1 := h.mul (hi.pow 3)
    have h2 := (((hi.const_mul c2).add ((hi.pow 2).const_mul c1)).add
      ((hi.pow 3).const_mul c0)).const_add c3
    norm_num at h1 h2
    refine tendsto_nhds_unique (h2.congr' ?_) h1
    filter_upwards [eventually_gt_atTop 0] with t ht
    field_simp
    ring
  subst h3
  -- divide by `t²`: the limit is `c2`
  have h2' : c2 = 0 := by
    have h1 := h.mul (hi.pow 2)
    have h2 := ((hi.const_mul c1).add ((hi.pow 2).const_mul c0)).const_add c2
    norm_num at h1 h2
    refine tendsto_nhds_unique (h2.congr' ?_) h1
    filter_upwards [eventually_gt_atTop 0] with t ht
    field_simp
    ring
  subst h2'
  -- divide by `t`: the limit is `c1`
  have h1' : c1 = 0 := by
    have h1 := h.mul hi
    have h2 := (hi.const_mul c0).const_add c1
    norm_num at h1 h2
    refine tendsto_nhds_unique (h2.congr' ?_) h1
    filter_upwards [eventually_gt_atTop 0] with t ht
    field_simp
  subst h1'
  refine ⟨rfl, rfl, rfl, ?_⟩
  have h0 : Tendsto (fun _ : ℝ => c0) atTop (𝓝 0) := h.congr fun t => by ring
  exact tendsto_nhds_unique tendsto_const_nhds h0

/-- Exact rates for `u > 0`, with `z = t u + b`: `t^k (e^{ut} (σ(z) - z) + e^{-b} z) → 0` and
`t^k (e^{ut} (σ'(z) - 1) - e^{-b} (z - 1)) → 0`. -/
private lemma silu_exact_pos {u : ℝ} (hu : 0 < u) (b : ℝ) (k : ℕ) :
    Tendsto (fun t => t ^ k * (Real.exp (u * t) * (silu (t * u + b) - (t * u + b))
        + Real.exp (-b) * (t * u + b))) atTop (𝓝 0) ∧
      Tendsto (fun t => t ^ k * (Real.exp (u * t) * (siluDeriv (t * u + b) - 1)
        - Real.exp (-b) * (t * u + b - 1))) atTop (𝓝 0) := by
  -- `E t = e^{-(t u + b)}`, with `e^{ut} = e^{-b} / E t`, and `t^m E t → 0`
  have hW : ∀ t, Real.exp (u * t) = Real.exp (-b) / Real.exp (-(t * u + b)) := fun t => by
    rw [← Real.exp_sub]; ring_nf
  have hpE : ∀ m : ℕ, Tendsto (fun t => t ^ m * Real.exp (-(t * u + b))) atTop (𝓝 0) :=
    fun m => by
      have := (tendsto_pow_mul_exp_of_neg m (μ := -u) (by linarith)).const_mul (Real.exp (-b))
      rw [mul_zero] at this
      refine this.congr fun t => ?_
      rw [show -(t * u + b) = -b + -u * t by ring, Real.exp_add]; ring
  have hzE : ∀ m : ℕ, Tendsto (fun t => t ^ m * (t * u + b) * Real.exp (-(t * u + b))) atTop
      (𝓝 0) := fun m => by
    have := ((hpE (m + 1)).const_mul u).add ((hpE m).const_mul b)
    rw [mul_zero, mul_zero, add_zero] at this
    refine this.congr fun t => ?_
    ring
  have h0 : Tendsto (fun t => Real.exp (-(t * u + b))) atTop (𝓝 0) := by simpa using hpE 0
  have h1E : Tendsto (fun t => 1 + Real.exp (-(t * u + b))) atTop (𝓝 1) := by
    simpa using h0.const_add 1
  constructor
  · -- `t^k (e^{ut} (σ(z) - z) + e^{-b} z) = e^{-b} (t^k z E) / (1 + E)`
    have := ((hzE k).const_mul (Real.exp (-b))).div h1E one_ne_zero
    rw [mul_zero, zero_div] at this
    refine this.congr fun t => ?_
    have hE := Real.exp_pos (-(t * u + b))
    rw [Pi.div_apply, silu_sub_self, hW t]
    field_simp
    ring
  · -- `t^k (e^{ut} (σ'(z) - 1) - e^{-b} (z - 1)) = -e^{-b} (t^k E + (2 + E)(t^k z E - t^k E)) / (1 + E)²`
    have := (((hpE k).add ((h0.const_add 2).mul ((hzE k).sub (hpE k)))).const_mul
      (-Real.exp (-b))).div (h1E.pow 2) (by norm_num)
    simp only [sub_self, mul_zero, add_zero, zero_div] at this
    refine this.congr fun t => ?_
    have hE := Real.exp_pos (-(t * u + b))
    rw [Pi.div_apply, siluDeriv_sub_one, hW t]
    field_simp
    ring


/-- The rest of SiLU after its polynomial part along a ray of slope `u`: `σ(z) - [u > 0] z`. -/
private noncomputable def restS (u z : ℝ) : ℝ := silu z - if 0 < u then z else 0

/-- The rest of `σ'` after its polynomial part along a ray of slope `u`: `σ'(z) - [u > 0]`. -/
private noncomputable def restD (u z : ℝ) : ℝ := siluDeriv z - if 0 < u then 1 else 0

/-- Exact rates for `u ≠ 0` with sign `s`, `z = t u + b`: `t^k (e^{|u|t} restS + s e^{-sb} z) → 0`
and `t^k (e^{|u|t} restD - s e^{-sb} (s z - 1)) → 0`. The case `u < 0` reduces to `u > 0` by
`σ(-z) = σ(z) - z` and `σ'(-z) = 1 - σ'(z)`. -/
private lemma silu_exact {u s : ℝ} (hs : (s = 1 ∧ 0 < u) ∨ (s = -1 ∧ u < 0)) (b : ℝ) (k : ℕ) :
    Tendsto (fun t => t ^ k * (Real.exp (|u| * t) * restS u (t * u + b)
        + s * Real.exp (-(s * b)) * (t * u + b))) atTop (𝓝 0) ∧
      Tendsto (fun t => t ^ k * (Real.exp (|u| * t) * restD u (t * u + b)
        - s * Real.exp (-(s * b)) * (s * (t * u + b) - 1))) atTop (𝓝 0) := by
  rcases hs with ⟨rfl, hu⟩ | ⟨rfl, hu⟩
  · obtain ⟨h1, h2⟩ := silu_exact_pos hu b k
    simp only [restS, restD, ite_eq_left hu, abs_of_pos hu, one_mul]
    exact ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := silu_exact_pos (neg_pos.2 hu) (-b) k
    have e1 : ∀ t, silu (t * u + b) = silu (t * -u + -b) - (t * -u + -b) := fun t => by
      rw [← silu_neg]; congr 1; ring
    have e2 : ∀ t, siluDeriv (t * u + b) = 1 - siluDeriv (t * -u + -b) := fun t => by
      rw [← siluDeriv_neg]; congr 1; ring
    simp only [restS, restD, ite_eq_right (not_lt.2 hu.le), abs_of_neg hu, sub_zero]
    constructor
    · refine h1.congr fun t => ?_
      rw [e1]; ring_nf
    · have := h2.neg
      rw [neg_zero] at this
      refine this.congr fun t => ?_
      rw [e2]; ring_nf

/-- Decay for `u ≠ 0` and `μ < |u|`: `t^k e^{μ t} restS u (t u + b) → 0`, and the same for
`restD`. -/
private lemma silu_decay {u : ℝ} (hu : u ≠ 0) (b : ℝ) {μ : ℝ} (hμ : μ < |u|) (k : ℕ) :
    Tendsto (fun t => t ^ k * Real.exp (μ * t) * restS u (t * u + b)) atTop (𝓝 0) ∧
      Tendsto (fun t => t ^ k * Real.exp (μ * t) * restD u (t * u + b)) atTop (𝓝 0) := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, (s = 1 ∧ 0 < u) ∨ (s = -1 ∧ u < 0) := by
    rcases hu.lt_or_gt with h | h
    · exact ⟨-1, Or.inr ⟨rfl, h⟩⟩
    · exact ⟨1, Or.inl ⟨rfl, h⟩⟩
  obtain ⟨h1, h2⟩ := silu_exact hs b k
  have hc : μ - |u| < 0 := by linarith
  have hD : Tendsto (fun t => Real.exp ((μ - |u|) * t)) atTop (𝓝 0) := by
    simpa using tendsto_pow_mul_exp_of_neg 0 hc
  have hL1 := tendsto_pow_mul_lin_mul_exp_of_neg k u b hc
  have hL2 := tendsto_pow_mul_lin_mul_exp_of_neg k (s * u) (s * b - 1) hc
  -- `e^{μ t} = e^{(μ - |u|) t} e^{|u| t}`
  have hsplit : ∀ t, Real.exp (μ * t) = Real.exp ((μ - |u|) * t) * Real.exp (|u| * t) :=
    fun t => by rw [← Real.exp_add]; ring_nf
  constructor
  · have := (hD.mul h1).sub (hL1.const_mul (s * Real.exp (-(s * b))))
    rw [mul_zero, mul_zero, sub_zero] at this
    refine this.congr fun t => ?_
    rw [hsplit t]; ring
  · have := (hD.mul h2).add (hL2.const_mul (s * Real.exp (-(s * b))))
    rw [mul_zero, mul_zero, add_zero] at this
    refine this.congr fun t => ?_
    rw [hsplit t]; ring

/-- The rest of one unit, `restS (t F₁ + F₀) + restD (t² G₂ + t G₁ + G₀)`, weighted by `e^{μ t}`
with `μ < |u|`, tends to `0`. -/
private lemma rest_decay {u : ℝ} (hu : u ≠ 0) (b F1 F0 G2 G1 G0 : ℝ) {μ : ℝ} (hμ : μ < |u|) :
    Tendsto (fun t => Real.exp (μ * t) * (restS u (t * u + b) * (t * F1 + F0)
      + restD u (t * u + b) * (t ^ 2 * G2 + t * G1 + G0))) atTop (𝓝 0) := by
  have hS := fun k => (silu_decay hu b hμ k).1
  have hD := fun k => (silu_decay hu b hμ k).2
  have := (((hS 1).mul_const F1).add ((hS 0).mul_const F0)).add
    ((((hD 2).mul_const G2).add ((hD 1).mul_const G1)).add ((hD 0).mul_const G0))
  simp only [zero_mul, add_zero] at this
  refine this.congr fun t => ?_
  ring

/-- The rest of one unit weighted by `e^{|u| t}` is `s e^{-sb}` times the cubic
`-z f + (s z - 1) g` (`z = t u + b`, `f = t F₁ + F₀`, `g = t² G₂ + t G₁ + G₀`), up to `o(1)`. -/
private lemma rest_exact {u s : ℝ} (hs : (s = 1 ∧ 0 < u) ∨ (s = -1 ∧ u < 0))
    (b F1 F0 G2 G1 G0 : ℝ) :
    Tendsto (fun t => Real.exp (|u| * t) * (restS u (t * u + b) * (t * F1 + F0)
      + restD u (t * u + b) * (t ^ 2 * G2 + t * G1 + G0))
      - s * Real.exp (-(s * b)) * (-(t * u + b) * (t * F1 + F0)
        + (s * (t * u + b) - 1) * (t ^ 2 * G2 + t * G1 + G0))) atTop (𝓝 0) := by
  have hS := fun k => (silu_exact hs b k).1
  have hD := fun k => (silu_exact hs b k).2
  have := (((hS 1).mul_const F1).add ((hS 0).mul_const F0)).add
    ((((hD 2).mul_const G2).add ((hD 1).mul_const G1)).add ((hD 0).mul_const G0))
  simp only [zero_mul, add_zero] at this
  refine this.congr fun t => ?_
  ring

/-- **The ray argument**, in one output coordinate. Along a ray the identity reads
`t V + C + ∑ᵢ [σ(t uᵢ + bᵢ) (t F₁ᵢ + F₀ᵢ) + σ'(t uᵢ + bᵢ) (t² G₂ᵢ + t G₁ᵢ + G₀ᵢ)] = 0`. If
`|u_j| < |u_i|` for all `i ≠ j` and `s` is the sign of `u_j`, the four coefficients of the cubic
`-z_j f_j + (s z_j - 1) g_j` vanish. -/
private lemma ray_coeffs {q : Type*} [Fintype q] [DecidableEq q]
    (u b F1 F0 G2 G1 G0 : q → ℝ) (V C s : ℝ) (j : q)
    (hs : (s = 1 ∧ 0 < u j) ∨ (s = -1 ∧ u j < 0))
    (hk : ∀ i, i ≠ j → |u j| < |u i|)
    (hJ : ∀ t : ℝ, t * V + C + ∑ i, (silu (t * u i + b i) * (t * F1 i + F0 i)
      + siluDeriv (t * u i + b i) * (t ^ 2 * G2 i + t * G1 i + G0 i)) = 0) :
    s * u j * G2 j = 0 ∧
      -(u j * F1 j) + s * u j * G1 j + (s * b j - 1) * G2 j = 0 ∧
      -(u j * F0 j) - b j * F1 j + s * u j * G0 j + (s * b j - 1) * G1 j = 0 ∧
      -(b j * F0 j) + (s * b j - 1) * G0 j = 0 := by
  have huj : u j ≠ 0 := by
    rcases hs with ⟨-, h⟩ | ⟨-, h⟩
    · exact h.ne'
    · exact h.ne
  have hs0 : s ≠ 0 := by
    rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  have hu0 : ∀ i, u i ≠ 0 := fun i => by
    by_cases hi : i = j
    · subst hi; exact huj
    · exact abs_pos.1 ((abs_pos.2 huj).trans (hk i hi))
  -- the rest of unit `i` along the ray
  let R : q → ℝ → ℝ := fun i t => restS (u i) (t * u i + b i) * (t * F1 i + F0 i)
      + restD (u i) (t * u i + b i) * (t ^ 2 * G2 i + t * G1 i + G0 i)
  -- the coefficients of the polynomial part (units with `u_i > 0` contribute `z_i f_i + g_i`)
  set K2 : ℝ := ∑ i, (if 0 < u i then u i * F1 i + G2 i else 0) with hK2
  set K1 : ℝ := V + ∑ i, (if 0 < u i then u i * F0 i + b i * F1 i + G1 i else 0) with hK1
  set K0 : ℝ := C + ∑ i, (if 0 < u i then b i * F0 i + G0 i else 0) with hK0
  have hsplit : ∀ t, K2 * t ^ 2 + K1 * t + K0 + ∑ i, R i t = 0 := fun t => by
    rw [← hJ t]
    have e : ∀ i, silu (t * u i + b i) * (t * F1 i + F0 i)
        + siluDeriv (t * u i + b i) * (t ^ 2 * G2 i + t * G1 i + G0 i)
        = (if 0 < u i then u i * F1 i + G2 i else 0) * t ^ 2
          + (if 0 < u i then u i * F0 i + b i * F1 i + G1 i else 0) * t
          + (if 0 < u i then b i * F0 i + G0 i else 0) + R i t := fun i => by
      simp only [R, restS, restD]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun i _ => e i]
    simp only [hK2, hK1, hK0, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  -- (i) the rests tend to `0`, so the polynomial part vanishes identically
  have hR0 : Tendsto (fun t => ∑ i, R i t) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset q) fun i _ =>
      rest_decay (hu0 i) (b i) (F1 i) (F0 i) (G2 i) (G1 i) (G0 i) (μ := 0) (abs_pos.2 (hu0 i))
    simp only [Finset.sum_const_zero, zero_mul, Real.exp_zero, one_mul] at this
    exact this
  have hK : K2 = 0 ∧ K1 = 0 ∧ K0 = 0 := by
    have h : Tendsto (fun t => 0 * t ^ 3 + K2 * t ^ 2 + K1 * t + K0) atTop (𝓝 0) := by
      have := hR0.neg
      rw [neg_zero] at this
      refine this.congr fun t => ?_
      linear_combination -hsplit t
    obtain ⟨-, h2, h1, h0⟩ := cubic_eq_zero h
    exact ⟨h2, h1, h0⟩
  have hRz : ∀ t, ∑ i, R i t = 0 := fun t => by
    linear_combination hsplit t - t ^ 2 * hK.1 - t * hK.2.1 - hK.2.2
  -- (ii) weight `e^{|u_j| t}`: the rests of the other units decay, that of unit `j` is a cubic
  let Pj : ℝ → ℝ := fun t => -(t * u j + b j) * (t * F1 j + F0 j)
    + (s * (t * u j + b j) - 1) * (t ^ 2 * G2 j + t * G1 j + G0 j)
  have hlim : Tendsto (fun t => ∑ i, (Real.exp (|u j| * t) * R i t
      - if i = j then s * Real.exp (-(s * b j)) * Pj t else 0)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset q) fun i (_ : i ∈ Finset.univ) =>
      (show Tendsto (fun t => Real.exp (|u j| * t) * R i t
          - if i = j then s * Real.exp (-(s * b j)) * Pj t else 0) atTop (𝓝 0) from by
        by_cases hi : i = j
        · subst hi
          simp only
          exact rest_exact hs (b i) (F1 i) (F0 i) (G2 i) (G1 i) (G0 i)
        · simp only [ite_eq_right hi, sub_zero]
          exact rest_decay (hu0 i) (b i) (F1 i) (F0 i) (G2 i) (G1 i) (G0 i) (hk i hi))
    simpa only [Finset.sum_const_zero] using this
  have hP : Tendsto (fun t => -(s * Real.exp (-(s * b j))) * Pj t) atTop (𝓝 0) :=
    hlim.congr fun t => by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hRz t, mul_zero, Finset.sum_ite_eq',
        ite_eq_left (Finset.mem_univ j)]
      ring
  have hK0' : -(s * Real.exp (-(s * b j))) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero hs0 (Real.exp_pos _).ne')
  have hP' := hP.const_mul (-(s * Real.exp (-(s * b j))))⁻¹
  rw [mul_zero] at hP'
  exact cubic_eq_zero (hP'.congr fun t => by
    rw [← mul_assoc, inv_mul_cancel₀ hK0', one_mul]
    simp only [Pj]
    ring)

/-- Strict inequalities `u_j < |u_i|` (`i ≠ j`) persist under a small perturbation `u + ε d`. -/
private lemma eventually_lt_abs {q : Type*} [Finite q] (u d : q → ℝ) (j : q)
    (h : ∀ i, i ≠ j → u j < |u i|) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i, i ≠ j → u j + ε * d j < |u i + ε * d i| := by
  refine Filter.eventually_all.2 fun i => ?_
  by_cases hi : i = j
  · exact Filter.Eventually.of_forall fun _ h' => absurd hi h'
  · have : ∀ᶠ ε in 𝓝 (0 : ℝ), u j + ε * d j < |u i + ε * d i| :=
      ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using h i hi)
    exact this.mono fun _ h' _ => h'

/-- The good directions for unit `j` (`0 < ν c_j < |ν c_i|` for `i ≠ j`) form an open set: from a
good `ν`, the direction `ν + ε e` is good for all small `ε`. -/
private lemma eventually_good {n q : Type*} [Fintype n] [Finite q] (c : q → n → ℝ) (j : q)
    (ν e : n → ℝ) (hν : 0 < ν ⬝ᵥ c j ∧ ∀ i, i ≠ j → ν ⬝ᵥ c j < |ν ⬝ᵥ c i|) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < (ν + ε • e) ⬝ᵥ c j ∧
      ∀ i, i ≠ j → (ν + ε • e) ⬝ᵥ c j < |(ν + ε • e) ⬝ᵥ c i| := by
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < ν ⬝ᵥ c j + ε * (e ⬝ᵥ c j) :=
    ContinuousAt.eventually_lt (f := fun _ => (0 : ℝ)) (by fun_prop) (by fun_prop)
      (by simpa using hν.1)
  have h2 := eventually_lt_abs (fun i => ν ⬝ᵥ c i) (fun i => e ⬝ᵥ c i) j hν.2
  filter_upwards [h1, h2] with ε h1 h2
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
  exact ⟨h1, h2⟩

/-- **A good direction exists** for every unit `j`: a `ν` with `0 < ν c_j < |ν c_i|` for all
`i ≠ j`. First a `ν₀` with `ν₀ c_j = 0` and `ν₀ c_i ≠ 0` for `i ≠ j` (a real vector space is not
a finite union of proper subspaces), then `ν = ν₀ + δ c_j` for a small `δ > 0`. -/
private lemma exists_good {n q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ)
    (hc : ∀ i, c i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) (j : q) :
    ∃ ν : n → ℝ, 0 < ν ⬝ᵥ c j ∧ ∀ i, i ≠ j → ν ⬝ᵥ c j < |ν ⬝ᵥ c i| := by
  have hjj : 0 < c j ⬝ᵥ c j :=
    lt_of_le_of_ne (Finset.sum_nonneg fun m _ => mul_self_nonneg (c j m))
      (Ne.symm (dotProduct_self_eq_zero.not.2 (hc j)))
  -- `r i`: the component of `c i` orthogonal to `c j`; it is nonzero for `i ≠ j`
  set r : q → n → ℝ := fun i => c i - ((c j ⬝ᵥ c i) / (c j ⬝ᵥ c j)) • c j with hr_def
  have hr : ∀ i, i ≠ j → r i ≠ 0 := fun i hi h0 =>
    hcol i j hi _ (sub_eq_zero.1 h0)
  -- the kernels of `ν ↦ ν r_i` are proper subspaces, so some `ν` avoids all of them
  let K : {i // i ≠ j} → Submodule ℝ (n → ℝ) := fun i =>
    { carrier := {ν | ν ⬝ᵥ r i = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢; rw [add_dotProduct, hx, hy, add_zero]
      zero_mem' := by simp
      smul_mem' := fun s x hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢; rw [smul_dotProduct, hx, smul_zero] }
  obtain ⟨ν, hν⟩ : ∃ ν : n → ℝ, ∀ i, i ≠ j → ν ⬝ᵥ r i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ (p := K) (by
      ext ν
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      obtain ⟨i, hij, h0⟩ := hcon ν
      exact ⟨⟨i, hij⟩, h0⟩)
    have hmem : r i ∈ K i := hi ▸ Submodule.mem_top
    exact hr i.1 i.2 (dotProduct_self_eq_zero.1 hmem)
  -- `ν₀ = ν - (ν c_j / c_j c_j) c_j` lies on the hyperplane `ν₀ c_j = 0`, and `ν₀ c_i = ν r_i`
  set ν₀ := ν - ((ν ⬝ᵥ c j) / (c j ⬝ᵥ c j)) • c j with hν₀
  have h0j : ν₀ ⬝ᵥ c j = 0 := by
    rw [hν₀, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    field_simp
    ring
  have h0i : ∀ i, i ≠ j → 0 < |ν₀ ⬝ᵥ c i| := fun i hi => by
    refine abs_pos.2 ?_
    have : ν₀ ⬝ᵥ c i = ν ⬝ᵥ r i := by
      rw [hν₀, hr_def]
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    rw [this]; exact hν i hi
  -- move a little to the side of `c_j`
  have hev := eventually_lt_abs (fun i => ν₀ ⬝ᵥ c i) (fun i => c j ⬝ᵥ c i) j
    (fun i hi => by simpa only [h0j] using h0i i hi)
  obtain ⟨δ, hδ, hδ0⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin (s := Set.Ioi 0))).exists
  refine ⟨ν₀ + δ • c j, ?_, fun i hi => ?_⟩
  · rw [add_dotProduct, smul_dotProduct, smul_eq_mul, h0j, zero_add]
    exact mul_pos hδ0 hjj
  · simpa only [add_dotProduct, smul_dotProduct, smul_eq_mul] using hδ i hi

/-- A good direction `ν` for unit `j` (`0 < ν c_j < |ν c_i|` for `i ≠ j`) with `ν e ≠ 0` exists
when `e ≠ 0`: move a good direction a little along `e` if needed. -/
private lemma exists_good_ne {n q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ) (e : n → ℝ)
    (hc : ∀ i, c i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) (he : e ≠ 0) (j : q) :
    ∃ ν : n → ℝ, (0 < ν ⬝ᵥ c j ∧ ∀ i, i ≠ j → ν ⬝ᵥ c j < |ν ⬝ᵥ c i|) ∧ ν ⬝ᵥ e ≠ 0 := by
  obtain ⟨ν, hν⟩ := exists_good c hc hcol j
  by_cases hνe : ν ⬝ᵥ e = 0
  · obtain ⟨ε, hε, hε0⟩ := (((eventually_good c j ν e hν).filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_nhdsWithin (s := Set.Ioi 0))).exists
    refine ⟨ν + ε • e, hε, ?_⟩
    rw [add_dotProduct, smul_dotProduct, hνe, zero_add, smul_eq_mul]
    exact mul_ne_zero (ne_of_gt hε0) (dotProduct_self_eq_zero.not.2 he)
  · exact ⟨ν, hν, hνe⟩

/-- **A vector orthogonal to all good directions vanishes.** If `ν r = 0` for every `ν` with
`0 < ν c_j < |ν c_i|` (`i ≠ j`) and `ν e ≠ 0`, then `r = 0`: such directions form a nonempty open
set, and `ν + ε r` is one of them for a small `ε > 0`. -/
private lemma eq_zero_of_good {n q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ) (e : n → ℝ)
    (hc : ∀ i, c i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) (he : e ≠ 0) (j : q)
    (r : n → ℝ)
    (hr : ∀ ν : n → ℝ, (0 < ν ⬝ᵥ c j ∧ ∀ i, i ≠ j → ν ⬝ᵥ c j < |ν ⬝ᵥ c i|) → ν ⬝ᵥ e ≠ 0 →
      ν ⬝ᵥ r = 0) :
    r = 0 := by
  obtain ⟨ν, hν, hνe⟩ := exists_good_ne c e hc hcol he j
  have hne : ∀ᶠ ε in 𝓝 (0 : ℝ), (ν + ε • r) ⬝ᵥ e ≠ 0 := by
    have : ∀ᶠ ε in 𝓝 (0 : ℝ), ν ⬝ᵥ e + ε * (r ⬝ᵥ e) ≠ 0 :=
      ContinuousAt.eventually_ne (by fun_prop) (by simpa using hνe)
    refine this.mono fun ε hε => ?_
    rwa [add_dotProduct, smul_dotProduct, smul_eq_mul]
  obtain ⟨ε, ⟨hε, hεe⟩, hε0⟩ := ((((eventually_good c j ν r hν).and hne).filter_mono
    nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin (s := Set.Ioi 0))).exists
  have e2 := hr _ hε hεe
  rw [add_dotProduct, smul_dotProduct, hr ν hν hνe, zero_add, smul_eq_mul] at e2
  exact dotProduct_self_eq_zero.1 ((mul_eq_zero.1 e2).resolve_left (ne_of_gt hε0))

/-- **The identity along a ray** `x = t ν`, in the output coordinate `o`, in the form of
`ray_coeffs`: unit `i` contributes `σ(z_i) (t F₁ + F₀) + σ'(z_i) (t² G₂ + t G₁ + G₀)`. -/
private lemma ray_identity {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (e : q → n → ℝ) (β' : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψe : q → n → ℝ)
    (ψβ' : q → ℝ) (ψa : q → k → ℝ)
    (h : ∀ x : n → ℝ,
      x ᵥ* ψM + ψγ + ∑ i,
        ((silu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i)) • ψa i
          + (siluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i)) • a i
          + (silu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i)) • a i) = 0)
    (ν : n → ℝ) (o : k) (t : ℝ) :
    t * (ν ᵥ* ψM) o + ψγ o + ∑ i, (silu (t * (ν ⬝ᵥ c i) + β i)
        * (t * ((ν ⬝ᵥ e i) * ψa i o + (ν ⬝ᵥ ψe i) * a i o) + (β' i * ψa i o + ψβ' i * a i o))
      + siluDeriv (t * (ν ⬝ᵥ c i) + β i)
        * (t ^ 2 * ((ν ⬝ᵥ ψc i) * (ν ⬝ᵥ e i) * a i o)
          + t * (((ν ⬝ᵥ ψc i) * β' i + ψβ i * (ν ⬝ᵥ e i)) * a i o)
          + ψβ i * β' i * a i o)) = 0 := by
  have := congrFun (h (t • ν)) o
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, smul_vecMul,
    smul_dotProduct, Pi.zero_apply] at this
  rw [← this]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The coefficients of one unit.** Along a good direction `ν` for unit `j`, the ray lemma at
`x = t ν` (sign `+`) and at `x = -t ν` (sign `-`) gives, in every output coordinate `o`:
`t³`: `(ν ψ_{c_j}) (ν e_j) a_j = 0`; `t²` (both signs): `(ν e_j) ψ_{a_j} + (ν ψ_{e_j}) a_j = 0` and
`((ν ψ_{c_j}) β'_j + ψ_{β_j} (ν e_j)) a_j = 0`; `t`: `β'_j ψ_{a_j} + ψ_{β'_j} a_j = ψ_{β_j} β'_j a_j`. -/
private lemma unit_coeffs {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (e : q → n → ℝ) (β' : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψe : q → n → ℝ)
    (ψβ' : q → ℝ) (ψa : q → k → ℝ)
    (h : ∀ x : n → ℝ,
      x ᵥ* ψM + ψγ + ∑ i,
        ((silu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i)) • ψa i
          + (siluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i)) • a i
          + (silu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i)) • a i) = 0)
    (j : q) (ν : n → ℝ) (hν : 0 < ν ⬝ᵥ c j ∧ ∀ i, i ≠ j → ν ⬝ᵥ c j < |ν ⬝ᵥ c i|) (o : k) :
    (ν ⬝ᵥ ψc j) * (ν ⬝ᵥ e j) * a j o = 0 ∧
      (ν ⬝ᵥ e j) * ψa j o + (ν ⬝ᵥ ψe j) * a j o = 0 ∧
      ((ν ⬝ᵥ ψc j) * β' j + ψβ j * (ν ⬝ᵥ e j)) * a j o = 0 ∧
      β' j * ψa j o + ψβ' j * a j o = ψβ j * β' j * a j o := by
  classical
  have hu := hν.1
  have hk : ∀ i, i ≠ j → |ν ⬝ᵥ c j| < |ν ⬝ᵥ c i| := fun i hi => by
    rw [abs_of_pos hu]; exact hν.2 i hi
  -- the ray `x = t ν`: sign `+`
  obtain ⟨p3, p2, p1, -⟩ := ray_coeffs (fun i => ν ⬝ᵥ c i) β
    (fun i => (ν ⬝ᵥ e i) * ψa i o + (ν ⬝ᵥ ψe i) * a i o) (fun i => β' i * ψa i o + ψβ' i * a i o)
    (fun i => (ν ⬝ᵥ ψc i) * (ν ⬝ᵥ e i) * a i o)
    (fun i => ((ν ⬝ᵥ ψc i) * β' i + ψβ i * (ν ⬝ᵥ e i)) * a i o) (fun i => ψβ i * β' i * a i o)
    ((ν ᵥ* ψM) o) (ψγ o) 1 j (Or.inl ⟨rfl, hu⟩) hk
    (ray_identity c β e β' a ψM ψγ ψc ψβ ψe ψβ' ψa h ν o)
  -- the ray `x = -t ν`: sign `-`
  obtain ⟨-, m2, -, -⟩ := ray_coeffs (fun i => (-ν) ⬝ᵥ c i) β
    (fun i => ((-ν) ⬝ᵥ e i) * ψa i o + ((-ν) ⬝ᵥ ψe i) * a i o)
    (fun i => β' i * ψa i o + ψβ' i * a i o)
    (fun i => ((-ν) ⬝ᵥ ψc i) * ((-ν) ⬝ᵥ e i) * a i o)
    (fun i => (((-ν) ⬝ᵥ ψc i) * β' i + ψβ i * ((-ν) ⬝ᵥ e i)) * a i o)
    (fun i => ψβ i * β' i * a i o)
    (((-ν) ᵥ* ψM) o) (ψγ o) (-1) j (Or.inr ⟨rfl, by rw [neg_dotProduct]; linarith⟩)
    (fun i hi => by simp only [neg_dotProduct, abs_neg]; exact hk i hi)
    (ray_identity c β e β' a ψM ψγ ψc ψβ ψe ψβ' ψa h (-ν) o)
  simp only [neg_dotProduct] at m2
  -- `t³`
  have h3 : (ν ⬝ᵥ ψc j) * (ν ⬝ᵥ e j) * a j o = 0 := by
    rw [one_mul] at p3
    exact (mul_eq_zero.1 p3).resolve_left hu.ne'
  -- `t²`, both signs: `u F₁ = 0` and `u G₁ = 0`
  have h2a : (ν ⬝ᵥ c j) * ((ν ⬝ᵥ e j) * ψa j o + (ν ⬝ᵥ ψe j) * a j o) = 0 := by
    linear_combination (-1 / 2 : ℝ) * p2 + (-1 / 2 : ℝ) * m2 - h3
  have h2b : (ν ⬝ᵥ c j) * (((ν ⬝ᵥ ψc j) * β' j + ψβ j * (ν ⬝ᵥ e j)) * a j o) = 0 := by
    linear_combination (1 / 2 : ℝ) * p2 - (1 / 2 : ℝ) * m2 - β j * h3
  have hF1 := (mul_eq_zero.1 h2a).resolve_left hu.ne'
  have hG1 := (mul_eq_zero.1 h2b).resolve_left hu.ne'
  -- `t`
  have h1 : (ν ⬝ᵥ c j) * (ψβ j * β' j * a j o - (β' j * ψa j o + ψβ' j * a j o)) = 0 := by
    linear_combination p1 + β j * hF1 - (1 * β j - 1) * hG1
  exact ⟨h3, hF1, hG1, (sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hu.ne')).symm⟩

/-- **One unit only rescales its value.** For every unit `j`: `ψ_{c_j} = 0`, `ψ_{β_j} = 0`, and
`(ψ_{e_j}, ψ_{β'_j}, ψ_{a_j}) = (-α e_j, -α β'_j, α a_j)` for a number `α`. -/
private lemma unit_rescale {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (e : q → n → ℝ) (β' : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψe : q → n → ℝ)
    (ψβ' : q → ℝ) (ψa : q → k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) (he : ∀ i, e i ≠ 0)
    (h : ∀ x : n → ℝ,
      x ᵥ* ψM + ψγ + ∑ i,
        ((silu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i)) • ψa i
          + (siluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i)) • a i
          + (silu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i)) • a i) = 0)
    (j : q) :
    ψc j = 0 ∧ ψβ j = 0 ∧
      ∃ α : ℝ, ψe j = -α • e j ∧ ψβ' j = -α * β' j ∧ ψa j = α • a j := by
  have hU := fun ν hν o => unit_coeffs c β e β' a ψM ψγ ψc ψβ ψe ψβ' ψa h j ν hν o
  obtain ⟨o₀, ho₀⟩ := Function.ne_iff.1 (ha j)
  obtain ⟨m₀, hm₀⟩ := Function.ne_iff.1 (he j)
  rw [Pi.zero_apply] at ho₀ hm₀
  obtain ⟨ν₀, hν₀, hν₀e⟩ := exists_good_ne c (e j) hc hcol (he j) j
  -- `t³`: `ν ψ_{c_j} = 0` for every good `ν` with `ν e_j ≠ 0`, so `ψ_{c_j} = 0`
  have hψc : ψc j = 0 := eq_zero_of_good c (e j) hc hcol (he j) j (ψc j) fun ν hν hνe =>
    (mul_eq_zero.1 ((mul_eq_zero.1 (hU ν hν o₀).1).resolve_right ho₀)).resolve_right hνe
  -- `t²`, the two signs: `ψ_{β_j} (ν e_j) a_j = 0`, so `ψ_{β_j} = 0`
  have hψβ : ψβ j = 0 := by
    have := (hU ν₀ hν₀ o₀).2.2.1
    rw [hψc, dotProduct_zero, zero_mul, zero_add] at this
    exact (mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_right ho₀)).resolve_right hν₀e
  -- `t²`: `a_j(o) ψ_{e_j} + ψ_{a_j}(o) e_j` is orthogonal to all good directions, so it vanishes
  have hr : ∀ o, a j o • ψe j + ψa j o • e j = 0 := fun o =>
    eq_zero_of_good c (e j) hc hcol (he j) j _ fun ν hν hνe => by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      linear_combination (hU ν hν o).2.1
  -- `α = ψ_{a_j}(o₀) / a_j(o₀)`
  refine ⟨hψc, hψβ, ψa j o₀ / a j o₀, ?_⟩
  have hψe : ψe j = -(ψa j o₀ / a j o₀) • e j := funext fun m => by
    have := congrFun (hr o₀) m
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    have h2 : ψe j m = -(ψa j o₀ * e j m) / a j o₀ := by
      rw [eq_div_iff ho₀]; linear_combination this
    simp only [Pi.smul_apply, smul_eq_mul, h2]
    ring
  have hψa : ψa j = (ψa j o₀ / a j o₀) • a j := funext fun o => by
    have := congrFun (hr o) m₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [hψe] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have h2 : e j m₀ * (ψa j o - ψa j o₀ / a j o₀ * a j o) = 0 := by linear_combination this
    simp only [Pi.smul_apply, smul_eq_mul]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hm₀)
  -- `t`: `β'_j ψ_{a_j} + ψ_{β'_j} a_j = 0`, so `ψ_{β'_j} = -α β'_j`
  have hψβ' : ψβ' j = -(ψa j o₀ / a j o₀) * β' j := by
    have := (hU ν₀ hν₀ o₀).2.2.2
    rw [hψβ] at this
    rw [show -(ψa j o₀ / a j o₀) * β' j = -(β' j * ψa j o₀) / a j o₀ by ring, eq_div_iff ho₀]
    linear_combination this
  exact ⟨hψe, hψβ', hψa⟩

/-- **Lemma C.3 for SwiGLU.** Rows are indexed by `n` (the coordinates of an input `x`), hidden
units by `q`, and the coordinates of the output by `k`. -/
theorem silu_gated_units_flat {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (e : q → n → ℝ) (β' : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψe : q → n → ℝ)
    (ψβ' : q → ℝ) (ψa : q → k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j)
    (he : ∀ i, e i ≠ 0) (hec : ∀ i, ∀ r : ℝ, (e i, β' i) ≠ r • (c i, β i))
    (h : ∀ x : n → ℝ,
      x ᵥ* ψM + ψγ + ∑ i,
        ((silu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i)) • ψa i
          + (siluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i)) • a i
          + (silu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i)) • a i) = 0) :
    ψM = 0 ∧ ψγ = 0 ∧ ψc = 0 ∧ ψβ = 0 ∧
      ∃ α : q → ℝ, ∀ i, ψe i = -(α i) • e i ∧ ψβ' i = -(α i) * β' i ∧ ψa i = α i • a i := by
  classical
  -- every unit only rescales its value
  choose hψc hψβ α hα using
    unit_rescale c β e β' a ψM ψγ ψc ψβ ψe ψβ' ψa ha hc hcol he h
  -- so every unit term vanishes, and what is left is `x ψ_M + ψ_γ = 0` for all `x`
  have hlin : ∀ x : n → ℝ, x ᵥ* ψM + ψγ = 0 := fun x => by
    have hz : ∀ i, (silu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i)) • ψa i
        + (siluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i)) • a i
        + (silu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i)) • a i = 0 := fun i => by
      rw [(hα i).1, (hα i).2.1, (hα i).2.2, hψc i, hψβ i, dotProduct_zero, dotProduct_smul,
        smul_smul, ← add_smul, ← add_smul, smul_eq_mul]
      refine (congrArg (· • a i) ?_).trans (zero_smul ℝ (a i))
      ring
    have := h x
    rwa [Finset.sum_congr rfl fun i _ => hz i, Finset.sum_const_zero, add_zero] at this
  have hγ : ψγ = 0 := by simpa using hlin 0
  refine ⟨?_, hγ, funext hψc, funext hψβ, α, hα⟩
  ext m o
  simpa [hγ] using congrFun (hlin (Pi.single m 1)) o

end Skips
