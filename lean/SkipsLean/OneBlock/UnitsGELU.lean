import SkipsLean.Activations.GeluExpansion

/-!
# A flat direction of GELU hidden units vanishes

Paper (dimension paper): Lemma C.3, the case of GELU, in the generality in which the paper states
it: with a linear term `x M`, a constant `γ` and biases `β_i`.

The function is `G(φ, x) = x M + γ + ∑_i σ(z_i) a_i` with `σ(z) = z Φ(z)` and `z_i = x c_i + β_i`,
where `c_i` is the read column of hidden unit `i` and `a_i` its write row. A direction
`ψ = (ψ_M, ψ_γ, ψ_{c_i}, ψ_{β_i}, ψ_{a_i})` of these weights is flat if the derivative of `G`
along it vanishes at every input `x`:

  `x ψ_M + ψ_γ + ∑_i [ σ(z_i) ψ_{a_i} + σ'(z_i) (x ψ_{c_i} + ψ_{β_i}) a_i ] = 0`,

with `σ'(z) = Φ(z) + z φ(z)`. The lemma says that then `ψ = 0`, when every `a_i` is nonzero and the
`c_i` are nonzero and pairwise non-collinear. The proof of the paper follows a ray `x = t n` to
infinity: there `σ(z) = max(z, 0) - φ(z) + O(φ(z)/z²)` and
`σ'(z) = 1[z > 0] + φ(z)(z - 1/z) + O(φ(z)/|z|³)`, from the bounds on the tail of `Φ`
(`Activations/Gaussian.lean`), and the Gaussian parts of the hidden units decay at pairwise
different rates `e^{-u_k² t²/2}`.
-/

namespace Skips

open Matrix Filter Topology

/-- Gaussian decay beats `t²`: for `v² < u²`, `t² e^{-(t u + b)²/2 + (t v + d)²/2} → 0`. -/
private lemma tendsto_sq_mul_exp_quad {u v : ℝ} (b d : ℝ) (h : v ^ 2 < u ^ 2) :
    Tendsto (fun t => t ^ 2 * Real.exp (-(t * u + b) ^ 2 / 2 + (t * v + d) ^ 2 / 2)) atTop
      (𝓝 0) := by
  -- the exponent is `-α t² + β t + γ` with `α > 0`; it is `≤ -t + γ` once `α t ≥ β + 1`
  have hα : 0 < (u ^ 2 - v ^ 2) / 2 := by linarith
  have hexp : ∀ t, -(t * u + b) ^ 2 / 2 + (t * v + d) ^ 2 / 2
      = -((u ^ 2 - v ^ 2) / 2) * t ^ 2 + (v * d - u * b) * t + (d ^ 2 - b ^ 2) / 2 :=
    fun t => by ring
  have hlim := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul
    (Real.exp ((d ^ 2 - b ^ 2) / 2))
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun t => by positivity) ?_
  filter_upwards [eventually_ge_atTop (max 0 ((v * d - u * b + 1) / ((u ^ 2 - v ^ 2) / 2)))]
    with t ht
  have ht0 : 0 ≤ t := le_trans (le_max_left _ _) ht
  have ht1 : v * d - u * b + 1 ≤ (u ^ 2 - v ^ 2) / 2 * t := by
    have := le_trans (le_max_right _ _) ht
    rw [div_le_iff₀ hα] at this; linarith
  have hle : -((u ^ 2 - v ^ 2) / 2) * t ^ 2 + (v * d - u * b) * t + (d ^ 2 - b ^ 2) / 2
      ≤ -t + (d ^ 2 - b ^ 2) / 2 := by nlinarith
  rw [hexp, show Real.exp ((d ^ 2 - b ^ 2) / 2) * (t ^ 2 * Real.exp (-t))
    = t ^ 2 * Real.exp (-t + (d ^ 2 - b ^ 2) / 2) by rw [Real.exp_add]; ring]
  gcongr

/-- A quadratic `α t² + β t + γ` plus a term tending to `0` that vanishes for all large `t` has
`α = β = γ = 0`. -/
private lemma quad_eq_zero {α β γ : ℝ} {ε : ℝ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (h : ∀ᶠ t in atTop, α * t ^ 2 + β * t + γ + ε t = 0) : α = 0 ∧ β = 0 ∧ γ = 0 := by
  have hi := tendsto_inv_atTop_zero (𝕜 := ℝ)
  -- divide by `t²`
  have hα : α = 0 := by
    have h1 := ((tendsto_const_nhds (x := α)).add (hi.const_mul β)).add
      (((hi.const_mul γ).mul hi).add ((hε.mul hi).mul hi))
    simp only [mul_zero, add_zero] at h1
    refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
    filter_upwards [h, eventually_gt_atTop 0] with t ht ht0
    have e : α + β * t⁻¹ + (γ * t⁻¹ * t⁻¹ + ε t * t⁻¹ * t⁻¹)
        = (α * t ^ 2 + β * t + γ + ε t) * t⁻¹ * t⁻¹ := by
      field_simp; ring
    rw [e, ht, zero_mul, zero_mul]
  -- divide by `t`
  have hβ : β = 0 := by
    have h1 := ((tendsto_const_nhds (x := β)).add (hi.const_mul γ)).add (hε.mul hi)
    simp only [mul_zero, add_zero] at h1
    refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
    filter_upwards [h, eventually_gt_atTop 0] with t ht ht0
    have e : β + γ * t⁻¹ + ε t * t⁻¹ = (α * t ^ 2 + β * t + γ + ε t) * t⁻¹ := by
      rw [hα]; field_simp; ring
    rw [e, ht, zero_mul]
  -- the constant
  have hγ : γ = 0 := by
    have h1 := (tendsto_const_nhds (x := γ)).add hε
    rw [add_zero] at h1
    refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
    filter_upwards [h] with t ht
    rw [← ht, hα, hβ]; ring
  exact ⟨hα, hβ, hγ⟩

section expansions

variable {σ σ' φ : ℝ → ℝ}

/-- Crude form of the expansions for `z ≥ 1`: `|σ(z) - z| ≤ φ(z)`, `|σ'(z) - 1| ≤ φ(z)(z + 1)`. -/
private lemma crude_pos (hφ : ∀ z, 0 < φ z)
    (hσp : ∀ z, 0 < z → 0 ≤ σ z - z + φ z ∧ σ z - z + φ z ≤ φ z / z ^ 2)
    (hσ'p : ∀ z, 0 < z → 0 ≤ σ' z - 1 - φ z * (z - 1 / z) ∧
      σ' z - 1 - φ z * (z - 1 / z) ≤ φ z / z ^ 3)
    {z : ℝ} (hz : 1 ≤ z) : |σ z - z| ≤ φ z ∧ |σ' z - 1| ≤ φ z * (|z| + 1) := by
  have hz0 : 0 < z := by linarith
  have hφz := hφ z
  obtain ⟨h1, h2⟩ := hσp z hz0
  obtain ⟨h3, h4⟩ := hσ'p z hz0
  have e1 : φ z / z ^ 2 ≤ φ z := div_le_self hφz.le (one_le_pow₀ hz)
  have e2 : φ z / z ^ 3 ≤ φ z := div_le_self hφz.le (one_le_pow₀ hz)
  have e3 : 0 < 1 / z := by positivity
  have e4 : 1 / z ≤ 1 := by rw [div_le_one hz0]; exact hz
  have e5 : 0 ≤ φ z * (z - 1 / z) := mul_nonneg hφz.le (by linarith)
  have e6 : φ z * (z - 1 / z) ≤ φ z * z := mul_le_mul_of_nonneg_left (by linarith) hφz.le
  rw [abs_of_pos hz0, mul_add, mul_one]
  constructor
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

/-- Crude form of the expansions for `z ≤ -1`: `|σ(z)| ≤ φ(z)`, `|σ'(z)| ≤ φ(z)(|z| + 1)`. -/
private lemma crude_neg (hφ : ∀ z, 0 < φ z)
    (hσn : ∀ z, z < 0 → 0 ≤ σ z + φ z ∧ σ z + φ z ≤ φ z / z ^ 2)
    (hσ'n : ∀ z, z < 0 → φ z / z ^ 3 ≤ σ' z - φ z * (z - 1 / z) ∧
      σ' z - φ z * (z - 1 / z) ≤ 0)
    {z : ℝ} (hz : z ≤ -1) : |σ z| ≤ φ z ∧ |σ' z| ≤ φ z * (|z| + 1) := by
  have hz0 : z < 0 := by linarith
  have hφz := hφ z
  obtain ⟨h1, h2⟩ := hσn z hz0
  obtain ⟨h3, h4⟩ := hσ'n z hz0
  have e1 : φ z / z ^ 2 ≤ φ z := div_le_self hφz.le (by nlinarith)
  have hz3' : z ^ 3 ≤ -1 := by nlinarith
  have hz3 : z ^ 3 < 0 := by linarith
  have e2 : -φ z ≤ φ z / z ^ 3 := by
    rw [le_div_iff_of_neg hz3]
    have : φ z * z ^ 3 ≤ φ z * (-1) := mul_le_mul_of_nonneg_left hz3' hφz.le
    linarith
  have e3 : 1 / z < 0 := by rw [one_div]; exact inv_lt_zero.2 hz0
  have e4 : -1 ≤ 1 / z := by rw [le_div_iff_of_neg hz0]; linarith
  have e5 : φ z * (z - 1 / z) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hφz.le (by linarith)
  have e6 : φ z * z ≤ φ z * (z - 1 / z) := mul_le_mul_of_nonneg_left (by linarith) hφz.le
  rw [abs_of_neg hz0, mul_add, mul_one]
  constructor
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

end expansions

/-- Bookkeeping for the crude bound: if `|X| ≤ F` and `|Y| ≤ F (|z| + 1)` with `z = t u + b`,
`t ≥ 1`, then `|X A + Y (t w + p) a| ≤ K t² F` with `K = |A| + (|u| + |b| + 1)(|w| + |p|)|a|`. -/
private lemma bound_aux {X Y F t u b w p A a : ℝ} (hF : 0 ≤ F) (ht : 1 ≤ t)
    (hX : |X| ≤ F) (hY : |Y| ≤ F * (|t * u + b| + 1)) :
    |X * A + Y * (t * w + p) * a|
      ≤ (|A| + (|u| + |b| + 1) * (|w| + |p|) * |a|) * t ^ 2 * F := by
  have ht0 : 0 ≤ t := by linarith
  have hz : |t * u + b| + 1 ≤ (|u| + |b| + 1) * t := by
    have := abs_add_le (t * u) b
    rw [abs_mul, abs_of_nonneg ht0] at this
    nlinarith [abs_nonneg b]
  have hθ : |t * w + p| ≤ (|w| + |p|) * t := by
    have := abs_add_le (t * w) p
    rw [abs_mul, abs_of_nonneg ht0] at this
    nlinarith [abs_nonneg p]
  have h1 : |X| * |A| ≤ F * |A| * t ^ 2 := by
    have : 1 ≤ t ^ 2 := one_le_pow₀ ht
    calc |X| * |A| ≤ F * |A| := mul_le_mul_of_nonneg_right hX (abs_nonneg A)
      _ = F * |A| * 1 := (mul_one _).symm
      _ ≤ F * |A| * t ^ 2 := mul_le_mul_of_nonneg_left this (mul_nonneg hF (abs_nonneg A))
  have h2 : |Y| * |t * w + p| * |a| ≤ F * ((|u| + |b| + 1) * t) * ((|w| + |p|) * t) * |a| := by
    gcongr
    exact hY.trans (mul_le_mul_of_nonneg_left hz hF)
  calc |X * A + Y * (t * w + p) * a| ≤ |X * A| + |Y * (t * w + p) * a| := abs_add_le _ _
    _ = |X| * |A| + |Y| * |t * w + p| * |a| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ F * |A| * t ^ 2 + F * ((|u| + |b| + 1) * t) * ((|w| + |p|) * t) * |a| := add_le_add h1 h2
    _ = _ := by ring

/-- The line `t ↦ t u + b` tends to `+∞` for `u > 0`. -/
private lemma tendsto_line {u : ℝ} (hu : 0 < u) (b : ℝ) :
    Tendsto (fun t : ℝ => t * u + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.atTop_mul_const hu)

section ray

variable {σ σ' φ : ℝ → ℝ}

/-- **The crude bound.** Along the ray, unit `i` minus its polynomial part
`[u > 0] (z A + (t w + p) a)` is at most `K t² φ(z)` for large `t`, with `z = t u + b`. -/
private lemma unit_bound (hφ : ∀ z, 0 < φ z)
    (hσp : ∀ z, 0 < z → 0 ≤ σ z - z + φ z ∧ σ z - z + φ z ≤ φ z / z ^ 2)
    (hσn : ∀ z, z < 0 → 0 ≤ σ z + φ z ∧ σ z + φ z ≤ φ z / z ^ 2)
    (hσ'p : ∀ z, 0 < z → 0 ≤ σ' z - 1 - φ z * (z - 1 / z) ∧
      σ' z - 1 - φ z * (z - 1 / z) ≤ φ z / z ^ 3)
    (hσ'n : ∀ z, z < 0 → φ z / z ^ 3 ≤ σ' z - φ z * (z - 1 / z) ∧
      σ' z - φ z * (z - 1 / z) ≤ 0)
    {u : ℝ} (hu : u ≠ 0) (b w p A a : ℝ) :
    ∀ᶠ t in atTop, |σ (t * u + b) * A + σ' (t * u + b) * (t * w + p) * a
      - (if 0 < u then (t * u + b) * A + (t * w + p) * a else 0)|
      ≤ (|A| + (|u| + |b| + 1) * (|w| + |p|) * |a|) * t ^ 2 * φ (t * u + b) := by
  rcases hu.lt_or_gt with hneg | hpos
  · -- `u < 0`: eventually `z ≤ -1`, and the polynomial part is `0`
    filter_upwards [(tendsto_line (neg_pos.2 hneg) (-b)).eventually_ge_atTop 1,
      eventually_ge_atTop 1] with t hzt ht
    have hz1 : t * u + b ≤ -1 := by linarith
    obtain ⟨h1, h2⟩ := crude_neg hφ hσn hσ'n hz1
    rw [ite_eq_right (not_lt.2 hneg.le), sub_zero]
    exact bound_aux (hφ _).le ht h1 h2
  · -- `u > 0`: eventually `z ≥ 1`, and the polynomial part is `z A + (t w + p) a`
    filter_upwards [(tendsto_line hpos b).eventually_ge_atTop 1, eventually_ge_atTop 1]
      with t hzt ht
    obtain ⟨h1, h2⟩ := crude_pos hφ hσp hσ'p hzt
    rw [ite_eq_left hpos]
    have e : σ (t * u + b) * A + σ' (t * u + b) * (t * w + p) * a
        - ((t * u + b) * A + (t * w + p) * a)
        = (σ (t * u + b) - (t * u + b)) * A + (σ' (t * u + b) - 1) * (t * w + p) * a := by ring
    rw [e]
    exact bound_aux (hφ _).le ht h1 h2

/-- **The slowest unit**, `u > 0`. Divided by `φ(z)`, `z = t u + b`, the unit minus its polynomial
part is `Q(t) = a u w t² + a (u p + b w) t + (a b p - A - a w/u)` up to a term tending to `0`:
it is `A ρ/φ + a ((t w + p)/z) (z ρ'/φ) - a ((t w + p)/z - w/u)` with the remainders
`ρ = σ - z + φ`, `ρ' = σ' - 1 - φ (z - 1/z)`, and `0 ≤ ρ/φ, z ρ'/φ ≤ 1/z²`. -/
private lemma unit_main (hφ : ∀ z, 0 < φ z)
    (hσp : ∀ z, 0 < z → 0 ≤ σ z - z + φ z ∧ σ z - z + φ z ≤ φ z / z ^ 2)
    (hσ'p : ∀ z, 0 < z → 0 ≤ σ' z - 1 - φ z * (z - 1 / z) ∧
      σ' z - 1 - φ z * (z - 1 / z) ≤ φ z / z ^ 3)
    {u : ℝ} (hu : 0 < u) (b w p A a : ℝ) :
    Tendsto (fun t => (σ (t * u + b) * A + σ' (t * u + b) * (t * w + p) * a
      - (if 0 < u then (t * u + b) * A + (t * w + p) * a else 0)) / φ (t * u + b)
      - (a * u * w * t ^ 2 + a * (u * p + b * w) * t + (a * b * p - A - a * w / u))) atTop
      (𝓝 0) := by
  have hz := tendsto_line hu b
  -- `1/z² → 0`
  have hz2 : Tendsto (fun t => 1 / (t * u + b) ^ 2) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp hz).pow 2
    rw [zero_pow two_ne_zero] at this
    refine this.congr fun t => ?_
    simp only [Function.comp_apply, one_div, inv_pow]
  -- `ρ/φ → 0`
  have hρ : Tendsto (fun t => (σ (t * u + b) - (t * u + b) + φ (t * u + b)) / φ (t * u + b))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz2 ?_ ?_
    · filter_upwards [hz.eventually_gt_atTop 0] with t ht
      exact div_nonneg (hσp _ ht).1 (hφ _).le
    · filter_upwards [hz.eventually_gt_atTop 0] with t ht
      rw [div_le_iff₀ (hφ _)]
      calc _ ≤ φ (t * u + b) / (t * u + b) ^ 2 := (hσp _ ht).2
        _ = _ := by ring
  -- `z ρ'/φ → 0`
  have hρ' : Tendsto (fun t => (t * u + b) * (σ' (t * u + b) - 1
      - φ (t * u + b) * ((t * u + b) - 1 / (t * u + b))) / φ (t * u + b)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz2 ?_ ?_
    · filter_upwards [hz.eventually_gt_atTop 0] with t ht
      exact div_nonneg (mul_nonneg ht.le (hσ'p _ ht).1) (hφ _).le
    · filter_upwards [hz.eventually_gt_atTop 0] with t ht
      rw [div_le_iff₀ (hφ _)]
      calc _ ≤ (t * u + b) * (φ (t * u + b) / (t * u + b) ^ 3) :=
            mul_le_mul_of_nonneg_left (hσ'p _ ht).2 ht.le
        _ = _ := by field_simp
  -- `(t w + p)/z → w/u`
  have hθ : Tendsto (fun t => (t * w + p) / (t * u + b)) atTop (𝓝 (w / u)) := by
    have hi := tendsto_inv_atTop_zero (𝕜 := ℝ)
    have h1 := ((tendsto_const_nhds (x := w)).add (hi.const_mul p)).div
      ((tendsto_const_nhds (x := u)).add (hi.const_mul b)) (by simp [hu.ne'])
    simp only [mul_zero, add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0, hz.eventually_gt_atTop 0] with t ht hzt
    have := hzt.ne'
    rw [Pi.div_apply]
    field_simp
  -- combine the three limits
  have hlim := ((hρ.const_mul A).add ((hθ.mul hρ').const_mul a)).sub
    ((hθ.sub_const (w / u)).const_mul a)
  simp only [mul_zero, add_zero, sub_self] at hlim
  refine hlim.congr' ?_
  filter_upwards [hz.eventually_gt_atTop 0] with t hzt
  rw [ite_eq_left hu]
  have hφz := (hφ (t * u + b)).ne'
  have hz0 := hzt.ne'
  have hu0 := hu.ne'
  field_simp
  ring

end ray

/-- **The ray argument**, in one output coordinate. Along the ray `x = t ν` the identity reads
`t V + C + ∑ᵢ [σ(t uᵢ + bᵢ) Aᵢ + σ'(t uᵢ + bᵢ) (t wᵢ + pᵢ) aᵢ] = 0`. If `u_j > 0` and
`u_j < |u_i|` for all `i ≠ j`, then `w_j a_j = 0`, `p_j a_j = 0` and `A_j = 0`. Here `φ` is the
Gaussian `e^{-z²/2}/κ`, and `σ`, `σ'` satisfy the expansions of `Activations/GeluExpansion.lean`. -/
private lemma ray_coeffs {q : Type*} [Fintype q] [DecidableEq q] {σ σ' φ : ℝ → ℝ} {κ : ℝ}
    (hκ : 0 < κ) (hφ : ∀ z, φ z = Real.exp (-z ^ 2 / 2) / κ)
    (hσp : ∀ z, 0 < z → 0 ≤ σ z - z + φ z ∧ σ z - z + φ z ≤ φ z / z ^ 2)
    (hσn : ∀ z, z < 0 → 0 ≤ σ z + φ z ∧ σ z + φ z ≤ φ z / z ^ 2)
    (hσ'p : ∀ z, 0 < z → 0 ≤ σ' z - 1 - φ z * (z - 1 / z) ∧
      σ' z - 1 - φ z * (z - 1 / z) ≤ φ z / z ^ 3)
    (hσ'n : ∀ z, z < 0 → φ z / z ^ 3 ≤ σ' z - φ z * (z - 1 / z) ∧
      σ' z - φ z * (z - 1 / z) ≤ 0)
    (u b w p A a : q → ℝ) (V C : ℝ) (j : q) (hj : 0 < u j) (hk : ∀ i, i ≠ j → u j < |u i|)
    (hJ : ∀ t : ℝ, t * V + C + ∑ i, (σ (t * u i + b i) * A i
      + σ' (t * u i + b i) * (t * w i + p i) * a i) = 0) :
    w j * a j = 0 ∧ p j * a j = 0 ∧ A j = 0 := by
  have hφ0 : ∀ z, 0 < φ z := fun z => by rw [hφ]; positivity
  have hu0 : ∀ i, u i ≠ 0 := fun i => by
    by_cases hi : i = j
    · subst hi; exact hj.ne'
    · exact abs_pos.1 (hj.trans (hk i hi))
  -- `E i t`: unit `i` minus its polynomial part `[uᵢ > 0] (zᵢ Aᵢ + (t wᵢ + pᵢ) aᵢ)`
  obtain ⟨E, hE⟩ : ∃ E : q → ℝ → ℝ, ∀ i t, E i t = σ (t * u i + b i) * A i
      + σ' (t * u i + b i) * (t * w i + p i) * a i
      - (if 0 < u i then (t * u i + b i) * A i + (t * w i + p i) * a i else 0) :=
    ⟨_, fun _ _ => rfl⟩
  -- the crude bound `|E i t| ≤ Kᵢ t² φ(zᵢ)` for large `t`
  have hEb : ∀ i, ∀ᶠ t in atTop, |E i t| ≤ (|A i| + (|u i| + |b i| + 1) * (|w i| + |p i|)
      * |a i|) * t ^ 2 * φ (t * u i + b i) := fun i => by
    filter_upwards [unit_bound hφ0 hσp hσn hσ'p hσ'n (hu0 i) (b i) (w i) (p i) (A i) (a i)]
      with t ht
    rw [hE]; exact ht
  -- (i) every `E i` tends to `0`, as `t² φ(zᵢ) → 0`
  have hE0 : ∀ i, Tendsto (E i) atTop (𝓝 0) := fun i => by
    have hd := (tendsto_sq_mul_exp_quad (u := u i) (v := 0) (b i) 0
      (by rw [sq_lt_sq, abs_zero]; exact abs_pos.2 (hu0 i))).const_mul
      ((|A i| + (|u i| + |b i| + 1) * (|w i| + |p i|) * |a i|) / κ)
    rw [mul_zero] at hd
    refine squeeze_zero_norm' ?_ hd
    filter_upwards [hEb i] with t ht
    rw [Real.norm_eq_abs]
    refine ht.trans (le_of_eq ?_)
    rw [hφ, show (t * 0 + 0) ^ 2 / 2 = (0 : ℝ) by ring, add_zero]
    ring
  -- (ii) the polynomial parts add up to `t V₁ + C₁`, so `t (V + V₁) + (C + C₁) = -∑ E i t → 0`:
  -- both coefficients vanish, and `∑ E i t = 0` for all `t`
  have hsplit : ∀ t, ∑ i, (σ (t * u i + b i) * A i + σ' (t * u i + b i) * (t * w i + p i) * a i)
      = ∑ i, E i t + (t * ∑ i, (if 0 < u i then u i * A i + w i * a i else 0)
        + ∑ i, (if 0 < u i then b i * A i + p i * a i else 0)) := fun t => by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hE]
    split_ifs <;> ring
  have hS : Tendsto (fun t => ∑ i, E i t) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ fun i _ => hE0 i
  obtain ⟨-, hV, hC⟩ := quad_eq_zero (α := 0)
    (β := V + ∑ i, (if 0 < u i then u i * A i + w i * a i else 0))
    (γ := C + ∑ i, (if 0 < u i then b i * A i + p i * a i else 0)) hS
    (Eventually.of_forall fun t => by
      have h1 := hJ t
      rw [hsplit t] at h1
      linear_combination h1)
  have hsum : ∀ t, ∑ i, E i t = 0 := fun t => by
    have h1 := hJ t
    rw [hsplit t] at h1
    linear_combination h1 - t * hV - hC
  -- (iii) divided by `φ(z_j)`: unit `j` gives the quadratic `Q`, the others tend to `0`
  have hlimj : Tendsto (fun t => E j t / φ (t * u j + b j)
      - (a j * u j * w j * t ^ 2 + a j * (u j * p j + b j * w j) * t
        + (a j * b j * p j - A j - a j * w j / u j))) atTop (𝓝 0) :=
    (unit_main hφ0 hσp hσ'p hj (b j) (w j) (p j) (A j) (a j)).congr fun t => by rw [hE]
  have hlimk : ∀ i, i ≠ j → Tendsto (fun t => E i t / φ (t * u j + b j)) atTop (𝓝 0) :=
    fun i hi => by
    have hd := (tendsto_sq_mul_exp_quad (u := u i) (v := u j) (b i) (b j)
      (by rw [sq_lt_sq, abs_of_pos hj]; exact hk i hi)).const_mul
      (|A i| + (|u i| + |b i| + 1) * (|w i| + |p i|) * |a i|)
    rw [mul_zero] at hd
    refine squeeze_zero_norm' ?_ hd
    filter_upwards [hEb i] with t ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hφ0 _), div_le_iff₀ (hφ0 _)]
    refine ht.trans (le_of_eq ?_)
    have e : Real.exp (-(t * u i + b i) ^ 2 / 2) = Real.exp (-(t * u i + b i) ^ 2 / 2
        + (t * u j + b j) ^ 2 / 2) * Real.exp (-(t * u j + b j) ^ 2 / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hφ, hφ, e]
    ring
  have hε : Tendsto (fun t => ∑ i, (E i t / φ (t * u j + b j)
      - if i = j then a j * u j * w j * t ^ 2 + a j * (u j * p j + b j * w j) * t
        + (a j * b j * p j - A j - a j * w j / u j) else 0)) atTop (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) =>
      (show Tendsto (fun t => E i t / φ (t * u j + b j)
        - if i = j then a j * u j * w j * t ^ 2 + a j * (u j * p j + b j * w j) * t
          + (a j * b j * p j - A j - a j * w j / u j) else 0) atTop (𝓝 0) by
        by_cases hi : i = j
        · subst hi; simpa only [ite_true] using hlimj
        · simpa only [hi, ite_false, sub_zero] using hlimk i hi)
    simpa using h
  obtain ⟨h1, h2, h3⟩ := quad_eq_zero (α := a j * u j * w j)
    (β := a j * (u j * p j + b j * w j)) (γ := a j * b j * p j - A j - a j * w j / u j) hε
    (Eventually.of_forall fun t => by
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [← Finset.sum_div, hsum t, zero_div]
      ring)
  -- (iv) read off the coefficients
  have hwa : w j * a j = 0 := by
    have : u j * (w j * a j) = 0 := by linear_combination h1
    exact (mul_eq_zero.1 this).resolve_left hj.ne'
  have hpa : p j * a j = 0 := by
    have : u j * (p j * a j) = 0 := by linear_combination h2 - b j * hwa
    exact (mul_eq_zero.1 this).resolve_left hj.ne'
  refine ⟨hwa, hpa, ?_⟩
  linear_combination -h3 + b j * hpa - (1 / u j) * hwa


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

/-- **One unit vanishes.** Along a good direction `ν` for unit `j`, the ray argument at `x = t ν`
gives `ν ψ_{c_j} = 0`, `ψ_{β_j} = 0` and `ψ_{a_j} = 0` (for GELU one ray suffices). -/
private lemma unit_vanish {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψa : q → k → ℝ)
    (ha : ∀ i, a i ≠ 0)
    (h : ∀ x : n → ℝ,
      x ᵥ* ψM + ψγ + ∑ i, (gelu (x ⬝ᵥ c i + β i) • ψa i
        + (geluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i)) • a i) = 0)
    (j : q) (ν : n → ℝ) (hν : 0 < ν ⬝ᵥ c j ∧ ∀ i, i ≠ j → ν ⬝ᵥ c j < |ν ⬝ᵥ c i|) :
    ν ⬝ᵥ ψc j = 0 ∧ ψβ j = 0 ∧ ψa j = 0 := by
  classical
  -- the identity on the ray `x = t ν`, in the output coordinate `o`
  have hray : ∀ o t, t * (ν ᵥ* ψM) o + ψγ o + ∑ i, (gelu (t * (ν ⬝ᵥ c i) + β i) * ψa i o
      + geluDeriv (t * (ν ⬝ᵥ c i) + β i) * (t * (ν ⬝ᵥ ψc i) + ψβ i) * a i o) = 0 :=
    fun o t => by
      simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, smul_vecMul,
        smul_dotProduct, Pi.zero_apply] using congrFun (h (t • ν)) o
  -- the scalar ray argument, with `φ = gaussPdf`, `σ = gelu`, `σ' = geluDeriv`
  have h1 : ∀ o, (ν ⬝ᵥ ψc j) * a j o = 0 ∧ ψβ j * a j o = 0 ∧ ψa j o = 0 := fun o =>
    ray_coeffs (σ := gelu) (σ' := geluDeriv) (φ := gaussPdf) (κ := Real.sqrt (2 * Real.pi))
      (Real.sqrt_pos.2 (by positivity)) (fun _ => rfl) (fun _ hz => gelu_expansion_pos hz)
      (fun _ hz => gelu_expansion_neg hz) (fun _ hz => geluDeriv_expansion_pos hz)
      (fun _ hz => geluDeriv_expansion_neg hz) (fun i => ν ⬝ᵥ c i) β (fun i => ν ⬝ᵥ ψc i) ψβ
      (fun i => ψa i o) (fun i => a i o) ((ν ᵥ* ψM) o) (ψγ o) j hν.1 hν.2 (hray o)
  -- `a_j ≠ 0`: pick an output coordinate `o` with `a_j o ≠ 0`
  obtain ⟨o, ho⟩ := Function.ne_iff.1 (ha j)
  rw [Pi.zero_apply] at ho
  exact ⟨(mul_eq_zero.1 (h1 o).1).resolve_right ho, (mul_eq_zero.1 (h1 o).2.1).resolve_right ho,
    funext fun o => (h1 o).2.2⟩

/-- **Lemma C.3 for GELU.** Rows are indexed by `n` (the coordinates of an input `x`), hidden
units by `q`, and the coordinates of the output by `k`. -/
theorem gelu_units_flat_eq_zero {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψa : q → k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j)
    (h : ∀ x : n → ℝ,
      x ᵥ* ψM + ψγ + ∑ i, (gelu (x ⬝ᵥ c i + β i) • ψa i
        + (geluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i)) • a i) = 0) :
    ψM = 0 ∧ ψγ = 0 ∧ ψc = 0 ∧ ψβ = 0 ∧ ψa = 0 := by
  classical
  -- every unit vanishes
  have hunit : ∀ j, ψc j = 0 ∧ ψβ j = 0 ∧ ψa j = 0 := fun j => by
    obtain ⟨ν, hν⟩ := exists_good c hc hcol j
    obtain ⟨e1, hβ, hA⟩ := unit_vanish c β a ψM ψγ ψc ψβ ψa ha h j ν hν
    refine ⟨?_, hβ, hA⟩
    -- `ν + ε ψ_{c_j}` is a good direction too for some `ε > 0`, so `ε ψ_{c_j} ψ_{c_j} = 0`
    obtain ⟨ε, hε, hε0⟩ := (((eventually_good c j ν (ψc j) hν).filter_mono
      nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin (s := Set.Ioi 0))).exists
    have e2 := (unit_vanish c β a ψM ψγ ψc ψβ ψa ha h j (ν + ε • ψc j) hε).1
    rw [add_dotProduct, smul_dotProduct, e1, zero_add, smul_eq_mul] at e2
    exact dotProduct_self_eq_zero.1 ((mul_eq_zero.1 e2).resolve_left (ne_of_gt hε0))
  have hψc : ψc = 0 := funext fun j => (hunit j).1
  have hψβ : ψβ = 0 := funext fun j => (hunit j).2.1
  have hψa : ψa = 0 := funext fun j => (hunit j).2.2
  -- what is left is `x ψ_M + ψ_γ = 0` for all `x`
  have hlin : ∀ x : n → ℝ, x ᵥ* ψM + ψγ = 0 := fun x => by
    simpa [hψc, hψβ, hψa] using h x
  have hγ : ψγ = 0 := by simpa using hlin 0
  refine ⟨?_, hγ, hψc, hψβ, hψa⟩
  ext m o
  simpa [hγ] using congrFun (hlin (Pi.single m 1)) o

end Skips
