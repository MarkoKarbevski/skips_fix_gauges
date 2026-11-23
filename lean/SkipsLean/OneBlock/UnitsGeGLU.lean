import SkipsLean.Activations.GeluExpansion

/-!
# A flat direction of GeGLU hidden units only rescales their values

Paper (dimension paper): Lemma C.3, the case of GeGLU, in the generality in which the paper states
it: with a linear term `x M`, a constant `γ` and biases `β_i`, `β'_i`.

A GeGLU hidden unit computes `σ(z_i) w_i a_i` with the gate `z_i = x c_i + β_i`, the value
`w_i = x e_i + β'_i` and `σ(z) = z Φ(z)` (GELU). The function is
`G(φ, x) = x M + γ + ∑_i σ(z_i) w_i a_i`, and a direction
`ψ = (ψ_M, ψ_γ, ψ_{c_i}, ψ_{β_i}, ψ_{e_i}, ψ_{β'_i}, ψ_{a_i})` of the weights is flat if the
derivative of `G` along it vanishes at every input `x`:

  `x ψ_M + ψ_γ + ∑_i [ σ(z_i) w_i ψ_{a_i} + σ'(z_i) (x ψ_{c_i} + ψ_{β_i}) w_i a_i
      + σ(z_i) (x ψ_{e_i} + ψ_{β'_i}) a_i ] = 0`,

with `σ'(z) = Φ(z) + z φ(z)`. The lemma says that then `ψ_M = 0`, `ψ_γ = 0`, `ψ_{c_i} = 0`,
`ψ_{β_i} = 0`, and `(ψ_{e_i}, ψ_{β'_i}) = -α_i (e_i, β'_i)`, `ψ_{a_i} = α_i a_i` for some numbers
`α_i`: the direction of the rescaling `(e_i, a_i) ↦ (e_i/λ, λ a_i)` of the value of each hidden
unit. The proof of the paper follows a ray `x = t n` to infinity, with the expansions of GELU
(`UnitsGELU.lean`): the rest of the slowest hidden unit `j` is `φ(z_j)` times a polynomial in `t`
and `1/z_j`, whose coefficients vanish.

As for SwiGLU, the statement is proved without the hypothesis of the paper that `(e_i, β'_i)` is
not proportional to `(c_i, β_i)`; the form of the paper follows.
-/

namespace Skips

open Matrix Filter Topology

/-- The rest of GELU after its polynomial part along a ray of slope `u`: `σ(z) - [u > 0] z`. -/
private noncomputable def restS (u z : ℝ) : ℝ := gelu z - if 0 < u then z else 0

/-- The rest of `σ'` after its polynomial part along a ray of slope `u`: `σ'(z) - [u > 0]`. -/
private noncomputable def restD (u z : ℝ) : ℝ := geluDeriv z - if 0 < u then 1 else 0

/-- The expansions of GELU far out on the side of `u` (`z` of the sign of `u`, `|z| ≥ 1`):
`|restS + φ| ≤ φ/z²` and `|restD - φ (z - 1/z)| ≤ φ/|z|³`. -/
private lemma rest_bounds {u z : ℝ} (hz : (0 < u ∧ 1 ≤ z) ∨ (u < 0 ∧ z ≤ -1)) :
    |restS u z + gaussPdf z| ≤ gaussPdf z / z ^ 2 ∧
      |restD u z - gaussPdf z * (z - 1 / z)| ≤ gaussPdf z / |z| ^ 3 := by
  rcases hz with ⟨hu, hz⟩ | ⟨hu, hz⟩
  · have hz0 : 0 < z := by linarith
    obtain ⟨h1, h2⟩ := gelu_expansion_pos hz0
    obtain ⟨h3, h4⟩ := geluDeriv_expansion_pos hz0
    simp only [restS, restD, ite_eq_left hu]
    rw [abs_of_pos hz0]
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩
  · have hz0 : z < 0 := by linarith
    obtain ⟨h1, h2⟩ := gelu_expansion_neg hz0
    obtain ⟨h3, h4⟩ := geluDeriv_expansion_neg hz0
    simp only [restS, restD, ite_eq_right (not_lt.2 hu.le), sub_zero]
    have e : gaussPdf z / |z| ^ 3 = -(gaussPdf z / z ^ 3) := by
      rw [abs_of_neg hz0, show (-z) ^ 3 = -z ^ 3 by ring, div_neg]
    rw [e]
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

private lemma side_abs {u z : ℝ} (hz : (0 < u ∧ 1 ≤ z) ∨ (u < 0 ∧ z ≤ -1)) : 1 ≤ |z| := by
  rcases hz with ⟨-, hz⟩ | ⟨-, hz⟩
  · rw [abs_of_pos (by linarith)]; exact hz
  · rw [abs_of_neg (by linarith)]; linarith

/-- Far out on a ray, `z = t u + b` has the sign of `u` and `|z| ≥ 1`. -/
private lemma eventually_side {u : ℝ} (hu : u ≠ 0) (b : ℝ) :
    ∀ᶠ t in atTop, (0 < u ∧ 1 ≤ t * u + b) ∨ (u < 0 ∧ t * u + b ≤ -1) := by
  rcases hu.lt_or_gt with hu | hu
  · filter_upwards [eventually_ge_atTop ((-1 - b) / u)] with t ht
    exact Or.inr ⟨hu, by linarith [(div_le_iff_of_neg hu).1 ht]⟩
  · filter_upwards [eventually_ge_atTop ((1 - b) / u)] with t ht
    exact Or.inl ⟨hu, by linarith [(div_le_iff₀ hu).1 ht]⟩

/-- Crude bounds far out: `|restS| ≤ 2 φ(z)` and `|restD| ≤ (|z| + 2) φ(z)`. -/
private lemma rest_crude {u z : ℝ} (hz : (0 < u ∧ 1 ≤ z) ∨ (u < 0 ∧ z ≤ -1)) :
    |restS u z| ≤ 2 * gaussPdf z ∧ |restD u z| ≤ (|z| + 2) * gaussPdf z := by
  obtain ⟨h1, h2⟩ := rest_bounds hz
  have hz1 := side_abs hz
  have hp := gaussPdf_pos z
  have e1 : gaussPdf z / z ^ 2 ≤ gaussPdf z :=
    div_le_self hp.le (by rw [← sq_abs]; nlinarith)
  have e2 : gaussPdf z / |z| ^ 3 ≤ gaussPdf z := div_le_self hp.le (one_le_pow₀ hz1)
  have hinv : |1 / z| ≤ 1 := by
    rw [abs_div, abs_one, div_le_one (by linarith)]; exact hz1
  have e3 : |z - 1 / z| ≤ |z| + 1 := by
    obtain ⟨a1, a2⟩ := abs_le.1 hinv
    exact abs_le.2 ⟨by linarith [neg_abs_le z], by linarith [le_abs_self z]⟩
  have e4 : |gaussPdf z * (z - 1 / z)| ≤ gaussPdf z * (|z| + 1) := by
    rw [abs_mul, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left e3 hp.le
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  obtain ⟨h2a, h2b⟩ := abs_le.1 h2
  obtain ⟨h4a, h4b⟩ := abs_le.1 e4
  exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

/-- `φ(x) / φ(y) = e^{-x²/2 + y²/2}`. -/
private lemma gaussPdf_div (x y : ℝ) :
    gaussPdf x / gaussPdf y = Real.exp (-x ^ 2 / 2 - -y ^ 2 / 2) := by
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  rw [gaussPdf, gaussPdf, div_div_div_cancel_right₀ hs, ← Real.exp_sub]

/-- **Super-polynomial decay of the ratio**: for `|u'| < |u|`,
`t^m φ(t u + b) / φ(t u' + b') → 0`. -/
private lemma tendsto_pow_mul_ratio {u u' : ℝ} (h : |u'| < |u|) (b b' : ℝ) (m : ℕ) :
    Tendsto (fun t => t ^ m * (gaussPdf (t * u + b) / gaussPdf (t * u' + b'))) atTop (𝓝 0) := by
  -- the exponent is `-t - Q(t)` with `Q(t) = t (A t + B) + C → ∞`, `A = (u² - u'²)/2 > 0`
  have hA : 0 < (u ^ 2 - u' ^ 2) / 2 := by
    have := sq_lt_sq.2 h; linarith
  have hQ : Tendsto (fun t : ℝ => t * ((u ^ 2 - u' ^ 2) / 2 * t + (u * b - u' * b' - 1))
      + (b ^ 2 - b' ^ 2) / 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_atTop₀
      (tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hA)))
  have hE := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hQ)
  have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).mul hE
  rw [zero_mul] at this
  refine this.congr fun t => ?_
  simp only [Function.comp_apply]
  rw [gaussPdf_div, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Decay for `|u'| < |u|`: `t^k restS u (t u + b) / φ(t u' + b') → 0`, and the same for
`restD`. -/
private lemma rest_decay_aux {u u' : ℝ} (h : |u'| < |u|) (b b' : ℝ) (k : ℕ) :
    Tendsto (fun t => t ^ k * (restS u (t * u + b) / gaussPdf (t * u' + b'))) atTop (𝓝 0) ∧
      Tendsto (fun t => t ^ k * (restD u (t * u + b) / gaussPdf (t * u' + b'))) atTop
        (𝓝 0) := by
  have hu : u ≠ 0 := abs_pos.1 ((abs_nonneg u').trans_lt h)
  have hev := (eventually_side hu b).and (eventually_ge_atTop (1 : ℝ))
  constructor
  · have := (tendsto_pow_mul_ratio h b b' k).const_mul 2
    rw [mul_zero] at this
    refine squeeze_zero_norm' ?_ this
    filter_upwards [hev] with t ⟨hs, ht⟩
    have hp := gaussPdf_pos (t * u' + b')
    have htk : 0 ≤ t ^ k := pow_nonneg (by linarith) k
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hp, abs_of_nonneg htk]
    have h1 := (rest_crude hs).1
    calc t ^ k * (|restS u (t * u + b)| / gaussPdf (t * u' + b'))
        ≤ t ^ k * (2 * gaussPdf (t * u + b) / gaussPdf (t * u' + b')) := by gcongr
      _ = 2 * (t ^ k * (gaussPdf (t * u + b) / gaussPdf (t * u' + b'))) := by ring
  · have := (tendsto_pow_mul_ratio h b b' (k + 1)).const_mul (|u| + |b| + 2)
    rw [mul_zero] at this
    refine squeeze_zero_norm' ?_ this
    filter_upwards [hev] with t ⟨hs, ht⟩
    have hp := gaussPdf_pos (t * u' + b')
    have hp' := gaussPdf_pos (t * u + b)
    have htk : 0 ≤ t ^ k := pow_nonneg (by linarith) k
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hp, abs_of_nonneg htk]
    have h1 := (rest_crude hs).2
    have h2 : |t * u + b| + 2 ≤ (|u| + |b| + 2) * t := by
      have := abs_add_le (t * u) b
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)] at this
      nlinarith [abs_nonneg u, abs_nonneg b, mul_nonneg (sub_nonneg.2 ht) (abs_nonneg b)]
    calc t ^ k * (|restD u (t * u + b)| / gaussPdf (t * u' + b'))
        ≤ t ^ k * ((|t * u + b| + 2) * gaussPdf (t * u + b) / gaussPdf (t * u' + b')) := by
          gcongr
      _ ≤ t ^ k * ((|u| + |b| + 2) * t * gaussPdf (t * u + b) / gaussPdf (t * u' + b')) := by
          gcongr
      _ = (|u| + |b| + 2) * (t ^ (k + 1) * (gaussPdf (t * u + b) / gaussPdf (t * u' + b'))) := by
          ring

/-- The rest of one unit, `restS (t F₁ + F₀) + restD (t² G₂ + t G₁ + G₀)`, divided by
`φ(t u' + b')` with `|u'| < |u|`, tends to `0`. -/
private lemma rest_decay {u u' : ℝ} (h : |u'| < |u|) (b b' F1 F0 G2 G1 G0 : ℝ) :
    Tendsto (fun t => (restS u (t * u + b) * (t * F1 + F0)
      + restD u (t * u + b) * (t ^ 2 * G2 + t * G1 + G0)) / gaussPdf (t * u' + b')) atTop
      (𝓝 0) := by
  have hS := fun k => (rest_decay_aux h b b' k).1
  have hD := fun k => (rest_decay_aux h b b' k).2
  have := (((hS 1).mul_const F1).add ((hS 0).mul_const F0)).add
    ((((hD 2).mul_const G2).add ((hD 1).mul_const G1)).add ((hD 0).mul_const G0))
  simp only [zero_mul, add_zero] at this
  refine this.congr fun t => ?_
  ring

/-- `t / (t u + b) → 1/u`. -/
private lemma tendsto_div_lin {u : ℝ} (hu : u ≠ 0) (b : ℝ) :
    Tendsto (fun t : ℝ => t / (t * u + b)) atTop (𝓝 u⁻¹) := by
  have h : Tendsto (fun t : ℝ => (u + b * t⁻¹)⁻¹) atTop (𝓝 u⁻¹) := by
    have := (tendsto_inv_atTop_zero.const_mul b).const_add u
    rw [mul_zero, add_zero] at this
    exact this.inv₀ hu
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have ht0 := ht.ne'
  rw [show u + b * t⁻¹ = (t * u + b) / t by field_simp, inv_div]

/-- `(t F₁ + F₀) / z² → 0` and `(t² G₂ + t G₁ + G₀) / z³ → 0` for `z = t u + b`, `u ≠ 0`. -/
private lemma tendsto_poly_div {u : ℝ} (hu : u ≠ 0) (b F1 F0 G2 G1 G0 : ℝ) :
    Tendsto (fun t => (t * F1 + F0) / (t * u + b) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun t => (t ^ 2 * G2 + t * G1 + G0) / (t * u + b) ^ 3) atTop (𝓝 0) := by
  have hζ := tendsto_div_lin hu b
  have hι : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hev := (eventually_side hu b).and (eventually_gt_atTop (0 : ℝ))
  constructor
  · have := ((hι.const_mul F1).add ((hι.pow 2).const_mul F0)).mul (hζ.pow 2)
    rw [show (F1 * 0 + F0 * 0 ^ 2) * u⁻¹ ^ 2 = (0 : ℝ) by ring] at this
    refine this.congr' ?_
    filter_upwards [hev] with t ⟨hs, ht⟩
    have ht0 := ht.ne'
    have hz0 : t * u + b ≠ 0 := abs_pos.1 (by linarith [side_abs hs])
    field_simp
  · have := (((hι.const_mul G2).add ((hι.pow 2).const_mul G1)).add
      ((hι.pow 3).const_mul G0)).mul (hζ.pow 3)
    rw [show (G2 * 0 + G1 * 0 ^ 2 + G0 * 0 ^ 3) * u⁻¹ ^ 3 = (0 : ℝ) by ring] at this
    refine this.congr' ?_
    filter_upwards [hev] with t ⟨hs, ht⟩
    have ht0 := ht.ne'
    have hz0 : t * u + b ≠ 0 := abs_pos.1 (by linarith [side_abs hs])
    field_simp

/-- Far out, `|R/φ(z) - (-f + (z - 1/z) g)| ≤ |f/z²| + |g/z³|` for the rest
`R = restS f + restD g` of a unit. -/
private lemma rest_exact_bound {u z : ℝ} (hz : (0 < u ∧ 1 ≤ z) ∨ (u < 0 ∧ z ≤ -1)) (f g : ℝ) :
    |(restS u z * f + restD u z * g) / gaussPdf z - (-f + (z - 1 / z) * g)|
      ≤ |f / z ^ 2| + |g / z ^ 3| := by
  obtain ⟨e1, e2⟩ := rest_bounds hz
  have hp := gaussPdf_pos z
  -- the difference is `((restS + φ)/φ) f + ((restD - φ (z - 1/z))/φ) g`
  have key : (restS u z * f + restD u z * g) / gaussPdf z - (-f + (z - 1 / z) * g)
      = ((restS u z + gaussPdf z) / gaussPdf z) * f
        + ((restD u z - gaussPdf z * (z - 1 / z)) / gaussPdf z) * g := by
    field_simp
    ring
  have hA : |(restS u z + gaussPdf z) / gaussPdf z| ≤ 1 / z ^ 2 := by
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    calc |restS u z + gaussPdf z| ≤ gaussPdf z / z ^ 2 := e1
      _ = 1 / z ^ 2 * gaussPdf z := by ring
  have hB : |(restD u z - gaussPdf z * (z - 1 / z)) / gaussPdf z| ≤ 1 / |z| ^ 3 := by
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    calc |restD u z - gaussPdf z * (z - 1 / z)| ≤ gaussPdf z / |z| ^ 3 := e2
      _ = 1 / |z| ^ 3 * gaussPdf z := by ring
  rw [key]
  calc _ ≤ |(restS u z + gaussPdf z) / gaussPdf z * f|
        + |(restD u z - gaussPdf z * (z - 1 / z)) / gaussPdf z * g| := abs_add_le _ _
    _ = |(restS u z + gaussPdf z) / gaussPdf z| * |f|
        + |(restD u z - gaussPdf z * (z - 1 / z)) / gaussPdf z| * |g| := by
          rw [abs_mul, abs_mul]
    _ ≤ 1 / z ^ 2 * |f| + 1 / |z| ^ 3 * |g| := by gcongr
    _ = |f / z ^ 2| + |g / z ^ 3| := by
          rw [abs_div, abs_div, abs_pow, abs_pow, sq_abs]; ring

/-- **The rest of unit `j` relative to `φ(z_j)`**: `R_j / φ(z_j) = -f + (z - 1/z) g + o(1)`
(`z = t u + b`, `f = t F₁ + F₀`, `g = t² G₂ + t G₁ + G₀`). -/
private lemma rest_exact {u : ℝ} (hu : u ≠ 0) (b F1 F0 G2 G1 G0 : ℝ) :
    Tendsto (fun t => (restS u (t * u + b) * (t * F1 + F0)
      + restD u (t * u + b) * (t ^ 2 * G2 + t * G1 + G0)) / gaussPdf (t * u + b)
      - (-(t * F1 + F0) + ((t * u + b) - 1 / (t * u + b)) * (t ^ 2 * G2 + t * G1 + G0)))
      atTop (𝓝 0) := by
  obtain ⟨h1, h2⟩ := tendsto_poly_div hu b F1 F0 G2 G1 G0
  have hb := h1.abs.add h2.abs
  rw [abs_zero, add_zero] at hb
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_side hu b] with t hs
  rw [Real.norm_eq_abs]
  exact rest_exact_bound hs _ _

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

/-- **The coefficients of the slowest unit**: if `-f + (z - 1/z) g → 0` (`z = t u + b`, `u ≠ 0`,
`f = t F₁ + F₀`, `g = t² G₂ + t G₁ + G₀`), then `G₂ = 0`, `G₁ = 0`, `F₁ = u G₀`, `F₀ = b G₀`.
Multiplied by `z/t → u`, the function is `P(t)/t` for the quartic `P = -z f + (z² - 1) g`, so
the coefficients of `t⁴, t³, t², t` in `P` vanish. -/
private lemma coeffs_of_tendsto {u : ℝ} (hu : u ≠ 0) {b F1 F0 G2 G1 G0 : ℝ}
    (h : Tendsto (fun t => -(t * F1 + F0) + ((t * u + b) - 1 / (t * u + b))
      * (t ^ 2 * G2 + t * G1 + G0)) atTop (𝓝 0)) :
    G2 = 0 ∧ G1 = 0 ∧ F1 = u * G0 ∧ F0 = b * G0 := by
  have hzt : Tendsto (fun t : ℝ => (t * u + b) / t) atTop (𝓝 u) := by
    have := (tendsto_inv_atTop_zero.const_mul b).const_add u
    rw [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have ht0 := ht.ne'
    field_simp
  have hc0 : Tendsto (fun t : ℝ => (b ^ 2 * G0 - b * F0 - G0) * t⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (b ^ 2 * G0 - b * F0 - G0)
  have hP := (hzt.mul h).sub hc0
  rw [mul_zero, sub_zero] at hP
  obtain ⟨c4, c3, c2, c1⟩ := cubic_eq_zero (c3 := u ^ 2 * G2) (c2 := u ^ 2 * G1 + 2 * u * b * G2)
    (c1 := u ^ 2 * G0 + 2 * u * b * G1 + b ^ 2 * G2 - u * F1 - G2)
    (c0 := 2 * u * b * G0 + b ^ 2 * G1 - u * F0 - b * F1 - G1) (hP.congr' (by
      filter_upwards [eventually_gt_atTop 0, eventually_side hu b] with t ht hs
      have ht0 := ht.ne'
      have hz0 : t * u + b ≠ 0 := abs_pos.1 (by linarith [side_abs hs])
      field_simp
      ring))
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
  -- `t⁴`, `t³`, `t²`, `t`, in this order
  have hG2 : G2 = 0 := (mul_eq_zero.1 c4).resolve_left hu2
  have hG1 : G1 = 0 := by
    have : u ^ 2 * G1 = 0 := by rw [hG2] at c3; linarith
    exact (mul_eq_zero.1 this).resolve_left hu2
  have hF1 : F1 = u * G0 := by
    have : u * (u * G0 - F1) = 0 := by rw [hG1, hG2] at c2; linear_combination c2
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hu)).symm
  have hF0 : F0 = b * G0 := by
    have : u * (b * G0 - F0) = 0 := by linear_combination c1 + b * hF1 + (1 - b ^ 2) * hG1
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hu)).symm
  exact ⟨hG2, hG1, hF1, hF0⟩

/-- **The ray argument**, in one output coordinate. Along a ray the identity reads
`t V + C + ∑ᵢ [σ(t uᵢ + bᵢ) (t F₁ᵢ + F₀ᵢ) + σ'(t uᵢ + bᵢ) (t² G₂ᵢ + t G₁ᵢ + G₀ᵢ)] = 0`. If
`u_j ≠ 0` and `|u_j| < |u_i|` for all `i ≠ j`, then `G₂ⱼ = 0`, `G₁ⱼ = 0`, `F₁ⱼ = uⱼ G₀ⱼ` and
`F₀ⱼ = bⱼ G₀ⱼ`. -/
private lemma ray_coeffs {q : Type*} [Fintype q] [DecidableEq q]
    (u b F1 F0 G2 G1 G0 : q → ℝ) (V C : ℝ) (j : q)
    (huj : u j ≠ 0) (hk : ∀ i, i ≠ j → |u j| < |u i|)
    (hJ : ∀ t : ℝ, t * V + C + ∑ i, (gelu (t * u i + b i) * (t * F1 i + F0 i)
      + geluDeriv (t * u i + b i) * (t ^ 2 * G2 i + t * G1 i + G0 i)) = 0) :
    G2 j = 0 ∧ G1 j = 0 ∧ F1 j = u j * G0 j ∧ F0 j = b j * G0 j := by
  have hu0 : ∀ i, u i ≠ 0 := fun i => by
    by_cases hi : i = j
    · subst hi; exact huj
    · exact abs_pos.1 ((abs_nonneg _).trans_lt (hk i hi))
  -- the rest of unit `i` along the ray
  let R : q → ℝ → ℝ := fun i t => restS (u i) (t * u i + b i) * (t * F1 i + F0 i)
      + restD (u i) (t * u i + b i) * (t ^ 2 * G2 i + t * G1 i + G0 i)
  -- the coefficients of the polynomial part (units with `u_i > 0` contribute `z_i f_i + g_i`)
  set K2 : ℝ := ∑ i, (if 0 < u i then u i * F1 i + G2 i else 0) with hK2
  set K1 : ℝ := V + ∑ i, (if 0 < u i then u i * F0 i + b i * F1 i + G1 i else 0) with hK1
  set K0 : ℝ := C + ∑ i, (if 0 < u i then b i * F0 i + G0 i else 0) with hK0
  have hsplit : ∀ t, K2 * t ^ 2 + K1 * t + K0 + ∑ i, R i t = 0 := fun t => by
    rw [← hJ t]
    have e : ∀ i, gelu (t * u i + b i) * (t * F1 i + F0 i)
        + geluDeriv (t * u i + b i) * (t ^ 2 * G2 i + t * G1 i + G0 i)
        = (if 0 < u i then u i * F1 i + G2 i else 0) * t ^ 2
          + (if 0 < u i then u i * F0 i + b i * F1 i + G1 i else 0) * t
          + (if 0 < u i then b i * F0 i + G0 i else 0) + R i t := fun i => by
      simp only [R, restS, restD]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun i _ => e i]
    simp only [hK2, hK1, hK0, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  -- (i) the rests tend to `0` (compare with `φ(0)`), so the polynomial part vanishes identically
  have hR0 : Tendsto (fun t => ∑ i, R i t) atTop (𝓝 0) := by
    have := (tendsto_finsetSum (Finset.univ : Finset q) fun i _ =>
      rest_decay (u := u i) (u' := 0) (b' := 0) (by rw [abs_zero]; exact abs_pos.2 (hu0 i))
        (b i) (F1 i) (F0 i) (G2 i) (G1 i) (G0 i)).mul_const (gaussPdf 0)
    simp only [Finset.sum_const_zero, zero_mul] at this
    refine this.congr fun t => ?_
    rw [Finset.sum_mul]
    simp only [mul_zero, add_zero]
    exact Finset.sum_congr rfl fun i _ => div_mul_cancel₀ _ (gaussPdf_pos 0).ne'
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
  -- (ii) divide by `φ(z_j)`: the rests of the other units decay, that of unit `j` is
  -- `-f_j + (z_j - 1/z_j) g_j + o(1)`
  let Hj : ℝ → ℝ := fun t => -(t * F1 j + F0 j) + ((t * u j + b j) - 1 / (t * u j + b j))
    * (t ^ 2 * G2 j + t * G1 j + G0 j)
  have hlim : Tendsto (fun t => ∑ i, (R i t / gaussPdf (t * u j + b j)
      - if i = j then Hj t else 0)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset q) fun i (_ : i ∈ Finset.univ) =>
      (show Tendsto (fun t => R i t / gaussPdf (t * u j + b j)
          - if i = j then Hj t else 0) atTop (𝓝 0) from by
        by_cases hi : i = j
        · subst hi
          simp only [ite_true]
          exact rest_exact (hu0 i) (b i) (F1 i) (F0 i) (G2 i) (G1 i) (G0 i)
        · simp only [ite_eq_right hi, sub_zero]
          exact rest_decay (hk i hi) (b i) (b j) (F1 i) (F0 i) (G2 i) (G1 i) (G0 i))
    simpa only [Finset.sum_const_zero] using this
  have hH : Tendsto (fun t => -Hj t) atTop (𝓝 0) :=
    hlim.congr fun t => by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, hRz t, zero_div, Finset.sum_ite_eq',
        ite_eq_left (Finset.mem_univ j), zero_sub]
  have hH' := hH.neg
  rw [neg_zero] at hH'
  exact coeffs_of_tendsto huj (hH'.congr fun t => neg_neg _)

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
        ((gelu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i)) • ψa i
          + (geluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i)) • a i
          + (gelu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i)) • a i) = 0)
    (ν : n → ℝ) (o : k) (t : ℝ) :
    t * (ν ᵥ* ψM) o + ψγ o + ∑ i, (gelu (t * (ν ⬝ᵥ c i) + β i)
        * (t * ((ν ⬝ᵥ e i) * ψa i o + (ν ⬝ᵥ ψe i) * a i o) + (β' i * ψa i o + ψβ' i * a i o))
      + geluDeriv (t * (ν ⬝ᵥ c i) + β i)
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
`x = t ν` gives, in every output coordinate `o`: `(ν ψ_{c_j}) (ν e_j) a_j = 0`,
`((ν ψ_{c_j}) β'_j + ψ_{β_j} (ν e_j)) a_j = 0`,
`(ν e_j) ψ_{a_j} + (ν ψ_{e_j}) a_j = (ν c_j) ψ_{β_j} β'_j a_j` and
`β'_j ψ_{a_j} + ψ_{β'_j} a_j = β_j ψ_{β_j} β'_j a_j`. -/
private lemma unit_coeffs {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (e : q → n → ℝ) (β' : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψe : q → n → ℝ)
    (ψβ' : q → ℝ) (ψa : q → k → ℝ)
    (h : ∀ x : n → ℝ,
      x ᵥ* ψM + ψγ + ∑ i,
        ((gelu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i)) • ψa i
          + (geluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i)) • a i
          + (gelu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i)) • a i) = 0)
    (j : q) (ν : n → ℝ) (hν : 0 < ν ⬝ᵥ c j ∧ ∀ i, i ≠ j → ν ⬝ᵥ c j < |ν ⬝ᵥ c i|) (o : k) :
    (ν ⬝ᵥ ψc j) * (ν ⬝ᵥ e j) * a j o = 0 ∧
      ((ν ⬝ᵥ ψc j) * β' j + ψβ j * (ν ⬝ᵥ e j)) * a j o = 0 ∧
      (ν ⬝ᵥ e j) * ψa j o + (ν ⬝ᵥ ψe j) * a j o = (ν ⬝ᵥ c j) * (ψβ j * β' j * a j o) ∧
      β' j * ψa j o + ψβ' j * a j o = β j * (ψβ j * β' j * a j o) := by
  classical
  have hk : ∀ i, i ≠ j → |ν ⬝ᵥ c j| < |ν ⬝ᵥ c i| := fun i hi => by
    rw [abs_of_pos hν.1]; exact hν.2 i hi
  exact ray_coeffs (fun i => ν ⬝ᵥ c i) β
    (fun i => (ν ⬝ᵥ e i) * ψa i o + (ν ⬝ᵥ ψe i) * a i o) (fun i => β' i * ψa i o + ψβ' i * a i o)
    (fun i => (ν ⬝ᵥ ψc i) * (ν ⬝ᵥ e i) * a i o)
    (fun i => ((ν ⬝ᵥ ψc i) * β' i + ψβ i * (ν ⬝ᵥ e i)) * a i o) (fun i => ψβ i * β' i * a i o)
    ((ν ᵥ* ψM) o) (ψγ o) j hν.1.ne' hk
    (ray_identity c β e β' a ψM ψγ ψc ψβ ψe ψβ' ψa h ν o)

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
        ((gelu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i)) • ψa i
          + (geluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i)) • a i
          + (gelu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i)) • a i) = 0)
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
  -- `t²`: then `ψ_{β_j} (ν e_j) a_j = 0`, so `ψ_{β_j} = 0`
  have hψβ : ψβ j = 0 := by
    have := (hU ν₀ hν₀ o₀).2.1
    rw [hψc, dotProduct_zero, zero_mul, zero_add] at this
    exact (mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_right ho₀)).resolve_right hν₀e
  -- `t`: `a_j(o) ψ_{e_j} + ψ_{a_j}(o) e_j` is orthogonal to all good directions, so it vanishes
  have hr : ∀ o, a j o • ψe j + ψa j o • e j = 0 := fun o =>
    eq_zero_of_good c (e j) hc hcol (he j) j _ fun ν hν hνe => by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      linear_combination (hU ν hν o).2.2.1 + (ν ⬝ᵥ c j) * β' j * a j o * hψβ
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
  -- `1`: `β'_j ψ_{a_j} + ψ_{β'_j} a_j = 0`, so `ψ_{β'_j} = -α β'_j`
  have hψβ' : ψβ' j = -(ψa j o₀ / a j o₀) * β' j := by
    have := (hU ν₀ hν₀ o₀).2.2.2
    rw [hψβ] at this
    rw [show -(ψa j o₀ / a j o₀) * β' j = -(β' j * ψa j o₀) / a j o₀ by ring, eq_div_iff ho₀]
    linear_combination this
  exact ⟨hψe, hψβ', hψa⟩

/-- **Lemma C.3 for GeGLU,** without the hypothesis on proportionality. Rows are indexed by `n`
(the coordinates of an input `x`), hidden units by `q`, and the coordinates of the output by
`k`. -/
theorem gelu_gated_units_flat_of_value_ne_zero {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (e : q → n → ℝ) (β' : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψe : q → n → ℝ)
    (ψβ' : q → ℝ) (ψa : q → k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j)
    (he : ∀ i, e i ≠ 0)
    (h : ∀ x : n → ℝ,
      x ᵥ* ψM + ψγ + ∑ i,
        ((gelu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i)) • ψa i
          + (geluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i)) • a i
          + (gelu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i)) • a i) = 0) :
    ψM = 0 ∧ ψγ = 0 ∧ ψc = 0 ∧ ψβ = 0 ∧
      ∃ α : q → ℝ, ∀ i, ψe i = -(α i) • e i ∧ ψβ' i = -(α i) * β' i ∧ ψa i = α i • a i := by
  classical
  -- every unit only rescales its value
  choose hψc hψβ α hα using
    unit_rescale c β e β' a ψM ψγ ψc ψβ ψe ψβ' ψa ha hc hcol he h
  -- so every unit term vanishes, and what is left is `x ψ_M + ψ_γ = 0` for all `x`
  have hlin : ∀ x : n → ℝ, x ᵥ* ψM + ψγ = 0 := fun x => by
    have hz : ∀ i, (gelu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i)) • ψa i
        + (geluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i)) • a i
        + (gelu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i)) • a i = 0 := fun i => by
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

/-- **Lemma C.3 for GeGLU, as the paper states it,** with the hypothesis that `(e_i, β'_i)` is not
proportional to `(c_i, β_i)`. -/
theorem gelu_gated_units_flat {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (e : q → n → ℝ) (β' : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψe : q → n → ℝ)
    (ψβ' : q → ℝ) (ψa : q → k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j)
    (he : ∀ i, e i ≠ 0) (_hec : ∀ i, ∀ r : ℝ, (e i, β' i) ≠ r • (c i, β i))
    (h : ∀ x : n → ℝ,
      x ᵥ* ψM + ψγ + ∑ i,
        ((gelu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i)) • ψa i
          + (geluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i)) • a i
          + (gelu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i)) • a i) = 0) :
    ψM = 0 ∧ ψγ = 0 ∧ ψc = 0 ∧ ψβ = 0 ∧
      ∃ α : q → ℝ, ∀ i, ψe i = -(α i) • e i ∧ ψβ' i = -(α i) * β' i ∧ ψa i = α i • a i :=
  gelu_gated_units_flat_of_value_ne_zero c β e β' a ψM ψγ ψc ψβ ψe ψβ' ψa ha hc hcol he h

end Skips
