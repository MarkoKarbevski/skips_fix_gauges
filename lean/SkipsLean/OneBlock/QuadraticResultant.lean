import SkipsLean.Imports

/-!
# Two quadratic polynomials without a common root

Paper (skips paper), proof of Theorem B.1 (iv), "The skipless network: equality", "One scale":
"On a region where at least two units are active, the entries of `J` and of `h_1` are homogeneous
polynomials of degree `k` in `x`, and for generic parameters two entries `h_a` and `h_b` of `h_1`
have no common factor. From `J_a h_b = J_b h_a`, `h_a` divides `J_a`, so `J = c h_1` for a number
`c`, and `μ = c` on the region."

For `k = 2` (ReLU²) the library takes this step on a line `t ↦ x + t v` through the region, where
the entries of `h_1` and of `J` are polynomials of degree at most two in `t`:

* `quadRes p₀ p₁ p₂ r₀ r₁ r₂`: the resultant of `p₀ + p₁ t + p₂ t²` and `r₀ + r₁ t + r₂ t²`; it
  is not zero exactly when the two have no common root, real or complex or at infinity (the
  statements below use only that it is not zero);
* `quad_proportional_of_quadRes_ne_zero`: "From `J_a h_b = J_b h_a`, `h_a` divides `J_a`, so
  `J = c h_1`", for polynomials of degree at most two with `quadRes ≠ 0`, the identity being
  asked for small `t` only;
* `quad_vec_proportional_of_quadRes_ne_zero`: the same for vectors: if `J(t)` is a multiple of
  `h(t)` for all small `t` and two entries of `h` have `quadRes ≠ 0`, then `J = c h` with one
  number `c`.

Symbolic check of the first: the five coefficient equations have rank five, with every maximal
minor the resultant times a coefficient of `(h_a, h_b)`.
-/

namespace Skips

/-- The resultant of the quadratic polynomials `p₀ + p₁ t + p₂ t²` and `r₀ + r₁ t + r₂ t²`. -/
def quadRes (p₀ p₁ p₂ r₀ r₁ r₂ : ℝ) : ℝ :=
  (p₀ * r₂ - p₂ * r₀) ^ 2 - (p₀ * r₁ - p₁ * r₀) * (p₁ * r₂ - p₂ * r₁)

/-- **The five coefficients of `j r − k p` vanish:** a polynomial of degree at most four in `t`
that vanishes for `|t| < δ` vanishes at `t = 0, ±s, ±2s` (`s = δ/3`), and these five values give
its coefficients. -/
private lemma coeffs_qr {p₀ p₁ p₂ r₀ r₁ r₂ j₀ j₁ j₂ k₀ k₁ k₂ δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t : ℝ, |t| < δ → (j₀ + j₁ * t + j₂ * t ^ 2) * (r₀ + r₁ * t + r₂ * t ^ 2)
      = (k₀ + k₁ * t + k₂ * t ^ 2) * (p₀ + p₁ * t + p₂ * t ^ 2)) :
    j₀ * r₀ - k₀ * p₀ = 0 ∧ j₀ * r₁ + j₁ * r₀ - k₀ * p₁ - k₁ * p₀ = 0 ∧
      j₀ * r₂ + j₁ * r₁ + j₂ * r₀ - k₀ * p₂ - k₁ * p₁ - k₂ * p₀ = 0 ∧
      j₁ * r₂ + j₂ * r₁ - k₁ * p₂ - k₂ * p₁ = 0 ∧ j₂ * r₂ - k₂ * p₂ = 0 := by
  obtain ⟨s, hs, hsδ⟩ : ∃ s : ℝ, 0 < s ∧ 2 * s < δ := ⟨δ / 3, by positivity, by linarith⟩
  have h0 := h 0 (by rw [abs_zero]; exact hδ)
  have h1 := h s (abs_lt.2 ⟨by linarith, by linarith⟩)
  have hm1 := h (-s) (abs_lt.2 ⟨by linarith, by linarith⟩)
  have h2 := h (2 * s) (abs_lt.2 ⟨by linarith, by linarith⟩)
  have hm2 := h (-(2 * s)) (abs_lt.2 ⟨by linarith, by linarith⟩)
  -- the coefficient of `t^k`, times `s^k`, is a combination of the five values
  have e1 : 12 * s * (j₀ * r₁ + j₁ * r₀ - k₀ * p₁ - k₁ * p₀) = 0 := by
    linear_combination 8 * h1 - 8 * hm1 - h2 + hm2
  have e2 : 24 * s ^ 2 * (j₀ * r₂ + j₁ * r₁ + j₂ * r₀ - k₀ * p₂ - k₁ * p₁ - k₂ * p₀) = 0 := by
    linear_combination 16 * h1 + 16 * hm1 - h2 - hm2 - 30 * h0
  have e3 : 12 * s ^ 3 * (j₁ * r₂ + j₂ * r₁ - k₁ * p₂ - k₂ * p₁) = 0 := by
    linear_combination h2 - hm2 - 2 * h1 + 2 * hm1
  have e4 : 24 * s ^ 4 * (j₂ * r₂ - k₂ * p₂) = 0 := by
    linear_combination h2 + hm2 - 4 * h1 - 4 * hm1 + 6 * h0
  refine ⟨by linear_combination h0, (mul_eq_zero.1 e1).resolve_left (by positivity),
    (mul_eq_zero.1 e2).resolve_left (by positivity), (mul_eq_zero.1 e3).resolve_left
    (by positivity), (mul_eq_zero.1 e4).resolve_left (by positivity)⟩

/-- `w_l = (w_k / u_k) u_l` from `w_k u_l = w_l u_k`. -/
private lemma div_mul_of_qr {wk uk wl ul : ℝ} (hu : uk ≠ 0) (h : wk * ul = wl * uk) :
    wl = wk / uk * ul := by
  rw [div_mul_eq_mul_div, eq_div_iff hu]
  linear_combination -h

/-- **"From `J_a h_b = J_b h_a`, `h_a` divides `J_a`, so `J = c h_1`", for two polynomials of
degree at most two without a common root:** if `j(t) r(t) = k(t) p(t)` for all small `t`, with
`j`, `k`, `p`, `r` of degree at most two and the resultant of `p` and `r` not zero, then
`j = c p` and `k = c r` for one number `c`. -/
theorem quad_proportional_of_quadRes_ne_zero {p₀ p₁ p₂ r₀ r₁ r₂ j₀ j₁ j₂ k₀ k₁ k₂ δ : ℝ}
    (hres : quadRes p₀ p₁ p₂ r₀ r₁ r₂ ≠ 0) (hδ : 0 < δ)
    (h : ∀ t : ℝ, |t| < δ → (j₀ + j₁ * t + j₂ * t ^ 2) * (r₀ + r₁ * t + r₂ * t ^ 2)
      = (k₀ + k₁ * t + k₂ * t ^ 2) * (p₀ + p₁ * t + p₂ * t ^ 2)) :
    ∃ c : ℝ, j₀ = c * p₀ ∧ j₁ = c * p₁ ∧ j₂ = c * p₂ ∧ k₀ = c * r₀ ∧ k₁ = c * r₁ ∧ k₂ = c * r₂ := by
  obtain ⟨E0, E1, E2, E3, E4⟩ := coeffs_qr hδ h
  -- `quadRes * (w_k u_l - w_l u_k)` is a combination of the five coefficients, for
  -- `w = (j₀, j₁, j₂, k₀, k₁, k₂)` and `u = (p₀, p₁, p₂, r₀, r₁, r₂)`
  have key : ∀ x y : ℝ,
      ((p₀ * r₂ - p₂ * r₀) ^ 2 - (p₀ * r₁ - p₁ * r₀) * (p₁ * r₂ - p₂ * r₁)) * (x - y) = 0 →
      x = y := fun x y hxy => sub_eq_zero.1 ((mul_eq_zero.1 hxy).resolve_left hres)
  have hj₀j₁ : j₀ * p₁ = j₁ * p₀ := key _ _ (by
    linear_combination (-2*p₀*p₁*p₂*r₂ + p₀*p₂^2*r₁ + p₁^3*r₂ - p₁^2*p₂*r₁ + p₁*p₂^2*r₀) * E0
      + (p₀^2*p₂*r₂ - p₀*p₁^2*r₂ + p₀*p₁*p₂*r₁ - p₀*p₂^2*r₀) * E1
      + (p₀^2*p₁*r₂ - p₀^2*p₂*r₁) * E2
      + (-p₀^3*r₂ + p₀^2*p₂*r₀) * E3
      + (p₀^3*r₁ - p₀^2*p₁*r₀) * E4)
  have hj₀j₂ : j₀ * p₂ = j₂ * p₀ := key _ _ (by
    linear_combination (-p₀*p₂^2*r₂ + p₁^2*p₂*r₂ - p₁*p₂^2*r₁ + p₂^3*r₀) * E0
      + (-p₀*p₁*p₂*r₂ + p₀*p₂^2*r₁) * E1
      + (p₀^2*p₂*r₂ - p₀*p₂^2*r₀) * E2
      + (-p₀^2*p₂*r₁ + p₀*p₁*p₂*r₀) * E3
      + (-p₀^3*r₂ + p₀^2*p₁*r₁ + p₀^2*p₂*r₀ - p₀*p₁^2*r₀) * E4)
  have hj₀k₀ : j₀ * r₀ = k₀ * p₀ := key _ _ (by
    linear_combination (p₀^2*r₂^2 - p₀*p₁*r₁*r₂ - 2*p₀*p₂*r₀*r₂ + p₀*p₂*r₁^2 + p₁^2*r₀*r₂
        - p₁*p₂*r₀*r₁ + p₂^2*r₀^2) * E0)
  have hj₀k₁ : j₀ * r₁ = k₁ * p₀ := key _ _ (by
    linear_combination (-p₀*p₁*r₂^2 + p₁^2*r₁*r₂ - p₁*p₂*r₁^2 + p₂^2*r₀*r₁) * E0
      + (p₀^2*r₂^2 - p₀*p₁*r₁*r₂ - p₀*p₂*r₀*r₂ + p₀*p₂*r₁^2) * E1
      + (p₀*p₁*r₀*r₂ - p₀*p₂*r₀*r₁) * E2
      + (-p₀^2*r₀*r₂ + p₀*p₂*r₀^2) * E3
      + (p₀^2*r₀*r₁ - p₀*p₁*r₀^2) * E4)
  have hj₀k₂ : j₀ * r₂ = k₂ * p₀ := key _ _ (by
    linear_combination (-p₀*p₂*r₂^2 + p₁^2*r₂^2 - p₁*p₂*r₁*r₂ + p₂^2*r₀*r₂) * E0
      + (-p₀*p₁*r₂^2 + p₀*p₂*r₁*r₂) * E1
      + (p₀^2*r₂^2 - p₀*p₂*r₀*r₂) * E2
      + (-p₀^2*r₁*r₂ + p₀*p₁*r₀*r₂) * E3
      + (-p₀^2*r₀*r₂ + p₀^2*r₁^2 - p₀*p₁*r₀*r₁ + p₀*p₂*r₀^2) * E4)
  have hj₁j₂ : j₁ * p₂ = j₂ * p₁ := key _ _ (by
    linear_combination (p₁*p₂^2*r₂ - p₂^3*r₁) * E0
      + (-p₀*p₂^2*r₂ + p₂^3*r₀) * E1
      + (p₀*p₂^2*r₁ - p₁*p₂^2*r₀) * E2
      + (p₀^2*p₂*r₂ - p₀*p₁*p₂*r₁ - p₀*p₂^2*r₀ + p₁^2*p₂*r₀) * E3
      + (-p₀^2*p₁*r₂ - p₀^2*p₂*r₁ + p₀*p₁^2*r₁ + 2*p₀*p₁*p₂*r₀ - p₁^3*r₀) * E4)
  have hj₁k₀ : j₁ * r₀ = k₀ * p₁ := key _ _ (by
    linear_combination (p₀*p₁*r₂^2 - p₁^2*r₁*r₂ + p₁*p₂*r₁^2 - p₂^2*r₀*r₁) * E0
      + (-p₀*p₂*r₀*r₂ + p₁^2*r₀*r₂ - p₁*p₂*r₀*r₁ + p₂^2*r₀^2) * E1
      + (-p₀*p₁*r₀*r₂ + p₀*p₂*r₀*r₁) * E2
      + (p₀^2*r₀*r₂ - p₀*p₂*r₀^2) * E3
      + (-p₀^2*r₀*r₁ + p₀*p₁*r₀^2) * E4)
  have hj₁k₁ : j₁ * r₁ = k₁ * p₁ := key _ _ (by
    linear_combination (-p₁^2*r₂^2 + 2*p₁*p₂*r₁*r₂ - p₂^2*r₁^2) * E0
      + (p₀*p₁*r₂^2 - p₀*p₂*r₁*r₂ - p₁*p₂*r₀*r₂ + p₂^2*r₀*r₁) * E1
      + (-p₀*p₁*r₁*r₂ + p₀*p₂*r₁^2 + p₁^2*r₀*r₂ - p₁*p₂*r₀*r₁) * E2
      + (p₀^2*r₁*r₂ - p₀*p₁*r₀*r₂ - p₀*p₂*r₀*r₁ + p₁*p₂*r₀^2) * E3
      + (-p₀^2*r₁^2 + 2*p₀*p₁*r₀*r₁ - p₁^2*r₀^2) * E4)
  have hj₁k₂ : j₁ * r₂ = k₂ * p₁ := key _ _ (by
    linear_combination (p₁*p₂*r₂^2 - p₂^2*r₁*r₂) * E0
      + (-p₀*p₂*r₂^2 + p₂^2*r₀*r₂) * E1
      + (p₀*p₂*r₁*r₂ - p₁*p₂*r₀*r₂) * E2
      + (p₀^2*r₂^2 - p₀*p₁*r₁*r₂ - p₀*p₂*r₀*r₂ + p₁^2*r₀*r₂) * E3
      + (-p₀^2*r₁*r₂ + p₀*p₁*r₁^2 - p₁^2*r₀*r₁ + p₁*p₂*r₀^2) * E4)
  have hj₂k₀ : j₂ * r₀ = k₀ * p₂ := key _ _ (by
    linear_combination (p₀*p₂*r₂^2 - p₁*p₂*r₁*r₂ - p₂^2*r₀*r₂ + p₂^2*r₁^2) * E0
      + (p₁*p₂*r₀*r₂ - p₂^2*r₀*r₁) * E1
      + (-p₀*p₂*r₀*r₂ + p₂^2*r₀^2) * E2
      + (p₀*p₂*r₀*r₁ - p₁*p₂*r₀^2) * E3
      + (p₀^2*r₀*r₂ - p₀*p₁*r₀*r₁ - p₀*p₂*r₀^2 + p₁^2*r₀^2) * E4)
  have hj₂k₁ : j₂ * r₁ = k₁ * p₂ := key _ _ (by
    linear_combination (-p₁*p₂*r₂^2 + p₂^2*r₁*r₂) * E0
      + (p₀*p₂*r₂^2 - p₂^2*r₀*r₂) * E1
      + (-p₀*p₂*r₁*r₂ + p₁*p₂*r₀*r₂) * E2
      + (-p₀*p₂*r₀*r₂ + p₀*p₂*r₁^2 - p₁*p₂*r₀*r₁ + p₂^2*r₀^2) * E3
      + (p₀^2*r₁*r₂ - p₀*p₁*r₁^2 + p₁^2*r₀*r₁ - p₁*p₂*r₀^2) * E4)
  have hj₂k₂ : j₂ * r₂ = k₂ * p₂ := key _ _ (by
    linear_combination (p₀^2*r₂^2 - p₀*p₁*r₁*r₂ - 2*p₀*p₂*r₀*r₂ + p₀*p₂*r₁^2 + p₁^2*r₀*r₂
        - p₁*p₂*r₀*r₁ + p₂^2*r₀^2) * E4)
  have hk₀k₁ : k₀ * r₁ = k₁ * r₀ := key _ _ (by
    linear_combination (-p₀*r₁*r₂^2 - p₁*r₀*r₂^2 + p₁*r₁^2*r₂ + 2*p₂*r₀*r₁*r₂ - p₂*r₁^3) * E0
      + (p₀*r₀*r₂^2 - p₁*r₀*r₁*r₂ - p₂*r₀^2*r₂ + p₂*r₀*r₁^2) * E1
      + (p₁*r₀^2*r₂ - p₂*r₀^2*r₁) * E2
      + (-p₀*r₀^2*r₂ + p₂*r₀^3) * E3
      + (p₀*r₀^2*r₁ - p₁*r₀^3) * E4)
  have hk₀k₂ : k₀ * r₂ = k₂ * r₀ := key _ _ (by
    linear_combination (-p₀*r₂^3 + p₁*r₁*r₂^2 + p₂*r₀*r₂^2 - p₂*r₁^2*r₂) * E0
      + (-p₁*r₀*r₂^2 + p₂*r₀*r₁*r₂) * E1
      + (p₀*r₀*r₂^2 - p₂*r₀^2*r₂) * E2
      + (-p₀*r₀*r₁*r₂ + p₁*r₀^2*r₂) * E3
      + (-p₀*r₀^2*r₂ + p₀*r₀*r₁^2 - p₁*r₀^2*r₁ + p₂*r₀^3) * E4)
  have hk₁k₂ : k₁ * r₂ = k₂ * r₁ := key _ _ (by
    linear_combination (p₁*r₂^3 - p₂*r₁*r₂^2) * E0
      + (-p₀*r₂^3 + p₂*r₀*r₂^2) * E1
      + (p₀*r₁*r₂^2 - p₁*r₀*r₂^2) * E2
      + (p₀*r₀*r₂^2 - p₀*r₁^2*r₂ + p₁*r₀*r₁*r₂ - p₂*r₀^2*r₂) * E3
      + (-2*p₀*r₀*r₁*r₂ + p₀*r₁^3 + p₁*r₀^2*r₂ - p₁*r₀*r₁^2 + p₂*r₀^2*r₁) * E4)
  -- `w = c u` with `c = w_k / u_k` for an entry `u_k ≠ 0`
  by_cases hp₀ : p₀ ≠ 0
  · exact ⟨j₀ / p₀, (div_mul_cancel₀ _ hp₀).symm, div_mul_of_qr hp₀ hj₀j₁,
      div_mul_of_qr hp₀ hj₀j₂, div_mul_of_qr hp₀ hj₀k₀, div_mul_of_qr hp₀ hj₀k₁,
      div_mul_of_qr hp₀ hj₀k₂⟩
  by_cases hp₁ : p₁ ≠ 0
  · exact ⟨j₁ / p₁, div_mul_of_qr hp₁ hj₀j₁.symm, (div_mul_cancel₀ _ hp₁).symm,
      div_mul_of_qr hp₁ hj₁j₂, div_mul_of_qr hp₁ hj₁k₀, div_mul_of_qr hp₁ hj₁k₁,
      div_mul_of_qr hp₁ hj₁k₂⟩
  by_cases hp₂ : p₂ ≠ 0
  · exact ⟨j₂ / p₂, div_mul_of_qr hp₂ hj₀j₂.symm, div_mul_of_qr hp₂ hj₁j₂.symm,
      (div_mul_cancel₀ _ hp₂).symm, div_mul_of_qr hp₂ hj₂k₀, div_mul_of_qr hp₂ hj₂k₁,
      div_mul_of_qr hp₂ hj₂k₂⟩
  by_cases hr₀ : r₀ ≠ 0
  · exact ⟨k₀ / r₀, div_mul_of_qr hr₀ hj₀k₀.symm, div_mul_of_qr hr₀ hj₁k₀.symm,
      div_mul_of_qr hr₀ hj₂k₀.symm, (div_mul_cancel₀ _ hr₀).symm, div_mul_of_qr hr₀ hk₀k₁,
      div_mul_of_qr hr₀ hk₀k₂⟩
  by_cases hr₁ : r₁ ≠ 0
  · exact ⟨k₁ / r₁, div_mul_of_qr hr₁ hj₀k₁.symm, div_mul_of_qr hr₁ hj₁k₁.symm,
      div_mul_of_qr hr₁ hj₂k₁.symm, div_mul_of_qr hr₁ hk₀k₁.symm, (div_mul_cancel₀ _ hr₁).symm,
      div_mul_of_qr hr₁ hk₁k₂⟩
  by_cases hr₂ : r₂ ≠ 0
  · exact ⟨k₂ / r₂, div_mul_of_qr hr₂ hj₀k₂.symm, div_mul_of_qr hr₂ hj₁k₂.symm,
      div_mul_of_qr hr₂ hj₂k₂.symm, div_mul_of_qr hr₂ hk₀k₂.symm, div_mul_of_qr hr₂ hk₁k₂.symm,
      (div_mul_cancel₀ _ hr₂).symm⟩
  -- `u = 0` is excluded: then the resultant is `0`
  simp only [not_not] at hp₀ hp₁ hp₂ hr₀ hr₁ hr₂
  exact absurd (by rw [hp₀, hp₁, hp₂, hr₀, hr₁, hr₂, quadRes]; ring) hres

/-- **The vector statement from the `2 × 2` minors:** if every minor
`J(t)_g h(t)_{g'} − J(t)_{g'} h(t)_g` vanishes for small `t` and the entries `e`, `f` of `h` have a
resultant that is not zero, then `J = c h`. The scalar statement for `(e, f)` gives `c`; for another
entry `g`, it applied to `j = J_g − c h_g`, `k = 0` gives `j = c' h_e` and `0 = c' h_f`, and
`h_f ≠ 0`. -/
private lemma vec_of_minors_qr {m : Type*} {P₀ P₁ P₂ J₀ J₁ J₂ : m → ℝ} {e f : m} {δ : ℝ}
    (hres : quadRes (P₀ e) (P₁ e) (P₂ e) (P₀ f) (P₁ f) (P₂ f) ≠ 0) (hδ : 0 < δ)
    (h : ∀ t : ℝ, |t| < δ → ∀ g g' : m,
      (J₀ g + t * J₁ g + t ^ 2 * J₂ g) * (P₀ g' + t * P₁ g' + t ^ 2 * P₂ g')
        = (J₀ g' + t * J₁ g' + t ^ 2 * J₂ g') * (P₀ g + t * P₁ g + t ^ 2 * P₂ g)) :
    ∃ c : ℝ, J₀ = c • P₀ ∧ J₁ = c • P₁ ∧ J₂ = c • P₂ := by
  obtain ⟨c, -, -, -, hf₀, hf₁, hf₂⟩ := quad_proportional_of_quadRes_ne_zero
    (j₀ := J₀ e) (j₁ := J₁ e) (j₂ := J₂ e) (k₀ := J₀ f) (k₁ := J₁ f) (k₂ := J₂ f) hres hδ
    (fun t ht => by linear_combination h t ht e f)
  have hg : ∀ g, J₀ g = c * P₀ g ∧ J₁ g = c * P₁ g ∧ J₂ g = c * P₂ g := by
    intro g
    obtain ⟨c', h₀, h₁, h₂, h₃, h₄, h₅⟩ := quad_proportional_of_quadRes_ne_zero
      (j₀ := J₀ g - c * P₀ g) (j₁ := J₁ g - c * P₁ g) (j₂ := J₂ g - c * P₂ g)
      (k₀ := 0) (k₁ := 0) (k₂ := 0) hres hδ (fun t ht => by
        have hm := h t ht g f
        rw [hf₀, hf₁, hf₂] at hm
        linear_combination hm)
    by_cases hc' : c' = 0
    · rw [hc', zero_mul] at h₀ h₁ h₂
      exact ⟨by linear_combination h₀, by linear_combination h₁, by linear_combination h₂⟩
    · -- else `h_f = 0`, and the resultant is `0`
      have z₀ := (mul_eq_zero.1 h₃.symm).resolve_left hc'
      have z₁ := (mul_eq_zero.1 h₄.symm).resolve_left hc'
      have z₂ := (mul_eq_zero.1 h₅.symm).resolve_left hc'
      exact absurd (by rw [z₀, z₁, z₂, quadRes]; ring) hres
  refine ⟨c, funext fun g => ?_, funext fun g => ?_, funext fun g => ?_⟩
  · exact (hg g).1
  · exact (hg g).2.1
  · exact (hg g).2.2

/-- **The same for vectors:** let `J(t) = J₀ + t J₁ + t² J₂` and `h(t) = P₀ + t P₁ + t² P₂` be
vectors with polynomial entries of degree at most two. If `J(t)` is a multiple of `h(t)` for all
small `t`, and the entries `e` and `f` of `h` have a resultant that is not zero, then `J = c h`
for one number `c`: `J₀ = c P₀`, `J₁ = c P₁`, `J₂ = c P₂`. -/
theorem quad_vec_proportional_of_quadRes_ne_zero {m : Type*} {P₀ P₁ P₂ J₀ J₁ J₂ : m → ℝ}
    {e f : m} {δ : ℝ}
    (hres : quadRes (P₀ e) (P₁ e) (P₂ e) (P₀ f) (P₁ f) (P₂ f) ≠ 0) (hδ : 0 < δ)
    (h : ∀ t : ℝ, |t| < δ → ∃ μ : ℝ, J₀ + t • J₁ + t ^ 2 • J₂ = μ • (P₀ + t • P₁ + t ^ 2 • P₂)) :
    ∃ c : ℝ, J₀ = c • P₀ ∧ J₁ = c • P₁ ∧ J₂ = c • P₂ := by
  refine vec_of_minors_qr hres hδ fun t ht g g' => ?_
  obtain ⟨μ, hμ⟩ := h t ht
  have eg := congrFun hμ g
  have eg' := congrFun hμ g'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at eg eg'
  linear_combination (P₀ g' + t * P₁ g' + t ^ 2 * P₂ g') * eg
    - (P₀ g + t * P₁ g + t ^ 2 * P₂ g) * eg'

end Skips
