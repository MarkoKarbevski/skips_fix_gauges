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

/-- **"From `J_a h_b = J_b h_a`, `h_a` divides `J_a`, so `J = c h_1`", for two polynomials of
degree at most two without a common root:** if `j(t) r(t) = k(t) p(t)` for all small `t`, with
`j`, `k`, `p`, `r` of degree at most two and the resultant of `p` and `r` not zero, then
`j = c p` and `k = c r` for one number `c`. -/
theorem quad_proportional_of_quadRes_ne_zero {p₀ p₁ p₂ r₀ r₁ r₂ j₀ j₁ j₂ k₀ k₁ k₂ δ : ℝ}
    (hres : quadRes p₀ p₁ p₂ r₀ r₁ r₂ ≠ 0) (hδ : 0 < δ)
    (h : ∀ t : ℝ, |t| < δ → (j₀ + j₁ * t + j₂ * t ^ 2) * (r₀ + r₁ * t + r₂ * t ^ 2)
      = (k₀ + k₁ * t + k₂ * t ^ 2) * (p₀ + p₁ * t + p₂ * t ^ 2)) :
    ∃ c : ℝ, j₀ = c * p₀ ∧ j₁ = c * p₁ ∧ j₂ = c * p₂ ∧ k₀ = c * r₀ ∧ k₁ = c * r₁ ∧ k₂ = c * r₂ := by
  sorry

/-- **The same for vectors:** let `J(t) = J₀ + t J₁ + t² J₂` and `h(t) = P₀ + t P₁ + t² P₂` be
vectors with polynomial entries of degree at most two. If `J(t)` is a multiple of `h(t)` for all
small `t`, and the entries `e` and `f` of `h` have a resultant that is not zero, then `J = c h`
for one number `c`: `J₀ = c P₀`, `J₁ = c P₁`, `J₂ = c P₂`. -/
theorem quad_vec_proportional_of_quadRes_ne_zero {m : Type*} {P₀ P₁ P₂ J₀ J₁ J₂ : m → ℝ}
    {e f : m} {δ : ℝ}
    (hres : quadRes (P₀ e) (P₁ e) (P₂ e) (P₀ f) (P₁ f) (P₂ f) ≠ 0) (hδ : 0 < δ)
    (h : ∀ t : ℝ, |t| < δ → ∃ μ : ℝ, J₀ + t • J₁ + t ^ 2 • J₂ = μ • (P₀ + t • P₁ + t ^ 2 • P₂)) :
    ∃ c : ℝ, J₀ = c • P₀ ∧ J₁ = c • P₁ ∧ J₂ = c • P₂ := by
  sorry

end Skips
