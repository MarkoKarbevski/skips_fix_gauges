import SkipsLean.Activations.MillsAtInfinity
import SkipsLean.Depth.RaySeparation

/-!
# The induction on the exponents along a ray

Paper (dimension): Appendix D.5, proof of Lemma D.12, the paragraphs "The expansion", facts (a) to
(c), and "The induction", equations (34) to (36).

On a ray `n = t ξ` the left side of the identity for one block is expanded in the small terms
`δ_j(t)` of the gates: "at `δ = δ(t)` and `δ' = δ'(t)` the term of `δ^α` is of the order of
`e^{-r_α t^p / p}`, up to powers of `t`, and the term of `δ^α δ'_i` of the order of
`e^{-(r_α + r_i) t^p / p}`", with `r_α = ∑_j α_j r_j`. The numbers `r_j` are linearly independent
over `ℚ`, so "different multi-indices have different exponents `r_α`, and only finitely many
exponents lie below any bound." The paper shows by induction on the exponent `r_α` that every
coefficient vanishes: "No small factor, `α = 0`", "One small factor, `α = 1_j`", "Two or more small
factors, `|α| ≥ 2`".

Stated here in a form that does not mention the network. The small terms are positive functions
`ζ_j(t)` that lie between `e^{-r_j t^p}` divided and multiplied by a power of `t` (for the gates,
`ζ_j = δ_j(t)/t` and `r_j = |ξ c_j|^p / p`, by (25) and (32)). The left side of (34), divided by a
power of `t`, is `G₀(1/t, ζ(t)) + ∑_j ν_j(t) ζ_j(t) G_j(1/t, ζ(t))` with maps `G₀`, `G_j` that are
real-analytic at `(0, 0)` (fact (a): the coefficients are meromorphic at infinity) and with
functions `ν_j` that are at most a power of `t` (for the gates, `ν_j = t δ'_j(t)/δ_j(t)`, by (32)).
Fact (b) is the hypothesis `hid`: the left side is smaller than `e^{-R t^p}` for every `R`. The
step "one small factor" depends on the gate (Lemma D.9 for GELU, parity for SiLU) and on the
block (equation (29)); it is the hypothesis `hstep`: if (36) holds for `α = 1_j`, then `G_j`
vanishes. The conclusion is that `G₀` and every `G_j` vanish near `(0, 0)`: all coefficients of the
expansion vanish. Fact (c), the bound on the terms with a larger exponent, is part of the proof.

The values lie in a complete normed space `F` (in the paper, `ℝ^{1×d_out}`). Completeness is
needed: for a space that is not complete, a map that is real-analytic at `(0, 0)` need not be
differentiable at nearby points, and the derivative `∂G₀/∂y_j (1/t, 0)` in `hstep` loses its
meaning.
-/

namespace Skips

open Filter Topology
open scoped Matrix.Norms.Elementwise

/-- **The induction on the exponents** (proof of Lemma D.12, (34) to (36)). Let the rates
`r_j > 0` be linearly independent over `ℚ`, let `ζ_j(t)` lie between `e^{-r_j t^p}` divided and
multiplied by `A t^N`, let `|ν_j(t)| ≤ A t^N`, and let `G₀` and `G_j` be real-analytic at `(0, 0)`.
Suppose that `G₀(1/t, ζ(t)) + ∑_j ν_j(t) ζ_j(t) G_j(1/t, ζ(t))` is, for every `R`, at most
`e^{-R t^p}` for large `t`, and that, for every `j`, `G_j` vanishes near `(0, 0)` as soon as
`∂G₀/∂y_j (1/t, 0) + ν_j(t) G_j(1/t, 0)` tends to `0` faster than every power of `1/t`. Then `G₀`
and every `G_j` vanish near `(0, 0)`. -/
theorem ray_induction {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (p : ℕ) (hp : 1 ≤ p) (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (hrQ : LinearIndependent ℚ r) (ζ ν : ℝ → ι → ℝ) (A : ℝ) (N : ℕ)
    (hζl : ∀ᶠ t : ℝ in atTop, ∀ j, Real.exp (-(r j * t ^ p)) ≤ A * t ^ N * ζ t j)
    (hζu : ∀ᶠ t : ℝ in atTop, ∀ j, |ζ t j| ≤ A * t ^ N * Real.exp (-(r j * t ^ p)))
    (hν : ∀ᶠ t : ℝ in atTop, ∀ j, |ν t j| ≤ A * t ^ N)
    (G₀ : ℝ × (ι → ℝ) → F) (G : ι → ℝ × (ι → ℝ) → F)
    (hG₀ : AnalyticAt ℝ G₀ 0) (hG : ∀ j, AnalyticAt ℝ (G j) 0)
    (hid : ∀ R : ℝ, ∀ᶠ t : ℝ in atTop,
      ‖G₀ (1 / t, ζ t) + ∑ j, (ν t j * ζ t j) • G j (1 / t, ζ t)‖ ≤ Real.exp (-(R * t ^ p)))
    (hstep : ∀ j,
      FasterThanPowers (fun t : ℝ =>
        fderiv ℝ (fun y : ι → ℝ => G₀ (1 / t, y)) 0 (Pi.single j 1) + ν t j • G j (1 / t, 0)) →
      ∀ᶠ z in 𝓝 (0 : ℝ × (ι → ℝ)), G j z = 0) :
    (∀ᶠ z in 𝓝 (0 : ℝ × (ι → ℝ)), G₀ z = 0) ∧
      ∀ j, ∀ᶠ z in 𝓝 (0 : ℝ × (ι → ℝ)), G j z = 0 := by
  sorry

/-- **The induction on the exponents, for the hidden units of several tokens:** the same statement
with the small terms arranged in a matrix (one row per token, one column per hidden unit). -/
theorem ray_induction_matrix {T q : Type*} [Fintype T] [Fintype q] [DecidableEq T] [DecidableEq q]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (p : ℕ) (hp : 1 ≤ p)
    (r : Matrix T q ℝ) (hr : ∀ a j, 0 < r a j)
    (hrQ : LinearIndependent ℚ (fun i : T × q => r i.1 i.2)) (ζ ν : ℝ → Matrix T q ℝ) (A : ℝ)
    (N : ℕ)
    (hζl : ∀ᶠ t : ℝ in atTop, ∀ a j, Real.exp (-(r a j * t ^ p)) ≤ A * t ^ N * ζ t a j)
    (hζu : ∀ᶠ t : ℝ in atTop, ∀ a j, |ζ t a j| ≤ A * t ^ N * Real.exp (-(r a j * t ^ p)))
    (hν : ∀ᶠ t : ℝ in atTop, ∀ a j, |ν t a j| ≤ A * t ^ N)
    (G₀ : ℝ × Matrix T q ℝ → F) (G : T → q → ℝ × Matrix T q ℝ → F)
    (hG₀ : AnalyticAt ℝ G₀ 0) (hG : ∀ a j, AnalyticAt ℝ (G a j) 0)
    (hid : ∀ R : ℝ, ∀ᶠ t : ℝ in atTop,
      ‖G₀ (1 / t, ζ t) + ∑ a, ∑ j, (ν t a j * ζ t a j) • G a j (1 / t, ζ t)‖
        ≤ Real.exp (-(R * t ^ p)))
    (hstep : ∀ a j,
      FasterThanPowers (fun t : ℝ =>
        fderiv ℝ (fun y : Matrix T q ℝ => G₀ (1 / t, y)) 0 (Matrix.single a j 1)
          + ν t a j • G a j (1 / t, 0)) →
      ∀ᶠ z in 𝓝 (0 : ℝ × Matrix T q ℝ), G a j z = 0) :
    (∀ᶠ z in 𝓝 (0 : ℝ × Matrix T q ℝ), G₀ z = 0) ∧
      ∀ a j, ∀ᶠ z in 𝓝 (0 : ℝ × Matrix T q ℝ), G a j z = 0 := by
  sorry

end Skips
