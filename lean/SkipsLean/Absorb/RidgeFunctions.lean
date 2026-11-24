import SkipsLean.Imports
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Two facts about ridge functions

Paper (absorb paper), Appendix A.1, before Theorem A.7 (Identity absorption for GELU): "The GELU
case needs one classical fact about ridge functions, whose short proof we include."

Lemma A.5 (Vanishing sums of ridge functions): "Let `a_1, …, a_r ∈ ℝ^{d_model}` be nonzero and
pairwise non-collinear, and let `g_1, …, g_r : ℝ → ℝ^q` be `r − 1` times continuously
differentiable with `∑_i g_i(a_i · x) = 0` for all `x ∈ ℝ^{d_model}`. Then every `g_i` is a
polynomial of degree at most `r − 2`."

Lemma A.6 (Distinct scales): "Let `ψ : ℝ → ℝ` be real-analytic and not a polynomial. Let
`α_1, …, α_n > 0` be distinct and `a_1, …, a_n ∈ ℝ^q`. If `∑_k a_k ψ(α_k t)` is a polynomial in
`t`, then every `a_k` is zero."

Stated here as in the paper. In Lemma A.5 a function with values in `ℝ^q` is a polynomial of degree
at most `r − 2` when each of its `q` coordinates is: there is a real polynomial `P` of degree less
than `r − 1` (for `r = 1` this is the zero polynomial) that agrees with the coordinate. The step of
the paper's proof, "so `g_i^{(r−1)} = 0`", is stated as well. In Lemma A.6 "is a polynomial in `t`"
is asked of each coordinate.

The Lean proof of Theorem A.7 (`Absorb/Block.lean`) goes another way (from ReLU, along rays) and
does not use these two lemmas; they are stated because the paper numbers them.
-/

namespace Skips

open Matrix

/-- **Lemma A.5 of the absorb paper, as its proof obtains it:** for nonzero, pairwise
non-collinear `a_1, …, a_r` and `g_1, …, g_r : ℝ → ℝ^q` that are `r − 1` times continuously
differentiable with `∑_i g_i(a_i · x) = 0` for all `x`, the derivative of order `r − 1` of every
`g_i` vanishes. -/
theorem iteratedDeriv_eq_zero_of_sum_ridge_eq_zero {d q : Type*} [Fintype d] [Fintype q] {r : ℕ}
    (a : Fin r → d → ℝ) (ha : ∀ i, a i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ c : ℝ, a i ≠ c • a j)
    (g : Fin r → ℝ → q → ℝ) (hg : ∀ i, ContDiff ℝ (r - 1 : ℕ) (g i))
    (hsum : ∀ x : d → ℝ, ∑ i, g i (a i ⬝ᵥ x) = 0) (i : Fin r) :
    iteratedDeriv (r - 1) (g i) = 0 := by
  sorry

/-- **Lemma A.5 of the absorb paper (Vanishing sums of ridge functions):** for nonzero, pairwise
non-collinear `a_1, …, a_r` and `g_1, …, g_r : ℝ → ℝ^q` that are `r − 1` times continuously
differentiable with `∑_i g_i(a_i · x) = 0` for all `x`, every coordinate of every `g_i` is a
polynomial of degree at most `r − 2` (of degree less than `r − 1`). -/
theorem exists_polynomial_of_sum_ridge_eq_zero {d q : Type*} [Fintype d] [Fintype q] {r : ℕ}
    (a : Fin r → d → ℝ) (ha : ∀ i, a i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ c : ℝ, a i ≠ c • a j)
    (g : Fin r → ℝ → q → ℝ) (hg : ∀ i, ContDiff ℝ (r - 1 : ℕ) (g i))
    (hsum : ∀ x : d → ℝ, ∑ i, g i (a i ⬝ᵥ x) = 0) (i : Fin r) (k : q) :
    ∃ P : Polynomial ℝ, P.degree < ((r - 1 : ℕ) : WithBot ℕ) ∧ ∀ t, g i t k = P.eval t := by
  sorry

/-- **Lemma A.6 of the absorb paper (Distinct scales):** let `ψ` be real-analytic and not a
polynomial, `α_1, …, α_n > 0` distinct and `a_1, …, a_n ∈ ℝ^q`. If every coordinate of
`∑_k a_k ψ(α_k t)` is a polynomial in `t`, then every `a_k` is zero. -/
theorem eq_zero_of_sum_smul_scaled_eq_polynomial {q : Type*} {n : ℕ} (ψ : ℝ → ℝ)
    (hψ : AnalyticOnNhd ℝ ψ Set.univ) (hnp : ¬ ∃ P : Polynomial ℝ, ∀ t, ψ t = P.eval t)
    (α : Fin n → ℝ) (hα : ∀ k, 0 < α k) (hinj : Function.Injective α) (a : Fin n → q → ℝ)
    (hP : ∀ j : q, ∃ P : Polynomial ℝ, ∀ t, ∑ k, a k j * ψ (α k * t) = P.eval t) :
    ∀ k, a k = 0 := by
  sorry

end Skips
