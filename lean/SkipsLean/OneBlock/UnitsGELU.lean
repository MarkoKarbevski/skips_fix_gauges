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
  sorry

end Skips
