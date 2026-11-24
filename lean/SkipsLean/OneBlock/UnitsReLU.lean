import SkipsLean.Activations.ReLU

/-!
# A flat direction of ReLU or ReLU² hidden units only rescales them

Paper (dimension paper): Lemma C.3, the cases of ReLU and of ReLU², in the generality in which the
paper states it: with a linear term `x M`, a constant `γ` and biases `β_i`.

The function is `G(φ, x) = x M + γ + ∑_i σ(z_i) a_i` with `z_i = x c_i + β_i`, where `c_i` is the
read column of hidden unit `i` and `a_i` its write row. A direction
`ψ = (ψ_M, ψ_γ, ψ_{c_i}, ψ_{β_i}, ψ_{a_i})` of these weights is flat if the derivative of `G`
along it vanishes at every input `x` at which no hidden unit sits at its kink, `z_i ≠ 0` for all `i`:

  `x ψ_M + ψ_γ + ∑_i [ σ(z_i) ψ_{a_i} + σ'(z_i) (x ψ_{c_i} + ψ_{β_i}) a_i ] = 0`.

If every `a_i` is nonzero and the `c_i` are nonzero and pairwise non-collinear, then `ψ_M = 0`,
`ψ_γ = 0`, and for every unit `i` there is a number `λ_i` with
`(ψ_{c_i}, ψ_{β_i}) = λ_i (c_i, β_i)` and `ψ_{a_i} = -λ_i a_i` for ReLU, `ψ_{a_i} = -2 λ_i a_i` for
ReLU²: the direction of the rescaling `(c_i, β_i, a_i) ↦ (λ c_i, λ β_i, a_i / λ)` of the unit,
resp. `a_i / λ²`.

The proof of the paper works at the hyperplanes `H_i = {x : z_i = 0}`, which are pairwise
different: near a point of `H_i` that lies on no other `H_k`, only the terms of unit `i` fail to be
smooth across `H_i`.
-/

namespace Skips

open Matrix

/-- **Lemma C.3 for ReLU.** Rows are indexed by `n` (the coordinates of an input `x`), hidden
units by `q`, and the coordinates of the output by `k`. -/
theorem relu_units_flat {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψa : q → k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j)
    (h : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i + β i ≠ 0) →
      x ᵥ* ψM + ψγ + ∑ i, (relu (x ⬝ᵥ c i + β i) • ψa i
        + (reluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i)) • a i) = 0) :
    ψM = 0 ∧ ψγ = 0 ∧
      ∃ lam : q → ℝ, ∀ i, ψc i = lam i • c i ∧ ψβ i = lam i * β i ∧ ψa i = -(lam i) • a i := by
  sorry

/-- **Lemma C.3 for ReLU².** -/
theorem reluSq_units_flat {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψa : q → k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j)
    (h : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i + β i ≠ 0) →
      x ᵥ* ψM + ψγ + ∑ i, (reluSq (x ⬝ᵥ c i + β i) • ψa i
        + (reluSqDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i)) • a i) = 0) :
    ψM = 0 ∧ ψγ = 0 ∧
      ∃ lam : q → ℝ, ∀ i, ψc i = lam i • c i ∧ ψβ i = lam i * β i ∧
        ψa i = -(2 * lam i) • a i := by
  sorry

end Skips
