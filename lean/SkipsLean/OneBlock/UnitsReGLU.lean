import SkipsLean.Activations.ReLU

/-!
# A flat direction of ReGLU hidden units only rescales them

Paper (dimension paper): Lemma C.3, the case of ReGLU, in the generality in which the paper states
it: with a linear term `x M`, a constant `γ` and biases `β_i`, `β'_i`.

A ReGLU hidden unit computes `σ(z_i) w_i a_i` with the gate `z_i = x c_i + β_i`, the value
`w_i = x e_i + β'_i` and `σ(z) = max(z, 0)`. The function is
`G(φ, x) = x M + γ + ∑_i σ(z_i) w_i a_i`, and a direction
`ψ = (ψ_M, ψ_γ, ψ_{c_i}, ψ_{β_i}, ψ_{e_i}, ψ_{β'_i}, ψ_{a_i})` of the weights is flat if the
derivative of `G` along it vanishes at every input `x` at which no gate sits at its kink,
`z_i ≠ 0` for all `i`:

  `x ψ_M + ψ_γ + ∑_i [ σ(z_i) w_i ψ_{a_i} + σ'(z_i) (x ψ_{c_i} + ψ_{β_i}) w_i a_i
      + σ(z_i) (x ψ_{e_i} + ψ_{β'_i}) a_i ] = 0`,

with `σ'(z) = 1[z > 0]`. If every `a_i` and every `e_i` is nonzero, the `c_i` are nonzero and
pairwise non-collinear, and `(e_i, β'_i)` is not proportional to `(c_i, β_i)`, then `ψ_M = 0`,
`ψ_γ = 0`, and for every unit `i` there are numbers `λ_i` and `α_i` with
`(ψ_{c_i}, ψ_{β_i}) = λ_i (c_i, β_i)`, `(ψ_{e_i}, ψ_{β'_i}) = -α_i (e_i, β'_i)` and
`ψ_{a_i} = (α_i - λ_i) a_i`: the directions of the two rescalings of the unit, of its gate and of
its value. Unlike for SwiGLU and GeGLU, the hypothesis on proportionality is needed here (a
numerical check gives a larger kernel without it).
-/

namespace Skips

open Matrix

/-- **Lemma C.3 for ReGLU.** Rows are indexed by `n` (the coordinates of an input `x`), hidden
units by `q`, and the coordinates of the output by `k`. -/
theorem relu_gated_units_flat {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (e : q → n → ℝ) (β' : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψe : q → n → ℝ)
    (ψβ' : q → ℝ) (ψa : q → k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j)
    (he : ∀ i, e i ≠ 0) (hec : ∀ i, ∀ r : ℝ, (e i, β' i) ≠ r • (c i, β i))
    (h : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i + β i ≠ 0) →
      x ᵥ* ψM + ψγ + ∑ i,
        ((relu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i)) • ψa i
          + (reluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i)) • a i
          + (relu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i)) • a i) = 0) :
    ψM = 0 ∧ ψγ = 0 ∧
      ∃ (lam α : q → ℝ), ∀ i, ψc i = lam i • c i ∧ ψβ i = lam i * β i ∧
        ψe i = -(α i) • e i ∧ ψβ' i = -(α i) * β' i ∧ ψa i = (α i - lam i) • a i := by
  sorry

end Skips
