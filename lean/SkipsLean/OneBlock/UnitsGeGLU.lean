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
  sorry

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
