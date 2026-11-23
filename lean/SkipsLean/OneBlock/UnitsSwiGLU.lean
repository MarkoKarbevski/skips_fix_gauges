import Mathlib

/-!
# A flat direction of SwiGLU hidden units only rescales their values

Paper (dimension paper): Lemma C.3, the case of SwiGLU, with a linear term `x M`, a constant `γ`
and biases, as the paper states it.

A gated hidden unit computes `σ(z_i) w_i a_i` with the gate `z_i = x c_i + β_i` and the value
`w_i = x e_i + β'_i`; for SwiGLU `σ` is SiLU, `σ(z) = z / (1 + e^{-z})`. The function is
`G(φ, x) = x M + γ + ∑_i σ(z_i) w_i a_i`. A direction `ψ` of its weights is flat if the derivative
of `G` along it vanishes at every input `x`:

  `x ψ_M + ψ_γ + ∑_i [ σ(z_i) w_i ψ_{a_i} + σ'(z_i) (x ψ_{c_i} + ψ_{β_i}) w_i a_i
                        + σ(z_i) (x ψ_{e_i} + ψ_{β'_i}) a_i ] = 0`.

The lemma says that then `ψ_M = 0`, `ψ_γ = 0`, `ψ_{c_i} = 0`, `ψ_{β_i} = 0`, and for every unit
there is a number `α_i` with `(ψ_{e_i}, ψ_{β'_i}) = -α_i (e_i, β'_i)` and `ψ_{a_i} = α_i a_i`: the
direction of the rescaling `(e_i, a_i) ↦ (e_i/λ, λ a_i)` of the value of the unit.
-/

namespace Skips

open Matrix

/-- SiLU, the gate of a SwiGLU block: `σ(z) = z / (1 + e^{-z})`. -/
noncomputable def silu (z : ℝ) : ℝ := z / (1 + Real.exp (-z))

/-- The derivative of SiLU: `σ'(z) = (1 + e^{-z} + z e^{-z}) / (1 + e^{-z})²`. -/
noncomputable def siluDeriv (z : ℝ) : ℝ :=
  (1 + Real.exp (-z) + z * Real.exp (-z)) / (1 + Real.exp (-z)) ^ 2

theorem hasDerivAt_silu (z : ℝ) : HasDerivAt silu (siluDeriv z) z := by
  sorry

/-- **Lemma C.3 for SwiGLU.** Rows are indexed by `n` (the coordinates of an input `x`), hidden
units by `q`, and the coordinates of the output by `k`. -/
theorem silu_gated_units_flat {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (e : q → n → ℝ) (β' : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψe : q → n → ℝ)
    (ψβ' : q → ℝ) (ψa : q → k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j)
    (he : ∀ i, e i ≠ 0) (hec : ∀ i, ∀ r : ℝ, (e i, β' i) ≠ r • (c i, β i))
    (h : ∀ x : n → ℝ,
      x ᵥ* ψM + ψγ + ∑ i,
        ((silu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i)) • ψa i
          + (siluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i)) • a i
          + (silu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i)) • a i) = 0) :
    ψM = 0 ∧ ψγ = 0 ∧ ψc = 0 ∧ ψβ = 0 ∧
      ∃ α : q → ℝ, ∀ i, ψe i = -(α i) • e i ∧ ψβ' i = -(α i) * β' i ∧ ψa i = α i • a i := by
  sorry

end Skips
