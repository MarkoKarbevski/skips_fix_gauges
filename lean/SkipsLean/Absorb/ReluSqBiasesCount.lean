import SkipsLean.Absorb.ReluSqBiasesCells

/-!
# ReLU² blocks with biases: squares, costs and dimensions

Paper (absorb paper), Appendix C.2, proof of Theorem C.2 (iii).

"Squares. […] a unit with read `λ ω` and bias `λ ω_0` computes `λ² r(±(x ω + ω_0))` times its
write, on side `±` as `λ ≷ 0`. Let `μ_±` be the sum of `λ²` times the write over the units of
`B_{θ′}` on side `±`, minus the same sum over the units of `B_θ`. […] So `μ_+ = μ_− =: μ_H`, the
terms of `H` are `μ_H z²`, and `∑_H μ_H (x ω_H + ω_{0,H})² = x M + const` (12).
Costs. For generic `θ` the units of `B_θ` have nonzero reads and writes and lie on distinct
hyperplanes. […] Let `S` and `U` be the sets of units `i` of `B_θ` with `μ_{H_i} = −ŵ_i` and with
`μ_{H_i} ∉ {0, −ŵ_i}`, and `N` the set of the other hyperplanes with `μ_H ≠ 0`. Then
`n ≥ |U| + 2|N|`.
Dimensions. Modulo constants, a polynomial of degree at most two is a pair of a quadratic form
and a linear part, in a space of dimension `d_model (d_model + 3)/2`, in which `(x ω + ω_0)²`
becomes `φ(ω, ω_0) = (ω ω^⊤, 2 ω_0 ω)`. For each output coordinate `o`, with `M_{:,o}` the column
`o` of `M`, (12) reads `∑_{i∈U} μ_{H_i,o} φ(w_i, b_i) + ∑_{H∈N} μ_{H,o} φ(ω_H, ω_{0,H}) = τ_o`,
where `τ_o = (0, M_{:,o}) + ∑_{i∈S} ŵ_{i,o} φ(w_i, b_i)`. So the vectors `τ_1, …, τ_{d_model}` and
`φ(w_i, b_i)`, `i ∈ U`, lie in the span of `|U| + |N|` vectors. […]
Conclusion. So `|U| + |N| ≥ min(d_model (d_model + 3)/2, d_model + |U|)`. If the minimum is
`d_model + |U|`, then `|N| ≥ d_model` and `n ≥ 2 d_model`. Otherwise
`|U| + |N| ≥ d_model (d_model + 3)/2 ≥ 2 d_model`, and again `n ≥ 2 d_model`. For `M ≠ 0` of any
rank, the same argument with `rank M` in place of `d_model` gives `n ≥ 2`."

Here: `φ` (`sqForm`, with values in pairs of a matrix and a row) and `τ_o` (`sqTarget`); the three
steps "Squares", "Costs" and "Dimensions" as one statement, from the identities of the cells
(`Absorb/ReluSqBiasesCells.lean`); and the "Conclusion" under the generic condition of the proof.

The statement of the three steps avoids the list of the hyperplanes that carry no unit of `B_θ`:
the units of `B_{θ′}` on these hyperplanes are split into those whose argument is positive far
away in a fixed direction (`F₁`) and those whose argument is positive far away in the opposite
direction (`F₂`), and each `τ_o` lies in the span of the `φ(w_i, b_i)`, `i ∈ U`, with the `φ` of
the units of `F₁`, and also with those of `F₂`. A hyperplane of the paper's set `N` has a unit in
`F₁` and one in `F₂`, so this contains "`τ_o` lies in the span of `|U| + |N|` vectors", and the
count `n ≥ |U| + |F₁| + |F₂|` contains `n ≥ |U| + 2|N|`.

The generic condition is used in the form: for disjoint `S`, `U` with `|U| < 2 d`, the vectors
`τ_o` and `φ(w_i, b_i)`, `i ∈ U`, are linearly independent (for `|U| ≥ 2 d` the count alone gives
`n ≥ 2 d`; `2 d − 1 ≤ d (d + 1)/2`, so the paper's minimum is `d + |U|` for these `U`). For the
same width and `M ≠ 0` the condition is: for every `S` some `τ_o` is nonzero.
-/

namespace Skips

open Matrix

variable {p q m m' : Type*} [Fintype p] [Fintype m] [Fintype m']

/-- **`φ(ω, ω_0) = (ω ω^⊤, 2 ω_0 ω)`:** the polynomial `(x ω + ω_0)²` modulo constants, as the pair
of its quadratic form and its linear part. -/
def sqForm (ω : p → ℝ) (ω₀ : ℝ) : Matrix p p ℝ × (p → ℝ) :=
  (Matrix.vecMulVec ω ω, (2 * ω₀) • ω)

/-- **`τ_o = (0, M_{:,o}) + ∑_{i∈S} ŵ_{i,o} φ(w_i, b_i)`.** -/
def sqTarget (M : Matrix p q ℝ) (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (S : Finset m) (o : q) : Matrix p p ℝ × (p → ℝ) :=
  ((0 : Matrix p p ℝ), fun a => M a o) + ∑ i ∈ S, Ww i o • sqForm (Wrᵀ i) (b i)

/-- **Proof of Theorem C.2 (iii) of the absorb paper, "Squares", "Costs" and "Dimensions":** let
the units of `B_θ` have nonzero reads and writes and lie on distinct hyperplanes, and let the
polynomials of the cells of the two blocks satisfy `y M + B_θ = B_{θ′}` at every `x₀` off the
hyperplanes. Then there are disjoint sets `S`, `U` of units of `B_θ` and disjoint sets `F₁`, `F₂`
of units of `B_{θ′}` such that `B_{θ′}` has at least `|U| + |F₁| + |F₂|` more units than `B_θ`,
and every `τ_o` lies in the span of the `φ(w_i, b_i)`, `i ∈ U`, with the `φ` of the units of
`F₁`, and in their span with the `φ` of the units of `F₂`. -/
theorem exists_sqTarget_mem_span_of_reluSqCell (Wr : Matrix p m ℝ) (b : m → ℝ)
    (Ww : Matrix m q ℝ) (c : q → ℝ) (Wr' : Matrix p m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' q ℝ)
    (c' : q → ℝ) (M : Matrix p q ℝ)
    (hr : ∀ i, Wrᵀ i ≠ 0) (hw : ∀ i, Ww i ≠ 0)
    (hH : ∀ i k, i ≠ k → ∀ r : ℝ, ¬ (Wrᵀ i = r • Wrᵀ k ∧ b i = r * b k))
    (hcell : ∀ x₀ : p → ℝ, (∀ i, (x₀ ᵥ* Wr) i + b i ≠ 0) →
      (∀ j, (x₀ ᵥ* Wr') j + b' j = 0 → Wr'ᵀ j = 0) →
      ∀ y : p → ℝ, y ᵥ* M + reluSqCell Wr b Ww c x₀ y = reluSqCell Wr' b' Ww' c' x₀ y) :
    ∃ (S U : Finset m) (F₁ F₂ : Finset m'), Disjoint S U ∧ Disjoint F₁ F₂ ∧
      Fintype.card m + U.card + F₁.card + F₂.card ≤ Fintype.card m' ∧
      ∀ o : q,
        sqTarget M Wr b Ww S o ∈
          Submodule.span ℝ ((fun i => sqForm (Wrᵀ i) (b i)) '' (U : Set m)) ⊔
            Submodule.span ℝ ((fun j => sqForm (Wr'ᵀ j) (b' j)) '' (F₁ : Set m')) ∧
        sqTarget M Wr b Ww S o ∈
          Submodule.span ℝ ((fun i => sqForm (Wrᵀ i) (b i)) '' (U : Set m)) ⊔
            Submodule.span ℝ ((fun j => sqForm (Wr'ᵀ j) (b' j)) '' (F₂ : Set m')) := by
  sorry

/-- **Proof of Theorem C.2 (iii) of the absorb paper, "Conclusion":** under the hypotheses of the
three steps, if for all disjoint sets `S`, `U` of units of `B_θ` with `|U| < 2 d` the vectors
`τ_o` (`o` an output) and `φ(w_i, b_i)`, `i ∈ U`, are linearly independent, then `B_{θ′}` has at
least `2 d` more units than `B_θ`, with `d` the number of outputs. -/
theorem card_add_two_mul_card_le_of_reluSqCell [Fintype q] (Wr : Matrix p m ℝ) (b : m → ℝ)
    (Ww : Matrix m q ℝ) (c : q → ℝ) (Wr' : Matrix p m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' q ℝ)
    (c' : q → ℝ) (M : Matrix p q ℝ)
    (hr : ∀ i, Wrᵀ i ≠ 0) (hw : ∀ i, Ww i ≠ 0)
    (hH : ∀ i k, i ≠ k → ∀ r : ℝ, ¬ (Wrᵀ i = r • Wrᵀ k ∧ b i = r * b k))
    (hG : ∀ S U : Finset m, Disjoint S U → U.card < 2 * Fintype.card q →
      LinearIndependent ℝ (Sum.elim (fun o : q => sqTarget M Wr b Ww S o)
        (fun i : U => sqForm (Wrᵀ (i : m)) (b i))))
    (hcell : ∀ x₀ : p → ℝ, (∀ i, (x₀ ᵥ* Wr) i + b i ≠ 0) →
      (∀ j, (x₀ ᵥ* Wr') j + b' j = 0 → Wr'ᵀ j = 0) →
      ∀ y : p → ℝ, y ᵥ* M + reluSqCell Wr b Ww c x₀ y = reluSqCell Wr' b' Ww' c' x₀ y) :
    Fintype.card m + 2 * Fintype.card q ≤ Fintype.card m' := by
  sorry

/-- **Proof of Theorem C.2 (iii) of the absorb paper, last sentence, for the same width:** under
the hypotheses of the three steps, if for every set `S` of units of `B_θ` some `τ_o` is nonzero,
then `B_{θ′}` has more units than `B_θ`. -/
theorem card_lt_card_of_reluSqCell (Wr : Matrix p m ℝ) (b : m → ℝ)
    (Ww : Matrix m q ℝ) (c : q → ℝ) (Wr' : Matrix p m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' q ℝ)
    (c' : q → ℝ) (M : Matrix p q ℝ)
    (hr : ∀ i, Wrᵀ i ≠ 0) (hw : ∀ i, Ww i ≠ 0)
    (hH : ∀ i k, i ≠ k → ∀ r : ℝ, ¬ (Wrᵀ i = r • Wrᵀ k ∧ b i = r * b k))
    (hG : ∀ S : Finset m, ∃ o : q, sqTarget M Wr b Ww S o ≠ 0)
    (hcell : ∀ x₀ : p → ℝ, (∀ i, (x₀ ᵥ* Wr) i + b i ≠ 0) →
      (∀ j, (x₀ ᵥ* Wr') j + b' j = 0 → Wr'ᵀ j = 0) →
      ∀ y : p → ℝ, y ᵥ* M + reluSqCell Wr b Ww c x₀ y = reluSqCell Wr' b' Ww' c' x₀ y) :
    Fintype.card m < Fintype.card m' := by
  sorry

end Skips
