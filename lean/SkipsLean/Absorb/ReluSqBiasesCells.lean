import SkipsLean.Absorb.BiasesConstructions

/-!
# ReLU² blocks with biases: the polynomial of a cell

Paper (absorb paper), Appendix C.2, proof of Theorem C.2 (iii): "let `B_{θ′}`, with `n` more units
than `B_θ`, satisfy (2), and let `r(z) = max(z, 0)²`. Squares. Group the units of both blocks with
a nonzero read by the hyperplane `H = {x : x ω + ω_0 = 0}` on which their argument vanishes […].
By (2), `B_{θ′} − B_θ` is a polynomial. Near a point of `H` on no other hyperplane, the terms of
`H` are `μ_+ r(z) + μ_− r(−z)`, with `z = x ω + ω_0` […]."

A unit of a ReLU² block with biases computes `r(x w_i + b_i) ŵ_i`, which is the polynomial
`(x w_i + b_i)² ŵ_i` where its argument is positive and `0` where it is negative. So on the cell of
an input `x₀` (the inputs at which the arguments of all units have the signs they have at `x₀`)
the block is the polynomial `y ↦ ∑_{i : x₀ w_i + b_i > 0} (y w_i + b_i)² ŵ_i + c` (`reluSqCell`).
If `x₀` lies on no hyperplane `x w + b = 0` of a unit with a nonzero read, of either block, the
cell contains a neighbourhood of `x₀`, and an equality of the blocks on it is an equality of
polynomials. This is the form in which the proof uses "`B_{θ′} − B_θ` is a polynomial": here (2)
becomes, for every such `x₀`, an identity in `y` between the polynomials of the two cells.
`reluSqCell` is not a notion of the paper.
-/

namespace Skips

open Matrix

variable {p q m m' : Type*} [Fintype p] [Fintype m] [Fintype m']

open scoped Classical in
/-- **The polynomial of a ReLU² block with biases on the cell of `x₀`:**
`y ↦ ∑_{i : x₀ w_i + b_i > 0} (y w_i + b_i)² ŵ_i + c`. -/
noncomputable def reluSqCell (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ)
    (x₀ y : p → ℝ) : q → ℝ :=
  (∑ i, if 0 < (x₀ ᵥ* Wr) i + b i then ((y ᵥ* Wr) i + b i) ^ 2 • Ww i else 0) + c

/-- At every input, a ReLU² block with biases is the polynomial of the cell of that input. -/
theorem vanillaBlockB_reluSq_eq_reluSqCell (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (x : p → ℝ) :
    vanillaBlockB reluSq Wr b Ww c x = reluSqCell Wr b Ww c x x := by
  sorry

/-- **Proof of Theorem C.2 (iii) of the absorb paper, "`B_{θ′} − B_θ` is a polynomial", cell by
cell:** let ReLU² blocks with biases `B_θ` and `B_{θ′}`, of any widths, satisfy
`x M + B_θ(x) = B_{θ′}(x)` for all `x`. Then for every `x₀` on no hyperplane `x w + b = 0` of a
unit with a nonzero read, of either block, the polynomials of the cell of `x₀` satisfy the same
equation at every `y`. -/
theorem reluSqCell_eq_of_vanillaBlockB_absorb (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (Wr' : Matrix p m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' q ℝ) (c' : q → ℝ)
    (M : Matrix p q ℝ)
    (h : ∀ x : p → ℝ,
      x ᵥ* M + vanillaBlockB reluSq Wr b Ww c x = vanillaBlockB reluSq Wr' b' Ww' c' x)
    (x₀ : p → ℝ) (hx : ∀ i, (x₀ ᵥ* Wr) i + b i = 0 → Wrᵀ i = 0)
    (hx' : ∀ j, (x₀ ᵥ* Wr') j + b' j = 0 → Wr'ᵀ j = 0) :
    ∀ y : p → ℝ, y ᵥ* M + reluSqCell Wr b Ww c x₀ y = reluSqCell Wr' b' Ww' c' x₀ y := by
  sorry

end Skips
