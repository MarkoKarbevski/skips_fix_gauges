import SkipsLean.OneBlock.UnitsReLU

/-!
# A direction that keeps the output of ReLU or ReLU² units parallel: a scale and rescalings

Paper (skips paper), proof of Theorem B.1 (iv), "The skipless network: equality", for
`σ(z) = max(z, 0)^k`, `k = 1` or `2`, with `h_1 = ∑_i σ(x c_i) a_i`: equation (18),

`J(x) := ∑_i [σ(x c_i) (ψa_i − a_i Y) + σ'(x c_i) (x ψc_i) a_i] = μ(x) h_1(x)` on `Ω`,

then "The kinks stay": "In both cases `x_0 ψc_i = 0` on an open subset of the hyperplane, so
`ψc_i = λ_i c_i` for a number `λ_i`", and "One scale": "Hence `μ = c` on `Ω` for one number `c`".
With `β_i = ψa_i − a_i Y` the two steps say: `ψc_i = λ_i c_i` and `β_i = (c − k λ_i) a_i`.

Here these two steps as one statement on vectors, with no network in it (the twin of Lemma B.3,
`UnitsRescale` in `OneBlock/Rescale.lean`, with a multiple `μ(x)` of the output on the right side
in place of `0`), **for units whose columns `c_i` are linearly independent and whose rows `a_i`
are linearly independent** (a block of width exactly `d_model` at generic parameters), and at
least two units. Then every pattern of active units occurs, and the argument is elementary:

* ReLU: across the kink of unit `i`, at a point where another unit is active, `J` jumps by
  `(x ψc_i) a_i` and `h_1` does not jump; `a_i` is not parallel to `h_1(x)`, so `x ψc_i = 0` on the
  hyperplane `x c_i = 0`. Where all units are active, `J` and `h_1` are linear in `x` and
  parallel, and `h_1` has rank at least `2`, so `J = c h_1`.
* ReLU²: where all units are active, `J` and `h_1` are quadratic, and comparing coefficients in
  the independent linear forms `x c_i` gives both conclusions.

With one unit the statement is false (`ψc` is then arbitrary). The paper's argument for blocks
wider than `d_model` (a resultant, and entries of `h_1` without a common factor) is not stated
here. Numeric check of the dimension `q + 1` of the solutions:
`units_parallel_check_2026-11-24.py`.
-/

namespace Skips

open Matrix

/-- **The kinks stay, and one scale (proof of Theorem B.1 (iv) of the skips paper), as a property
of an activation `σ` with derivative `σ'` off the kink and degree `k`:** for at least two hidden
units with linearly independent columns `c_i` and linearly independent rows `a_i`, if at every
input `x` off the kinks at which the output `∑_i σ(x c_i) a_i` is not zero the vector
`∑_i [σ(x c_i) β_i + σ'(x c_i) (x ψc_i) a_i]` is a multiple of the output, then there are numbers
`c₀` and `λ_i` with `ψc_i = λ_i c_i` and `β_i = (c₀ − k λ_i) a_i`. Rows of the input are indexed
by `n`, the coordinates of the output by `m`, the hidden units by `q`. -/
def UnitsParallel (σ σ' : ℝ → ℝ) (k : ℕ) (n m q : Type*) [Fintype n] [Fintype m] [Fintype q] :
    Prop :=
  ∀ (c : q → n → ℝ) (a : q → m → ℝ) (ψc : q → n → ℝ) (β : q → m → ℝ),
    LinearIndependent ℝ c → LinearIndependent ℝ a → 2 ≤ Fintype.card q →
    (∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, σ (x ⬝ᵥ c i) • a i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = μ • ∑ i, σ (x ⬝ᵥ c i) • a i) →
    ∃ (c₀ : ℝ) (lam : q → ℝ), ∀ i, ψc i = lam i • c i ∧ β i = (c₀ - (k : ℝ) * lam i) • a i

/-- **The kinks stay, and one scale, for ReLU units** (`k = 1`). -/
theorem relu_unitsParallel (n m q : Type*) [Fintype n] [Fintype m] [Fintype q] :
    UnitsParallel relu reluDeriv 1 n m q := by
  sorry

/-- **The kinks stay, and one scale, for ReLU² units** (`k = 2`). -/
theorem reluSq_unitsParallel (n m q : Type*) [Fintype n] [Fintype m] [Fintype q] :
    UnitsParallel reluSq reluSqDeriv 2 n m q := by
  sorry

end Skips
