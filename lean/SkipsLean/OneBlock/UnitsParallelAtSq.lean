import SkipsLean.OneBlock.UnitsParallelAt
import SkipsLean.OneBlock.QuadraticResultant

/-!
# A direction that keeps the output of ReLU² units parallel: units in general position

Paper (skips paper), proof of Theorem B.1 (iv), "The skipless network: equality", for
`σ(z) = max(z, 0)^k`, `k = 1` or `2`, with `h_1 = ∑_i σ(x c_i) a_i`: equation (18),

`J(x) := ∑_i [σ(x c_i) (ψa_i − a_i Y) + σ'(x c_i) (x ψc_i) a_i] = μ(x) h_1(x)` on `Ω`,

"The kinks stay": "For `k = 2`, both sides, `μ` and the derivative of `h_1` in `x` are continuous
at `x_0`. The derivative in `x` of the left side jumps by the matrix `2 (x_0 ψc_i) c_i a_i`, and
that of the right side by a column times the row `h_1(x_0)`; two such matrices are equal only if
both vanish. In both cases `x_0 ψc_i = 0` on an open subset of the hyperplane, so
`ψc_i = λ_i c_i` for a number `λ_i`", and "One scale": "On a region where at least two units are
active, the entries of `J` and of `h_1` are homogeneous polynomials of degree `k` in `x`, and for
generic parameters two entries `h_a` and `h_b` of `h_1` have no common factor. […] Hence `μ = c`
on `Ω` for one number `c`".

`OneBlock/UnitsParallel.lean` has the two steps for linearly independent columns `c_i` and rows
`a_i` (a block of width exactly `d_model`), for ReLU and ReLU²; `OneBlock/UnitsParallelAt.lean`
for ReLU units in general position, also more units than coordinates. Here the same for ReLU²
(`k = 2`), also more units than coordinates. The paper's "for generic parameters" are hypotheses
on `c` and `a`:

* the `c_i` are pairwise non-collinear (also not opposite), the `a_i` nonzero;
* `h_1 ≠ 0` on `Ω` ("for generic parameters `h_1 ≠ 0` there"), at every `x` with an active unit;
* for every unit `i` one point `x_0` of its hyperplane, on no other hyperplane, at which
  `h_1(x_0)` is not a multiple of `a_i`;
* "two entries `h_a` and `h_b` of `h_1` have no common factor": for every set `S` of at least two
  units there are a line `t ↦ u + t v` and two entries `e`, `f` such that the two polynomials of
  degree at most two `t ↦ ∑_{i∈S} ((u + t v) c_i)² a_{i e}` and
  `t ↦ ∑_{i∈S} ((u + t v) c_i)² a_{i f}` have a resultant that is not zero (`quadRes`,
  `OneBlock/QuadraticResultant.lean`). The paper does not show that its condition holds for
  generic parameters; this one does, at almost every parameter
  (`OneBlock/SkiplessReluSqWideRMSZero.lean`).

The Lean route for "The kinks stay" uses no derivative in `x`: on the two sides of the
hyperplane of unit `i` the vectors `J` and `h_1` are parallel, which are polynomial identities;
their difference, divided by `x c_i`, has the value `2 (x_0 ψc_i) a_i ∧ h_1(x_0)` at `x_0`.

Exact check of the dimension `q + 1` of the solutions, more units than coordinates (up to eight
units in two coordinates): `units_parallel_relusq_wide_check_2026-11-25.py` (28 cases; with two
collinear columns the dimension is higher).
-/

namespace Skips

open Matrix

/-- **"The kinks stay" and "One scale" for ReLU² units in general position** (proof of Theorem
B.1 (iv) of the skips paper, "The skipless network: equality", `k = 2`; any number of units, also
more units than coordinates): let the columns `c_i` be pairwise non-collinear and the rows `a_i`
nonzero; let the output `h_1(x) = ∑_i max(x c_i, 0)² a_i` be nonzero wherever a unit is active;
for every unit `i` let there be a point `x_0` of its hyperplane `x c_i = 0`, on no other
hyperplane, at which `h_1(x_0)` is not a multiple of `a_i`; and for every set `S` of at least two
units let there be a line `t ↦ u + t v` on which two entries of `∑_{i∈S} (x c_i)² a_i` are
polynomials in `t` with a resultant that is not zero. Then `UnitsParallelAt` holds: a direction
`(ψc, β)` whose derivative of the output is a multiple of the output off the kinks is
`ψc_i = λ_i c_i`, `β_i = (c₀ − 2 λ_i) a_i`. -/
theorem reluSq_unitsParallelAt_of_generic {n m q : Type*} [Fintype n] [Fintype m] [Fintype q]
    (c : q → n → ℝ) (a : q → m → ℝ)
    (hcc : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) (ha : ∀ i, a i ≠ 0)
    (hne : ∀ x : n → ℝ, (∃ i, 0 < x ⬝ᵥ c i) → ∑ i, reluSq (x ⬝ᵥ c i) • a i ≠ 0)
    (hkink : ∀ i, ∃ x₀ : n → ℝ, x₀ ⬝ᵥ c i = 0 ∧ (∀ j, j ≠ i → x₀ ⬝ᵥ c j ≠ 0) ∧
      ∀ r : ℝ, ∑ j, reluSq (x₀ ⬝ᵥ c j) • a j ≠ r • a i)
    (hres : ∀ S : Finset q, 2 ≤ S.card → ∃ (u v : n → ℝ) (e f : m),
      quadRes (∑ i ∈ S, (u ⬝ᵥ c i) ^ 2 * a i e)
        (2 * ∑ i ∈ S, (u ⬝ᵥ c i) * (v ⬝ᵥ c i) * a i e) (∑ i ∈ S, (v ⬝ᵥ c i) ^ 2 * a i e)
        (∑ i ∈ S, (u ⬝ᵥ c i) ^ 2 * a i f)
        (2 * ∑ i ∈ S, (u ⬝ᵥ c i) * (v ⬝ᵥ c i) * a i f) (∑ i ∈ S, (v ⬝ᵥ c i) ^ 2 * a i f) ≠ 0) :
    UnitsParallelAt reluSq reluSqDeriv 2 c a := by
  sorry

end Skips
