import SkipsLean.OneBlock.UnitsParallel

/-!
# A direction that keeps the output of ReLU units parallel: units in general position

Paper (skips paper), proof of Theorem B.1 (iv), "The skipless network: equality", for
`σ(z) = max(z, 0)^k`, `k = 1` or `2`, with `h_1 = ∑_i σ(x c_i) a_i`: equation (18),

`J(x) := ∑_i [σ(x c_i) (ψa_i − a_i Y) + σ'(x c_i) (x ψc_i) a_i] = μ(x) h_1(x)` on `Ω`,

"The kinks stay": "Fix a unit `i` and a point `x_0` with `x_0 c_i = 0`, on no other hyperplane
`x c_j = 0`, at which another unit is active. For generic parameters and `x_0` in an open dense
set of such points, `h_1(x_0)` is not parallel to `a_i`. […] In both cases `x_0 ψc_i = 0` on an
open subset of the hyperplane, so `ψc_i = λ_i c_i` for a number `λ_i`", and "One scale": "On a
region where only unit `j` is active, `b_j = μ(x) a_j`, so `μ` is constant. On a region where at
least two units are active, the entries of `J` and of `h_1` are homogeneous polynomials of degree
`k` in `x`, and for generic parameters two entries `h_a` and `h_b` of `h_1` have no common factor.
[…] So `μ` is continuous on `Ω` and constant on every region. The set `Ω` is connected: it is the
union of the open half-spaces `{x : x c_i > 0}`, and any two of them meet, as the `c_i` are
pairwise non-collinear. Hence `μ = c` on `Ω` for one number `c`".

`OneBlock/UnitsParallel.lean` has the two steps as the property `UnitsParallel` of an activation,
for linearly independent columns `c_i` and rows `a_i` (a block of width exactly `d_model`). Here:

* `UnitsParallelAt σ σ' k c a`: the same conclusion for given units `c`, `a` (no condition on them
  in the definition), so that the network statement can take it as a hypothesis at its own
  weights;
* for ReLU (`k = 1`), units in general position, also more units than coordinates: the paper's
  three "for generic parameters" are hypotheses on `c` and `a`:
  - `h_1 ≠ 0` on `Ω` ("for generic parameters `h_1 ≠ 0` there"), at every `x` with an active unit;
  - for every unit `i` one point `x_0` of its hyperplane, on no other hyperplane, at which
    `h_1(x_0)` is not a multiple of `a_i` (then another unit is active there);
  - where at least two units are active, the linear map that `h_1` is on the region of `x` has
    rank at least two ("two entries […] of `h_1` have no common factor", for `k = 1`): some `y`
    is mapped to a vector that is not a multiple of `h_1(x)`;
  and the `c_i` are pairwise non-collinear (also not opposite), the `a_i` nonzero.

Not stated: ReLU² units in general position (the paper's proof uses that two quadratic entries
of `h_1` have no common factor). Exact check of the dimension `q + 1` of the solutions for more
units than coordinates: `units_parallel_wide_check_2026-11-24.py` (24 cases).
-/

namespace Skips

open Matrix

/-- **"The kinks stay" and "One scale" at given units:** if at every `x` off the kinks at which
the output `∑_i σ(x c_i) a_i` is not zero the vector `∑_i [σ(x c_i) β_i + σ'(x c_i) (x ψc_i) a_i]`
is a multiple of the output, then there are numbers `c₀` and `λ_i` with `ψc_i = λ_i c_i` and
`β_i = (c₀ − k λ_i) a_i`. (`UnitsParallel σ σ' k n m q` says this for all linearly independent
`c`, linearly independent `a` and at least two units.) -/
def UnitsParallelAt (σ σ' : ℝ → ℝ) (k : ℕ) {n m q : Type*} [Fintype n] [Fintype m] [Fintype q]
    (c : q → n → ℝ) (a : q → m → ℝ) : Prop :=
  ∀ (ψc : q → n → ℝ) (β : q → m → ℝ),
    (∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, σ (x ⬝ᵥ c i) • a i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = μ • ∑ i, σ (x ⬝ᵥ c i) • a i) →
    ∃ (c₀ : ℝ) (lam : q → ℝ), ∀ i, ψc i = lam i • c i ∧ β i = (c₀ - (k : ℝ) * lam i) • a i

/-- The property `UnitsParallel` of an activation gives `UnitsParallelAt` at linearly independent
columns `c_i`, linearly independent rows `a_i` and at least two units. -/
theorem unitsParallelAt_of_unitsParallel {σ σ' : ℝ → ℝ} {k : ℕ} {n m q : Type*} [Fintype n]
    [Fintype m] [Fintype q] (h : UnitsParallel σ σ' k n m q) {c : q → n → ℝ} {a : q → m → ℝ}
    (hc : LinearIndependent ℝ c) (ha : LinearIndependent ℝ a) (hq : 2 ≤ Fintype.card q) :
    UnitsParallelAt σ σ' k c a :=
  fun ψc β hpar => h c a ψc β hc ha hq hpar

/-- **"The kinks stay" and "One scale" for ReLU units in general position** (proof of Theorem
B.1 (iv) of the skips paper, "The skipless network: equality", `k = 1`; any number of units, also
more units than coordinates): let the columns `c_i` be pairwise non-collinear and the rows `a_i`
nonzero; let the output `h_1(x) = ∑_i max(x c_i, 0) a_i` be nonzero wherever a unit is active; for
every unit `i` let there be a point `x_0` of its hyperplane `x c_i = 0`, on no other hyperplane,
at which `h_1(x_0)` is not a multiple of `a_i`; and at every `x` off the kinks with at least two
active units let there be a `y` for which `∑_{i active at x} (y c_i) a_i` is not a multiple of
`h_1(x)`. Then `UnitsParallelAt` holds: a direction `(ψc, β)` whose derivative of the output is a
multiple of the output off the kinks is `ψc_i = λ_i c_i`, `β_i = (c₀ − λ_i) a_i`. -/
theorem relu_unitsParallelAt_of_generic {n m q : Type*} [Fintype n] [Fintype m] [Fintype q]
    (c : q → n → ℝ) (a : q → m → ℝ)
    (hcc : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) (ha : ∀ i, a i ≠ 0)
    (hne : ∀ x : n → ℝ, (∃ i, 0 < x ⬝ᵥ c i) → ∑ i, relu (x ⬝ᵥ c i) • a i ≠ 0)
    (hkink : ∀ i, ∃ x₀ : n → ℝ, x₀ ⬝ᵥ c i = 0 ∧ (∀ j, j ≠ i → x₀ ⬝ᵥ c j ≠ 0) ∧
      ∀ r : ℝ, ∑ j, relu (x₀ ⬝ᵥ c j) • a j ≠ r • a i)
    (hrank : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) →
      (∃ i j, i ≠ j ∧ 0 < x ⬝ᵥ c i ∧ 0 < x ⬝ᵥ c j) →
      ∃ y : n → ℝ, ∀ r : ℝ, ∑ i, (reluDeriv (x ⬝ᵥ c i) * (y ⬝ᵥ c i)) • a i
        ≠ r • ∑ i, relu (x ⬝ᵥ c i) • a i) :
    UnitsParallelAt relu reluDeriv 1 c a := by
  sorry

end Skips
