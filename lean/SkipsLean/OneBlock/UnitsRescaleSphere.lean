import SkipsLean.OneBlock.Rescale

/-!
# ReLU and ReLU² units and a symmetric change of the input: only a scaling and rescalings

Paper (skips paper), proof of Theorem B.1 (iii). Step 4 has, for a symmetric matrix `X_s` and a
direction `ψ` of the weights of the block, equation (17), `∂_ψ B(n) = q(n) DB(n) n` with
`q(n) = n X_s nᵀ / d_model`, on the image of `N_ε`. "The case `ε = 0`": "(17) holds with `X_0` in
place of `X_s` on the sphere. […] For ReLU, ReLU² and ReGLU, both sides of (17) are positively
homogeneous, of degrees `k` and `k + 2`, so `‖n‖² ∂_ψ B(n) = k d_model q(n) B(n)` for all
`n ≠ 0`. On each region where no `n c_k` changes sign, both sides are polynomials in `n`. Across
the hyperplane `n c_i = 0`, at a point of no other such hyperplane, only the terms of unit `i`
change, so they satisfy the identity on their own: `‖n‖²` times a polynomial equals
`k d_model q(n)` times `(n c_i) a_i`, `(n c_i)² a_i` or `(n c_i)(n e_i) a_i`. Since `‖n‖²` has no
real linear factor, it divides `q(n)`, so `X_0` is a multiple of `I`, and `X_0 = 0` because its
trace vanishes. Then Step 5 gives equality."

Here this step, together with Lemma B.3 for the remaining direction, as one statement on vectors
with no network in it (a twin of `UnitsRescale`, `OneBlock/Rescale.lean`), for the units
`σ(x c_i) a_i` of a ReLU or ReLU² block: `B(x) = ∑_i σ(x c_i) a_i`,
`∂_ψ B(x) = ∑_i [σ(x c_i) β_i + σ'(x c_i) (x ψc_i) a_i]`, and `k d_model q(x) = k (x X xᵀ)`. If

`‖x‖² ∑_i [σ(x c_i) β_i + σ'(x c_i) (x ψc_i) a_i] = k (x X xᵀ) ∑_i σ(x c_i) a_i`

at every `x` with no unit at its kink, for a symmetric `X`, then `X = c₀ I` and the direction is
a rescaling of the units shifted by `c₀`: `ψc_i = λ_i c_i`, `β_i = k (c₀ − λ_i) a_i`. (The paper's
`X_0` has trace zero, which gives `c₀ = 0`; here `X` is any symmetric matrix, and `c₀ I` is the
scaling of the hidden state.) At least one unit is asked: with no unit both sides vanish for
every `X`. Exact check of the dimension `q + 1` of the solutions:
`units_rescale_sphere_check_2026-11-24.py`. Not stated: ReGLU units.
-/

namespace Skips

open Matrix

/-- **Step 4 of the proof of Theorem B.1 (iii) of the skips paper for `ε = 0`, with Lemma B.3, as
a property of an activation `σ` with derivative `σ'` off the kink and degree `k`:** for hidden
units `σ(x c_i) a_i` with nonzero rows `a_i` and nonzero, pairwise non-collinear columns `c_i`, a
symmetric matrix `X` and a direction `(ψc, β)` of the weights, if at every input `x` with no unit
at its kink `‖x‖² ∑_i [σ(x c_i) β_i + σ'(x c_i) (x ψc_i) a_i] = k (x X xᵀ) ∑_i σ(x c_i) a_i`, then
`X = c₀ I` for a number `c₀`, and `ψc_i = λ_i c_i`, `β_i = k (c₀ − λ_i) a_i` for numbers `λ_i`.
The coordinates of the input are indexed by `n`, those of the output by `m`, the hidden units by
`q` (at least one). -/
def UnitsRescaleSphere (σ σ' : ℝ → ℝ) (k : ℕ) (n m q : Type*) [Fintype n] [DecidableEq n]
    [Fintype m] [Fintype q] : Prop :=
  ∀ (c : q → n → ℝ) (a : q → m → ℝ) (X : Matrix n n ℝ) (ψc : q → n → ℝ) (β : q → m → ℝ),
    (∀ i, a i ≠ 0) → (∀ i, c i ≠ 0) → (∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) → Xᵀ = X →
    (∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) →
      (x ⬝ᵥ x) • ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = ((k : ℝ) * ((x ᵥ* X) ⬝ᵥ x)) • ∑ i, σ (x ⬝ᵥ c i) • a i) →
    ∃ (c₀ : ℝ) (lam : q → ℝ), X = c₀ • (1 : Matrix n n ℝ) ∧
      ∀ i, ψc i = lam i • c i ∧ β i = ((k : ℝ) * (c₀ - lam i)) • a i

/-- **The symmetric part is a scaling, for ReLU units** (`k = 1`; at least one unit). -/
theorem relu_unitsRescaleSphere (n m q : Type*) [Fintype n] [DecidableEq n] [Fintype m]
    [Fintype q] [Nonempty q] : UnitsRescaleSphere relu reluDeriv 1 n m q := by
  sorry

/-- **The symmetric part is a scaling, for ReLU² units** (`k = 2`; at least one unit). -/
theorem reluSq_unitsRescaleSphere (n m q : Type*) [Fintype n] [DecidableEq n] [Fintype m]
    [Fintype q] [Nonempty q] : UnitsRescaleSphere reluSq reluSqDeriv 2 n m q := by
  sorry

end Skips
