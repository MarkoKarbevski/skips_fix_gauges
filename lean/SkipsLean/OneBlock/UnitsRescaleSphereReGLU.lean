import SkipsLean.OneBlock.UnitsRescaleSphere
import SkipsLean.OneBlock.UnitsReGLU

/-!
# ReGLU units and a symmetric change of the input: only a scaling and rescalings

Paper (skips paper), proof of Theorem B.1 (iii), "The case `ε = 0`": "For ReLU, ReLU² and ReGLU,
both sides of (17) are positively homogeneous, of degrees `k` and `k + 2`, so
`‖n‖² ∂_ψ B(n) = k d_model q(n) B(n)` for all `n ≠ 0`. On each region where no `n c_k` changes
sign, both sides are polynomials in `n`. Across the hyperplane `n c_i = 0`, at a point of no
other such hyperplane, only the terms of unit `i` change, so they satisfy the identity on their
own: `‖n‖²` times a polynomial equals `k d_model q(n)` times `(n c_i) a_i`, `(n c_i)² a_i` or
`(n c_i)(n e_i) a_i`. Since `‖n‖²` has no real linear factor, it divides `q(n)`, so `X_0` is a
multiple of `I`, and `X_0 = 0` because its trace vanishes. Then Step 5 gives equality."

`OneBlock/UnitsRescaleSphere.lean` has this step for ReLU and ReLU² units. Here the same for
ReGLU units `σ(x g_i) (x v_i) a_i` with `σ = ReLU` (the paper's `c_i` is the gate column `g_i`,
its `e_i` the value column `v_i`; the block has degree `k = 2`), together with Lemma B.3 for
ReGLU (`relu_gated_units_flat`, `OneBlock/UnitsReGLU.lean`), as one statement on vectors with no
network in it: `B(x) = ∑_i σ(x g_i)(x v_i) a_i`,

`∂_ψ B(x) = ∑_i [σ(x g_i)(x v_i) β_i + σ'(x g_i)(x ψg_i)(x v_i) a_i + σ(x g_i)(x ψv_i) a_i]`,

and `k d_model q(x) = 2 (x X xᵀ)`. If `‖x‖² ∂_ψ B(x) = 2 (x X xᵀ) B(x)` at every `x` with no gate
at its kink, for a symmetric `X`, then `X = c₀ I` and the direction is a rescaling of the gates
and of the values shifted by `c₀`: `ψg_i = λ_i g_i`, `ψv_i = μ_i v_i`,
`β_i = (2 c₀ − λ_i − μ_i) a_i`. The hypotheses are those of Lemma B.3 for ReGLU (no value column
is proportional to the gate column of its unit, which also makes it nonzero) and at least one
unit. Exact check of the dimension `2 q + 1` of the solutions:
`gated_units_rescale_sphere_check_2026-11-24.py`.
-/

namespace Skips

open Matrix

/-- **Step 4 of the proof of Theorem B.1 (iii) of the skips paper for `ε = 0`, with Lemma B.3, for
ReGLU units:** for hidden units `relu(x g_i) (x v_i) a_i` (at least one) with nonzero rows `a_i`,
nonzero, pairwise non-collinear gate columns `g_i` and no value column `v_i` proportional to its
gate column, a symmetric matrix `X` and a direction `(ψg, ψv, β)` of the weights: if at every
input `x` with no gate at its kink
`‖x‖² ∑_i [σ(x g_i)(x v_i) β_i + σ'(x g_i)(x ψg_i)(x v_i) a_i + σ(x g_i)(x ψv_i) a_i]
  = 2 (x X xᵀ) ∑_i σ(x g_i)(x v_i) a_i`,
then `X = c₀ I` for a number `c₀`, and `ψg_i = λ_i g_i`, `ψv_i = μ_i v_i`,
`β_i = (2 c₀ − λ_i − μ_i) a_i` for numbers `λ_i`, `μ_i`. -/
theorem reglu_unitsRescaleSphere {n m q : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    [Fintype q] [Nonempty q]
    (g v : q → n → ℝ) (a : q → m → ℝ) (X : Matrix n n ℝ) (ψg ψv : q → n → ℝ) (β : q → m → ℝ)
    (ha : ∀ i, a i ≠ 0) (hg : ∀ i, g i ≠ 0) (hgg : ∀ i j, i ≠ j → ∀ r : ℝ, g i ≠ r • g j)
    (hvg : ∀ i, ∀ r : ℝ, v i ≠ r • g i) (hX : Xᵀ = X)
    (h : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ g i ≠ 0) →
      (x ⬝ᵥ x) • ∑ i, ((relu (x ⬝ᵥ g i) * (x ⬝ᵥ v i)) • β i
          + (reluDeriv (x ⬝ᵥ g i) * (x ⬝ᵥ ψg i) * (x ⬝ᵥ v i)) • a i
          + (relu (x ⬝ᵥ g i) * (x ⬝ᵥ ψv i)) • a i)
        = (2 * ((x ᵥ* X) ⬝ᵥ x)) • ∑ i, (relu (x ⬝ᵥ g i) * (x ⬝ᵥ v i)) • a i) :
    ∃ (c₀ : ℝ) (lam mu : q → ℝ), X = c₀ • (1 : Matrix n n ℝ) ∧
      ∀ i, ψg i = lam i • g i ∧ ψv i = mu i • v i ∧
        β i = (2 * c₀ - lam i - mu i) • a i := by
  sorry

end Skips
