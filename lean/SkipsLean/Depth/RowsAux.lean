import SkipsLean.Depth.StepTanh

/-!
# Three facts about rows, for the step on the path

Paper (dimension paper): Appendix D.6, proof of Lemma D.18 (the step for `tanh` on the path).

* "By (S2), for integers `κ_j` that are not all zero, `∑_j κ_j ξ c_j = ξ ∑_j κ_j c_j` vanishes only
  for `ξ` in a hyperplane. Let `P' ⊂ P` be the dense set of the `ξ` for which `ξ c_1, …, ξ c_q` are
  linearly independent over `ℚ`."
* "A matrix for which every row of an open set is an eigenvector is a multiple of the identity."
* A matrix `M` with `ξ M = 0` for every row `ξ` of a nonempty open set is `0` (used for
  `ξ (Y_k W + η_W) = 0`).

Rows are functions `d → ℝ`, and `ξ M` is `ξ ᵥ* M`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {d : Type*} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
/-- **The set `P'` is dense:** if the columns `c_j` of `W` are linearly independent over `ℚ`, then
for a dense set of rows `ξ` the numbers `ξ c_1, …, ξ c_q` are linearly independent over `ℚ`. -/
theorem dense_setOf_linearIndependent_vecMul {q : Type*} [Fintype q] (W : Matrix d q ℝ)
    (hW : LinearIndependent ℚ (fun j : q => fun i : d => W i j)) :
    Dense {ξ : d → ℝ | LinearIndependent ℚ (fun j : q => (ξ ᵥ* W) j)} := by
  sorry

/-- **"A matrix for which every row of an open set is an eigenvector is a multiple of the
identity":** if `ξ S` is parallel to `ξ` (all `2 × 2` minors of the two rows vanish) for every `ξ`
in a nonempty open set, then `S = c I`. -/
theorem exists_eq_smul_one_of_vecMul_parallel (S : Matrix d d ℝ) (U : Set (d → ℝ))
    (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ ξ ∈ U, ∀ i j, (ξ ᵥ* S) i * ξ j = (ξ ᵥ* S) j * ξ i) :
    ∃ c : ℝ, S = c • (1 : Matrix d d ℝ) := by
  sorry

omit [DecidableEq d] in
/-- A matrix `M` with `ξ M = 0` for every row `ξ` of a nonempty open set is `0`. -/
theorem eq_zero_of_vecMul_eq_zero_of_isOpen {q : Type*} [Fintype q] (M : Matrix d q ℝ)
    (U : Set (d → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) (h : ∀ ξ ∈ U, ξ ᵥ* M = 0) : M = 0 := by
  sorry

end Skips
