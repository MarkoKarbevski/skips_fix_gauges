import SkipsLean.Depth.StepTanh

/-!
# Generic rays: the exponents of the gates are independent over `ℚ`

Paper (dimension): Appendix D.5, proof of Lemma D.12, "A generic ray", condition (i): "the numbers
`r_1, …, r_q` are linearly independent over `ℚ`", where `r_j = |ξ c_j|^p`. "These `ξ` are dense in
`C_k`. For (i): if integers `κ_1, …, κ_q` are not all zero, `∑_j κ_j r_j` is
`ξ (∑_j κ_j c_j c_j^⊤) ξ^⊤` for GELU and GeGLU blocks and `ξ ∑_j κ_j s_j c_j` for SwiGLU blocks,
and by (K3) it vanishes only for `ξ` on a quadric, or in a hyperplane."

Stated here for the hidden units of several tokens: `Ξ` has one row `ξ_t` per token, and the
numbers `|ξ_t c_j|` (`p = 1`), or `(ξ_t c_j)²` (`p = 2`), over all tokens `t` and all hidden units
`j`, are linearly independent over `ℚ` for a dense set of `Ξ`. (For `p = 1` the sign of `ξ_t c_j`
does not matter for the independence.) The same statement for the numbers `ξ_t c_j` themselves is
`dense_setOf_linearIndependent_mul` in `Depth/StepTanh.lean`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d : Type*} [Fintype T] [Fintype d] [DecidableEq d]

/-- **(i) on a generic ray, `p = 1`:** if the columns `c_j` are linearly independent over `ℚ`, then
for a dense set of matrices `Ξ` the numbers `|ξ_t c_j|`, over all tokens and all hidden units, are
linearly independent over `ℚ`. -/
theorem dense_setOf_linearIndependent_abs_dotProduct {q : Type*} [Fintype q] (c : q → d → ℝ)
    (hc : LinearIndependent ℚ c) :
    Dense {Ξ : Matrix T d ℝ | LinearIndependent ℚ (fun i : T × q => |Ξ i.1 ⬝ᵥ c i.2|)} := by
  sorry

/-- **(i) on a generic ray, `p = 2`:** if the matrices `c_j c_j^⊤` are linearly independent over
`ℚ`, then for a dense set of matrices `Ξ` the numbers `(ξ_t c_j)²`, over all tokens and all hidden
units, are linearly independent over `ℚ`. -/
theorem dense_setOf_linearIndependent_sq_dotProduct {q : Type*} [Fintype q] (c : q → d → ℝ)
    (hc : LinearIndependent ℚ (fun j : q => Matrix.vecMulVec (c j) (c j))) :
    Dense {Ξ : Matrix T d ℝ | LinearIndependent ℚ (fun i : T × q => (Ξ i.1 ⬝ᵥ c i.2) ^ 2)} := by
  sorry

end Skips
