import SkipsLean.Depth.CondP
import SkipsLean.Activations.MillsC

/-!
# One GELU block that satisfies all conditions of the case (0)

Paper (dimension paper): Appendix D.6, "Parameters that satisfy all conditions, in the case (0)":
"We choose the blocks from the last to the first. Let `D` and the blocks `ℓ + 1, …, L` be chosen,
regular and with […] (P1) and (P2) for GELU. This fixes `κ_ℓ` (Lemma D.14). We choose
`(W, V) = (W_read^ℓ, W_write^ℓ)`. Conditions that fail on a set of measure zero of pairs `(W, V)`.
(R1), (S1), (S2) and (P1) are of this kind […]. (R2): […]. (R3): […]. Conditions that hold on a
nonempty open set of pairs. […] (P2): take a row `α` with positive entries, any `V` with
`αV ≠ 0`, and `W° = ξ₀ᵀ α`. For `W°` the left sides of the first two inequalities of (P2) vanish
and `ξ₀c°_j = α_j > 0`, so these two inequalities hold for all `W = λ (W° + W')` with `λ > 0` and
`W'` small. For fixed small `W'`, the third holds for large `λ` […]. A nonempty open set minus a
set of measure zero is not empty."

Stated here: for every `κ > 0` there is a pair `(W, V)` that satisfies the conditions of one GELU
block, for one row (the paper's one token): (R1) for the write, `V` has rank `d`; (R2)
`GELU(nW) V ≠ 0` for every row `n` on the sphere `‖n‖² = d`; (R3) at some such `n`, a `v ⊥ n` with
`𝐃g(n) v ∈ ℝ g(n)` is `0`, where `g(n) = GELU(nW) V`; (P1); (P2) for `κ`.

The existence needs one pair only, and the Lean proof may take an explicit one, with the hidden
units `d ⊕ Fin m`: the columns of `W` are `λ (𝟙 + ε e_i)` (`i ∈ d`, `𝟙` the row of ones) and
`λ μ_j 𝟙`, the rows of `V` are `e_i` and `η 𝟙`, with `ξ₀ = 𝟙/√d`, `ε` small, `λ` large, then `η`
small.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **The conditions on one GELU block in the case (0),** for the read `W` (columns `c_j`), the
write `V` (rows `a_j`) and `κ`: (R1) for `V`, (R2), (R3), (P1), and (P2) for `κ`. -/
structure GeluPathBlock {q : Type*} [Fintype q] (W : Matrix d q ℝ) (V : Matrix q d ℝ) (κ : ℝ) :
    Prop where
  /-- (R1) for the write: `V` has rank `d`. -/
  rank_write : V.rank = Fintype.card d
  /-- (R2): `g(n) = GELU(nW) V ≠ 0` for every row `n` on the sphere `‖n‖² = d`. -/
  ne_zero : ∀ n : d → ℝ, n ⬝ᵥ n = (Fintype.card d : ℝ) →
    (fun j : q => gelu ((n ᵥ* W) j)) ᵥ* V ≠ 0
  /-- (R3): at some `n` on the sphere, a `v ⊥ n` with `𝐃g(n) v ∈ ℝ g(n)` is `0`. -/
  deriv : ∃ n : d → ℝ, n ⬝ᵥ n = (Fintype.card d : ℝ) ∧ ∀ v : d → ℝ, v ⬝ᵥ n = 0 →
    (∃ a : ℝ,
      fderiv ℝ (fun n' : d → ℝ => (fun j : q => gelu ((n' ᵥ* W) j)) ᵥ* V) n v
        = a • ((fun j : q => gelu ((n ᵥ* W) j)) ᵥ* V)) →
    v = 0
  /-- (P1): the columns of `W` are pairwise different. -/
  cols_ne : ∀ i j : q, i ≠ j → (fun a : d => W a i) ≠ fun a : d => W a j
  /-- (P1): no row of `V` vanishes. -/
  rows_ne : ∀ j : q, V j ≠ 0
  /-- (P1): `W V` is invertible. -/
  det_unit : IsUnit (W * V).det
  /-- (P2) for `κ`: a unit row `ξ₀` such that the three inequalities hold with every unit row `ξ'`
  orthogonal to `ξ₀`. -/
  p2 : ∃ ξ₀ : d → ℝ, ξ₀ ⬝ᵥ ξ₀ = 1 ∧
    ∀ ξ' : d → ℝ, ξ' ⬝ᵥ ξ' = 1 → ξ₀ ⬝ᵥ ξ' = 0 → PathP2 W V κ ξ₀ ξ'

/-- **"Parameters that satisfy all conditions, in the case (0)", one GELU block:** for `d ≥ 2`, at
least `d` hidden units and every `κ > 0`, there are a read `W` and a write `V` that satisfy (R1)
for the write, (R2), (R3), (P1), and (P2) for `κ`. -/
theorem exists_geluPathBlock {q : Type*} [Fintype q] (hd : 2 ≤ Fintype.card d)
    (hq : Fintype.card d ≤ Fintype.card q) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (W : Matrix d q ℝ) (V : Matrix q d ℝ), GeluPathBlock W V κ := by
  sorry

end Skips
