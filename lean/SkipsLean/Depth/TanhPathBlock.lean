import SkipsLean.Depth.ComplexRMSNorm

/-!
# One `tanh` block that satisfies all conditions of the case (0)

Paper (dimension paper): Appendix D.6, "Parameters that satisfy all conditions, in the case (0)":
"We choose the blocks from the last to the first. Let `D` and the blocks `ℓ + 1, …, L` be chosen,
regular and with (S1) to (S3) for tanh […]. This fixes `κ_ℓ` (Lemma D.14). We choose
`(W, V) = (W_read^ℓ, W_write^ℓ)`. Conditions that fail on a set of measure zero of pairs `(W, V)`.
(R1), (S1), (S2) and (P1) are of this kind […]. (R2): […]. (R3): the determinant in the proof of
Lemma D.2 is real-analytic in `(n, W, V)`, so (R3) fails on a set of measure zero once it holds for
one pair. It holds for `W = [I | 0]` and `V` with the rows of `I` and zero rows, at any `n ∈ S`
with positive entries `n_i` […]. Conditions that hold on a nonempty open set of pairs. (S3): take
any `V` and `W°`, with the columns `c°_j`, and a unit row `ξ₀` with `ξ₀c°_j ≠ 0` and `s̄V ≠ 0` for
the row `s̄` of the signs. As `s̄V` is a real nonzero row, there is a `ρ` as in (S3). Then
`W = λW°` satisfies (S3) for large `λ > 0` […]. A nonempty open set minus a set of measure zero is
not empty."

Stated here: for every cone `C_κ`, `κ > 0`, there is a pair `(W, V)` that satisfies the conditions
of one `tanh` block, for one row (the paper's one token):
(R1) for the write, `V` has rank `d`; (R2) `tanh(nW) V ≠ 0` for every row `n` on the sphere
`‖n‖² = d`; (R3) at some such `n`, a `v ⊥ n` with `𝐃g(n) v ∈ ℝ g(n)` is `0`, where
`g(n) = tanh(nW) V`; (S1) any two rows of `V` are linearly independent; (S2) the columns of `W` are
linearly independent over `ℚ`; (S3) for `C_κ`.

The existence needs one pair only, and the Lean proof may take it in the family `V = Wᵀ` (the
paper's pair for (R3) is of this kind): there (R2) holds as soon as `W` has rank `d`, because
`⟨tanh(nW) Wᵀ, n⟩ = ∑_j tanh(n c_j) (n c_j) > 0`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {d : Type*} [Fintype d]

/-- **The conditions on one `tanh` block in the case (0),** for the read `W` (columns `c_j`), the
write `V` and the cone `C_κ`: (R1) for `V`, (R2), (R3), (S1), (S2), and (S3) for `C_κ`. -/
structure TanhPathBlock {q : Type*} [Fintype q] (W : Matrix d q ℝ) (V : Matrix q d ℝ) (κ : ℝ) :
    Prop where
  /-- (R1) for the write: `V` has rank `d`. -/
  rank_write : V.rank = Fintype.card d
  /-- (R2): `g(n) = tanh(nW) V ≠ 0` for every row `n` on the sphere `‖n‖² = d`. -/
  ne_zero : ∀ n : d → ℝ, n ⬝ᵥ n = (Fintype.card d : ℝ) →
    (fun j : q => Real.tanh ((n ᵥ* W) j)) ᵥ* V ≠ 0
  /-- (R3): at some `n` on the sphere, a `v ⊥ n` with `𝐃g(n) v ∈ ℝ g(n)` is `0`. -/
  deriv : ∃ n : d → ℝ, n ⬝ᵥ n = (Fintype.card d : ℝ) ∧ ∀ v : d → ℝ, v ⬝ᵥ n = 0 →
    (∃ a : ℝ,
      fderiv ℝ (fun n' : d → ℝ => (fun j : q => Real.tanh ((n' ᵥ* W) j)) ᵥ* V) n v
        = a • ((fun j : q => Real.tanh ((n ᵥ* W) j)) ᵥ* V)) →
    v = 0
  /-- (S1): any two rows of `V` are linearly independent. -/
  rows_indep : ∀ i j : q, i ≠ j → ∀ a c : ℝ, a • V i + c • V j = 0 → a = 0 ∧ c = 0
  /-- (S2): the columns of `W` are linearly independent over `ℚ`. -/
  cols_indep : LinearIndependent ℚ (fun j : q => fun i : d => W i j)
  /-- (S3) for `C_κ`: a unit row `ξ₀` and a `ρ ∈ (0, 1]` such that every `ξ₀c_j ≠ 0`, the rows
  `w̃V` with `|w̃_j − s_j| ≤ ρ` (`s_j` the sign of `ξ₀c_j`) lie in `C_κ`, and
  `e^{−2√d |ξ₀c_j|} < ρ/3`. -/
  saturated : ∃ (ξ₀ : d → ℝ) (ρ : ℝ), ξ₀ ⬝ᵥ ξ₀ = 1 ∧ 0 < ρ ∧ ρ ≤ 1 ∧
    (∀ j : q, (ξ₀ ᵥ* W) j ≠ 0) ∧
    (∀ w : q → ℂ, (∀ j, ‖w j - ((Real.sign ((ξ₀ ᵥ* W) j) : ℝ) : ℂ)‖ ≤ ρ) →
      w ᵥ* V.map (fun x : ℝ => (x : ℂ)) ∈ complexCone κ) ∧
    ∀ j : q, Real.exp (-(2 * (Real.sqrt (Fintype.card d) * |(ξ₀ ᵥ* W) j|))) < ρ / 3

/-- **"Parameters that satisfy all conditions, in the case (0)", one block:** for `d ≥ 2`, at least
`d` hidden units and every `κ > 0`, there are a read `W` and a write `V` that satisfy (R1) for the
write, (R2), (R3), (S1), (S2), and (S3) for the cone `C_κ`. -/
theorem exists_tanhPathBlock {q : Type*} [Fintype q] (hd : 2 ≤ Fintype.card d)
    (hq : Fintype.card d ≤ Fintype.card q) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (W : Matrix d q ℝ) (V : Matrix q d ℝ), TanhPathBlock W V κ := by
  sorry

end Skips
