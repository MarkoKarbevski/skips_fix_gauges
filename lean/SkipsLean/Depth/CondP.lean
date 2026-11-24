import SkipsLean.Depth.ComplexBlockIdentity

/-!
# The conditions (P1) and (P2) on a GELU block, and the rates of the hidden units

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), "The step for GELU on the path":

"Consider, for a block `ℓ` with `W = W_read^ℓ`, its columns `c_j`, `V = W_write^ℓ`, its rows `a_j`,
and `κ_ℓ` of Lemma D.14:
 (P1) the columns of `W` are pairwise different, no row of `V` vanishes, and the matrix `W V` is
      invertible;
 (P2) there is a unit row `ξ₀` such that, for every unit row `ξ'` orthogonal to `ξ₀`,
      `|ξ'c_j| < ξ₀c_j` for every `j`, `‖ξ' W V‖ < (κ_ℓ/2) ‖ξ₀ W V‖`,
      `∑_j e^{−d (ξ₀c_j)²/2} ‖a_j‖ < (κ_ℓ √d / 8) ‖ξ₀ W V‖`."

And from the proof of Lemma D.19: "Both sides of every inequality of (P2), the left sides as
suprema over `ξ'`, are continuous in `ξ₀`. So there is an open set `P` of unit rows around `ξ₀`
such that (P2) holds for every `ξ ∈ P` in the place of `ξ₀`"; "`r_j = (ξc_j)² − (ξ'c_j)² > 0`";
"Step 2: […] On an open dense set of pairs `(ξ, ξ')` the numbers `r_1, …, r_q` are pairwise
different: `r_i = r_j` on an open set of pairs would make `c_i c_iᵀ − c_j c_jᵀ` a multiple of the
identity, which is impossible for `c_i ≠ ±c_j`, and `c_i ≠ c_j` by (P1), `c_i ≠ −c_j` by (P2). Take
a hidden unit `j` and a nonempty open set of pairs, with `ξ ∈ P`, on which `r_j < r_i` for all
`i ≠ j`"; "Step 4: […] Take a nonempty open set of pairs `(ξ, ξ')`, with `ξ ∈ P`, on which
`r_{j_1} < r_{j_2} < ⋯ < r_{j_q}` for one order `j_1, …, j_q` of the hidden units."

The norms of rows in (P2) are Euclidean: `‖v‖ = √(v ⬝ᵥ v)` (the norm of `d → ℝ` in Lean is the sup
norm). `PathP2 W V κ ξ ξ'` holds the three inequalities for one pair `ξ, ξ'`. Rows are not asked to
be unit rows in the two statements: the unit row of `x ≠ 0` is `x̂ = ‖x‖⁻¹ x`, so that open sets of
rows `x` stand for open sets of unit rows. In `exists_isOpen_rates_lt` the open set of pairs is the
graph of a map `x ↦ ξ'(x)` over an open set `N` of rows, and the order `j_1, …, j_q` is a
bijection `e` of the hidden units with `Fin q`; the same `N` serves Step 2 (the unit `j_1`) and
Step 4. Block `k : Fin L` is the paper's block `k + 1`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

/-- **Condition (P1)** for block `k`: the columns of the read `W` are pairwise different, no row of
the write `V` vanishes, and `W V` is invertible. -/
def CondP1 (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin L) :
    Prop :=
  (∀ i j : hid k, i ≠ j → (fun a : d => θ.read k a i) ≠ fun a : d => θ.read k a j) ∧
    (∀ j : hid k, θ.write k j ≠ 0) ∧ IsUnit (θ.read k * θ.write k).det

/-- **The three inequalities of (P2) for one pair of rows `ξ, ξ'`,** for a read `W` (columns
`c_j`), a write `V` (rows `a_j`) and `κ`: `|ξ'c_j| < ξc_j` for every `j`,
`‖ξ' W V‖ < (κ/2) ‖ξ W V‖`, and `∑_j e^{−d (ξc_j)²/2} ‖a_j‖ < (κ √d / 8) ‖ξ W V‖`, with Euclidean
norms. -/
def PathP2 {q : Type*} [Fintype q] (W : Matrix d q ℝ) (V : Matrix q d ℝ) (κ : ℝ)
    (ξ ξ' : d → ℝ) : Prop :=
  (∀ j : q, |(ξ' ᵥ* W) j| < (ξ ᵥ* W) j) ∧
    Real.sqrt ((ξ' ᵥ* (W * V)) ⬝ᵥ (ξ' ᵥ* (W * V)))
      < κ / 2 * Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V))) ∧
    ∑ j : q, Real.exp (-((Fintype.card d : ℝ) * ((ξ ᵥ* W) j) ^ 2 / 2)) * Real.sqrt (V j ⬝ᵥ V j)
      < κ * Real.sqrt (Fintype.card d) / 8 * Real.sqrt ((ξ ᵥ* (W * V)) ⬝ᵥ (ξ ᵥ* (W * V)))

/-- **Condition (P2)** for block `k` and `κ`: there is a unit row `ξ₀` such that the three
inequalities hold for `ξ₀` and every unit row `ξ'` orthogonal to `ξ₀`. -/
def CondP2 (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (k : Fin L)
    (κ : ℝ) : Prop :=
  ∃ ξ₀ : d → ℝ, ξ₀ ⬝ᵥ ξ₀ = 1 ∧
    ∀ ξ' : d → ℝ, ξ' ⬝ᵥ ξ' = 1 → ξ₀ ⬝ᵥ ξ' = 0 → PathP2 (θ.read k) (θ.write k) κ ξ₀ ξ'

omit [DecidableEq d] in
/-- **"So there is an open set `P` of unit rows around `ξ₀` such that (P2) holds for every `ξ ∈ P`
in the place of `ξ₀`":** the rows `x ≠ 0` whose unit row `x̂ = ‖x‖⁻¹ x` satisfies the three
inequalities of (P2) with every unit row `ξ'` orthogonal to it form an open set. -/
theorem isOpen_setOf_pathP2 {q : Type*} [Fintype q] (W : Matrix d q ℝ) (V : Matrix q d ℝ)
    (κ : ℝ) :
    IsOpen {x : d → ℝ | x ≠ 0 ∧ ∀ ξ' : d → ℝ, ξ' ⬝ᵥ ξ' = 1 → x ⬝ᵥ ξ' = 0 →
      PathP2 W V κ ((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) ξ'} := by
  sorry

omit [DecidableEq d] in
/-- **The rates of the hidden units are in one strict order on an open set of pairs:** let
`d ≥ 2`, let the columns of `W` satisfy `c_i ≠ c_j` and `c_i ≠ −c_j` for `i ≠ j`, and let `U` be a
nonempty open set of rows. Then there are a nonempty open set `N ⊆ U` of rows `x ≠ 0`, for every
`x` a unit row `ξ'(x)` orthogonal to `x`, and an order `e` of the hidden units such that, for
every `x ∈ N`, the numbers `r_j = (x̂c_j)² − (ξ'(x)c_j)²` increase strictly along `e`. -/
theorem exists_isOpen_rates_lt {q : Type*} [Fintype q] (hd : 2 ≤ Fintype.card d)
    (W : Matrix d q ℝ)
    (hne : ∀ i j : q, i ≠ j → (fun a : d => W a i) ≠ fun a : d => W a j)
    (hneg : ∀ i j : q, i ≠ j → (fun a : d => W a i) ≠ fun a : d => -W a j)
    (U : Set (d → ℝ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ (N : Set (d → ℝ)) (ξ' : (d → ℝ) → d → ℝ) (e : q ≃ Fin (Fintype.card q)),
      IsOpen N ∧ N.Nonempty ∧ N ⊆ U ∧ (∀ x ∈ N, x ≠ 0) ∧
      ∀ x ∈ N, ξ' x ⬝ᵥ ξ' x = 1 ∧ x ⬝ᵥ ξ' x = 0 ∧
        ∀ i j : q, e i < e j →
          ((((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) ᵥ* W) i) ^ 2 - ((ξ' x ᵥ* W) i) ^ 2
            < ((((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) ᵥ* W) j) ^ 2 - ((ξ' x ᵥ* W) j) ^ 2 := by
  sorry

end Skips
