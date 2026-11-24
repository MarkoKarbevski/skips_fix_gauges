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
/-- Helper: a nonzero row has `x ⬝ x > 0`. -/
private theorem dotProduct_self_pos_cp {x : d → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x :=
  lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (x j))
    (Ne.symm (fun h => hx (dotProduct_self_eq_zero.1 h)))

omit [DecidableEq d] in
/-- Helper: `x ↦ ‖f x‖⁻¹ f x` is continuous at a point where `f` is continuous and nonzero. -/
private theorem continuousAt_unit_cp {E : Type*} [TopologicalSpace E] {f : E → d → ℝ}
    {x₀ : E} (hf : ContinuousAt f x₀) (h0 : f x₀ ≠ 0) :
    ContinuousAt (fun x => (Real.sqrt (f x ⬝ᵥ f x))⁻¹ • f x) x₀ := by
  have hdot : Continuous fun v : d → ℝ => v ⬝ᵥ v := by fun_prop
  have hs : ContinuousAt (fun x => Real.sqrt (f x ⬝ᵥ f x)) x₀ :=
    Real.continuous_sqrt.continuousAt.comp (hdot.continuousAt.comp hf)
  exact (hs.inv₀ (Real.sqrt_ne_zero'.2 (dotProduct_self_pos_cp h0))).smul hf

omit [DecidableEq d] in
/-- Helper: the unit rows form a compact set. -/
private theorem isCompact_unitRows_cp : IsCompact {ξ : d → ℝ | ξ ⬝ᵥ ξ = 1} := by
  have hc : IsClosed {ξ : d → ℝ | ξ ⬝ᵥ ξ = 1} := isClosed_eq (by fun_prop) continuous_const
  refine (isCompact_closedBall (0 : d → ℝ) 1).of_isClosed_subset hc fun ξ hξ => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  have h : ξ a * ξ a ≤ ξ ⬝ᵥ ξ :=
    Finset.single_le_sum (f := fun b => ξ b * ξ b) (fun b _ => mul_self_nonneg (ξ b))
      (Finset.mem_univ a)
  have h1 : ξ ⬝ᵥ ξ = 1 := hξ
  rw [h1] at h
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

omit [DecidableEq d] in
/-- Helper: the pairs `(ξ, ξ')` with the three inequalities of (P2) form an open set. -/
private theorem isOpen_pathP2_cp {q : Type*} [Fintype q] (W : Matrix d q ℝ) (V : Matrix q d ℝ)
    (κ : ℝ) : IsOpen {r : (d → ℝ) × (d → ℝ) | PathP2 W V κ r.1 r.2} := by
  rw [isOpen_iff_mem_nhds]
  rintro r₀ ⟨h1, h2, h3⟩
  have e1 : ∀ᶠ r in nhds r₀, ∀ j, |(r.2 ᵥ* W) j| < (r.1 ᵥ* W) j := by
    refine Filter.eventually_all.2 fun j => ?_
    have ha : Continuous fun r : (d → ℝ) × (d → ℝ) => |(r.2 ᵥ* W) j| := by fun_prop
    have hb : Continuous fun r : (d → ℝ) × (d → ℝ) => (r.1 ᵥ* W) j := by fun_prop
    exact ha.continuousAt.eventually_lt hb.continuousAt (h1 j)
  have e2 : ∀ᶠ r : (d → ℝ) × (d → ℝ) in nhds r₀,
      Real.sqrt ((r.2 ᵥ* (W * V)) ⬝ᵥ (r.2 ᵥ* (W * V)))
        < κ / 2 * Real.sqrt ((r.1 ᵥ* (W * V)) ⬝ᵥ (r.1 ᵥ* (W * V))) := by
    have ha : Continuous fun r : (d → ℝ) × (d → ℝ) =>
        Real.sqrt ((r.2 ᵥ* (W * V)) ⬝ᵥ (r.2 ᵥ* (W * V))) := by fun_prop
    have hb : Continuous fun r : (d → ℝ) × (d → ℝ) =>
        κ / 2 * Real.sqrt ((r.1 ᵥ* (W * V)) ⬝ᵥ (r.1 ᵥ* (W * V))) := by fun_prop
    exact ha.continuousAt.eventually_lt hb.continuousAt h2
  have e3 : ∀ᶠ r : (d → ℝ) × (d → ℝ) in nhds r₀,
      ∑ j : q, Real.exp (-((Fintype.card d : ℝ) * ((r.1 ᵥ* W) j) ^ 2 / 2))
          * Real.sqrt (V j ⬝ᵥ V j)
        < κ * Real.sqrt (Fintype.card d) / 8
          * Real.sqrt ((r.1 ᵥ* (W * V)) ⬝ᵥ (r.1 ᵥ* (W * V))) := by
    have ha : Continuous fun r : (d → ℝ) × (d → ℝ) =>
        ∑ j : q, Real.exp (-((Fintype.card d : ℝ) * ((r.1 ᵥ* W) j) ^ 2 / 2))
          * Real.sqrt (V j ⬝ᵥ V j) := by fun_prop
    have hb : Continuous fun r : (d → ℝ) × (d → ℝ) =>
        κ * Real.sqrt (Fintype.card d) / 8
          * Real.sqrt ((r.1 ᵥ* (W * V)) ⬝ᵥ (r.1 ᵥ* (W * V))) := by fun_prop
    exact ha.continuousAt.eventually_lt hb.continuousAt h3
  filter_upwards [e1, e2, e3] with r hr1 hr2 hr3
  exact And.intro hr1 (And.intro hr2 hr3)

omit [DecidableEq d] in
/-- **"So there is an open set `P` of unit rows around `ξ₀` such that (P2) holds for every `ξ ∈ P`
in the place of `ξ₀`":** the rows `x ≠ 0` whose unit row `x̂ = ‖x‖⁻¹ x` satisfies the three
inequalities of (P2) with every unit row `ξ'` orthogonal to it form an open set. -/
theorem isOpen_setOf_pathP2 {q : Type*} [Fintype q] (W : Matrix d q ℝ) (V : Matrix q d ℝ)
    (κ : ℝ) :
    IsOpen {x : d → ℝ | x ≠ 0 ∧ ∀ ξ' : d → ℝ, ξ' ⬝ᵥ ξ' = 1 → x ⬝ᵥ ξ' = 0 →
      PathP2 W V κ ((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) ξ'} := by
  rw [isOpen_iff_mem_nhds]
  rintro x₀ ⟨hx₀, h₀⟩
  -- near `(x₀, ξ'₀)`, for every unit row `ξ'₀`, the implication "orthogonal → (P2)" holds
  have hloc : ∀ ξ'₀ ∈ {ξ' : d → ℝ | ξ' ⬝ᵥ ξ' = 1},
      ∀ᶠ z : (d → ℝ) × (d → ℝ) in nhds (x₀, ξ'₀),
        z.1 ⬝ᵥ z.2 = 0 → PathP2 W V κ ((Real.sqrt (z.1 ⬝ᵥ z.1))⁻¹ • z.1) z.2 := by
    intro ξ'₀ hξ'₀
    by_cases h : x₀ ⬝ᵥ ξ'₀ = 0
    · -- (P2) holds at `(x̂₀, ξ'₀)`, and the set of pairs where it holds is open
      have hg : ContinuousAt (fun z : (d → ℝ) × (d → ℝ) =>
          ((Real.sqrt (z.1 ⬝ᵥ z.1))⁻¹ • z.1, z.2)) (x₀, ξ'₀) :=
        (continuousAt_unit_cp (f := Prod.fst) continuous_fst.continuousAt hx₀).prodMk
          continuousAt_snd
      have hmem := (isOpen_pathP2_cp W V κ).mem_nhds
        (x := ((Real.sqrt (x₀ ⬝ᵥ x₀))⁻¹ • x₀, ξ'₀)) (h₀ ξ'₀ hξ'₀ h)
      exact (hg.eventually_mem hmem).mono fun z hz _ => hz
    · -- `x ⬝ ξ' ≠ 0` near `(x₀, ξ'₀)`
      have hc : Continuous fun z : (d → ℝ) × (d → ℝ) => z.1 ⬝ᵥ z.2 := by fun_prop
      exact (hc.continuousAt.eventually_ne h).mono fun z hz h' => absurd h' hz
  -- the unit rows are compact: the tube lemma
  filter_upwards [isCompact_unitRows_cp.eventually_forall_of_forall_eventually
    (P := fun x ξ' => x ⬝ᵥ ξ' = 0 → PathP2 W V κ ((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) ξ') hloc,
    eventually_ne_nhds hx₀] with x hx hx0
  exact ⟨hx0, fun ξ' h1 h2 => hx ξ' h1 h2⟩


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
