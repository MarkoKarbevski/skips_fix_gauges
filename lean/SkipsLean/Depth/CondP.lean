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
/-- Helper: `v(x, y) = (x ⬝ x) y − (x ⬝ y) x`, a row orthogonal to `x`. -/
private noncomputable def orthRow_cp (x y : d → ℝ) : d → ℝ := (x ⬝ᵥ x) • y - (x ⬝ᵥ y) • x

omit [DecidableEq d] in
/-- Helper: `F_{ij}(x, y) = ((x c_i)² − (x c_j)²)(v ⬝ v) − ((v c_i)² − (v c_j)²)(x ⬝ x)`, with
`v = v(x, y)`, a polynomial in `(x, y)`. -/
private noncomputable def rateDiff_cp {q : Type*} [Fintype q] (W : Matrix d q ℝ) (i j : q)
    (p : (d → ℝ) × (d → ℝ)) : ℝ :=
  ((p.1 ᵥ* W) i ^ 2 - (p.1 ᵥ* W) j ^ 2) * (orthRow_cp p.1 p.2 ⬝ᵥ orthRow_cp p.1 p.2) -
    ((orthRow_cp p.1 p.2 ᵥ* W) i ^ 2 - (orthRow_cp p.1 p.2 ᵥ* W) j ^ 2) * (p.1 ⬝ᵥ p.1)

omit [DecidableEq d] in
/-- Helper: `x ⬝ v(x, y) = 0`. -/
private theorem dot_orthRow_cp (x y : d → ℝ) : x ⬝ᵥ orthRow_cp x y = 0 := by
  unfold orthRow_cp
  rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

omit [DecidableEq d] in
/-- Helper: the coordinates of `x` and `y` are analytic functions of the pair `(x, y)`. -/
private theorem analyticAt_coord_cp (p : (d → ℝ) × (d → ℝ)) (a : d) :
    AnalyticAt ℝ (fun p : (d → ℝ) × (d → ℝ) => p.1 a) p ∧
      AnalyticAt ℝ (fun p : (d → ℝ) × (d → ℝ) => p.2 a) p :=
  ⟨(ContinuousLinearMap.proj a ∘L ContinuousLinearMap.fst ℝ (d → ℝ) (d → ℝ)).analyticAt p,
    (ContinuousLinearMap.proj a ∘L ContinuousLinearMap.snd ℝ (d → ℝ) (d → ℝ)).analyticAt p⟩

omit [DecidableEq d] in
/-- Helper: `G₀(x, y) = (x ⬝ x)(v ⬝ v)` is analytic (a polynomial in the entries of `(x, y)`). -/
private theorem analyticAt_gram_cp (p : (d → ℝ) × (d → ℝ)) :
    AnalyticAt ℝ (fun p : (d → ℝ) × (d → ℝ) =>
      (p.1 ⬝ᵥ p.1) * (orthRow_cp p.1 p.2 ⬝ᵥ orthRow_cp p.1 p.2)) p := by
  have h1 := fun a => (analyticAt_coord_cp p a).1
  have h2 := fun a => (analyticAt_coord_cp p a).2
  unfold orthRow_cp
  simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

omit [DecidableEq d] in
/-- Helper: `F_{ij}` is analytic (a polynomial in the entries of `(x, y)`). -/
private theorem analyticAt_rateDiff_cp {q : Type*} [Fintype q] (W : Matrix d q ℝ) (i j : q)
    (p : (d → ℝ) × (d → ℝ)) : AnalyticAt ℝ (rateDiff_cp W i j) p := by
  have h1 := fun a => (analyticAt_coord_cp p a).1
  have h2 := fun a => (analyticAt_coord_cp p a).2
  unfold rateDiff_cp orthRow_cp
  simp only [dotProduct, vecMul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

omit [DecidableEq d] in
/-- Helper: for `x ⬝ y = 0`, `v(x, y) = (x ⬝ x) y`, and `F_{ij}(x, y)` is `(x ⬝ x)²` times
`((x c_i)² − (x c_j)²)(y ⬝ y) − ((y c_i)² − (y c_j)²)(x ⬝ x)`. -/
private theorem rateDiff_of_orth_cp {q : Type*} [Fintype q] (W : Matrix d q ℝ) (i j : q)
    {x y : d → ℝ} (h : x ⬝ᵥ y = 0) :
    rateDiff_cp W i j (x, y) = (x ⬝ᵥ x) ^ 2 * (((x ᵥ* W) i ^ 2 - (x ᵥ* W) j ^ 2) * (y ⬝ᵥ y) -
      ((y ᵥ* W) i ^ 2 - (y ᵥ* W) j ^ 2) * (x ⬝ᵥ x)) := by
  have hv : orthRow_cp x y = (x ⬝ᵥ x) • y := by
    unfold orthRow_cp
    rw [h, zero_smul, sub_zero]
  unfold rateDiff_cp
  dsimp only
  simp only [hv, smul_vecMul, dotProduct_smul, smul_dotProduct, Pi.smul_apply, smul_eq_mul]
  ring

/-- Helper (the brief's Steps 1 and 3): for columns `c_i ≠ ±c_j`, `F_{ij}` is not identically
zero. -/
private theorem exists_rateDiff_ne_zero_cp {q : Type*} [Fintype q]
    (hd : 2 ≤ Fintype.card d) (W : Matrix d q ℝ) {i j : q}
    (hne : (fun a : d => W a i) ≠ fun a : d => W a j)
    (hneg : (fun a : d => W a i) ≠ fun a : d => -W a j) :
    ∃ p, rateDiff_cp W i j p ≠ 0 := by
  by_contra hF
  have hF' : ∀ p, rateDiff_cp W i j p = 0 := fun p => by_contra fun h => hF ⟨p, h⟩
  have hdd : ∀ a b : d, Pi.single a (1 : ℝ) ⬝ᵥ Pi.single b 1 = if a = b then 1 else 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp only [dotProduct_single, Pi.single_eq_same, mul_one, ↓reduceIte]
    · simp only [dotProduct_single, ne_eq, hab, not_false_eq_true, Pi.single_eq_of_ne', mul_one,
        ↓reduceIte]
  have hvm : ∀ (a : d) (k : q), (Pi.single a (1 : ℝ) ᵥ* W) k = W a k := by
    intro a k
    simp only [single_vecMul, Pi.smul_apply, row_apply, smul_eq_mul, one_mul]
  -- the pair `(e_a, e_b)` gives `M_aa = M_bb`
  have h1 : ∀ a b : d, a ≠ b → W a i ^ 2 - W a j ^ 2 = W b i ^ 2 - W b j ^ 2 := by
    intro a b hab
    have h := hF' (Pi.single a 1, Pi.single b 1)
    rw [rateDiff_of_orth_cp W i j (by simp only [hdd, hab, ↓reduceIte])] at h
    simp only [hvm, hdd, ↓reduceIte] at h
    linear_combination h
  -- the pair `(e_a + e_b, e_a − e_b)` gives `M_ab = 0`
  have h2 : ∀ a b : d, a ≠ b → W a i * W b i = W a j * W b j := by
    intro a b hab
    have h := hF' ((Pi.single a 1 + Pi.single b 1 : d → ℝ),
      (Pi.single a 1 - Pi.single b 1 : d → ℝ))
    have horth : (Pi.single a 1 + Pi.single b 1 : d → ℝ) ⬝ᵥ
        (Pi.single a 1 - Pi.single b 1 : d → ℝ) = 0 := by
      simp only [add_dotProduct, dotProduct_sub, hdd, hab, Ne.symm hab, ↓reduceIte]
      ring
    rw [rateDiff_of_orth_cp W i j horth] at h
    simp only [add_vecMul, sub_vecMul, Pi.add_apply, Pi.sub_apply, hvm, add_dotProduct,
      dotProduct_add, sub_dotProduct, dotProduct_sub, hdd, hab, Ne.symm hab, ↓reduceIte] at h
    linear_combination h / 32
  -- hence `c_i(a)² = c_j(a)²` for every `a`
  have hsq : ∀ a, W a i ^ 2 = W a j ^ 2 := by
    intro a
    obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card d) a
    have e1 := h1 a b (Ne.symm hb)
    have e2 := h2 a b (Ne.symm hb)
    -- `(c_i(a)² − c_j(a)²)² + (c_i(a) c_j(b) − c_j(a) c_i(b))² = 0`
    have key : (W a i ^ 2 - W a j ^ 2) ^ 2 + (W a i * W b j - W a j * W b i) ^ 2 = 0 := by
      linear_combination (W a i ^ 2 - W a j ^ 2) * e1 + (W a i * W b i - W a j * W b j) * e2
    have hX : (W a i ^ 2 - W a j ^ 2) ^ 2 = 0 := by
      linarith [sq_nonneg (W a i ^ 2 - W a j ^ 2), sq_nonneg (W a i * W b j - W a j * W b i)]
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hX)
  -- and `c_i(a) c_i(b) = c_j(a) c_j(b)` for all `a, b`
  have hprod : ∀ a b, W a i * W b i = W a j * W b j := by
    intro a b
    by_cases hab : a = b
    · subst hab
      linear_combination hsq a
    · exact h2 a b hab
  -- so `c_i = ±c_j`
  by_cases h0 : ∃ a₀, W a₀ i ≠ 0
  · obtain ⟨a₀, ha₀⟩ := h0
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hsq a₀) with h | h
    · exact hne (funext fun b => mul_left_cancel₀ ha₀
        (by linear_combination hprod a₀ b - W b j * h))
    · exact hneg (funext fun b => mul_left_cancel₀ ha₀
        (by linear_combination hprod a₀ b + W b j * h))
  · simp only [not_exists, not_not] at h0
    apply hne
    funext a
    have h := hsq a
    rw [h0 a] at h ⊢
    have h' : W a j ^ 2 = 0 := by rw [← h]; norm_num
    exact ((pow_eq_zero_iff two_ne_zero).1 h').symm

/-- Helper: the nonzero set of a real-analytic function on a normed space that is not identically
zero is open and dense (identity theorem). -/
private theorem dense_ne_zero_cp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : AnalyticOnNhd ℝ f Set.univ) (hne : ∃ x, f x ≠ 0) :
    IsOpen {x | f x ≠ 0} ∧ Dense {x | f x ≠ 0} := by
  have hc : Continuous f := continuousOn_univ.mp hf.continuousOn
  refine ⟨isOpen_ne_fun hc continuous_const, ?_⟩
  rw [dense_iff_inter_open]
  rintro O hO ⟨z, hz⟩
  by_contra h
  have hzero : f =ᶠ[nhds z] 0 := by
    filter_upwards [hO.mem_nhds hz] with w hw
    by_contra hw'
    exact h ⟨w, hw, hw'⟩
  obtain ⟨x, hx⟩ := hne
  exact hx (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z) hzero (Set.mem_univ x))

omit [DecidableEq d] in
/-- Helper: a nonzero row, normalized, is a unit row. -/
private theorem unit_dot_self_cp {v : d → ℝ} (hv : v ≠ 0) :
    ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) ⬝ᵥ ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) = 1 := by
  have hx := dotProduct_self_pos_cp hv
  rw [smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul, ← _root_.mul_inv,
    Real.mul_self_sqrt hx.le, inv_mul_cancel₀ hx.ne']

omit [DecidableEq d] in
/-- Helper: `((x̂ W)_i)² = (x W)_i² / (x ⬝ x)`. -/
private theorem sq_unit_vecMul_cp {q : Type*} [Fintype q] (W : Matrix d q ℝ) (x : d → ℝ)
    (i : q) : ((((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) ᵥ* W) i) ^ 2 = (x ᵥ* W) i ^ 2 / (x ⬝ᵥ x) := by
  have h0 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun a _ => mul_self_nonneg (x a)
  rw [smul_vecMul, Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow, Real.sq_sqrt h0,
    div_eq_inv_mul]

omit [DecidableEq d] in
/-- Helper: with `ξ = x̂` and `ξ' = v̂`, `v = v(x, y)`, equal rates `r_i = r_j` give
`F_{ij}(x, y) = 0` (as `(x ⬝ x)(v ⬝ v)(r_i − r_j) = F_{ij}(x, y)`). -/
private theorem rateDiff_eq_zero_cp {q : Type*} [Fintype q] (W : Matrix d q ℝ) {x y : d → ℝ}
    (hx : x ≠ 0) (hv : orthRow_cp x y ≠ 0) (r : q → ℝ)
    (hr : ∀ k, r k = ((((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) ᵥ* W) k) ^ 2 -
      ((((Real.sqrt (orthRow_cp x y ⬝ᵥ orthRow_cp x y))⁻¹ • orthRow_cp x y) ᵥ* W) k) ^ 2)
    {i j : q} (h : r i = r j) : rateDiff_cp W i j (x, y) = 0 := by
  have h1 := (dotProduct_self_pos_cp hx).ne'
  have h2 := (dotProduct_self_pos_cp hv).ne'
  rw [hr, hr, sq_unit_vecMul_cp, sq_unit_vecMul_cp, sq_unit_vecMul_cp, sq_unit_vecMul_cp] at h
  unfold rateDiff_cp
  dsimp only
  field_simp at h
  linear_combination h

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
  classical
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card d)
  -- Step 4: `G₀ = (x ⬝ x)(v ⬝ v)` and the `F_{ij}`, `i ≠ j`, are nonzero on a dense open set of
  -- pairs `(x, y)`, which meets the open set of pairs with `x ∈ U`
  have hG := dense_ne_zero_cp (f := fun p : (d → ℝ) × (d → ℝ) =>
      (p.1 ⬝ᵥ p.1) * (orthRow_cp p.1 p.2 ⬝ᵥ orthRow_cp p.1 p.2))
    (fun p _ => analyticAt_gram_cp p) ⟨(Pi.single a 1, Pi.single b 1), by
      have hv : orthRow_cp (Pi.single a (1 : ℝ)) (Pi.single b 1) = Pi.single b 1 := by
        unfold orthRow_cp
        simp only [dotProduct_single, Pi.single_eq_same, mul_one, one_smul, ne_eq, hab,
          not_false_eq_true, Pi.single_eq_of_ne', zero_smul, sub_zero]
      simp only [hv, dotProduct_single, Pi.single_eq_same, mul_one, ne_eq, one_ne_zero,
        not_false_eq_true]⟩
  set S : Set (q × q) := {ij | ij.1 ≠ ij.2} with hS
  have hF : ∀ ij ∈ S, IsOpen {p : (d → ℝ) × (d → ℝ) | rateDiff_cp W ij.1 ij.2 p ≠ 0} ∧
      Dense {p : (d → ℝ) × (d → ℝ) | rateDiff_cp W ij.1 ij.2 p ≠ 0} := fun ij hij =>
    dense_ne_zero_cp (fun p _ => analyticAt_rateDiff_cp W ij.1 ij.2 p)
      (exists_rateDiff_ne_zero_cp hd W (hne _ _ hij) (hneg _ _ hij))
  have hD := hG.2.inter_of_isOpen_left (dense_biInter_of_isOpen (fun ij h => (hF ij h).1)
    S.to_countable fun ij h => (hF ij h).2) hG.1
  obtain ⟨x₀, hx₀⟩ := hUne
  obtain ⟨⟨x₁, y₁⟩, hx₁U, hG₁, hF₁⟩ :=
    hD.inter_open_nonempty (Prod.fst ⁻¹' U) (hU.preimage continuous_fst) ⟨(x₀, 0), hx₀⟩
  have hG₁' : x₁ ⬝ᵥ x₁ * (orthRow_cp x₁ y₁ ⬝ᵥ orthRow_cp x₁ y₁) ≠ 0 := hG₁
  have hx₁ : x₁ ≠ 0 := fun h => (mul_ne_zero_iff.1 hG₁').1 (by rw [h, zero_dotProduct])
  have hv₁ : orthRow_cp x₁ y₁ ≠ 0 := fun h =>
    (mul_ne_zero_iff.1 hG₁').2 (by rw [h, zero_dotProduct])
  have hF₁' : ∀ i j : q, i ≠ j → rateDiff_cp W i j (x₁, y₁) ≠ 0 := fun i j hij =>
    Set.mem_iInter₂.1 hF₁ (i, j) hij
  -- Step 5: `ξ'(x) = v̂(x, y₁)` and the rates `ρ_i(x) = (x̂ c_i)² − (ξ'(x) c_i)²`
  obtain ⟨ξ', hξ'⟩ : ∃ ξ' : (d → ℝ) → d → ℝ, ∀ x, ξ' x =
      (Real.sqrt (orthRow_cp x y₁ ⬝ᵥ orthRow_cp x y₁))⁻¹ • orthRow_cp x y₁ := ⟨_, fun _ => rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : q → (d → ℝ) → ℝ, ∀ i x, ρ i x =
      ((((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) ᵥ* W) i) ^ 2 - ((ξ' x ᵥ* W) i) ^ 2 :=
    ⟨_, fun _ _ => rfl⟩
  -- the rates at `x₁` are pairwise different
  have hinj : Function.Injective fun i => ρ i x₁ := fun i j h => by_contra fun hij =>
    hF₁' i j hij (rateDiff_eq_zero_cp W hx₁ hv₁ (fun k => ρ k x₁)
      (fun k => by rw [hρ, hξ']) h)
  -- the order `e` of the hidden units along which the rates at `x₁` increase
  let _ : LinearOrder q := LinearOrder.lift' _ hinj
  set o : q ≃o Fin (Fintype.card q) := (Fintype.orderIsoFinOfCardEq q rfl).symm with ho
  have he : ∀ i j, o.toEquiv i < o.toEquiv j → ρ i x₁ < ρ j x₁ := fun i j h => o.lt_iff_lt.1 h
  -- `ρ_i` is continuous where `x ≠ 0` and `v(x, y₁) ≠ 0`
  have hvc : Continuous fun x => orthRow_cp x y₁ := by
    unfold orthRow_cp
    fun_prop
  have hρc : ∀ i x, x ≠ 0 → orthRow_cp x y₁ ≠ 0 → ContinuousAt (ρ i) x := by
    intro i x hx hv
    have hW : Continuous fun v : d → ℝ => (v ᵥ* W) i := by fun_prop
    have h1 := continuousAt_unit_cp (f := id) continuousAt_id hx
    have h2 := continuousAt_unit_cp hvc.continuousAt hv
    have h3 := ((hW.continuousAt.comp h1).pow 2).sub ((hW.continuousAt.comp h2).pow 2)
    have hρf : ρ i = fun x => ((((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) ᵥ* W) i) ^ 2 - ((ξ' x ᵥ* W) i) ^ 2 :=
      funext (hρ i)
    simp only [hρf, hξ']
    exact h3
  -- the open set `N`
  refine ⟨{x | x ∈ U ∧ x ≠ 0 ∧ orthRow_cp x y₁ ≠ 0 ∧
      ∀ i j, o.toEquiv i < o.toEquiv j → ρ i x < ρ j x}, ξ', o.toEquiv, ?_,
    ⟨x₁, hx₁U, hx₁, hv₁, he⟩, fun x hx => hx.1, fun x hx => hx.2.1, fun x hx => ?_⟩
  · rw [isOpen_iff_mem_nhds]
    rintro x₂ ⟨hU2, hx2, hv2, hρ2⟩
    have hall : ∀ᶠ x in nhds x₂, ∀ i j, o.toEquiv i < o.toEquiv j → ρ i x < ρ j x := by
      refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      by_cases hij : o.toEquiv i < o.toEquiv j
      · exact ((hρc i x₂ hx2 hv2).eventually_lt (hρc j x₂ hx2 hv2) (hρ2 i j hij)).mono
          fun x hx _ => hx
      · exact Filter.Eventually.of_forall fun x h => absurd h hij
    filter_upwards [hU.mem_nhds hU2, eventually_ne_nhds hx2,
      hvc.continuousAt.eventually_ne hv2, hall] with x h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  · obtain ⟨-, -, hv, hρx⟩ := hx
    refine ⟨by rw [hξ']; exact unit_dot_self_cp hv, ?_, fun i j hij => ?_⟩
    · rw [hξ', dotProduct_smul, dot_orthRow_cp, smul_zero]
    · have h := hρx i j hij
      rw [hρ, hρ] at h
      exact h

end Skips
