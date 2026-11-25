import SkipsLean.OneBlock.UnitsParallelAt
import SkipsLean.OneBlock.QuadraticResultant

/-!
# A direction that keeps the output of ReLU² units parallel: units in general position

Paper (skips paper), proof of Theorem B.1 (iv), "The skipless network: equality", for
`σ(z) = max(z, 0)^k`, `k = 1` or `2`, with `h_1 = ∑_i σ(x c_i) a_i`: equation (18),

`J(x) := ∑_i [σ(x c_i) (ψa_i − a_i Y) + σ'(x c_i) (x ψc_i) a_i] = μ(x) h_1(x)` on `Ω`,

"The kinks stay": "For `k = 2`, both sides, `μ` and the derivative of `h_1` in `x` are continuous
at `x_0`. The derivative in `x` of the left side jumps by the matrix `2 (x_0 ψc_i) c_i a_i`, and
that of the right side by a column times the row `h_1(x_0)`; two such matrices are equal only if
both vanish. In both cases `x_0 ψc_i = 0` on an open subset of the hyperplane, so
`ψc_i = λ_i c_i` for a number `λ_i`", and "One scale": "On a region where at least two units are
active, the entries of `J` and of `h_1` are homogeneous polynomials of degree `k` in `x`, and for
generic parameters two entries `h_a` and `h_b` of `h_1` have no common factor. […] Hence `μ = c`
on `Ω` for one number `c`".

`OneBlock/UnitsParallel.lean` has the two steps for linearly independent columns `c_i` and rows
`a_i` (a block of width exactly `d_model`), for ReLU and ReLU²; `OneBlock/UnitsParallelAt.lean`
for ReLU units in general position, also more units than coordinates. Here the same for ReLU²
(`k = 2`), also more units than coordinates. The paper's "for generic parameters" are hypotheses
on `c` and `a`:

* the `c_i` are pairwise non-collinear (also not opposite), the `a_i` nonzero;
* `h_1 ≠ 0` on `Ω` ("for generic parameters `h_1 ≠ 0` there"), at every `x` with an active unit;
* for every unit `i` one point `x_0` of its hyperplane, on no other hyperplane, at which
  `h_1(x_0)` is not a multiple of `a_i`;
* "two entries `h_a` and `h_b` of `h_1` have no common factor": for every set `S` of at least two
  units there are a line `t ↦ u + t v` and two entries `e`, `f` such that the two polynomials of
  degree at most two `t ↦ ∑_{i∈S} ((u + t v) c_i)² a_{i e}` and
  `t ↦ ∑_{i∈S} ((u + t v) c_i)² a_{i f}` have a resultant that is not zero (`quadRes`,
  `OneBlock/QuadraticResultant.lean`). The paper does not show that its condition holds for
  generic parameters; this one does, at almost every parameter
  (`OneBlock/SkiplessReluSqWideRMSZero.lean`).

The Lean route for "The kinks stay" uses no derivative in `x`: on the two sides of the
hyperplane of unit `i` the vectors `J` and `h_1` are parallel, which are polynomial identities;
their difference, divided by `x c_i`, has the value `2 (x_0 ψc_i) a_i ∧ h_1(x_0)` at `x_0`.

Exact check of the dimension `q + 1` of the solutions, more units than coordinates (up to eight
units in two coordinates): `units_parallel_relusq_wide_check_2026-11-25.py` (28 cases; with two
collinear columns the dimension is higher).
-/

namespace Skips

open Matrix

/-- `max(y, 0)² = 1[y > 0] y²`. -/
private lemma reluSq_eq_upq (y : ℝ) : reluSq y = reluDeriv y * (y * y) := by
  unfold reluSq reluDeriv
  split_ifs with h
  · rw [one_mul, max_eq_left h.le, sq]
  · rw [zero_mul, max_eq_right (not_lt.1 h)]
    norm_num

/-- `2 max(y, 0) = 2 · 1[y > 0] y`. -/
private lemma reluSqDeriv_eq_upq (y : ℝ) : reluSqDeriv y = 2 * (reluDeriv y * y) := by
  unfold reluSqDeriv reluDeriv
  split_ifs with h
  · rw [one_mul, max_eq_left h.le]
  · rw [zero_mul, max_eq_right (not_lt.1 h)]

/-- Two numbers of the same sign have the same slope `1[· > 0]`. -/
private lemma reluDeriv_eq_upq {u v : ℝ} (h : 0 < u * v) : reluDeriv v = reluDeriv u := by
  unfold reluDeriv
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · simp only [hu, hv, ↓reduceIte]
  · simp only [not_lt.2 hu.le, not_lt.2 hv.le, ↓reduceIte]

/-- On the cone of `u` (`u v > 0`), and at `v = 0`: `σ(v) = 1[u > 0] v²` and
`σ'(v) = 2 · 1[u > 0] v`. -/
private lemma cone_upq {u v : ℝ} (h : 0 < u * v ∨ v = 0) :
    reluSq v = reluDeriv u * (v * v) ∧ reluSqDeriv v = 2 * (reluDeriv u * v) := by
  rcases h with h | rfl
  · rw [reluSq_eq_upq, reluSqDeriv_eq_upq, reluDeriv_eq_upq h]
    exact ⟨rfl, rfl⟩
  · constructor <;> simp [reluSq, reluSqDeriv]

/-- The same on the closed cone `u v ≥ 0` of a number `u ≠ 0`. -/
private lemma cone'_upq {u v : ℝ} (hu : u ≠ 0) (h : 0 ≤ u * v) :
    reluSq v = reluDeriv u * (v * v) ∧ reluSqDeriv v = 2 * (reluDeriv u * v) := by
  rcases h.lt_or_eq with h | h
  · exact cone_upq (Or.inl h)
  · exact cone_upq (Or.inr ((mul_eq_zero.1 h.symm).resolve_left hu))

private lemma pos_of_mul_upq {u v : ℝ} (h : 0 < u * v) (hu : 0 < u) : 0 < v :=
  pos_of_mul_pos_right h hu.le

private lemma dot_self_pos_upq {n : Type*} [Fintype n] {u : n → ℝ} (hu : u ≠ 0) :
    0 < u ⬝ᵥ u :=
  lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (u j))
    (Ne.symm (mt dotProduct_self_eq_zero.1 hu))

/-- A vector orthogonal to every `w` with `w u = 0` is a multiple of `u`. -/
private lemma smul_of_ker_upq {n : Type*} [Fintype n] {u v : n → ℝ} (hu : u ⬝ᵥ u ≠ 0)
    (h : ∀ w : n → ℝ, w ⬝ᵥ u = 0 → w ⬝ᵥ v = 0) : v = ((u ⬝ᵥ v) / (u ⬝ᵥ u)) • u := by
  classical
  funext o
  have e := h (Pi.single o 1 - ((u o) / (u ⬝ᵥ u)) • u) (by
    rw [sub_dotProduct, smul_dotProduct, single_one_dotProduct, smul_eq_mul,
      div_mul_cancel₀ _ hu, sub_self])
  rw [sub_dotProduct, smul_dotProduct, single_one_dotProduct, smul_eq_mul, sub_eq_zero] at e
  rw [Pi.smul_apply, smul_eq_mul, e]
  ring

/-- Finitely many hyperplanes do not cover the space. -/
private lemma exists_off_upq {n q : Type*} [Fintype n] [Finite q] {c : q → n → ℝ}
    (hc : ∀ j, c j ≠ 0) : ∃ v : n → ℝ, ∀ j, v ⬝ᵥ c j ≠ 0 := by
  by_contra h
  let p : q → Submodule ℝ (n → ℝ) := fun j =>
    { carrier := {x | x ⬝ᵥ c j = 0}
      add_mem' := by
        intro x y hx hy
        change x ⬝ᵥ c j = 0 at hx
        change y ⬝ᵥ c j = 0 at hy
        change (x + y) ⬝ᵥ c j = 0
        rw [add_dotProduct, hx, hy, add_zero]
      zero_mem' := zero_dotProduct (c j)
      smul_mem' := by
        intro r x hx
        change x ⬝ᵥ c j = 0 at hx
        change (r • x) ⬝ᵥ c j = 0
        rw [smul_dotProduct, hx, smul_zero] }
  have hcov : ⋃ j, (p j : Set (n → ℝ)) = Set.univ := by
    refine Set.eq_univ_of_forall fun v => Set.mem_iUnion.2 ?_
    by_contra hv
    exact h ⟨v, fun j hj => hv ⟨j, hj⟩⟩
  obtain ⟨j, hj⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
  have hmem : c j ∈ p j := by rw [hj]; exact Submodule.mem_top
  exact hc j (dotProduct_self_eq_zero.1 hmem)

/-- Two half-spaces `x u > 0`, `x v > 0` meet unless `v` is a multiple of `u`. -/
private lemma inter_upq {n : Type*} [Fintype n] {u v : n → ℝ} (hu : u ≠ 0)
    (hv : ∀ r : ℝ, v ≠ r • u) : ∃ x : n → ℝ, 0 < x ⬝ᵥ u ∧ 0 < x ⬝ᵥ v := by
  by_contra h
  refine hv _ (smul_of_ker_upq (mt dotProduct_self_eq_zero.1 hu) fun w hw => ?_)
  by_contra hwv
  refine h ⟨u + ((1 - u ⬝ᵥ v) / (w ⬝ᵥ v)) • w, ?_, ?_⟩
  · rw [add_dotProduct, smul_dotProduct, hw, smul_zero, add_zero]
    exact dot_self_pos_upq hu
  · rw [add_dotProduct, smul_dotProduct, smul_eq_mul, div_mul_cancel₀ _ hwv]
    linarith

/-- **`Ω` is preconnected:** a union of half-spaces, any two of which meet. -/
private lemma preconnected_upq {n q : Type*} [Fintype n] {c : q → n → ℝ} (hc : ∀ i, c i ≠ 0)
    (hcc : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) :
    IsPreconnected (⋃ i, {x : n → ℝ | 0 < x ⬝ᵥ c i}) := by
  refine IsPreconnected.iUnion_of_reflTransGen (fun i => ?_) (fun i j => ?_)
  · refine Convex.isPreconnected (convex_halfSpace_gt ?_ 0)
    exact ⟨fun x y => add_dotProduct x y (c i), fun r x => smul_dotProduct r x (c i)⟩
  · refine Relation.ReflTransGen.single ?_
    by_cases hij : i = j
    · subst hij
      exact ⟨c i, dot_self_pos_upq (hc i), dot_self_pos_upq (hc i)⟩
    · obtain ⟨x, h1, h2⟩ := inter_upq (hc i) (hcc j i (Ne.symm hij))
      exact ⟨x, h1, h2⟩

/-- Near `x`, along `v`, the units with `x c_j ≠ 0` keep their sign. -/
private lemma signs_upq {n q : Type*} [Fintype n] [Finite q] (c : q → n → ℝ) (x v : n → ℝ) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → ∀ j, x ⬝ᵥ c j ≠ 0 →
      0 < (x ⬝ᵥ c j) * ((x + t • v) ⬝ᵥ c j) := by
  have h : ∀ᶠ t in nhds (0 : ℝ), ∀ j, x ⬝ᵥ c j ≠ 0 →
      0 < (x ⬝ᵥ c j) * ((x + t • v) ⬝ᵥ c j) := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hj : x ⬝ᵥ c j = 0
    · exact Filter.Eventually.of_forall fun _ h => absurd hj h
    · have hc : Continuous fun t : ℝ => (x ⬝ᵥ c j) * ((x + t • v) ⬝ᵥ c j) := by
        simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
        fun_prop
      have h0 : 0 < (x ⬝ᵥ c j) * ((x + (0 : ℝ) • v) ⬝ᵥ c j) := by
        rw [zero_smul, add_zero]; exact mul_self_pos.2 hj
      filter_upwards [Filter.Tendsto.eventually_const_lt h0 (hc.tendsto 0)] with t ht _
      exact ht
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 h
  exact ⟨ε, hε, fun t ht => h (by rwa [Real.dist_eq, sub_zero])⟩

/-- **The two sides of the kink of unit `i`** at a point `x₀` of its hyperplane on no other one:
points `x₀ ± s e` (`e c_i = 1`, `s` small) on no hyperplane, whose slopes differ only at `i`. -/
private lemma facet_upq {n q : Type*} [Fintype n] [Fintype q] {c : q → n → ℝ} {i : q}
    (hci : c i ≠ 0) {x₀ : n → ℝ} (h0 : x₀ ⬝ᵥ c i = 0) (hx₀ : ∀ j, j ≠ i → x₀ ⬝ᵥ c j ≠ 0) :
    ∃ xp xm e : n → ℝ, e ⬝ᵥ c i = 1 ∧ (∀ j, xp ⬝ᵥ c j ≠ 0) ∧ (∀ j, xm ⬝ᵥ c j ≠ 0) ∧
      0 < xp ⬝ᵥ c i ∧ (∀ j, 0 < x₀ ⬝ᵥ c j → 0 < xm ⬝ᵥ c j) ∧
      (∀ j, j ≠ i → reluDeriv (xp ⬝ᵥ c j) = reluDeriv (xm ⬝ᵥ c j)) ∧
      reluDeriv (xp ⬝ᵥ c i) = 1 ∧ reluDeriv (xm ⬝ᵥ c i) = 0 := by
  have hcc : c i ⬝ᵥ c i ≠ 0 := mt dotProduct_self_eq_zero.1 hci
  obtain ⟨e, he⟩ : ∃ e : n → ℝ, e ⬝ᵥ c i = 1 :=
    ⟨(c i ⬝ᵥ c i)⁻¹ • c i, by rw [smul_dotProduct, smul_eq_mul, inv_mul_cancel₀ hcc]⟩
  obtain ⟨ε, hε, hs⟩ := signs_upq c x₀ e
  have hdot : ∀ t : ℝ, (x₀ + t • e) ⬝ᵥ c i = t := fun t => by
    rw [add_dotProduct, smul_dotProduct, h0, he, smul_eq_mul, mul_one, zero_add]
  have hε2 : 0 < ε / 2 := half_pos hε
  have hp := hs (ε / 2) (by rw [abs_of_pos hε2]; exact half_lt_self hε)
  have hm := hs (-(ε / 2)) (by rw [abs_neg, abs_of_pos hε2]; exact half_lt_self hε)
  have hn : ¬ (0 : ℝ) < -(ε / 2) := by linarith
  refine ⟨x₀ + (ε / 2) • e, x₀ + (-(ε / 2)) • e, e, he, fun j => ?_, fun j => ?_,
    by rw [hdot]; exact hε2, fun j hj => pos_of_mul_upq (hm j hj.ne') hj, fun j hj => ?_, ?_,
    ?_⟩
  · by_cases hj : j = i
    · rw [hj, hdot]; exact hε2.ne'
    · exact right_ne_zero_of_mul (hp j (hx₀ j hj)).ne'
  · by_cases hj : j = i
    · rw [hj, hdot]; exact (neg_neg_of_pos hε2).ne
    · exact right_ne_zero_of_mul (hm j (hx₀ j hj)).ne'
  · rw [reluDeriv_eq_upq (hp j (hx₀ j hj)), reluDeriv_eq_upq (hm j (hx₀ j hj))]
  · rw [hdot]; simp only [reluDeriv, hε2, ↓reduceIte]
  · rw [hdot]; simp only [reluDeriv, hn, ↓reduceIte]

/-- The output of units with slopes `d_j`, with a second family of columns `c'`:
`∑_j d_j (z c_j) (z c'_j) f_j`, a quadratic map of `z`. With `c' = c` and the slopes of a region,
it is the output on that region; with `c' = ψc`, the part of `J` with `σ'`. -/
private noncomputable def pf_upq {n m q : Type*} [Fintype n] [Fintype q] (c c' : q → n → ℝ)
    (d : q → ℝ) (f : q → m → ℝ) (z : n → ℝ) : m → ℝ :=
  ∑ l, (d l * ((z ⬝ᵥ c l) * (z ⬝ᵥ c' l))) • f l

/-- Its polar form `∑_j d_j ((x c_j) (v c'_j) + (v c_j) (x c'_j)) f_j`. -/
private noncomputable def pf1_upq {n m q : Type*} [Fintype n] [Fintype q] (c c' : q → n → ℝ)
    (d : q → ℝ) (f : q → m → ℝ) (x v : n → ℝ) : m → ℝ :=
  ∑ l, (d l * ((x ⬝ᵥ c l) * (v ⬝ᵥ c' l) + (v ⬝ᵥ c l) * (x ⬝ᵥ c' l))) • f l

/-- On a line: `Q(x + t v) = Q(x) + t Q₁(x, v) + t² Q(v)`. -/
private lemma pf_add_upq {n m q : Type*} [Fintype n] [Fintype q] (c c' : q → n → ℝ)
    (d : q → ℝ) (f : q → m → ℝ) (x v : n → ℝ) (t : ℝ) :
    pf_upq c c' d f (x + t • v)
      = pf_upq c c' d f x + t • pf1_upq c c' d f x v + t ^ 2 • pf_upq c c' d f v := by
  unfold pf_upq pf1_upq
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
    smul_eq_mul]
  module

private lemma pf1_add_upq {n m q : Type*} [Fintype n] [Fintype q] (c c' : q → n → ℝ)
    (d : q → ℝ) (f : q → m → ℝ) (x v z : n → ℝ) (s : ℝ) :
    pf1_upq c c' d f x (v + s • z) = pf1_upq c c' d f x v + s • pf1_upq c c' d f x z := by
  unfold pf1_upq
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
    smul_eq_mul]
  module

/-- Two slope patterns that differ only at unit `i`, where they are `1` and `0`. -/
private lemma pf_facet_upq {n m q : Type*} [Fintype n] [Fintype q] (c c' : q → n → ℝ)
    {d d' : q → ℝ} (f : q → m → ℝ) {i : q} (hd : ∀ j, j ≠ i → d j = d' j) (hi : d i = 1)
    (hi' : d' i = 0) (z : n → ℝ) :
    pf_upq c c' d f z = pf_upq c c' d' f z + ((z ⬝ᵥ c i) * (z ⬝ᵥ c' i)) • f i := by
  classical
  unfold pf_upq
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hs : ∑ j ∈ Finset.univ.erase i, (d j * ((z ⬝ᵥ c j) * (z ⬝ᵥ c' j))) • f j
      = ∑ j ∈ Finset.univ.erase i, (d' j * ((z ⬝ᵥ c j) * (z ⬝ᵥ c' j))) • f j :=
    Finset.sum_congr rfl fun j hj => by rw [hd j (Finset.ne_of_mem_erase hj)]
  rw [hs, hi, hi']
  module

/-- The output at a point `w` whose units have the slopes `d`. -/
private lemma sum_reluSq_upq {n m q : Type*} [Fintype n] [Fintype q] {c : q → n → ℝ}
    {d : q → ℝ} (f : q → m → ℝ) {w : n → ℝ}
    (h : ∀ j, reluSq (w ⬝ᵥ c j) = d j * ((w ⬝ᵥ c j) * (w ⬝ᵥ c j))) :
    ∑ j, reluSq (w ⬝ᵥ c j) • f j = pf_upq c c d f w :=
  Finset.sum_congr rfl fun j _ => by rw [h j]

/-- The vector `J(w)` of a direction, at a point `w` whose units have the slopes `d`. -/
private lemma J_eq_upq {n m q : Type*} [Fintype n] [Fintype q] {c ψc : q → n → ℝ}
    {a β : q → m → ℝ} {d : q → ℝ} {w : n → ℝ}
    (h : ∀ j, reluSq (w ⬝ᵥ c j) = d j * ((w ⬝ᵥ c j) * (w ⬝ᵥ c j)) ∧
      reluSqDeriv (w ⬝ᵥ c j) = 2 * (d j * (w ⬝ᵥ c j))) :
    ∑ j, (reluSq (w ⬝ᵥ c j) • β j + (reluSqDeriv (w ⬝ᵥ c j) * (w ⬝ᵥ ψc j)) • a j)
      = pf_upq c c d β w + (2 : ℝ) • pf_upq c ψc d a w := by
  unfold pf_upq
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(h j).1, (h j).2]
  module

/-- Once `ψc_j = λ_j c_j`: `J(w) = ∑_j σ(w c_j) b_j` with `b_j = β_j + 2 λ_j a_j`
(`σ'(u) u = 2 σ(u)`). -/
private lemma J_eq_b_upq {n m q : Type*} [Fintype n] [Fintype q] {c ψc : q → n → ℝ}
    {a β : q → m → ℝ} {lam : q → ℝ} (hψ : ∀ j, ψc j = lam j • c j) {d : q → ℝ} {w : n → ℝ}
    (h : ∀ j, reluSq (w ⬝ᵥ c j) = d j * ((w ⬝ᵥ c j) * (w ⬝ᵥ c j)) ∧
      reluSqDeriv (w ⬝ᵥ c j) = 2 * (d j * (w ⬝ᵥ c j))) :
    ∑ j, (reluSq (w ⬝ᵥ c j) • β j + (reluSqDeriv (w ⬝ᵥ c j) * (w ⬝ᵥ ψc j)) • a j)
      = pf_upq c c d (fun j => β j + (2 * lam j) • a j) w := by
  unfold pf_upq
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(h j).1, (h j).2, hψ j, dotProduct_smul, smul_eq_mul]
  dsimp only
  module

/-- The entries of the output on a region, as sums over its active units `S`. -/
private lemma pf_coord_upq {n m q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ)
    (x : n → ℝ) (f : q → m → ℝ) (z : n → ℝ) (o : m) :
    pf_upq c c (fun j => reluDeriv (x ⬝ᵥ c j)) f z o
      = ∑ i ∈ Finset.univ.filter (fun l => 0 < x ⬝ᵥ c l), (z ⬝ᵥ c i) ^ 2 * f i o := by
  unfold pf_upq
  rw [Finset.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases hl : 0 < x ⬝ᵥ c l
  · simp only [reluDeriv, hl, ↓reduceIte]
    ring
  · simp only [reluDeriv, hl, ↓reduceIte]
    ring

private lemma pf1_coord_upq {n m q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ)
    (x : n → ℝ) (f : q → m → ℝ) (u v : n → ℝ) (o : m) :
    pf1_upq c c (fun j => reluDeriv (x ⬝ᵥ c j)) f u v o
      = 2 * ∑ i ∈ Finset.univ.filter (fun l => 0 < x ⬝ᵥ c l),
        (u ⬝ᵥ c i) * (v ⬝ᵥ c i) * f i o := by
  unfold pf1_upq
  rw [Finset.sum_apply, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases hl : 0 < x ⬝ᵥ c l
  · simp only [reluDeriv, hl, ↓reduceIte]
    ring
  · simp only [reluDeriv, hl, ↓reduceIte]
    ring

/-- Every `2 × 2` minor of two parallel vectors vanishes. -/
private lemma minor_upq {m : Type*} {U V : m → ℝ} {μ : ℝ} (h : U = μ • V) (o o' : m) :
    U o * V o' = U o' * V o := by
  rw [h]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- If every minor of `(a, H)` vanishes and `a ≠ 0`, then `H` is a multiple of `a`. -/
private lemma smul_of_minors_upq {m : Type*} {a H : m → ℝ} (ha : a ≠ 0)
    (h : ∀ o o', a o * H o' = a o' * H o) : ∃ r : ℝ, H = r • a := by
  obtain ⟨o, ho⟩ := Function.ne_iff.1 ha
  have ho' : a o ≠ 0 := ho
  refine ⟨H o / a o, funext fun o' => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff ho']
  linear_combination h o o'

/-- **The coefficient of `t⁴`:** if `j(t) r(t) = k(t) p(t)` for `|t| < δ` (polynomials of degree
at most two), then `j₂ r₂ = k₂ p₂` (the values at `t = 0, ±s, ±2s`). -/
private lemma lead_upq {p₀ p₁ p₂ r₀ r₁ r₂ j₀ j₁ j₂ k₀ k₁ k₂ δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t : ℝ, |t| < δ → (j₀ + j₁ * t + j₂ * t ^ 2) * (r₀ + r₁ * t + r₂ * t ^ 2)
      = (k₀ + k₁ * t + k₂ * t ^ 2) * (p₀ + p₁ * t + p₂ * t ^ 2)) :
    j₂ * r₂ = k₂ * p₂ := by
  obtain ⟨s, hs, hsδ⟩ : ∃ s : ℝ, 0 < s ∧ 2 * s < δ := ⟨δ / 3, by positivity, by linarith⟩
  have h0 := h 0 (by rw [abs_zero]; exact hδ)
  have h1 := h s (abs_lt.2 ⟨by linarith, by linarith⟩)
  have hm1 := h (-s) (abs_lt.2 ⟨by linarith, by linarith⟩)
  have h2 := h (2 * s) (abs_lt.2 ⟨by linarith, by linarith⟩)
  have hm2 := h (-(2 * s)) (abs_lt.2 ⟨by linarith, by linarith⟩)
  have e4 : 24 * s ^ 4 * (j₂ * r₂ - k₂ * p₂) = 0 := by
    linear_combination h2 + hm2 - 4 * h1 - 4 * hm1 + 6 * h0
  exact sub_eq_zero.1 ((mul_eq_zero.1 e4).resolve_left (by positivity))

/-- The vector statement of `OneBlock/QuadraticResultant.lean` from the `2 × 2` minors (copy of
its private helper). -/
private lemma vec_of_minors_upq {m : Type*} {P₀ P₁ P₂ J₀ J₁ J₂ : m → ℝ} {e f : m} {δ : ℝ}
    (hres : quadRes (P₀ e) (P₁ e) (P₂ e) (P₀ f) (P₁ f) (P₂ f) ≠ 0) (hδ : 0 < δ)
    (h : ∀ t : ℝ, |t| < δ → ∀ g g' : m,
      (J₀ g + t * J₁ g + t ^ 2 * J₂ g) * (P₀ g' + t * P₁ g' + t ^ 2 * P₂ g')
        = (J₀ g' + t * J₁ g' + t ^ 2 * J₂ g') * (P₀ g + t * P₁ g + t ^ 2 * P₂ g)) :
    ∃ c : ℝ, J₀ = c • P₀ ∧ J₁ = c • P₁ ∧ J₂ = c • P₂ := by
  obtain ⟨c, -, -, -, hf₀, hf₁, hf₂⟩ := quad_proportional_of_quadRes_ne_zero
    (j₀ := J₀ e) (j₁ := J₁ e) (j₂ := J₂ e) (k₀ := J₀ f) (k₁ := J₁ f) (k₂ := J₂ f) hres hδ
    (fun t ht => by linear_combination h t ht e f)
  have hg : ∀ g, J₀ g = c * P₀ g ∧ J₁ g = c * P₁ g ∧ J₂ g = c * P₂ g := by
    intro g
    obtain ⟨c', h₀, h₁, h₂, h₃, h₄, h₅⟩ := quad_proportional_of_quadRes_ne_zero
      (j₀ := J₀ g - c * P₀ g) (j₁ := J₁ g - c * P₁ g) (j₂ := J₂ g - c * P₂ g)
      (k₀ := 0) (k₁ := 0) (k₂ := 0) hres hδ (fun t ht => by
        have hm := h t ht g f
        rw [hf₀, hf₁, hf₂] at hm
        linear_combination hm)
    by_cases hc' : c' = 0
    · rw [hc', zero_mul] at h₀ h₁ h₂
      exact ⟨by linear_combination h₀, by linear_combination h₁, by linear_combination h₂⟩
    · have z₀ := (mul_eq_zero.1 h₃.symm).resolve_left hc'
      have z₁ := (mul_eq_zero.1 h₄.symm).resolve_left hc'
      have z₂ := (mul_eq_zero.1 h₅.symm).resolve_left hc'
      exact absurd (by rw [z₀, z₁, z₂, quadRes]; ring) hres
  refine ⟨c, funext fun g => ?_, funext fun g => ?_, funext fun g => ?_⟩
  · exact (hg g).1
  · exact (hg g).2.1
  · exact (hg g).2.2

/-- **The jump across a kink, on a line.** Let `K(t) = K₀ + t K₁ + t² K₂` be a multiple of
`H(t) = H₀ + t H₁ + t² H₂` for `-ε < t < 0`, and `K(t) + t² b + 2t (L + t L') a` a multiple of
`H(t) + t² a` for `0 < t < ε`. Then `L (a ∧ H₀) = 0`: every minor is a polynomial of degree at
most four in `t` on each side, and the coefficients of `t` on the two sides differ by
`2 L (a ∧ H₀)` (the values at `t = ±s, …, ±5s`). -/
private lemma kinkpoly_upq {m : Type*} {K₀ K₁ K₂ H₀ H₁ H₂ b a : m → ℝ} {L L' ε : ℝ}
    (hε : 0 < ε)
    (hneg : ∀ t : ℝ, -ε < t → t < 0 →
      ∃ μ : ℝ, K₀ + t • K₁ + t ^ 2 • K₂ = μ • (H₀ + t • H₁ + t ^ 2 • H₂))
    (hpos : ∀ t : ℝ, 0 < t → t < ε → ∃ μ : ℝ,
      K₀ + t • K₁ + t ^ 2 • K₂ + t ^ 2 • b + (2 * t * (L + t * L')) • a
        = μ • (H₀ + t • H₁ + t ^ 2 • H₂ + t ^ 2 • a))
    (o o' : m) : L * (a o * H₀ o' - a o' * H₀ o) = 0 := by
  obtain ⟨s, hs, hsε⟩ : ∃ s : ℝ, 0 < s ∧ 5 * s < ε := ⟨ε / 6, by positivity, by linarith⟩
  have N : ∀ t : ℝ, -ε < t → t < 0 →
      (K₀ o + t * K₁ o + t ^ 2 * K₂ o) * (H₀ o' + t * H₁ o' + t ^ 2 * H₂ o')
        = (K₀ o' + t * K₁ o' + t ^ 2 * K₂ o') * (H₀ o + t * H₁ o + t ^ 2 * H₂ o) := by
    intro t h1 h2
    obtain ⟨μ, hμ⟩ := hneg t h1 h2
    have hm := minor_upq hμ o o'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hm
    linear_combination hm
  have P : ∀ t : ℝ, 0 < t → t < ε →
      (K₀ o + t * K₁ o + t ^ 2 * K₂ o + t ^ 2 * b o + 2 * t * (L + t * L') * a o)
          * (H₀ o' + t * H₁ o' + t ^ 2 * H₂ o' + t ^ 2 * a o')
        = (K₀ o' + t * K₁ o' + t ^ 2 * K₂ o' + t ^ 2 * b o' + 2 * t * (L + t * L') * a o')
          * (H₀ o + t * H₁ o + t ^ 2 * H₂ o + t ^ 2 * a o) := by
    intro t h1 h2
    obtain ⟨μ, hμ⟩ := hpos t h1 h2
    have hm := minor_upq hμ o o'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hm
    linear_combination hm
  have P1 := P s hs (by linarith)
  have P2 := P (2 * s) (by linarith) (by linarith)
  have P3 := P (3 * s) (by linarith) (by linarith)
  have P4 := P (4 * s) (by linarith) (by linarith)
  have P5 := P (5 * s) (by linarith) (by linarith)
  have N1 := N (-s) (by linarith) (by linarith)
  have N2 := N (-(2 * s)) (by linarith) (by linarith)
  have N3 := N (-(3 * s)) (by linarith) (by linarith)
  have N4 := N (-(4 * s)) (by linarith) (by linarith)
  have N5 := N (-(5 * s)) (by linarith) (by linarith)
  -- the coefficient of `t`, times `s`, on each side: weights `-77/12, 107/6, -39/2, 61/6, -25/12`
  have key : s * (2 * (L * (a o * H₀ o' - a o' * H₀ o))) = 0 := by
    linear_combination (-77 / 12 : ℝ) * P1 + (107 / 6 : ℝ) * P2 + (-39 / 2 : ℝ) * P3
      + (61 / 6 : ℝ) * P4 + (-25 / 12 : ℝ) * P5 + (-77 / 12 : ℝ) * N1 + (107 / 6 : ℝ) * N2
      + (-39 / 2 : ℝ) * N3 + (61 / 6 : ℝ) * N4 + (-25 / 12 : ℝ) * N5
  exact (mul_eq_zero.1 ((mul_eq_zero.1 key).resolve_left hs.ne')).resolve_left two_ne_zero

/-- **The kinks stay, at one point.** At a point `x₁` of the hyperplane of unit `i`, on no other
hyperplane, where the output is not a multiple of `a_i`: `x₁ ψc_i = 0`. On the line `x₁ + t u`
(`u c_i = 1`) the output and `J` are quadratic in `t` on each side of `t = 0`; across it the
output gains `t² a_i` and `J` gains `t² β_i + 2 t (x ψc_i) a_i` (`kinkpoly_upq`). -/
private lemma kink_upq {n m q : Type*} [Fintype n] [Fintype q] {c ψc : q → n → ℝ}
    {a β : q → m → ℝ} (ha : ∀ i, a i ≠ 0)
    (hne : ∀ x : n → ℝ, (∃ i, 0 < x ⬝ᵥ c i) → ∑ i, reluSq (x ⬝ᵥ c i) • a i ≠ 0)
    (hpar : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, reluSq (x ⬝ᵥ c i) • a i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (reluSq (x ⬝ᵥ c i) • β i + (reluSqDeriv (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = μ • ∑ i, reluSq (x ⬝ᵥ c i) • a i)
    {i : q} (hci : c i ≠ 0) {x₁ : n → ℝ} (h0 : x₁ ⬝ᵥ c i = 0)
    (hx₁ : ∀ j, j ≠ i → x₁ ⬝ᵥ c j ≠ 0)
    (hB : ∀ r : ℝ, ∑ j, reluSq (x₁ ⬝ᵥ c j) • a j ≠ r • a i) : x₁ ⬝ᵥ ψc i = 0 := by
  classical
  have hcc : c i ⬝ᵥ c i ≠ 0 := mt dotProduct_self_eq_zero.1 hci
  obtain ⟨u, hu⟩ : ∃ u : n → ℝ, u ⬝ᵥ c i = 1 :=
    ⟨(c i ⬝ᵥ c i)⁻¹ • c i, by rw [smul_dotProduct, smul_eq_mul, inv_mul_cancel₀ hcc]⟩
  obtain ⟨ε, hε, hs⟩ := signs_upq c x₁ u
  have hdot : ∀ t : ℝ, (x₁ + t • u) ⬝ᵥ c i = t := fun t => by
    rw [add_dotProduct, smul_dotProduct, h0, hu, smul_eq_mul, mul_one, zero_add]
  have hdotψ : ∀ t : ℝ, (x₁ + t • u) ⬝ᵥ ψc i = x₁ ⬝ᵥ ψc i + t * (u ⬝ᵥ ψc i) := fun t => by
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
  -- an active unit at `x₁`
  obtain ⟨j, hj⟩ : ∃ j, 0 < x₁ ⬝ᵥ c j := by
    by_contra hno
    refine hB 0 ?_
    rw [zero_smul]
    exact Finset.sum_eq_zero fun j _ => by
      rw [reluSq, max_eq_right (not_lt.1 fun h => hno ⟨j, h⟩)]
      simp
  have hji : j ≠ i := fun h => by rw [h, h0] at hj; exact lt_irrefl 0 hj
  -- the slopes `dm` on the side `t < 0` and `dp` on the side `t > 0`
  obtain ⟨dm, hdm⟩ : ∃ dm : q → ℝ, dm = fun l => reluDeriv (x₁ ⬝ᵥ c l) := ⟨_, rfl⟩
  obtain ⟨dp, hdp⟩ : ∃ dp : q → ℝ, dp = fun l => if l = i then 1 else reluDeriv (x₁ ⬝ᵥ c l) :=
    ⟨_, rfl⟩
  have hdmi : dm i = 0 := by rw [hdm]; simp only [h0, reluDeriv, lt_irrefl, ↓reduceIte]
  have hdpi : dp i = 1 := by rw [hdp]; simp only [↓reduceIte]
  have hdpl : ∀ l, l ≠ i → dp l = dm l := fun l hl => by
    rw [hdp, hdm]; simp only [hl, ↓reduceIte]
  -- the points `x₁ + t u`, `0 < |t| < ε`: off the kinks, the output is not zero
  have hoff : ∀ t : ℝ, |t| < ε → t ≠ 0 → ∀ l, (x₁ + t • u) ⬝ᵥ c l ≠ 0 := fun t ht ht0 l => by
    by_cases hl : l = i
    · rw [hl, hdot]; exact ht0
    · exact right_ne_zero_of_mul (hs t ht l (hx₁ l hl)).ne'
  have hB0 : ∀ t : ℝ, |t| < ε → ∑ l, reluSq ((x₁ + t • u) ⬝ᵥ c l) • a l ≠ 0 := fun t ht =>
    hne _ ⟨j, pos_of_mul_upq (hs t ht j (hx₁ j hji)) hj⟩
  have hslope : ∀ t : ℝ, |t| < ε → ∀ l, l ≠ i →
      reluDeriv ((x₁ + t • u) ⬝ᵥ c l) = dm l := fun t ht l hl => by
    rw [hdm]; exact reluDeriv_eq_upq (hs t ht l (hx₁ l hl))
  -- on a side with slopes `d`: `J = μ h` with both quadratic maps of the region
  have side : ∀ (d : q → ℝ) (t : ℝ), |t| < ε → t ≠ 0 →
      (∀ l, reluDeriv ((x₁ + t • u) ⬝ᵥ c l) = d l) → ∃ μ : ℝ,
        pf_upq c c d β (x₁ + t • u) + (2 : ℝ) • pf_upq c ψc d a (x₁ + t • u)
          = μ • pf_upq c c d a (x₁ + t • u) := by
    intro d t ht ht0 hd
    have hpat : ∀ l, reluSq ((x₁ + t • u) ⬝ᵥ c l)
          = d l * (((x₁ + t • u) ⬝ᵥ c l) * ((x₁ + t • u) ⬝ᵥ c l)) ∧
        reluSqDeriv ((x₁ + t • u) ⬝ᵥ c l) = 2 * (d l * ((x₁ + t • u) ⬝ᵥ c l)) := fun l => by
      rw [reluSq_eq_upq, reluSqDeriv_eq_upq, hd l]
      exact ⟨rfl, rfl⟩
    obtain ⟨μ, hμ⟩ := hpar _ (hoff t ht ht0) (hB0 t ht)
    rw [J_eq_upq hpat, sum_reluSq_upq a fun l => (hpat l).1] at hμ
    exact ⟨μ, hμ⟩
  -- the jump: `x₁ ψc_i (a_i ∧ h(x₁)) = 0`
  have hmin : ∀ o o', (x₁ ⬝ᵥ ψc i)
      * (a i o * pf_upq c c dm a x₁ o' - a i o' * pf_upq c c dm a x₁ o) = 0 := by
    intro o o'
    refine kinkpoly_upq (K₀ := pf_upq c c dm β x₁ + (2 : ℝ) • pf_upq c ψc dm a x₁)
      (K₁ := pf1_upq c c dm β x₁ u + (2 : ℝ) • pf1_upq c ψc dm a x₁ u)
      (K₂ := pf_upq c c dm β u + (2 : ℝ) • pf_upq c ψc dm a u)
      (H₁ := pf1_upq c c dm a x₁ u) (H₂ := pf_upq c c dm a u) (b := β i)
      (L' := u ⬝ᵥ ψc i) hε (fun t ht1 ht2 => ?_) (fun t ht1 ht2 => ?_) o o'
    · have ht : |t| < ε := abs_lt.2 ⟨ht1, by linarith⟩
      obtain ⟨μ, hμ⟩ := side dm t ht ht2.ne fun l => by
        by_cases hl : l = i
        · rw [hl, hdot, hdmi]; simp only [reluDeriv, not_lt.2 ht2.le, ↓reduceIte]
        · exact hslope t ht l hl
      rw [pf_add_upq, pf_add_upq, pf_add_upq] at hμ
      exact ⟨μ, by linear_combination (norm := module) hμ⟩
    · have ht : |t| < ε := abs_lt.2 ⟨by linarith, ht2⟩
      obtain ⟨μ, hμ⟩ := side dp t ht ht1.ne' fun l => by
        by_cases hl : l = i
        · rw [hl, hdot, hdpi]; simp only [reluDeriv, ht1, ↓reduceIte]
        · rw [hdpl l hl]; exact hslope t ht l hl
      rw [pf_facet_upq c c β hdpl hdpi hdmi, pf_facet_upq c ψc a hdpl hdpi hdmi,
        pf_facet_upq c c a hdpl hdpi hdmi, hdot, hdotψ, pf_add_upq, pf_add_upq,
        pf_add_upq] at hμ
      exact ⟨μ, by linear_combination (norm := module) hμ⟩
  -- `h(x₁)` is not a multiple of `a_i`, so `x₁ ψc_i = 0`
  by_contra hL
  obtain ⟨r, hr⟩ := smul_of_minors_upq (H := pf_upq c c dm a x₁) (ha i) fun o o' => by
    have h1 := (mul_eq_zero.1 (hmin o o')).resolve_left hL
    linear_combination h1
  refine hB r ?_
  rw [sum_reluSq_upq (d := dm) a fun l => by rw [hdm]; exact reluSq_eq_upq _, hr]

/-- **The kinks stay, on the whole hyperplane.** From `hkink`'s point `x₀`, the points `x₀ + t w`
(`w c_i = 0`, `t` small) are on the hyperplane of unit `i` only; the output is quadratic in `t`
there, so at one of `t = s, 2s, 3s` it is not a multiple of `a_i`. -/
private lemma psi_upq {n m q : Type*} [Fintype n] [Fintype q] {c ψc : q → n → ℝ}
    {a β : q → m → ℝ} (ha : ∀ i, a i ≠ 0)
    (hne : ∀ x : n → ℝ, (∃ i, 0 < x ⬝ᵥ c i) → ∑ i, reluSq (x ⬝ᵥ c i) • a i ≠ 0)
    (hpar : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, reluSq (x ⬝ᵥ c i) • a i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (reluSq (x ⬝ᵥ c i) • β i + (reluSqDeriv (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = μ • ∑ i, reluSq (x ⬝ᵥ c i) • a i)
    {i : q} (hci : c i ≠ 0) {x₀ : n → ℝ} (h0 : x₀ ⬝ᵥ c i = 0)
    (hx₀ : ∀ j, j ≠ i → x₀ ⬝ᵥ c j ≠ 0)
    (hB : ∀ r : ℝ, ∑ j, reluSq (x₀ ⬝ᵥ c j) • a j ≠ r • a i) {w : n → ℝ} (hw : w ⬝ᵥ c i = 0) :
    w ⬝ᵥ ψc i = 0 := by
  have hk0 := kink_upq ha hne hpar hci h0 hx₀ hB
  obtain ⟨ε, hε, hs⟩ := signs_upq c x₀ w
  have hdot : ∀ t : ℝ, (x₀ + t • w) ⬝ᵥ c i = 0 := fun t => by
    rw [add_dotProduct, smul_dotProduct, h0, hw, smul_zero, add_zero]
  have hx : ∀ t : ℝ, |t| < ε → ∀ j, j ≠ i → (x₀ + t • w) ⬝ᵥ c j ≠ 0 := fun t ht j hj =>
    right_ne_zero_of_mul (hs t ht j (hx₀ j hj)).ne'
  -- near `x₀` on the hyperplane, the output is quadratic in `t`
  have hquad : ∀ t : ℝ, |t| < ε → ∑ j, reluSq ((x₀ + t • w) ⬝ᵥ c j) • a j
      = ∑ j, reluSq (x₀ ⬝ᵥ c j) • a j
        + t • pf1_upq c c (fun j => reluDeriv (x₀ ⬝ᵥ c j)) a x₀ w
        + t ^ 2 • pf_upq c c (fun j => reluDeriv (x₀ ⬝ᵥ c j)) a w := by
    intro t ht
    have hr : ∀ j, reluSq ((x₀ + t • w) ⬝ᵥ c j)
        = reluDeriv (x₀ ⬝ᵥ c j) * (((x₀ + t • w) ⬝ᵥ c j) * ((x₀ + t • w) ⬝ᵥ c j)) := by
      intro j
      by_cases hj : j = i
      · exact (cone_upq (Or.inr (by rw [hj, hdot]))).1
      · exact (cone_upq (Or.inl (hs t ht j (hx₀ j hj)))).1
    rw [sum_reluSq_upq a hr, pf_add_upq, sum_reluSq_upq (w := x₀) a fun j => reluSq_eq_upq _]
  obtain ⟨s, hs0, hsε⟩ : ∃ s : ℝ, 0 < s ∧ 3 * s < ε := ⟨ε / 4, by positivity, by linarith⟩
  have hone : ∃ t : ℝ, t ≠ 0 ∧ |t| < ε ∧
      ∀ r : ℝ, ∑ j, reluSq ((x₀ + t • w) ⬝ᵥ c j) • a j ≠ r • a i := by
    by_contra hno
    have hmul : ∀ t : ℝ, 0 < t → t < ε →
        ∃ r : ℝ, ∑ j, reluSq ((x₀ + t • w) ⬝ᵥ c j) • a j = r • a i := by
      intro t ht0 htε
      by_contra h
      exact hno ⟨t, ht0.ne', abs_lt.2 ⟨by linarith, htε⟩, fun r hr => h ⟨r, hr⟩⟩
    obtain ⟨r₁, e₁⟩ := hmul s hs0 (by linarith)
    obtain ⟨r₂, e₂⟩ := hmul (2 * s) (by linarith) (by linarith)
    obtain ⟨r₃, e₃⟩ := hmul (3 * s) (by linarith) (by linarith)
    rw [hquad s (abs_lt.2 ⟨by linarith, by linarith⟩)] at e₁
    rw [hquad (2 * s) (abs_lt.2 ⟨by linarith, by linarith⟩)] at e₂
    rw [hquad (3 * s) (abs_lt.2 ⟨by linarith, by linarith⟩)] at e₃
    -- the value at `t = 0` of a quadratic is `3 F(s) - 3 F(2s) + F(3s)`
    exact hB (3 * r₁ - 3 * r₂ + r₃)
      (by linear_combination (norm := module) (3 : ℝ) • e₁ - (3 : ℝ) • e₂ + e₃)
  obtain ⟨t, ht0, ht, htB⟩ := hone
  have h := kink_upq ha hne hpar hci (hdot t) (hx t ht) htB
  rw [add_dotProduct, smul_dotProduct, hk0, zero_add, smul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left ht0

/-- **"The kinks stay" and "One scale" for ReLU² units in general position** (proof of Theorem
B.1 (iv) of the skips paper, "The skipless network: equality", `k = 2`; any number of units, also
more units than coordinates): let the columns `c_i` be pairwise non-collinear and the rows `a_i`
nonzero; let the output `h_1(x) = ∑_i max(x c_i, 0)² a_i` be nonzero wherever a unit is active;
for every unit `i` let there be a point `x_0` of its hyperplane `x c_i = 0`, on no other
hyperplane, at which `h_1(x_0)` is not a multiple of `a_i`; and for every set `S` of at least two
units let there be a line `t ↦ u + t v` on which two entries of `∑_{i∈S} (x c_i)² a_i` are
polynomials in `t` with a resultant that is not zero. Then `UnitsParallelAt` holds: a direction
`(ψc, β)` whose derivative of the output is a multiple of the output off the kinks is
`ψc_i = λ_i c_i`, `β_i = (c₀ − 2 λ_i) a_i`. -/
theorem reluSq_unitsParallelAt_of_generic {n m q : Type*} [Fintype n] [Fintype m] [Fintype q]
    (c : q → n → ℝ) (a : q → m → ℝ)
    (hcc : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) (ha : ∀ i, a i ≠ 0)
    (hne : ∀ x : n → ℝ, (∃ i, 0 < x ⬝ᵥ c i) → ∑ i, reluSq (x ⬝ᵥ c i) • a i ≠ 0)
    (hkink : ∀ i, ∃ x₀ : n → ℝ, x₀ ⬝ᵥ c i = 0 ∧ (∀ j, j ≠ i → x₀ ⬝ᵥ c j ≠ 0) ∧
      ∀ r : ℝ, ∑ j, reluSq (x₀ ⬝ᵥ c j) • a j ≠ r • a i)
    (hres : ∀ S : Finset q, 2 ≤ S.card → ∃ (u v : n → ℝ) (e f : m),
      quadRes (∑ i ∈ S, (u ⬝ᵥ c i) ^ 2 * a i e)
        (2 * ∑ i ∈ S, (u ⬝ᵥ c i) * (v ⬝ᵥ c i) * a i e) (∑ i ∈ S, (v ⬝ᵥ c i) ^ 2 * a i e)
        (∑ i ∈ S, (u ⬝ᵥ c i) ^ 2 * a i f)
        (2 * ∑ i ∈ S, (u ⬝ᵥ c i) * (v ⬝ᵥ c i) * a i f) (∑ i ∈ S, (v ⬝ᵥ c i) ^ 2 * a i f) ≠ 0) :
    UnitsParallelAt reluSq reluSqDeriv 2 c a := by
  sorry

end Skips
