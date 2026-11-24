import SkipsLean.OneBlock.UnitsParallel

/-!
# A direction that keeps the output of ReLU units parallel: units in general position

Paper (skips paper), proof of Theorem B.1 (iv), "The skipless network: equality", for
`σ(z) = max(z, 0)^k`, `k = 1` or `2`, with `h_1 = ∑_i σ(x c_i) a_i`: equation (18),

`J(x) := ∑_i [σ(x c_i) (ψa_i − a_i Y) + σ'(x c_i) (x ψc_i) a_i] = μ(x) h_1(x)` on `Ω`,

"The kinks stay": "Fix a unit `i` and a point `x_0` with `x_0 c_i = 0`, on no other hyperplane
`x c_j = 0`, at which another unit is active. For generic parameters and `x_0` in an open dense
set of such points, `h_1(x_0)` is not parallel to `a_i`. […] In both cases `x_0 ψc_i = 0` on an
open subset of the hyperplane, so `ψc_i = λ_i c_i` for a number `λ_i`", and "One scale": "On a
region where only unit `j` is active, `b_j = μ(x) a_j`, so `μ` is constant. On a region where at
least two units are active, the entries of `J` and of `h_1` are homogeneous polynomials of degree
`k` in `x`, and for generic parameters two entries `h_a` and `h_b` of `h_1` have no common factor.
[…] So `μ` is continuous on `Ω` and constant on every region. The set `Ω` is connected: it is the
union of the open half-spaces `{x : x c_i > 0}`, and any two of them meet, as the `c_i` are
pairwise non-collinear. Hence `μ = c` on `Ω` for one number `c`".

`OneBlock/UnitsParallel.lean` has the two steps as the property `UnitsParallel` of an activation,
for linearly independent columns `c_i` and rows `a_i` (a block of width exactly `d_model`). Here:

* `UnitsParallelAt σ σ' k c a`: the same conclusion for given units `c`, `a` (no condition on them
  in the definition), so that the network statement can take it as a hypothesis at its own
  weights;
* for ReLU (`k = 1`), units in general position, also more units than coordinates: the paper's
  three "for generic parameters" are hypotheses on `c` and `a`:
  - `h_1 ≠ 0` on `Ω` ("for generic parameters `h_1 ≠ 0` there"), at every `x` with an active unit;
  - for every unit `i` one point `x_0` of its hyperplane, on no other hyperplane, at which
    `h_1(x_0)` is not a multiple of `a_i` (then another unit is active there);
  - where at least two units are active, the linear map that `h_1` is on the region of `x` has
    rank at least two ("two entries […] of `h_1` have no common factor", for `k = 1`): some `y`
    is mapped to a vector that is not a multiple of `h_1(x)`;
  and the `c_i` are pairwise non-collinear (also not opposite), the `a_i` nonzero.

Not stated: ReLU² units in general position (the paper's proof uses that two quadratic entries
of `h_1` have no common factor). Exact check of the dimension `q + 1` of the solutions for more
units than coordinates: `units_parallel_wide_check_2026-11-24.py` (24 cases).
-/

namespace Skips

open Matrix

/-- **"The kinks stay" and "One scale" at given units:** if at every `x` off the kinks at which
the output `∑_i σ(x c_i) a_i` is not zero the vector `∑_i [σ(x c_i) β_i + σ'(x c_i) (x ψc_i) a_i]`
is a multiple of the output, then there are numbers `c₀` and `λ_i` with `ψc_i = λ_i c_i` and
`β_i = (c₀ − k λ_i) a_i`. (`UnitsParallel σ σ' k n m q` says this for all linearly independent
`c`, linearly independent `a` and at least two units.) -/
def UnitsParallelAt (σ σ' : ℝ → ℝ) (k : ℕ) {n m q : Type*} [Fintype n] [Fintype m] [Fintype q]
    (c : q → n → ℝ) (a : q → m → ℝ) : Prop :=
  ∀ (ψc : q → n → ℝ) (β : q → m → ℝ),
    (∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, σ (x ⬝ᵥ c i) • a i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = μ • ∑ i, σ (x ⬝ᵥ c i) • a i) →
    ∃ (c₀ : ℝ) (lam : q → ℝ), ∀ i, ψc i = lam i • c i ∧ β i = (c₀ - (k : ℝ) * lam i) • a i

/-- The property `UnitsParallel` of an activation gives `UnitsParallelAt` at linearly independent
columns `c_i`, linearly independent rows `a_i` and at least two units. -/
theorem unitsParallelAt_of_unitsParallel {σ σ' : ℝ → ℝ} {k : ℕ} {n m q : Type*} [Fintype n]
    [Fintype m] [Fintype q] (h : UnitsParallel σ σ' k n m q) {c : q → n → ℝ} {a : q → m → ℝ}
    (hc : LinearIndependent ℝ c) (ha : LinearIndependent ℝ a) (hq : 2 ≤ Fintype.card q) :
    UnitsParallelAt σ σ' k c a :=
  fun ψc β hpar => h c a ψc β hc ha hq hpar

/-- The output of units with slopes `d_j` (`d_j = 1` at an active unit, `0` at an inactive one):
`∑_j d_j (z c_j) f_j`, linear in `z`. On a region of inputs, the output is this map. -/
private noncomputable def lin_upa {n m q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ)
    (d : q → ℝ) (f : q → m → ℝ) (z : n → ℝ) : m → ℝ :=
  ∑ j, (d j * (z ⬝ᵥ c j)) • f j

/-- `max(u, 0) = 1[u > 0] u`. -/
private lemma relu_eq_upa (u : ℝ) : relu u = reluDeriv u * u := by
  unfold relu reluDeriv
  split_ifs with h
  · rw [one_mul, max_eq_left h.le]
  · rw [zero_mul, max_eq_right (not_lt.1 h)]

/-- Two numbers of the same sign have the same slope `1[· > 0]`. -/
private lemma reluDeriv_eq_upa {u v : ℝ} (h : 0 < u * v) : reluDeriv v = reluDeriv u := by
  unfold reluDeriv
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · simp only [hu, hv, ↓reduceIte]
  · simp only [not_lt.2 hu.le, not_lt.2 hv.le, ↓reduceIte]

/-- On the closed cone of a point `u ≠ 0` (`u v ≥ 0`): `max(v, 0) = 1[u > 0] v`. -/
private lemma relu_cone_upa {u v : ℝ} (hu : u ≠ 0) (h : 0 ≤ u * v) :
    relu v = reluDeriv u * v := by
  unfold relu reluDeriv
  rcases hu.lt_or_gt with hu | hu
  · have hv : v ≤ 0 := by nlinarith
    simp only [not_lt.2 hu.le, ↓reduceIte, zero_mul]
    exact max_eq_right hv
  · have hv : 0 ≤ v := by nlinarith
    simp only [hu, ↓reduceIte, one_mul]
    exact max_eq_left hv

private lemma pos_of_mul_upa {u v : ℝ} (h : 0 < u * v) (hu : 0 < u) : 0 < v :=
  pos_of_mul_pos_right h hu.le

private lemma dot_self_pos_upa {n : Type*} [Fintype n] {u : n → ℝ} (hu : u ≠ 0) :
    0 < u ⬝ᵥ u :=
  lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (u j))
    (Ne.symm (mt dotProduct_self_eq_zero.1 hu))

private lemma lin_add_upa {n m q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ) (d : q → ℝ)
    (f : q → m → ℝ) (x v : n → ℝ) (s : ℝ) :
    lin_upa c d f (x + s • v) = lin_upa c d f x + s • lin_upa c d f v := by
  unfold lin_upa
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
  module

private lemma lin_add'_upa {n m q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ) (d : q → ℝ)
    (f : q → m → ℝ) (x v : n → ℝ) :
    lin_upa c d f (x + v) = lin_upa c d f x + lin_upa c d f v := by
  simpa only [one_smul] using lin_add_upa c d f x v 1

/-- Two slope patterns that differ only at unit `i`, where they are `1` and `0`. -/
private lemma lin_facet_upa {n m q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ)
    {d d' : q → ℝ} (f : q → m → ℝ) {i : q} (hd : ∀ j, j ≠ i → d j = d' j) (hi : d i = 1)
    (hi' : d' i = 0) (z : n → ℝ) :
    lin_upa c d f z = lin_upa c d' f z + (z ⬝ᵥ c i) • f i := by
  classical
  unfold lin_upa
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hs : ∑ j ∈ Finset.univ.erase i, (d j * (z ⬝ᵥ c j)) • f j
      = ∑ j ∈ Finset.univ.erase i, (d' j * (z ⬝ᵥ c j)) • f j :=
    Finset.sum_congr rfl fun j hj => by rw [hd j (Finset.ne_of_mem_erase hj)]
  rw [hs, hi, hi']
  module

private lemma sum_relu_upa {n m q : Type*} [Fintype n] [Fintype q] {c : q → n → ℝ} {d : q → ℝ}
    (f : q → m → ℝ) {w : n → ℝ} (h : ∀ j, relu (w ⬝ᵥ c j) = d j * (w ⬝ᵥ c j)) :
    ∑ j, relu (w ⬝ᵥ c j) • f j = lin_upa c d f w :=
  Finset.sum_congr rfl fun j _ => by rw [h j]

private lemma sum_relu_eq_lin_upa {n m q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ)
    (f : q → m → ℝ) (w : n → ℝ) :
    ∑ j, relu (w ⬝ᵥ c j) • f j = lin_upa c (fun j => reluDeriv (w ⬝ᵥ c j)) f w :=
  sum_relu_upa f fun _ => relu_eq_upa _

/-- The vector `J(w)` of a direction, at a point with slopes `d`. -/
private lemma J_eq_upa {n m q : Type*} [Fintype n] [Fintype q] {c ψc : q → n → ℝ}
    {a β : q → m → ℝ} {d : q → ℝ} {w : n → ℝ} (hd : ∀ j, reluDeriv (w ⬝ᵥ c j) = d j) :
    ∑ j, (relu (w ⬝ᵥ c j) • β j + (reluDeriv (w ⬝ᵥ c j) * (w ⬝ᵥ ψc j)) • a j)
      = lin_upa c d β w + lin_upa ψc d a w := by
  unfold lin_upa
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [relu_eq_upa, hd j]

private lemma lin_psi_upa {n m q : Type*} [Fintype n] [Fintype q] {c ψc : q → n → ℝ}
    {lam : q → ℝ} (hψ : ∀ j, ψc j = lam j • c j) (d : q → ℝ) (a : q → m → ℝ) (z : n → ℝ) :
    lin_upa ψc d a z = lin_upa c d (fun j => lam j • a j) z :=
  Finset.sum_congr rfl fun j _ => by
    rw [hψ j, dotProduct_smul, smul_eq_mul]
    module

private lemma lin_addf_upa {n m q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ) (d : q → ℝ)
    (f g : q → m → ℝ) (z : n → ℝ) :
    lin_upa c d f z + lin_upa c d g z = lin_upa c d (fun j => f j + g j) z := by
  unfold lin_upa
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => (smul_add _ _ _).symm

/-- Near `x`, along `v`, the units with `x c_j ≠ 0` keep their sign. -/
private lemma signs_upa {n q : Type*} [Fintype n] [Finite q] (c : q → n → ℝ) (x v : n → ℝ) :
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

/-- **The value at `s = 0`.** If `P + s Q` is a multiple of `U + s V` at `s = δ, 2δ, 3δ` and
`U ≠ 0`, then `P` is a multiple of `U` (every `2 × 2` minor is a quadratic in `s`). -/
private lemma par0_upa {m : Type*} {P Q U V : m → ℝ} {δ : ℝ} (hU : U ≠ 0)
    (h : ∀ k : ℝ, k = 1 ∨ k = 2 ∨ k = 3 → ∃ μ : ℝ, P + (k * δ) • Q = μ • (U + (k * δ) • V)) :
    ∃ μ : ℝ, P = μ • U := by
  obtain ⟨o, ho⟩ := Function.ne_iff.1 hU
  have ho' : U o ≠ 0 := ho
  refine ⟨P o / U o, funext fun o' => ?_⟩
  have key : ∀ k : ℝ, k = 1 ∨ k = 2 ∨ k = 3 → (P o' + k * δ * Q o') * (U o + k * δ * V o)
      = (P o + k * δ * Q o) * (U o' + k * δ * V o') := by
    intro k hk
    obtain ⟨μ, hμ⟩ := h k hk
    have e1 := congrFun hμ o
    have e2 := congrFun hμ o'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    linear_combination (U o + k * δ * V o) * e2 - (U o' + k * δ * V o') * e1
  have k1 := key 1 (Or.inl rfl)
  have k2 := key 2 (Or.inr (Or.inl rfl))
  have k3 := key 3 (Or.inr (Or.inr rfl))
  have h0 : P o' * U o = P o * U o' := by linear_combination 3 * k1 - 3 * k2 + k3
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, eq_div_iff ho']
  linear_combination h0

/-- `U ≠ 0` and `V` not a multiple of `U`: `U`, `V` are independent. -/
private lemma indep_upa {m : Type*} {U V : m → ℝ} (hU : U ≠ 0) (hV : ∀ r : ℝ, V ≠ r • U)
    {α β : ℝ} (h : α • U + β • V = 0) : α = 0 ∧ β = 0 := by
  have hβ : β = 0 := by
    by_contra hβ
    refine hV (-α / β) (funext fun o => ?_)
    have e := congrFun h o
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    field_simp
    linear_combination e
  refine ⟨?_, hβ⟩
  rw [hβ, zero_smul, add_zero] at h
  exact (smul_eq_zero.1 h).resolve_right hU

/-- A vector orthogonal to every `w` with `w u = 0` is a multiple of `u`. -/
private lemma smul_of_ker_upa {n : Type*} [Fintype n] {u v : n → ℝ} (hu : u ⬝ᵥ u ≠ 0)
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
private lemma exists_off_upa {n q : Type*} [Fintype n] [Finite q] {c : q → n → ℝ}
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
private lemma inter_upa {n : Type*} [Fintype n] {u v : n → ℝ} (hu : u ≠ 0)
    (hv : ∀ r : ℝ, v ≠ r • u) : ∃ x : n → ℝ, 0 < x ⬝ᵥ u ∧ 0 < x ⬝ᵥ v := by
  by_contra h
  refine hv _ (smul_of_ker_upa (mt dotProduct_self_eq_zero.1 hu) fun w hw => ?_)
  by_contra hwv
  refine h ⟨u + ((1 - u ⬝ᵥ v) / (w ⬝ᵥ v)) • w, ?_, ?_⟩
  · rw [add_dotProduct, smul_dotProduct, hw, smul_zero, add_zero]
    exact dot_self_pos_upa hu
  · rw [add_dotProduct, smul_dotProduct, smul_eq_mul, div_mul_cancel₀ _ hwv]
    linarith

/-- **`Ω` is preconnected:** a union of half-spaces, any two of which meet. -/
private lemma preconnected_upa {n q : Type*} [Fintype n] {c : q → n → ℝ} (hc : ∀ i, c i ≠ 0)
    (hcc : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) :
    IsPreconnected (⋃ i, {x : n → ℝ | 0 < x ⬝ᵥ c i}) := by
  refine IsPreconnected.iUnion_of_reflTransGen (fun i => ?_) (fun i j => ?_)
  · refine Convex.isPreconnected (convex_halfSpace_gt ?_ 0)
    exact ⟨fun x y => add_dotProduct x y (c i), fun r x => smul_dotProduct r x (c i)⟩
  · refine Relation.ReflTransGen.single ?_
    by_cases hij : i = j
    · subst hij
      exact ⟨c i, dot_self_pos_upa (hc i), dot_self_pos_upa (hc i)⟩
    · obtain ⟨x, h1, h2⟩ := inter_upa (hc i) (hcc j i (Ne.symm hij))
      exact ⟨x, h1, h2⟩

/-- **The two sides of the kink of unit `i`** at a point `x₀` of its hyperplane on no other one:
points `x₀ ± s e` (`e c_i = 1`, `s` small) on no hyperplane, whose slopes differ only at `i`. -/
private lemma facet_upa {n q : Type*} [Fintype n] [Fintype q] {c : q → n → ℝ} {i : q}
    (hci : c i ≠ 0) {x₀ : n → ℝ} (h0 : x₀ ⬝ᵥ c i = 0) (hx₀ : ∀ j, j ≠ i → x₀ ⬝ᵥ c j ≠ 0) :
    ∃ xp xm e : n → ℝ, e ⬝ᵥ c i = 1 ∧ (∀ j, xp ⬝ᵥ c j ≠ 0) ∧ (∀ j, xm ⬝ᵥ c j ≠ 0) ∧
      0 < xp ⬝ᵥ c i ∧ (∀ j, 0 < x₀ ⬝ᵥ c j → 0 < xm ⬝ᵥ c j) ∧
      (∀ j, 0 ≤ (xp ⬝ᵥ c j) * (x₀ ⬝ᵥ c j)) ∧ (∀ j, 0 ≤ (xm ⬝ᵥ c j) * (x₀ ⬝ᵥ c j)) ∧
      (∀ j, j ≠ i → reluDeriv (xp ⬝ᵥ c j) = reluDeriv (xm ⬝ᵥ c j)) ∧
      reluDeriv (xp ⬝ᵥ c i) = 1 ∧ reluDeriv (xm ⬝ᵥ c i) = 0 := by
  have hcc : c i ⬝ᵥ c i ≠ 0 := mt dotProduct_self_eq_zero.1 hci
  obtain ⟨e, he⟩ : ∃ e : n → ℝ, e ⬝ᵥ c i = 1 :=
    ⟨(c i ⬝ᵥ c i)⁻¹ • c i, by rw [smul_dotProduct, smul_eq_mul, inv_mul_cancel₀ hcc]⟩
  obtain ⟨ε, hε, hs⟩ := signs_upa c x₀ e
  have hdot : ∀ t : ℝ, (x₀ + t • e) ⬝ᵥ c i = t := fun t => by
    rw [add_dotProduct, smul_dotProduct, h0, he, smul_eq_mul, mul_one, zero_add]
  have hε2 : 0 < ε / 2 := half_pos hε
  have hp := hs (ε / 2) (by rw [abs_of_pos hε2]; exact half_lt_self hε)
  have hm := hs (-(ε / 2)) (by rw [abs_neg, abs_of_pos hε2]; exact half_lt_self hε)
  have hn : ¬ (0 : ℝ) < -(ε / 2) := by linarith
  refine ⟨x₀ + (ε / 2) • e, x₀ + (-(ε / 2)) • e, e, he, fun j => ?_, fun j => ?_,
    by rw [hdot]; exact hε2, fun j hj => pos_of_mul_upa (hm j hj.ne') hj, fun j => ?_,
    fun j => ?_, fun j hj => ?_, ?_, ?_⟩
  · by_cases hj : j = i
    · rw [hj, hdot]; exact hε2.ne'
    · exact right_ne_zero_of_mul (hp j (hx₀ j hj)).ne'
  · by_cases hj : j = i
    · rw [hj, hdot]; exact (neg_neg_of_pos hε2).ne
    · exact right_ne_zero_of_mul (hm j (hx₀ j hj)).ne'
  · by_cases hj : j = i
    · rw [hj, h0, mul_zero]
    · rw [mul_comm]; exact (hp j (hx₀ j hj)).le
  · by_cases hj : j = i
    · rw [hj, h0, mul_zero]
    · rw [mul_comm]; exact (hm j (hx₀ j hj)).le
  · rw [reluDeriv_eq_upa (hp j (hx₀ j hj)), reluDeriv_eq_upa (hm j (hx₀ j hj))]
  · rw [hdot]; simp only [reluDeriv, hε2, ↓reduceIte]
  · rw [hdot]; simp only [reluDeriv, hn, ↓reduceIte]

/-- **The limit on the boundary of a region.** Let `x` be on no hyperplane with an active unit,
and `x₁` in the closed cone of its region, with output `≠ 0`. Then the linear extensions of `J`
and of the output from the region are parallel at `x₁` (points `x₁ + s (x − x₁)`, `s ∈ (0, 1]`). -/
private lemma closure_par_upa {n m q : Type*} [Fintype n] [Fintype q] {c ψc : q → n → ℝ}
    {a β : q → m → ℝ}
    (hne : ∀ x : n → ℝ, (∃ i, 0 < x ⬝ᵥ c i) → ∑ i, relu (x ⬝ᵥ c i) • a i ≠ 0)
    (hpar : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, relu (x ⬝ᵥ c i) • a i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (relu (x ⬝ᵥ c i) • β i + (reluDeriv (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = μ • ∑ i, relu (x ⬝ᵥ c i) • a i)
    {x : n → ℝ} (hx : ∀ j, x ⬝ᵥ c j ≠ 0) {j₀ : q} (hj₀ : 0 < x ⬝ᵥ c j₀)
    {x₁ : n → ℝ} (hcone : ∀ j, 0 ≤ (x ⬝ᵥ c j) * (x₁ ⬝ᵥ c j))
    (hL : lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) a x₁ ≠ 0) :
    ∃ μ : ℝ, lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) β x₁
        + lin_upa ψc (fun j => reluDeriv (x ⬝ᵥ c j)) a x₁
      = μ • lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) a x₁ := by
  refine par0_upa (δ := 1 / 3) (V := lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) a (x - x₁))
    (Q := lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) β (x - x₁)
      + lin_upa ψc (fun j => reluDeriv (x ⬝ᵥ c j)) a (x - x₁)) hL fun k hk => ?_
  have hk0 : 0 < k * (1 / 3) := by rcases hk with rfl | rfl | rfl <;> norm_num
  have hk1 : k * (1 / 3) ≤ 1 := by rcases hk with rfl | rfl | rfl <;> norm_num
  -- the point `w = x₁ + s (x − x₁)` has the pattern of `x`
  have hpat : ∀ j, 0 < (x ⬝ᵥ c j) * ((x₁ + (k * (1 / 3)) • (x - x₁)) ⬝ᵥ c j) := by
    intro j
    rw [add_dotProduct, smul_dotProduct, sub_dotProduct, smul_eq_mul]
    have h1 := hcone j
    have h2 := mul_self_pos.2 (hx j)
    nlinarith
  have hw0 : ∀ j, (x₁ + (k * (1 / 3)) • (x - x₁)) ⬝ᵥ c j ≠ 0 := fun j =>
    right_ne_zero_of_mul (hpat j).ne'
  have hdw : ∀ j, reluDeriv ((x₁ + (k * (1 / 3)) • (x - x₁)) ⬝ᵥ c j) = reluDeriv (x ⬝ᵥ c j) :=
    fun j => reluDeriv_eq_upa (hpat j)
  have hB : ∑ j, relu ((x₁ + (k * (1 / 3)) • (x - x₁)) ⬝ᵥ c j) • a j
      = lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) a (x₁ + (k * (1 / 3)) • (x - x₁)) :=
    sum_relu_upa a fun j => by rw [relu_eq_upa, hdw j]
  obtain ⟨μ, hμ⟩ := hpar _ hw0 (hne _ ⟨j₀, pos_of_mul_upa (hpat j₀) hj₀⟩)
  rw [J_eq_upa hdw, hB, lin_add_upa, lin_add_upa, lin_add_upa] at hμ
  exact ⟨μ, by linear_combination (norm := module) hμ⟩

/-- **The kinks stay, at one point.** At a point `x₁` of the hyperplane of unit `i`, on no other
hyperplane, where the output is not a multiple of `a_i`: `x₁ ψc_i = 0`. Across the hyperplane `J`
jumps by `(x₁ ψc_i) a_i` and the output does not jump. -/
private lemma kink_upa {n m q : Type*} [Fintype n] [Fintype q] {c ψc : q → n → ℝ}
    {a β : q → m → ℝ} (ha : ∀ i, a i ≠ 0)
    (hne : ∀ x : n → ℝ, (∃ i, 0 < x ⬝ᵥ c i) → ∑ i, relu (x ⬝ᵥ c i) • a i ≠ 0)
    (hpar : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, relu (x ⬝ᵥ c i) • a i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (relu (x ⬝ᵥ c i) • β i + (reluDeriv (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = μ • ∑ i, relu (x ⬝ᵥ c i) • a i)
    {i : q} (hci : c i ≠ 0) {x₁ : n → ℝ} (h0 : x₁ ⬝ᵥ c i = 0)
    (hx₁ : ∀ j, j ≠ i → x₁ ⬝ᵥ c j ≠ 0)
    (hB : ∀ r : ℝ, ∑ j, relu (x₁ ⬝ᵥ c j) • a j ≠ r • a i) : x₁ ⬝ᵥ ψc i = 0 := by
  obtain ⟨xp, xm, e, -, hxp, hxm, hpi, hmj, hcp, hcm, hdj, hdp, hdm⟩ := facet_upa hci h0 hx₁
  -- an active unit at `x₁`
  obtain ⟨j, hj⟩ : ∃ j, 0 < x₁ ⬝ᵥ c j := by
    by_contra hno
    refine hB 0 ?_
    rw [zero_smul]
    exact Finset.sum_eq_zero fun j _ => by
      rw [relu, max_eq_right (not_lt.1 fun h => hno ⟨j, h⟩), zero_smul]
  have hB0 : ∑ j, relu (x₁ ⬝ᵥ c j) • a j ≠ 0 := by
    have h := hB 0
    rwa [zero_smul] at h
  have hBp := sum_relu_upa a fun l => relu_cone_upa (hxp l) (hcp l)
  have hBm := sum_relu_upa a fun l => relu_cone_upa (hxm l) (hcm l)
  obtain ⟨μp, hμp⟩ := closure_par_upa hne hpar hxp hpi hcp (hBp ▸ hB0)
  obtain ⟨μm, hμm⟩ := closure_par_upa hne hpar hxm (hmj j hj) hcm (hBm ▸ hB0)
  -- the two sides differ by the terms of unit `i`
  rw [lin_facet_upa c β hdj hdp hdm, lin_facet_upa ψc a hdj hdp hdm,
    lin_facet_upa c a hdj hdp hdm, h0] at hμp
  have key : (x₁ ⬝ᵥ ψc i) • a i = (μp - μm) • ∑ j, relu (x₁ ⬝ᵥ c j) • a j := by
    rw [hBm]
    linear_combination (norm := module) hμp - hμm
  by_contra hψ
  have hμ : μp - μm ≠ 0 := fun h => by
    rw [h, zero_smul] at key
    exact hψ ((smul_eq_zero.1 key).resolve_right (ha i))
  refine hB ((x₁ ⬝ᵥ ψc i) / (μp - μm)) ?_
  rw [div_eq_inv_mul, mul_smul, key, smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- **The kinks stay, on the whole hyperplane.** From `hkink`'s point `x₀`, the points `x₀ + t w`
(`w c_i = 0`, `t` small) are on the hyperplane of unit `i` only, and at one of `t = ε/2, ε/4`
the output is not a multiple of `a_i`. -/
private lemma psi_upa {n m q : Type*} [Fintype n] [Fintype q] {c ψc : q → n → ℝ}
    {a β : q → m → ℝ} (ha : ∀ i, a i ≠ 0)
    (hne : ∀ x : n → ℝ, (∃ i, 0 < x ⬝ᵥ c i) → ∑ i, relu (x ⬝ᵥ c i) • a i ≠ 0)
    (hpar : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, relu (x ⬝ᵥ c i) • a i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (relu (x ⬝ᵥ c i) • β i + (reluDeriv (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = μ • ∑ i, relu (x ⬝ᵥ c i) • a i)
    {i : q} (hci : c i ≠ 0) {x₀ : n → ℝ} (h0 : x₀ ⬝ᵥ c i = 0)
    (hx₀ : ∀ j, j ≠ i → x₀ ⬝ᵥ c j ≠ 0)
    (hB : ∀ r : ℝ, ∑ j, relu (x₀ ⬝ᵥ c j) • a j ≠ r • a i) {w : n → ℝ} (hw : w ⬝ᵥ c i = 0) :
    w ⬝ᵥ ψc i = 0 := by
  have hk0 := kink_upa ha hne hpar hci h0 hx₀ hB
  obtain ⟨ε, hε, hs⟩ := signs_upa c x₀ w
  have hdot : ∀ t : ℝ, (x₀ + t • w) ⬝ᵥ c i = 0 := fun t => by
    rw [add_dotProduct, smul_dotProduct, h0, hw, smul_zero, add_zero]
  have hx : ∀ t : ℝ, |t| < ε → ∀ j, j ≠ i → (x₀ + t • w) ⬝ᵥ c j ≠ 0 := fun t ht j hj =>
    right_ne_zero_of_mul (hs t ht j (hx₀ j hj)).ne'
  -- near `x₀` on the hyperplane, the output is affine in `t`
  have hlin : ∀ t : ℝ, |t| < ε → ∑ j, relu ((x₀ + t • w) ⬝ᵥ c j) • a j
      = ∑ j, relu (x₀ ⬝ᵥ c j) • a j
        + t • lin_upa c (fun j => reluDeriv (x₀ ⬝ᵥ c j)) a w := by
    intro t ht
    have hr : ∀ j, relu ((x₀ + t • w) ⬝ᵥ c j)
        = reluDeriv (x₀ ⬝ᵥ c j) * ((x₀ + t • w) ⬝ᵥ c j) := by
      intro j
      by_cases hj : j = i
      · rw [hj, hdot, h0]; exact relu_eq_upa 0
      · exact relu_cone_upa (hx₀ j hj) (hs t ht j (hx₀ j hj)).le
    rw [sum_relu_upa a hr, lin_add_upa, sum_relu_eq_lin_upa]
  have ht1 : |ε / 2| < ε := by rw [abs_of_pos (half_pos hε)]; exact half_lt_self hε
  have ht2 : |ε / 4| < ε := by rw [abs_of_pos (by positivity)]; linarith
  have hone : ∃ t : ℝ, t ≠ 0 ∧ |t| < ε ∧
      ∀ r : ℝ, ∑ j, relu ((x₀ + t • w) ⬝ᵥ c j) • a j ≠ r • a i := by
    by_contra hno
    have h1 : ∃ r : ℝ, ∑ j, relu ((x₀ + (ε / 2) • w) ⬝ᵥ c j) • a j = r • a i := by
      by_contra h
      exact hno ⟨ε / 2, (half_pos hε).ne', ht1, fun r hr => h ⟨r, hr⟩⟩
    have h2 : ∃ r : ℝ, ∑ j, relu ((x₀ + (ε / 4) • w) ⬝ᵥ c j) • a j = r • a i := by
      by_contra h
      exact hno ⟨ε / 4, (by positivity), ht2, fun r hr => h ⟨r, hr⟩⟩
    obtain ⟨r₁, e₁⟩ := h1
    obtain ⟨r₂, e₂⟩ := h2
    rw [hlin _ ht1] at e₁
    rw [hlin _ ht2] at e₂
    exact hB (2 * r₂ - r₁) (by linear_combination (norm := module) (2 : ℝ) • e₂ - e₁)
  obtain ⟨t, ht0, ht, htB⟩ := hone
  have h := kink_upa ha hne hpar hci (hdot t) (hx t ht) htB
  rw [add_dotProduct, smul_dotProduct, hk0, zero_add, smul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left ht0

/-- **One constant on a region.** Let `x` be on no hyperplane with an active unit, `d` its
slopes, and let `L_e(w) = ∑_j d_j (w c_j) e_j` be a multiple of `L_a(w)` on the region of `x`.
Then `L_e = κ L_a` for one number `κ` (with one active unit directly; with two, by `hrank`). -/
private lemma good_upa {n m q : Type*} [Fintype n] [Fintype q] {c : q → n → ℝ}
    {a e : q → m → ℝ} {x : n → ℝ} (hx : ∀ j, x ⬝ᵥ c j ≠ 0) {j₀ : q} (hj₀ : 0 < x ⬝ᵥ c j₀)
    (hreg : ∀ w : n → ℝ, (∀ j, 0 < (x ⬝ᵥ c j) * (w ⬝ᵥ c j)) →
      ∃ μ : ℝ, lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) e w
        = μ • lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) a w)
    (hLx : lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) a x ≠ 0)
    (hrank : (∃ i j, i ≠ j ∧ 0 < x ⬝ᵥ c i ∧ 0 < x ⬝ᵥ c j) →
      ∃ y : n → ℝ, ∀ r : ℝ, lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) a y
        ≠ r • lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) a x) :
    ∃ κ : ℝ, ∀ z, lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) e z
      = κ • lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) a z := by
  set d : q → ℝ := fun j => reluDeriv (x ⬝ᵥ c j) with hd
  obtain ⟨μ₀, hμ₀⟩ := hreg x fun j => mul_self_pos.2 (hx j)
  refine ⟨μ₀, ?_⟩
  by_cases h2 : ∃ i j, i ≠ j ∧ 0 < x ⬝ᵥ c i ∧ 0 < x ⬝ᵥ c j
  · obtain ⟨y, hy⟩ := hrank h2
    -- at a `y'` whose image is not a multiple of `L_a(x)`: points `x + t y'`, `t = ε/2, ε/4`
    have P : ∀ y' : n → ℝ, (∀ r : ℝ, lin_upa c d a y' ≠ r • lin_upa c d a x) →
        lin_upa c d e y' = μ₀ • lin_upa c d a y' := by
      intro y' hy'
      obtain ⟨ε, hε, hs⟩ := signs_upa c x y'
      have key : ∀ t : ℝ, |t| < ε → ∃ l : ℝ, t • (lin_upa c d e y' - μ₀ • lin_upa c d a y')
          = l • (lin_upa c d a x + t • lin_upa c d a y') := by
        intro t ht
        obtain ⟨μ, hμ⟩ := hreg (x + t • y') fun j => hs t ht j (hx j)
        rw [lin_add_upa, lin_add_upa] at hμ
        exact ⟨μ - μ₀, by linear_combination (norm := module) hμ - hμ₀⟩
      obtain ⟨l₁, h1⟩ := key (ε / 2) (by rw [abs_of_pos (half_pos hε)]; exact half_lt_self hε)
      obtain ⟨l₂, h2⟩ := key (ε / 4) (by rw [abs_of_pos (by positivity)]; linarith)
      have h3 : ((ε / 4) * l₁ - (ε / 2) * l₂) • lin_upa c d a x
          + ((ε / 2) * (ε / 4) * (l₁ - l₂)) • lin_upa c d a y' = 0 := by
        linear_combination (norm := module) (ε / 2) • h2 - (ε / 4) • h1
      obtain ⟨h4, h5⟩ := indep_upa hLx hy' h3
      have h6 : l₁ - l₂ = 0 := (mul_eq_zero.1 h5).resolve_left (by positivity)
      have h7 : ε * l₁ = 0 := by linear_combination -4 * h4 + 2 * ε * h6
      rw [(mul_eq_zero.1 h7).resolve_left hε.ne', zero_smul] at h1
      exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left (half_pos hε).ne')
    intro z
    by_cases hz : ∀ r : ℝ, lin_upa c d a z ≠ r • lin_upa c d a x
    · exact P z hz
    · push Not at hz
      obtain ⟨r, hr⟩ := hz
      have hyz := P (y + z) fun r' h => hy (r' - r) (by
        rw [lin_add'_upa, hr] at h
        linear_combination (norm := module) h)
      rw [lin_add'_upa, lin_add'_upa, P y hy] at hyz
      linear_combination (norm := module) hyz
  · -- one active unit `j₀`: `L_f(z) = (z c_j₀) f_j₀`
    push Not at h2
    have hz : ∀ l, l ≠ j₀ → d l = 0 := fun l hl => by
      simp only [hd, reluDeriv, not_lt.2 (h2 j₀ l (Ne.symm hl) hj₀), ↓reduceIte]
    have hd0 : d j₀ = 1 := by simp only [hd, reluDeriv, hj₀, ↓reduceIte]
    have hone : ∀ (f : q → m → ℝ) (z : n → ℝ), lin_upa c d f z = (z ⬝ᵥ c j₀) • f j₀ := by
      intro f z
      unfold lin_upa
      rw [Finset.sum_eq_single j₀ (fun l _ hl => by rw [hz l hl, zero_mul, zero_smul])
        (fun h => absurd (Finset.mem_univ j₀) h), hd0, one_mul]
    rw [hone, hone] at hμ₀
    have he : e j₀ = μ₀ • a j₀ := by
      have h' : (x ⬝ᵥ c j₀) • (e j₀ - μ₀ • a j₀) = 0 := by
        linear_combination (norm := module) hμ₀
      exact sub_eq_zero.1 ((smul_eq_zero.1 h').resolve_left (hx j₀))
    intro z
    rw [hone, hone, he]
    module

/-- **"The kinks stay" and "One scale" for ReLU units in general position** (proof of Theorem
B.1 (iv) of the skips paper, "The skipless network: equality", `k = 1`; any number of units, also
more units than coordinates): let the columns `c_i` be pairwise non-collinear and the rows `a_i`
nonzero; let the output `h_1(x) = ∑_i max(x c_i, 0) a_i` be nonzero wherever a unit is active; for
every unit `i` let there be a point `x_0` of its hyperplane `x c_i = 0`, on no other hyperplane,
at which `h_1(x_0)` is not a multiple of `a_i`; and at every `x` off the kinks with at least two
active units let there be a `y` for which `∑_{i active at x} (y c_i) a_i` is not a multiple of
`h_1(x)`. Then `UnitsParallelAt` holds: a direction `(ψc, β)` whose derivative of the output is a
multiple of the output off the kinks is `ψc_i = λ_i c_i`, `β_i = (c₀ − λ_i) a_i`. -/
theorem relu_unitsParallelAt_of_generic {n m q : Type*} [Fintype n] [Fintype m] [Fintype q]
    (c : q → n → ℝ) (a : q → m → ℝ)
    (hcc : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) (ha : ∀ i, a i ≠ 0)
    (hne : ∀ x : n → ℝ, (∃ i, 0 < x ⬝ᵥ c i) → ∑ i, relu (x ⬝ᵥ c i) • a i ≠ 0)
    (hkink : ∀ i, ∃ x₀ : n → ℝ, x₀ ⬝ᵥ c i = 0 ∧ (∀ j, j ≠ i → x₀ ⬝ᵥ c j ≠ 0) ∧
      ∀ r : ℝ, ∑ j, relu (x₀ ⬝ᵥ c j) • a j ≠ r • a i)
    (hrank : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) →
      (∃ i j, i ≠ j ∧ 0 < x ⬝ᵥ c i ∧ 0 < x ⬝ᵥ c j) →
      ∃ y : n → ℝ, ∀ r : ℝ, ∑ i, (reluDeriv (x ⬝ᵥ c i) * (y ⬝ᵥ c i)) • a i
        ≠ r • ∑ i, relu (x ⬝ᵥ c i) • a i) :
    UnitsParallelAt relu reluDeriv 1 c a := by
  classical
  intro ψc β hpar
  rcases isEmpty_or_nonempty q with hq | ⟨⟨i₀⟩⟩
  · exact ⟨0, fun _ => 0, fun i => isEmptyElim i⟩
  -- where the output is not a multiple of `a_i`, some unit is active
  have hact : ∀ (i : q) (x₀ : n → ℝ), (∀ r : ℝ, ∑ j, relu (x₀ ⬝ᵥ c j) • a j ≠ r • a i) →
      ∃ j, 0 < x₀ ⬝ᵥ c j := by
    intro i x₀ hB
    by_contra h
    refine hB 0 ?_
    rw [zero_smul]
    exact Finset.sum_eq_zero fun j _ => by
      rw [relu, max_eq_right (not_lt.1 fun hj => h ⟨j, hj⟩), zero_smul]
  -- every `c_i` is nonzero: at `x₀` of `hkink` another unit is active
  have hci : ∀ i, c i ≠ 0 := by
    intro i hc0
    obtain ⟨x₀, h0, -, hB⟩ := hkink i
    obtain ⟨j, hj⟩ := hact i x₀ hB
    have hji : j ≠ i := fun h => by rw [h, h0] at hj; exact lt_irrefl 0 hj
    exact hcc i j hji.symm 0 (by rw [hc0, zero_smul])
  -- Step 1, the kinks stay: `ψc_i = λ_i c_i`
  obtain ⟨lam, hlam⟩ : ∃ lam : q → ℝ, ∀ i, ψc i = lam i • c i := by
    refine ⟨fun i => (c i ⬝ᵥ ψc i) / (c i ⬝ᵥ c i), fun i => ?_⟩
    obtain ⟨x₀, h0, hx₀, hB⟩ := hkink i
    exact smul_of_ker_upa (mt dotProduct_self_eq_zero.1 (hci i))
      fun w hw => psi_upa ha hne hpar (hci i) h0 hx₀ hB hw
  -- then `J(x) = ∑_i relu(x c_i) e_i` with `e_i = β_i + λ_i a_i`
  obtain ⟨e, he⟩ : ∃ e : q → m → ℝ, e = fun j => β j + lam j • a j := ⟨_, rfl⟩
  -- Step 2, one constant on each region
  have hgood : ∀ x : n → ℝ, (∀ j, x ⬝ᵥ c j ≠ 0) → ∀ j₀, 0 < x ⬝ᵥ c j₀ → ∃ κ : ℝ, ∀ z,
      lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) e z
        = κ • lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) a z := by
    intro x hx j₀ hj₀
    refine good_upa hx hj₀ (fun w hw => ?_) ?_ (fun h => ?_)
    · have hw0 : ∀ j, w ⬝ᵥ c j ≠ 0 := fun j => right_ne_zero_of_mul (hw j).ne'
      have hdw : ∀ j, reluDeriv (w ⬝ᵥ c j) = reluDeriv (x ⬝ᵥ c j) :=
        fun j => reluDeriv_eq_upa (hw j)
      have hB : ∑ j, relu (w ⬝ᵥ c j) • a j = lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) a w :=
        sum_relu_upa a fun j => by rw [relu_eq_upa, hdw j]
      obtain ⟨μ, hμ⟩ := hpar w hw0 (hne w ⟨j₀, pos_of_mul_upa (hw j₀) hj₀⟩)
      rw [J_eq_upa hdw, hB, lin_psi_upa hlam, lin_addf_upa, ← he] at hμ
      exact ⟨μ, hμ⟩
    · rw [← sum_relu_eq_lin_upa]
      exact hne x ⟨j₀, hj₀⟩
    · obtain ⟨y, hy⟩ := hrank x hx h
      exact ⟨y, fun r h' => hy r (by rw [sum_relu_eq_lin_upa]; exact h')⟩
  -- Step 3, one constant: `μ(x) = ⟨E(x), B(x)⟩ / ‖B(x)‖²` on `Ω`
  obtain ⟨B, hB⟩ : ∃ B : (n → ℝ) → m → ℝ, B = fun x => ∑ j, relu (x ⬝ᵥ c j) • a j := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : (n → ℝ) → m → ℝ, E = fun x => ∑ j, relu (x ⬝ᵥ c j) • e j := ⟨_, rfl⟩
  obtain ⟨μf, hμf⟩ : ∃ μf : (n → ℝ) → ℝ, μf = fun x => (E x ⬝ᵥ B x) / (B x ⬝ᵥ B x) :=
    ⟨_, rfl⟩
  have hBne : ∀ w, (∃ j, 0 < w ⬝ᵥ c j) → B w ≠ 0 := fun w h => by rw [hB]; exact hne w h
  -- a good point gives `E = κ B` on the closed cone of its region
  have hcl : ∀ x : n → ℝ, (∀ j, x ⬝ᵥ c j ≠ 0) → ∀ κ : ℝ,
      (∀ z, lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) e z
        = κ • lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) a z) →
      ∀ w, (∀ j, 0 ≤ (x ⬝ᵥ c j) * (w ⬝ᵥ c j)) → E w = κ • B w := by
    intro x hx κ hκ w hw
    rw [hE, hB]
    dsimp only
    rw [sum_relu_upa e fun j => relu_cone_upa (hx j) (hw j),
      sum_relu_upa a fun j => relu_cone_upa (hx j) (hw j)]
    exact hκ w
  have hμκ : ∀ w κ, E w = κ • B w → B w ≠ 0 → μf w = κ := by
    intro w κ h hB0
    rw [hμf]
    dsimp only
    rw [h, smul_dotProduct, smul_eq_mul, mul_div_assoc,
      div_self (mt dotProduct_self_eq_zero.1 hB0), mul_one]
  -- the good pairs `(x, κ)`, and their finitely many values `κ`
  obtain ⟨G, hG⟩ : ∃ G : (n → ℝ) → ℝ → Prop, G = fun x κ => (∀ j, x ⬝ᵥ c j ≠ 0) ∧
      (∃ j, 0 < x ⬝ᵥ c j) ∧ ∀ z, lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) e z
        = κ • lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) a z := ⟨_, rfl⟩
  have hVfin : {κ | ∃ x, G x κ}.Finite := by
    refine Set.Finite.subset (Set.finite_iUnion fun S : q → Prop =>
      Set.Subsingleton.finite (s := {κ | ∃ x, G x κ ∧ (fun j => 0 < x ⬝ᵥ c j) = S}) ?_) ?_
    · rintro κ₁ ⟨x₁, hG₁, hS₁⟩ κ₂ ⟨x₂, hG₂, hS₂⟩
      rw [hG] at hG₁ hG₂
      obtain ⟨hx₁, -, hκ₁⟩ := hG₁
      obtain ⟨hx₂, ⟨j, hj⟩, hκ₂⟩ := hG₂
      have hpat : ∀ l, (0 < x₁ ⬝ᵥ c l ↔ 0 < x₂ ⬝ᵥ c l) := fun l =>
        Iff.of_eq (congrFun (hS₁.trans hS₂.symm) l)
      have hcone : ∀ l, 0 ≤ (x₁ ⬝ᵥ c l) * (x₂ ⬝ᵥ c l) := fun l => by
        rcases (hx₁ l).lt_or_gt with h | h
        · have h' : x₂ ⬝ᵥ c l ≤ 0 := not_lt.1 fun h' => absurd ((hpat l).2 h') (not_lt.2 h.le)
          nlinarith
        · exact (mul_pos h ((hpat l).1 h)).le
      have hB2 := hBne x₂ ⟨j, hj⟩
      exact (hμκ x₂ κ₁ (hcl x₁ hx₁ κ₁ hκ₁ x₂ hcone) hB2).symm.trans
        (hμκ x₂ κ₂ (hcl x₂ hx₂ κ₂ hκ₂ x₂ fun l => mul_self_nonneg _) hB2)
    · rintro κ ⟨x, hGx⟩
      exact Set.mem_iUnion.2 ⟨fun j => 0 < x ⬝ᵥ c j, x, hGx, rfl⟩
  -- every point of `Ω` is in the closed cone of a good point: `μ(w)` is a good value
  obtain ⟨v, hv⟩ := exists_off_upa hci
  have hval : ∀ w, (∃ j, 0 < w ⬝ᵥ c j) → ∃ x, G x (μf w) := by
    rintro w ⟨j₀, hj₀⟩
    obtain ⟨ε, hε, hs⟩ := signs_upa c w v
    have hε2 : 0 < ε / 2 := half_pos hε
    have ht : |ε / 2| < ε := by rw [abs_of_pos hε2]; exact half_lt_self hε
    have hxp : ∀ j, (w + (ε / 2) • v) ⬝ᵥ c j ≠ 0 := fun j => by
      by_cases hj : w ⬝ᵥ c j = 0
      · rw [add_dotProduct, smul_dotProduct, hj, zero_add, smul_eq_mul]
        exact mul_ne_zero hε2.ne' (hv j)
      · exact right_ne_zero_of_mul (hs _ ht j hj).ne'
    have hcone : ∀ j, 0 ≤ ((w + (ε / 2) • v) ⬝ᵥ c j) * (w ⬝ᵥ c j) := fun j => by
      by_cases hj : w ⬝ᵥ c j = 0
      · rw [hj, mul_zero]
      · rw [mul_comm]; exact (hs _ ht j hj).le
    have hact' : 0 < (w + (ε / 2) • v) ⬝ᵥ c j₀ := pos_of_mul_upa (hs _ ht j₀ hj₀.ne') hj₀
    obtain ⟨κ, hκ⟩ := hgood _ hxp j₀ hact'
    refine ⟨w + (ε / 2) • v, ?_⟩
    rw [hμκ w κ (hcl _ hxp κ hκ w hcone) (hBne w ⟨j₀, hj₀⟩), hG]
    exact ⟨hxp, ⟨j₀, hact'⟩, hκ⟩
  -- `μ` is continuous on `Ω`, `Ω` is preconnected, `μ` takes finitely many values: constant
  have hcont : ContinuousOn μf (⋃ i, {x : n → ℝ | 0 < x ⬝ᵥ c i}) := by
    have hrelu : Continuous relu := continuous_id.max continuous_const
    have hsum : ∀ f : q → m → ℝ, Continuous fun x : n → ℝ => ∑ j, relu (x ⬝ᵥ c j) • f j :=
      fun f => continuous_finsetSum _ fun j _ =>
        (hrelu.comp (continuous_id.dotProduct continuous_const)).smul continuous_const
    have hBc : Continuous B := by rw [hB]; exact hsum a
    have hEc : Continuous E := by rw [hE]; exact hsum e
    rw [hμf]
    refine ContinuousOn.div (f := fun x => E x ⬝ᵥ B x) (g := fun x => B x ⬝ᵥ B x)
      (hEc.dotProduct hBc).continuousOn (hBc.dotProduct hBc).continuousOn fun w hw => ?_
    exact mt dotProduct_self_eq_zero.1 (hBne w (Set.mem_iUnion.1 hw))
  have hconn := preconnected_upa hci hcc
  have hconst : ∀ x y, (∃ j, 0 < x ⬝ᵥ c j) → (∃ j, 0 < y ⬝ᵥ c j) → μf x = μf y := by
    intro x y hx hy
    have hxΩ : x ∈ ⋃ i, {x : n → ℝ | 0 < x ⬝ᵥ c i} := Set.mem_iUnion.2 hx
    have hyΩ : y ∈ ⋃ i, {x : n → ℝ | 0 < x ⬝ᵥ c i} := Set.mem_iUnion.2 hy
    have himg : μf '' (⋃ i, {x : n → ℝ | 0 < x ⬝ᵥ c i}) ⊆ {κ | ∃ x, G x κ} := by
      rintro _ ⟨w, hw, rfl⟩
      exact hval w (Set.mem_iUnion.1 hw)
    by_contra hxy
    rcases lt_or_gt_of_ne hxy with h | h
    · exact Set.Icc_infinite h
        (hVfin.subset ((hconn.intermediate_value hxΩ hyΩ hcont).trans himg))
    · exact Set.Icc_infinite h
        (hVfin.subset ((hconn.intermediate_value hyΩ hxΩ hcont).trans himg))
  -- every good value is `c₀ = μ(c_{i₀})`
  have hc₀ : ∀ x, (∀ j, x ⬝ᵥ c j ≠ 0) → (∃ j, 0 < x ⬝ᵥ c j) → ∀ κ : ℝ,
      (∀ z, lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) e z
        = κ • lin_upa c (fun j => reluDeriv (x ⬝ᵥ c j)) a z) → κ = μf (c i₀) := by
    intro x hx0 hx κ hκ
    rw [← hμκ x κ (hcl x hx0 κ hκ x fun j => mul_self_nonneg _) (hBne x hx)]
    exact hconst x (c i₀) hx ⟨i₀, dot_self_pos_upa (hci i₀)⟩
  -- Step 4: across the kink of unit `i`, `e_i = c₀ a_i`
  refine ⟨μf (c i₀), lam, fun i => ⟨hlam i, ?_⟩⟩
  obtain ⟨x₀, h0, hx₀, hB₀⟩ := hkink i
  obtain ⟨j, hj⟩ := hact i x₀ hB₀
  obtain ⟨xp, xm, u, hu, hxp, hxm, hpi, hmj, -, -, hdj, hdp, hdm⟩ := facet_upa (hci i) h0 hx₀
  obtain ⟨κp, hκp⟩ := hgood xp hxp i hpi
  obtain ⟨κm, hκm⟩ := hgood xm hxm j (hmj j hj)
  have h1 := hκp u
  have h2 := hκm u
  rw [hc₀ xp hxp ⟨i, hpi⟩ κp hκp, lin_facet_upa c e hdj hdp hdm,
    lin_facet_upa c a hdj hdp hdm, hu] at h1
  rw [hc₀ xm hxm ⟨j, hmj j hj⟩ κm hκm] at h2
  have h3 : e i = μf (c i₀) • a i := by linear_combination (norm := module) h1 - h2
  rw [he] at h3
  rw [Nat.cast_one, one_mul]
  linear_combination (norm := module) h3

end Skips
