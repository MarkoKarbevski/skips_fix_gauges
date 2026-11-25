import SkipsLean.OneBlock.Rescale

/-!
# ReLU and ReLU² units and a symmetric change of the input: only a scaling and rescalings

Paper (skips paper), proof of Theorem B.1 (iii). Step 4 has, for a symmetric matrix `X_s` and a
direction `ψ` of the weights of the block, equation (17), `∂_ψ B(n) = q(n) DB(n) n` with
`q(n) = n X_s nᵀ / d_model`, on the image of `N_ε`. "The case `ε = 0`": "(17) holds with `X_0` in
place of `X_s` on the sphere. […] For ReLU, ReLU² and ReGLU, both sides of (17) are positively
homogeneous, of degrees `k` and `k + 2`, so `‖n‖² ∂_ψ B(n) = k d_model q(n) B(n)` for all
`n ≠ 0`. On each region where no `n c_k` changes sign, both sides are polynomials in `n`. Across
the hyperplane `n c_i = 0`, at a point of no other such hyperplane, only the terms of unit `i`
change, so they satisfy the identity on their own: `‖n‖²` times a polynomial equals
`k d_model q(n)` times `(n c_i) a_i`, `(n c_i)² a_i` or `(n c_i)(n e_i) a_i`. Since `‖n‖²` has no
real linear factor, it divides `q(n)`, so `X_0` is a multiple of `I`, and `X_0 = 0` because its
trace vanishes. Then Step 5 gives equality."

Here this step, together with Lemma B.3 for the remaining direction, as one statement on vectors
with no network in it (a twin of `UnitsRescale`, `OneBlock/Rescale.lean`), for the units
`σ(x c_i) a_i` of a ReLU or ReLU² block: `B(x) = ∑_i σ(x c_i) a_i`,
`∂_ψ B(x) = ∑_i [σ(x c_i) β_i + σ'(x c_i) (x ψc_i) a_i]`, and `k d_model q(x) = k (x X xᵀ)`. If

`‖x‖² ∑_i [σ(x c_i) β_i + σ'(x c_i) (x ψc_i) a_i] = k (x X xᵀ) ∑_i σ(x c_i) a_i`

at every `x` with no unit at its kink, for a symmetric `X`, then `X = c₀ I` and the direction is
a rescaling of the units shifted by `c₀`: `ψc_i = λ_i c_i`, `β_i = k (c₀ − λ_i) a_i`. (The paper's
`X_0` has trace zero, which gives `c₀ = 0`; here `X` is any symmetric matrix, and `c₀ I` is the
scaling of the hidden state.) At least one unit is asked: with no unit both sides vanish for
every `X`. Exact check of the dimension `q + 1` of the solutions:
`units_rescale_sphere_check_2026-11-24.py`. ReGLU units: `OneBlock/UnitsRescaleSphereReGLU.lean`.
-/

namespace Skips

open Matrix

/-- **Step 4 of the proof of Theorem B.1 (iii) of the skips paper for `ε = 0`, with Lemma B.3, as
a property of an activation `σ` with derivative `σ'` off the kink and degree `k`:** for hidden
units `σ(x c_i) a_i` with nonzero rows `a_i` and nonzero, pairwise non-collinear columns `c_i`, a
symmetric matrix `X` and a direction `(ψc, β)` of the weights, if at every input `x` with no unit
at its kink `‖x‖² ∑_i [σ(x c_i) β_i + σ'(x c_i) (x ψc_i) a_i] = k (x X xᵀ) ∑_i σ(x c_i) a_i`, then
`X = c₀ I` for a number `c₀`, and `ψc_i = λ_i c_i`, `β_i = k (c₀ − λ_i) a_i` for numbers `λ_i`.
The coordinates of the input are indexed by `n`, those of the output by `m`, the hidden units by
`q` (at least one). -/
def UnitsRescaleSphere (σ σ' : ℝ → ℝ) (k : ℕ) (n m q : Type*) [Fintype n] [DecidableEq n]
    [Fintype m] [Fintype q] : Prop :=
  ∀ (c : q → n → ℝ) (a : q → m → ℝ) (X : Matrix n n ℝ) (ψc : q → n → ℝ) (β : q → m → ℝ),
    (∀ i, a i ≠ 0) → (∀ i, c i ≠ 0) → (∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) → Xᵀ = X →
    (∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) →
      (x ⬝ᵥ x) • ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = ((k : ℝ) * ((x ᵥ* X) ⬝ᵥ x)) • ∑ i, σ (x ⬝ᵥ c i) • a i) →
    ∃ (c₀ : ℝ) (lam : q → ℝ), X = c₀ • (1 : Matrix n n ℝ) ∧
      ∀ i, ψc i = lam i • c i ∧ β i = ((k : ℝ) * (c₀ - lam i)) • a i

/-! ### Analytic functions of the input -/

open Filter Topology in
/-- The identity theorem on `n → ℝ`: an analytic function that vanishes near a point vanishes
everywhere. -/
private lemma eq_zero_of_eventually_urs {n m : Type*} [Fintype n] [Fintype m]
    {f : (n → ℝ) → m → ℝ} (hf : ∀ x, AnalyticAt ℝ f x) {z : n → ℝ}
    (hz : ∀ᶠ x in 𝓝 z, f x = 0) (y : n → ℝ) : f y = 0 :=
  congrFun (AnalyticOnNhd.eq_of_eventuallyEq (g := fun _ => 0) (fun x _ => hf x)
    (fun _ _ => analyticAt_const) hz) y

/-- A coordinate `x ↦ x_i` is analytic. -/
private lemma analyticAt_coord_urs {n : Type*} [Fintype n] (i : n) (x : n → ℝ) :
    AnalyticAt ℝ (fun y : n → ℝ => y i) x :=
  (analyticAt_pi_iff (f := fun j (y : n → ℝ) => y j) (e := x)).1 analyticAt_id i

/-- `x ↦ x c` is analytic. -/
private lemma analyticAt_dot_urs {n : Type*} [Fintype n] (c : n → ℝ) (x : n → ℝ) :
    AnalyticAt ℝ (fun y : n → ℝ => y ⬝ᵥ c) x :=
  Finset.analyticAt_fun_sum _ fun i _ =>
    (analyticAt_coord_urs i x).fun_mul analyticAt_const

/-- `x ↦ x X xᵀ` is analytic. -/
private lemma analyticAt_quad_urs {n : Type*} [Fintype n] (X : Matrix n n ℝ) (x : n → ℝ) :
    AnalyticAt ℝ (fun y : n → ℝ => (y ᵥ* X) ⬝ᵥ y) x :=
  Finset.analyticAt_fun_sum _ fun j _ =>
    (analyticAt_dot_urs (fun i => X i j) x).fun_mul
      (analyticAt_coord_urs j x)

/-- `x ↦ x xᵀ` is analytic. -/
private lemma analyticAt_dotSelf_urs {n : Type*} [Fintype n] (x : n → ℝ) :
    AnalyticAt ℝ (fun y : n → ℝ => y ⬝ᵥ y) x :=
  Finset.analyticAt_fun_sum _ fun j _ =>
    (analyticAt_coord_urs j x).fun_mul
      (analyticAt_coord_urs j x)

/-! ### The hyperplane of one unit -/

/-- A direction `v` with `v c_j = 0` and `v c_i ≠ 0` for `i ≠ j` (`exists_perp_dir` of
`UnitsReLU.lean`): a real vector space is not a finite union of proper subspaces. -/
private lemma exists_perp_dir_urs {n q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ)
    (hc : ∀ i, c i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) (j : q) :
    ∃ v : n → ℝ, v ⬝ᵥ c j = 0 ∧ ∀ i, i ≠ j → v ⬝ᵥ c i ≠ 0 := by
  have hjj : c j ⬝ᵥ c j ≠ 0 := dotProduct_self_eq_zero.not.2 (hc j)
  -- `r i`: the component of `c i` orthogonal to `c j`; it is nonzero for `i ≠ j`
  set r : q → n → ℝ := fun i => c i - ((c j ⬝ᵥ c i) / (c j ⬝ᵥ c j)) • c j with hr_def
  have hr : ∀ i, i ≠ j → r i ≠ 0 := fun i hi h0 =>
    hcol i j hi _ (sub_eq_zero.1 h0)
  -- the kernels of `ν ↦ ν r_i` are proper subspaces, so some `ν` avoids all of them
  let K : {i // i ≠ j} → Submodule ℝ (n → ℝ) := fun i =>
    { carrier := {ν | ν ⬝ᵥ r i = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢; rw [add_dotProduct, hx, hy, add_zero]
      zero_mem' := by simp
      smul_mem' := fun s x hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢; rw [smul_dotProduct, hx, smul_zero] }
  obtain ⟨ν, hν⟩ : ∃ ν : n → ℝ, ∀ i, i ≠ j → ν ⬝ᵥ r i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ (p := K) (by
      ext ν
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      obtain ⟨i, hij, h0⟩ := hcon ν
      exact ⟨⟨i, hij⟩, h0⟩)
    have hmem : r i ∈ K i := hi ▸ Submodule.mem_top
    exact hr i.1 i.2 (dotProduct_self_eq_zero.1 hmem)
  -- `v = ν - (ν c_j / c_j c_j) c_j` has `v c_j = 0` and `v c_i = ν r_i`
  refine ⟨ν - ((ν ⬝ᵥ c j) / (c j ⬝ᵥ c j)) • c j, ?_, fun i hi => ?_⟩
  · rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    field_simp
    ring
  · have : (ν - ((ν ⬝ᵥ c j) / (c j ⬝ᵥ c j)) • c j) ⬝ᵥ c i = ν ⬝ᵥ r i := by
      rw [hr_def]
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    rw [this]; exact hν i hi

open Filter Topology in
/-- Near a point where a continuous function is positive, it stays positive. -/
private lemma eventually_pos_urs {n : Type*} [Fintype n] {f : (n → ℝ) → ℝ} (hf : Continuous f)
    {z : n → ℝ} (hz : 0 < f z) : ∀ᶠ y in 𝓝 z, 0 < f y :=
  (hf.tendsto z).eventually (lt_mem_nhds hz)

/-! ### Step 1: one unit alone -/

open Filter Topology in
/-- **One unit alone.** Under (∗), every unit `i` satisfies, at every `x`,
`‖x‖² ((x c_i) β_i + k (x ψc_i) a_i) = k (x X xᵀ) (x c_i) a_i`. Unit `j` contributes
`(x c_j)^(k-1) P_j(x)` to (∗) on the side `x c_j > 0` and nothing on the side `x c_j < 0`, where
`P_j` is the difference of the two sides of the identity, a polynomial. Near a point `x₀` of the
hyperplane `x c_i = 0` on no other, the other units give one polynomial `Q`; it vanishes on the
side `x c_i < 0`, hence everywhere, and then `P_i` vanishes on the side `x c_i > 0`, hence
everywhere (the identity theorem for analytic functions). -/
private lemma unit_alone_urs {n m q : Type*} [Fintype n] [Fintype m] [Fintype q]
    {σ σ' : ℝ → ℝ} {k : ℕ} (hk : k ≠ 0)
    (hneg : ∀ u : ℝ, u < 0 → σ u = 0 ∧ σ' u = 0)
    (hpos : ∀ u : ℝ, 0 < u → σ u = u ^ k ∧ σ' u = k * u ^ (k - 1))
    {c : q → n → ℝ} {a : q → m → ℝ} {X : Matrix n n ℝ} {ψc : q → n → ℝ} {β : q → m → ℝ}
    (hc : ∀ i, c i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j)
    (h : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) →
      (x ⬝ᵥ x) • ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = ((k : ℝ) * ((x ᵥ* X) ⬝ᵥ x)) • ∑ i, σ (x ⬝ᵥ c i) • a i)
    (i : q) (x : n → ℝ) :
    (x ⬝ᵥ x) • ((x ⬝ᵥ c i) • β i + ((k : ℝ) * (x ⬝ᵥ ψc i)) • a i)
      = ((k : ℝ) * ((x ᵥ* X) ⬝ᵥ x) * (x ⬝ᵥ c i)) • a i := by
  classical
  -- `P_j`: the identity of unit `j` alone, as a difference
  obtain ⟨P, hP⟩ : ∃ P : q → (n → ℝ) → m → ℝ, ∀ j y, P j y = (y ⬝ᵥ y) • ((y ⬝ᵥ c j) • β j
      + ((k : ℝ) * (y ⬝ᵥ ψc j)) • a j) - ((k : ℝ) * ((y ᵥ* X) ⬝ᵥ y) * (y ⬝ᵥ c j)) • a j :=
    ⟨_, fun _ _ => rfl⟩
  -- `E_j`: the terms of unit `j` in (∗), as a difference
  obtain ⟨E, hE⟩ : ∃ E : q → (n → ℝ) → m → ℝ, ∀ j y, E j y = (y ⬝ᵥ y) • (σ (y ⬝ᵥ c j) • β j
      + (σ' (y ⬝ᵥ c j) * (y ⬝ᵥ ψc j)) • a j)
      - ((k : ℝ) * ((y ᵥ* X) ⬝ᵥ y)) • (σ (y ⬝ᵥ c j) • a j) :=
    ⟨_, fun _ _ => rfl⟩
  have hsum : ∀ y, (∀ j, y ⬝ᵥ c j ≠ 0) → ∑ j, E j y = 0 := fun y hy => by
    simp only [hE, Finset.sum_sub_distrib, ← Finset.smul_sum]
    rw [h y hy, sub_self]
  -- on the side `y c_j > 0`: `E_j = (y c_j)^(k-1) P_j`; on the side `y c_j < 0`: `E_j = 0`
  have hEpos : ∀ j y, 0 < y ⬝ᵥ c j → E j y = (y ⬝ᵥ c j) ^ (k - 1) • P j y := fun j y hy => by
    obtain ⟨h1, h2⟩ := hpos _ hy
    rw [hE, hP, h1, h2, ← pow_sub_one_mul hk]
    ext o
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hEneg : ∀ j y, y ⬝ᵥ c j < 0 → E j y = 0 := fun j y hy => by
    obtain ⟨h1, h2⟩ := hneg _ hy
    rw [hE, h1, h2]
    simp only [zero_smul, zero_mul, add_zero, smul_zero, sub_zero]
  -- analyticity
  have hPan : ∀ j x, AnalyticAt ℝ (P j) x := fun j x => by
    have e : P j = fun y => (y ⬝ᵥ y) • ((y ⬝ᵥ c j) • β j + ((k : ℝ) * (y ⬝ᵥ ψc j)) • a j)
        - ((k : ℝ) * ((y ᵥ* X) ⬝ᵥ y) * (y ⬝ᵥ c j)) • a j := funext (hP j)
    have h1 := analyticAt_dot_urs (c j) x
    have h2 := analyticAt_dot_urs (ψc j) x
    have h3 := analyticAt_quad_urs X x
    have h4 := analyticAt_dotSelf_urs x
    rw [e]
    fun_prop
  -- a point `x₀` of the hyperplane `x c_i = 0` on no other
  obtain ⟨x₀, hx₀i, hx₀j⟩ := exists_perp_dir_urs c hc hcol i
  -- `Q`: the units `j ≠ i` active at `x₀`
  obtain ⟨Q, hQ⟩ : ∃ Q : (n → ℝ) → m → ℝ, ∀ y, Q y = ∑ j ∈ (Finset.univ.erase i).filter
      (fun j => 0 < x₀ ⬝ᵥ c j), (y ⬝ᵥ c j) ^ (k - 1) • P j y := ⟨_, fun _ => rfl⟩
  have hQan : ∀ x, AnalyticAt ℝ Q x := fun x => by
    rw [funext hQ]
    exact Finset.analyticAt_fun_sum _ fun j _ =>
      ((analyticAt_dot_urs (c j) x).fun_pow (k - 1)).fun_smul (hPan j x)
  -- where the units `j ≠ i` have the signs they have at `x₀`, (∗) reads `E_i + Q = 0`
  have hsplit : ∀ y, (∀ j, j ≠ i → 0 < (y ⬝ᵥ c j) * (x₀ ⬝ᵥ c j)) →
      ∑ j, E j y = E i y + Q y := by
    intro y hy
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hQ, Finset.sum_filter]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    split_ifs with hj0
    · exact hEpos j y ((pos_iff_pos_of_mul_pos (hy j hji)).2 hj0)
    · exact hEneg j y ((neg_iff_neg_of_mul_pos (hy j hji)).2
        (lt_of_le_of_ne (not_lt.1 hj0) (hx₀j j hji)))
  -- such a region near a point `z`
  have hcont : ∀ v : n → ℝ, Continuous fun y : n → ℝ => y ⬝ᵥ v := fun v => by fun_prop
  have hreg : ∀ (s : ℝ) (z : n → ℝ), 0 < s * (z ⬝ᵥ c i) →
      (∀ j, j ≠ i → 0 < (z ⬝ᵥ c j) * (x₀ ⬝ᵥ c j)) →
      ∀ᶠ y in 𝓝 z, 0 < s * (y ⬝ᵥ c i) ∧ ∀ j, j ≠ i → 0 < (y ⬝ᵥ c j) * (x₀ ⬝ᵥ c j) :=
    fun s z hzi hzj => (eventually_pos_urs (continuous_const.mul (hcont (c i))) hzi).and
      (Filter.eventually_all.2 fun j => Filter.eventually_imp_distrib_left.2 fun hji =>
        eventually_pos_urs ((hcont (c j)).mul continuous_const) (hzj j hji))
  have hoff : ∀ (s : ℝ) (y : n → ℝ), 0 < s * (y ⬝ᵥ c i) →
      (∀ j, j ≠ i → 0 < (y ⬝ᵥ c j) * (x₀ ⬝ᵥ c j)) → ∀ j, y ⬝ᵥ c j ≠ 0 := by
    intro s y hyi hyj j
    by_cases hji : j = i
    · rw [hji]; exact right_ne_zero_of_mul hyi.ne'
    · exact left_ne_zero_of_mul (hyj j hji).ne'
  -- the points `z± = x₀ ± t c_i`, for a small `t > 0`
  have hev : ∀ᶠ y in 𝓝 x₀, ∀ j, j ≠ i → 0 < (y ⬝ᵥ c j) * (x₀ ⬝ᵥ c j) :=
    Filter.eventually_all.2 fun j => Filter.eventually_imp_distrib_left.2 fun hji =>
      eventually_pos_urs ((hcont (c j)).mul continuous_const) (mul_self_pos.2 (hx₀j j hji))
  have hline : ∀ s : ℝ, Tendsto (fun t : ℝ => x₀ + (s * t) • c i) (𝓝 0) (𝓝 x₀) := fun s => by
    have hcont' : Continuous (fun t : ℝ => x₀ + (s * t) • c i) := by fun_prop
    simpa using hcont'.tendsto 0
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ := ((((hline 1).eventually hev).and
    ((hline (-1)).eventually hev)).filter_mono nhdsWithin_le_nhds |>.and
      (eventually_mem_nhdsWithin (s := Set.Ioi 0))).exists
  have ht0 : 0 < t := ht
  have hii : 0 < c i ⬝ᵥ c i :=
    lt_of_le_of_ne (Finset.sum_nonneg fun o _ => mul_self_nonneg (c i o))
      (Ne.symm (dotProduct_self_eq_zero.not.2 (hc i)))
  have hzi : ∀ s : ℝ, s * ((x₀ + (s * t) • c i) ⬝ᵥ c i) = s ^ 2 * (t * (c i ⬝ᵥ c i)) :=
    fun s => by
      rw [add_dotProduct, smul_dotProduct, smul_eq_mul, hx₀i]
      ring
  have hpz : ∀ s : ℝ, s ≠ 0 → 0 < s * ((x₀ + (s * t) • c i) ⬝ᵥ c i) := fun s hs => by
    rw [hzi]; exact mul_pos (sq_pos_iff.2 hs) (mul_pos ht0 hii)
  -- on the side `y c_i < 0` near `z₋`, (∗) reads `Q = 0`; so `Q = 0` everywhere
  have hQ0 : ∀ y, Q y = 0 := by
    refine eq_zero_of_eventually_urs hQan (z := x₀ + (-1 * t) • c i) ?_
    filter_upwards [hreg (-1) _ (hpz (-1) (by norm_num)) h2] with y hy
    have hyi : y ⬝ᵥ c i < 0 := by linarith [hy.1]
    have e := hsum y (hoff (-1) y hy.1 hy.2)
    rwa [hsplit y hy.2, hEneg i y hyi, zero_add] at e
  -- on the side `y c_i > 0` near `z₊`, (∗) reads `(y c_i)^(k-1) P_i = 0`; so `P_i = 0`
  have hP0 : ∀ y, P i y = 0 := by
    refine eq_zero_of_eventually_urs (hPan i) (z := x₀ + (1 * t) • c i) ?_
    filter_upwards [hreg 1 _ (hpz 1 one_ne_zero) h1] with y hy
    have hyi : 0 < y ⬝ᵥ c i := by linarith [hy.1]
    have e := hsum y (hoff 1 y hy.1 hy.2)
    rw [hsplit y hy.2, hEpos i y hyi, hQ0 y, add_zero] at e
    exact (smul_eq_zero.1 e).resolve_left (pow_ne_zero _ hyi.ne')
  have e := hP0 x
  rwa [hP, sub_eq_zero] at e

/-! ### Step 2: the coefficients of one unit -/

/-- A vector is determined by its dot products with all `x`. -/
private lemma eq_smul_of_dot_urs {n : Type*} [Fintype n] {v w : n → ℝ} {l : ℝ}
    (h : ∀ x : n → ℝ, x ⬝ᵥ v = l * (x ⬝ᵥ w)) : v = l • w := by
  classical
  funext o
  have e := h (Pi.single o 1)
  simp only [single_one_dotProduct] at e
  simp only [Pi.smul_apply, smul_eq_mul]
  exact e

/-- **The coefficients of one unit.** If `‖x‖² ((x c) b + k (x ψ) a) = k (x X xᵀ) (x c) a` for
every `x`, with `a ≠ 0` and `c ≠ 0`, then `ψ = λ c`, `x X xᵀ = μ ‖x‖²` for every `x`, and
`b = k (μ − λ) a`. At an output `o` with `a_o ≠ 0`: on the hyperplane `x c = 0` the identity
gives `x ψ = 0`, so `ψ = λ c`; off it, dividing by `x c` gives `x X xᵀ = μ ‖x‖²`, and on it too
(compare `x ± c`); then `x = c` gives `b`. -/
private lemma unit_coeffs_urs {n m : Type*} [Fintype n] [Fintype m] {k : ℕ} (hk : k ≠ 0)
    {c ψ : n → ℝ} {a b : m → ℝ} {X : Matrix n n ℝ} (ha : a ≠ 0) (hc : c ≠ 0)
    (h : ∀ x : n → ℝ, (x ⬝ᵥ x) • ((x ⬝ᵥ c) • b + ((k : ℝ) * (x ⬝ᵥ ψ)) • a)
      = ((k : ℝ) * ((x ᵥ* X) ⬝ᵥ x) * (x ⬝ᵥ c)) • a) :
    ∃ lam μ : ℝ, ψ = lam • c ∧ (∀ x : n → ℝ, (x ᵥ* X) ⬝ᵥ x = μ * (x ⬝ᵥ x)) ∧
      b = ((k : ℝ) * (μ - lam)) • a := by
  obtain ⟨o, ho⟩ := Function.ne_iff.1 ha
  rw [Pi.zero_apply] at ho
  have hκ : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  have hcc : c ⬝ᵥ c ≠ 0 := dotProduct_self_eq_zero.not.2 hc
  have hcomp : ∀ (x : n → ℝ) (o' : m), (x ⬝ᵥ x) * ((x ⬝ᵥ c) * b o' + (k : ℝ) * (x ⬝ᵥ ψ) * a o')
      = (k : ℝ) * ((x ᵥ* X) ⬝ᵥ x) * (x ⬝ᵥ c) * a o' := fun x o' => by
    have e := congrFun (h x) o'
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at e
    linear_combination e
  -- on the hyperplane `x c = 0`: `‖x‖² k (x ψ) a_o = 0`, so `x ψ = 0`
  have hψ0 : ∀ x : n → ℝ, x ⬝ᵥ c = 0 → x ⬝ᵥ ψ = 0 := fun x hx => by
    by_cases hx0 : x = 0
    · rw [hx0, zero_dotProduct]
    have hxx : x ⬝ᵥ x ≠ 0 := dotProduct_self_eq_zero.not.2 hx0
    have e := hcomp x o
    rw [hx] at e
    have key : (x ⬝ᵥ x) * (k : ℝ) * a o * (x ⬝ᵥ ψ) = 0 := by linear_combination e
    exact (mul_eq_zero.1 key).resolve_left (mul_ne_zero (mul_ne_zero hxx hκ) ho)
  -- so `ψ = λ c`
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = (c ⬝ᵥ ψ) / (c ⬝ᵥ c) := ⟨_, rfl⟩
  have hlin : ∀ x : n → ℝ, x ⬝ᵥ ψ = lam * (x ⬝ᵥ c) := fun x => by
    have hw := hψ0 (x - ((x ⬝ᵥ c) / (c ⬝ᵥ c)) • c) (by
      rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, div_mul_cancel₀ _ hcc, sub_self])
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, sub_eq_zero] at hw
    rw [hw, hlam]
    ring
  have hψ : ψ = lam • c := eq_smul_of_dot_urs hlin
  -- off the hyperplane: `x X xᵀ = μ ‖x‖²` with `μ k a_o = b_o + k λ a_o`
  have hkao : (k : ℝ) * a o ≠ 0 := mul_ne_zero hκ ho
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ * ((k : ℝ) * a o) = b o + (k : ℝ) * lam * a o :=
    ⟨(b o + (k : ℝ) * lam * a o) / ((k : ℝ) * a o), div_mul_cancel₀ _ hkao⟩
  have hq' : ∀ x : n → ℝ, x ⬝ᵥ c ≠ 0 → (x ᵥ* X) ⬝ᵥ x = μ * (x ⬝ᵥ x) := fun x hx => by
    have e := hcomp x o
    rw [hlin x] at e
    have key : (x ⬝ᵥ c) * ((k : ℝ) * a o) * ((x ᵥ* X) ⬝ᵥ x - μ * (x ⬝ᵥ x)) = 0 := by
      linear_combination -e - (x ⬝ᵥ c) * (x ⬝ᵥ x) * hμ
    exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left (mul_ne_zero hx hkao))
  -- on the hyperplane too: `x + c` and `x - c` lie off it
  have hq : ∀ x : n → ℝ, (x ᵥ* X) ⬝ᵥ x = μ * (x ⬝ᵥ x) := fun x => by
    by_cases hx : x ⬝ᵥ c = 0
    · have e0 := hq' c hcc
      have e1 := hq' (x + c) (by rw [add_dotProduct, hx, zero_add]; exact hcc)
      have e2 := hq' (x - c) (by rw [sub_dotProduct, hx, zero_sub]; exact neg_ne_zero.2 hcc)
      simp only [add_vecMul, sub_vecMul, add_dotProduct, dotProduct_add, sub_dotProduct,
        dotProduct_sub] at e1 e2
      linear_combination (e1 + e2) / 2 - e0
    · exact hq' x hx
  refine ⟨lam, μ, hψ, hq, funext fun o' => ?_⟩
  -- every output at `x = c`: `(c c)² (b_o' − k (μ − λ) a_o') = 0`
  have e := hcomp c o'
  rw [hlin c, hq c] at e
  have key : (c ⬝ᵥ c) ^ 2 * (b o' - (k : ℝ) * (μ - lam) * a o') = 0 := by linear_combination e
  have := (mul_eq_zero.1 key).resolve_left (pow_ne_zero 2 hcc)
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith

/-- A symmetric matrix whose quadratic form is `μ ‖x‖²` is `μ I` (at `e_p` and `e_p + e_r`). -/
private lemma eq_smul_one_of_quad_urs {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℝ} (hX : Xᵀ = X) {μ : ℝ}
    (hq : ∀ x : n → ℝ, (x ᵥ* X) ⬝ᵥ x = μ * (x ⬝ᵥ x)) : X = μ • (1 : Matrix n n ℝ) := by
  have hpp : ∀ p, X p p = μ := fun p => by
    have e := hq (Pi.single p 1)
    simpa only [single_vecMul, one_smul, dotProduct_single, row_apply, mul_one,
      Pi.single_eq_same] using e
  ext p r
  by_cases hpr : p = r
  · subst hpr
    simp only [hpp, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
  · have hsym : X r p = X p r := by
      have e := congrFun (congrFun hX p) r
      rwa [transpose_apply] at e
    have e := hq (Pi.single p 1 + Pi.single r 1)
    simp only [add_vecMul, single_vecMul, one_smul, dotProduct_add, dotProduct_single,
      Pi.add_apply, row_apply, hpp, hsym, mul_one, Pi.single_eq_same, ne_eq, hpr,
      not_false_eq_true, Pi.single_eq_of_ne, add_zero, Ne.symm hpr, zero_add] at e
    simp only [Matrix.smul_apply, ne_eq, hpr, not_false_eq_true, one_apply_ne, smul_eq_mul,
      mul_zero]
    linarith

/-! ### The two activations -/

/-- **The symmetric part is a scaling, for an activation `σ` that vanishes with `σ'` on the
negative numbers and is `u ↦ u^k` with derivative `k u^(k-1)` on the positive numbers**
(`k ≠ 0`): every unit satisfies (∗) alone (step 1), which gives its coefficients and the
quadratic form `μ_i ‖x‖²` of `X` (step 2); all `μ_i` are equal, and `X = μ I`. -/
private lemma unitsRescaleSphere_urs {σ σ' : ℝ → ℝ} {k : ℕ} (hk : k ≠ 0)
    (hneg : ∀ u : ℝ, u < 0 → σ u = 0 ∧ σ' u = 0)
    (hpos : ∀ u : ℝ, 0 < u → σ u = u ^ k ∧ σ' u = k * u ^ (k - 1))
    (n m q : Type*) [Fintype n] [DecidableEq n] [Fintype m] [Fintype q] [Nonempty q] :
    UnitsRescaleSphere σ σ' k n m q := by
  intro c a X ψc β ha hc hcol hX h
  obtain ⟨i₀⟩ := ‹Nonempty q›
  -- steps 1 and 2 for every unit
  choose lam μ hψ hq hβ using fun i =>
    unit_coeffs_urs hk (ha i) (hc i) (unit_alone_urs hk hneg hpos hc hcol h i)
  -- the quadratic form of `X` is `μ_i ‖x‖²` for every `i`, so all `μ_i` are `μ_{i₀}`
  have hμ : ∀ i, μ i = μ i₀ := fun i =>
    mul_right_cancel₀ (dotProduct_self_eq_zero.not.2 (hc i))
      ((hq i (c i)).symm.trans (hq i₀ (c i)))
  refine ⟨μ i₀, lam, eq_smul_one_of_quad_urs hX (hq i₀), fun i => ⟨hψ i, ?_⟩⟩
  rw [hβ i, hμ i]

/-- **The symmetric part is a scaling, for ReLU units** (`k = 1`; at least one unit). -/
theorem relu_unitsRescaleSphere (n m q : Type*) [Fintype n] [DecidableEq n] [Fintype m]
    [Fintype q] [Nonempty q] : UnitsRescaleSphere relu reluDeriv 1 n m q := by
  -- on `u < 0`: `relu u = reluDeriv u = 0`; on `u > 0`: `relu u = u`, `reluDeriv u = 1`
  exact unitsRescaleSphere_urs (σ := relu) (σ' := reluDeriv) one_ne_zero
    (fun u hu => ⟨max_eq_right hu.le, by simp only [reluDeriv, not_lt.2 hu.le, ite_false]⟩)
    (fun u hu => ⟨by simp only [relu, max_eq_left hu.le, pow_one],
      by simp only [reluDeriv, hu, ite_true, Nat.cast_one, Nat.sub_self, pow_zero, mul_one]⟩)
    n m q

/-- **The symmetric part is a scaling, for ReLU² units** (`k = 2`; at least one unit). -/
theorem reluSq_unitsRescaleSphere (n m q : Type*) [Fintype n] [DecidableEq n] [Fintype m]
    [Fintype q] [Nonempty q] : UnitsRescaleSphere reluSq reluSqDeriv 2 n m q := by
  -- on `u < 0`: `reluSq u = reluSqDeriv u = 0`; on `u > 0`: `reluSq u = u²`, derivative `2 u`
  exact unitsRescaleSphere_urs (σ := reluSq) (σ' := reluSqDeriv) two_ne_zero
    (fun u hu => ⟨by rw [reluSq, max_eq_right hu.le]; norm_num,
      by rw [reluSqDeriv, max_eq_right hu.le, mul_zero]⟩)
    (fun u hu => ⟨by rw [reluSq, max_eq_left hu.le],
      by rw [reluSqDeriv, max_eq_left hu.le]; norm_num⟩)
    n m q

end Skips
