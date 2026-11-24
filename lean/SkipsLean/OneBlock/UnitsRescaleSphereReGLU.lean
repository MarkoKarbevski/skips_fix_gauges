import SkipsLean.OneBlock.UnitsRescaleSphere
import SkipsLean.OneBlock.UnitsReGLU

/-!
# ReGLU units and a symmetric change of the input: only a scaling and rescalings

Paper (skips paper), proof of Theorem B.1 (iii), "The case `ε = 0`": "For ReLU, ReLU² and ReGLU,
both sides of (17) are positively homogeneous, of degrees `k` and `k + 2`, so
`‖n‖² ∂_ψ B(n) = k d_model q(n) B(n)` for all `n ≠ 0`. On each region where no `n c_k` changes
sign, both sides are polynomials in `n`. Across the hyperplane `n c_i = 0`, at a point of no
other such hyperplane, only the terms of unit `i` change, so they satisfy the identity on their
own: `‖n‖²` times a polynomial equals `k d_model q(n)` times `(n c_i) a_i`, `(n c_i)² a_i` or
`(n c_i)(n e_i) a_i`. Since `‖n‖²` has no real linear factor, it divides `q(n)`, so `X_0` is a
multiple of `I`, and `X_0 = 0` because its trace vanishes. Then Step 5 gives equality."

`OneBlock/UnitsRescaleSphere.lean` has this step for ReLU and ReLU² units. Here the same for
ReGLU units `σ(x g_i) (x v_i) a_i` with `σ = ReLU` (the paper's `c_i` is the gate column `g_i`,
its `e_i` the value column `v_i`; the block has degree `k = 2`), together with Lemma B.3 for
ReGLU (`relu_gated_units_flat`, `OneBlock/UnitsReGLU.lean`), as one statement on vectors with no
network in it: `B(x) = ∑_i σ(x g_i)(x v_i) a_i`,

`∂_ψ B(x) = ∑_i [σ(x g_i)(x v_i) β_i + σ'(x g_i)(x ψg_i)(x v_i) a_i + σ(x g_i)(x ψv_i) a_i]`,

and `k d_model q(x) = 2 (x X xᵀ)`. If `‖x‖² ∂_ψ B(x) = 2 (x X xᵀ) B(x)` at every `x` with no gate
at its kink, for a symmetric `X`, then `X = c₀ I` and the direction is a rescaling of the gates
and of the values shifted by `c₀`: `ψg_i = λ_i g_i`, `ψv_i = μ_i v_i`,
`β_i = (2 c₀ − λ_i − μ_i) a_i`. The hypotheses are those of Lemma B.3 for ReGLU (no value column
is proportional to the gate column of its unit, which also makes it nonzero) and at least one
unit. Exact check of the dimension `2 q + 1` of the solutions:
`gated_units_rescale_sphere_check_2026-11-24.py`.
-/

namespace Skips

open Matrix

/-! ### Analytic functions of the input -/

open Filter Topology in
/-- The identity theorem on `n → ℝ`: an analytic function that vanishes near a point vanishes
everywhere. -/
private lemma eq_zero_of_eventually_urg {n F : Type*} [Fintype n] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : (n → ℝ) → F} (hf : ∀ x, AnalyticAt ℝ f x) {z : n → ℝ}
    (hz : ∀ᶠ x in 𝓝 z, f x = 0) (y : n → ℝ) : f y = 0 :=
  congrFun (AnalyticOnNhd.eq_of_eventuallyEq (g := fun _ => 0) (fun x _ => hf x)
    (fun _ _ => analyticAt_const) hz) y

/-- A coordinate `x ↦ x_i` is analytic. -/
private lemma analyticAt_coord_urg {n : Type*} [Fintype n] (i : n) (x : n → ℝ) :
    AnalyticAt ℝ (fun y : n → ℝ => y i) x :=
  (analyticAt_pi_iff (f := fun j (y : n → ℝ) => y j) (e := x)).1 analyticAt_id i

/-- `x ↦ x c` is analytic. -/
private lemma analyticAt_dot_urg {n : Type*} [Fintype n] (c : n → ℝ) (x : n → ℝ) :
    AnalyticAt ℝ (fun y : n → ℝ => y ⬝ᵥ c) x :=
  Finset.analyticAt_fun_sum _ fun i _ =>
    (analyticAt_coord_urg i x).fun_mul analyticAt_const

/-- `x ↦ x X xᵀ` is analytic. -/
private lemma analyticAt_quad_urg {n : Type*} [Fintype n] (X : Matrix n n ℝ) (x : n → ℝ) :
    AnalyticAt ℝ (fun y : n → ℝ => (y ᵥ* X) ⬝ᵥ y) x :=
  Finset.analyticAt_fun_sum _ fun j _ =>
    (analyticAt_dot_urg (fun i => X i j) x).fun_mul
      (analyticAt_coord_urg j x)

/-- `x ↦ x xᵀ` is analytic. -/
private lemma analyticAt_dotSelf_urg {n : Type*} [Fintype n] (x : n → ℝ) :
    AnalyticAt ℝ (fun y : n → ℝ => y ⬝ᵥ y) x :=
  Finset.analyticAt_fun_sum _ fun j _ =>
    (analyticAt_coord_urg j x).fun_mul
      (analyticAt_coord_urg j x)

/-! ### The hyperplane of one gate -/

/-- A direction `v` with `v c_j = 0` and `v c_i ≠ 0` for `i ≠ j` (`exists_perp_dir` of
`UnitsReLU.lean`): a real vector space is not a finite union of proper subspaces. -/
private lemma exists_perp_dir_urg {n q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ)
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
private lemma eventually_pos_urg {n : Type*} [Fintype n] {f : (n → ℝ) → ℝ} (hf : Continuous f)
    {z : n → ℝ} (hz : 0 < f z) : ∀ᶠ y in 𝓝 z, 0 < f y :=
  (hf.tendsto z).eventually (lt_mem_nhds hz)

/-! ### Step 1: one unit alone -/

open Filter Topology in
/-- **One unit alone.** Under (∗), every unit `i` satisfies, at every `x`,
`‖x‖² ((x g_i)(x v_i) β_i + (x ψg_i)(x v_i) a_i + (x g_i)(x ψv_i) a_i)
  = 2 (x X xᵀ) (x g_i)(x v_i) a_i`.
Unit `j` contributes `P_j(x)` to (∗) on the side `x g_j > 0` and nothing on the side
`x g_j < 0`, where `P_j` is the difference of the two sides of the identity, a polynomial. Near a
point `x₀` of the hyperplane `x g_i = 0` on no other, the other units give one polynomial `Q`; it
vanishes on the side `x g_i < 0`, hence everywhere, and then `P_i` vanishes on the side
`x g_i > 0`, hence everywhere (the identity theorem for analytic functions). -/
private lemma unit_alone_urg {n m q : Type*} [Fintype n] [Fintype m] [Fintype q]
    {g v : q → n → ℝ} {a : q → m → ℝ} {X : Matrix n n ℝ} {ψg ψv : q → n → ℝ}
    {β : q → m → ℝ} (hg : ∀ i, g i ≠ 0) (hgg : ∀ i j, i ≠ j → ∀ r : ℝ, g i ≠ r • g j)
    (h : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ g i ≠ 0) →
      (x ⬝ᵥ x) • ∑ i, ((relu (x ⬝ᵥ g i) * (x ⬝ᵥ v i)) • β i
          + (reluDeriv (x ⬝ᵥ g i) * (x ⬝ᵥ ψg i) * (x ⬝ᵥ v i)) • a i
          + (relu (x ⬝ᵥ g i) * (x ⬝ᵥ ψv i)) • a i)
        = (2 * ((x ᵥ* X) ⬝ᵥ x)) • ∑ i, (relu (x ⬝ᵥ g i) * (x ⬝ᵥ v i)) • a i)
    (i : q) (x : n → ℝ) :
    (x ⬝ᵥ x) • (((x ⬝ᵥ g i) * (x ⬝ᵥ v i)) • β i + ((x ⬝ᵥ ψg i) * (x ⬝ᵥ v i)) • a i
      + ((x ⬝ᵥ g i) * (x ⬝ᵥ ψv i)) • a i)
      = (2 * ((x ᵥ* X) ⬝ᵥ x) * (x ⬝ᵥ g i) * (x ⬝ᵥ v i)) • a i := by
  classical
  -- `P_j`: the identity of unit `j` alone, as a difference
  obtain ⟨P, hP⟩ : ∃ P : q → (n → ℝ) → m → ℝ, ∀ j y, P j y = (y ⬝ᵥ y) •
      (((y ⬝ᵥ g j) * (y ⬝ᵥ v j)) • β j + ((y ⬝ᵥ ψg j) * (y ⬝ᵥ v j)) • a j
        + ((y ⬝ᵥ g j) * (y ⬝ᵥ ψv j)) • a j)
      - (2 * ((y ᵥ* X) ⬝ᵥ y) * (y ⬝ᵥ g j) * (y ⬝ᵥ v j)) • a j :=
    ⟨_, fun _ _ => rfl⟩
  -- `E_j`: the terms of unit `j` in (∗), as a difference
  obtain ⟨E, hE⟩ : ∃ E : q → (n → ℝ) → m → ℝ, ∀ j y, E j y = (y ⬝ᵥ y) •
      ((relu (y ⬝ᵥ g j) * (y ⬝ᵥ v j)) • β j
        + (reluDeriv (y ⬝ᵥ g j) * (y ⬝ᵥ ψg j) * (y ⬝ᵥ v j)) • a j
        + (relu (y ⬝ᵥ g j) * (y ⬝ᵥ ψv j)) • a j)
      - (2 * ((y ᵥ* X) ⬝ᵥ y)) • ((relu (y ⬝ᵥ g j) * (y ⬝ᵥ v j)) • a j) :=
    ⟨_, fun _ _ => rfl⟩
  have hsum : ∀ y, (∀ j, y ⬝ᵥ g j ≠ 0) → ∑ j, E j y = 0 := fun y hy => by
    simp only [hE, Finset.sum_sub_distrib, ← Finset.smul_sum]
    rw [h y hy, sub_self]
  -- on the side `y g_j > 0`: `E_j = P_j`; on the side `y g_j < 0`: `E_j = 0`
  have hEpos : ∀ j y, 0 < y ⬝ᵥ g j → E j y = P j y := fun j y hy => by
    have h1 : relu (y ⬝ᵥ g j) = y ⬝ᵥ g j := max_eq_left hy.le
    have h2 : reluDeriv (y ⬝ᵥ g j) = 1 := by simp only [reluDeriv, hy, ite_true]
    rw [hE, hP, h1, h2]
    ext o
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hEneg : ∀ j y, y ⬝ᵥ g j < 0 → E j y = 0 := fun j y hy => by
    have h1 : relu (y ⬝ᵥ g j) = 0 := max_eq_right hy.le
    have h2 : reluDeriv (y ⬝ᵥ g j) = 0 := by simp only [reluDeriv, not_lt.2 hy.le, ite_false]
    rw [hE, h1, h2]
    simp only [zero_mul, zero_smul, add_zero, smul_zero, sub_zero]
  -- analyticity
  have hPan : ∀ j x, AnalyticAt ℝ (P j) x := fun j x => by
    have e : P j = fun y => (y ⬝ᵥ y) •
        (((y ⬝ᵥ g j) * (y ⬝ᵥ v j)) • β j + ((y ⬝ᵥ ψg j) * (y ⬝ᵥ v j)) • a j
          + ((y ⬝ᵥ g j) * (y ⬝ᵥ ψv j)) • a j)
        - (2 * ((y ᵥ* X) ⬝ᵥ y) * (y ⬝ᵥ g j) * (y ⬝ᵥ v j)) • a j := funext (hP j)
    have h1 := analyticAt_dot_urg (g j) x
    have h2 := analyticAt_dot_urg (v j) x
    have h3 := analyticAt_dot_urg (ψg j) x
    have h4 := analyticAt_dot_urg (ψv j) x
    have h5 := analyticAt_quad_urg X x
    have h6 := analyticAt_dotSelf_urg x
    rw [e]
    fun_prop
  -- a point `x₀` of the hyperplane `x g_i = 0` on no other
  obtain ⟨x₀, hx₀i, hx₀j⟩ := exists_perp_dir_urg g hg hgg i
  -- `Q`: the units `j ≠ i` active at `x₀`
  obtain ⟨Q, hQ⟩ : ∃ Q : (n → ℝ) → m → ℝ, ∀ y, Q y = ∑ j ∈ (Finset.univ.erase i).filter
      (fun j => 0 < x₀ ⬝ᵥ g j), P j y := ⟨_, fun _ => rfl⟩
  have hQan : ∀ x, AnalyticAt ℝ Q x := fun x => by
    rw [funext hQ]
    exact Finset.analyticAt_fun_sum _ fun j _ => hPan j x
  -- where the units `j ≠ i` have the signs they have at `x₀`, (∗) reads `E_i + Q = 0`
  have hsplit : ∀ y, (∀ j, j ≠ i → 0 < (y ⬝ᵥ g j) * (x₀ ⬝ᵥ g j)) →
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
  have hreg : ∀ (s : ℝ) (z : n → ℝ), 0 < s * (z ⬝ᵥ g i) →
      (∀ j, j ≠ i → 0 < (z ⬝ᵥ g j) * (x₀ ⬝ᵥ g j)) →
      ∀ᶠ y in 𝓝 z, 0 < s * (y ⬝ᵥ g i) ∧ ∀ j, j ≠ i → 0 < (y ⬝ᵥ g j) * (x₀ ⬝ᵥ g j) :=
    fun s z hzi hzj => (eventually_pos_urg (continuous_const.mul (hcont (g i))) hzi).and
      (Filter.eventually_all.2 fun j => Filter.eventually_imp_distrib_left.2 fun hji =>
        eventually_pos_urg ((hcont (g j)).mul continuous_const) (hzj j hji))
  have hoff : ∀ (s : ℝ) (y : n → ℝ), 0 < s * (y ⬝ᵥ g i) →
      (∀ j, j ≠ i → 0 < (y ⬝ᵥ g j) * (x₀ ⬝ᵥ g j)) → ∀ j, y ⬝ᵥ g j ≠ 0 := by
    intro s y hyi hyj j
    by_cases hji : j = i
    · rw [hji]; exact right_ne_zero_of_mul hyi.ne'
    · exact left_ne_zero_of_mul (hyj j hji).ne'
  -- the points `z± = x₀ ± t g_i`, for a small `t > 0`
  have hev : ∀ᶠ y in 𝓝 x₀, ∀ j, j ≠ i → 0 < (y ⬝ᵥ g j) * (x₀ ⬝ᵥ g j) :=
    Filter.eventually_all.2 fun j => Filter.eventually_imp_distrib_left.2 fun hji =>
      eventually_pos_urg ((hcont (g j)).mul continuous_const) (mul_self_pos.2 (hx₀j j hji))
  have hline : ∀ s : ℝ, Tendsto (fun t : ℝ => x₀ + (s * t) • g i) (𝓝 0) (𝓝 x₀) := fun s => by
    have hcont' : Continuous (fun t : ℝ => x₀ + (s * t) • g i) := by fun_prop
    simpa using hcont'.tendsto 0
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ := ((((hline 1).eventually hev).and
    ((hline (-1)).eventually hev)).filter_mono nhdsWithin_le_nhds |>.and
      (eventually_mem_nhdsWithin (s := Set.Ioi 0))).exists
  have ht0 : 0 < t := ht
  have hii : 0 < g i ⬝ᵥ g i :=
    lt_of_le_of_ne (Finset.sum_nonneg fun o _ => mul_self_nonneg (g i o))
      (Ne.symm (dotProduct_self_eq_zero.not.2 (hg i)))
  have hzi : ∀ s : ℝ, s * ((x₀ + (s * t) • g i) ⬝ᵥ g i) = s ^ 2 * (t * (g i ⬝ᵥ g i)) :=
    fun s => by
      rw [add_dotProduct, smul_dotProduct, smul_eq_mul, hx₀i]
      ring
  have hpz : ∀ s : ℝ, s ≠ 0 → 0 < s * ((x₀ + (s * t) • g i) ⬝ᵥ g i) := fun s hs => by
    rw [hzi]; exact mul_pos (sq_pos_iff.2 hs) (mul_pos ht0 hii)
  -- on the side `y g_i < 0` near `z₋`, (∗) reads `Q = 0`; so `Q = 0` everywhere
  have hQ0 : ∀ y, Q y = 0 := by
    refine eq_zero_of_eventually_urg hQan (z := x₀ + (-1 * t) • g i) ?_
    filter_upwards [hreg (-1) _ (hpz (-1) (by norm_num)) h2] with y hy
    have hyi : y ⬝ᵥ g i < 0 := by linarith [hy.1]
    have e := hsum y (hoff (-1) y hy.1 hy.2)
    rwa [hsplit y hy.2, hEneg i y hyi, zero_add] at e
  -- on the side `y g_i > 0` near `z₊`, (∗) reads `P_i = 0`; so `P_i = 0` everywhere
  have hP0 : ∀ y, P i y = 0 := by
    refine eq_zero_of_eventually_urg (hPan i) (z := x₀ + (1 * t) • g i) ?_
    filter_upwards [hreg 1 _ (hpz 1 one_ne_zero) h1] with y hy
    have hyi : 0 < y ⬝ᵥ g i := by linarith [hy.1]
    have e := hsum y (hoff 1 y hy.1 hy.2)
    rwa [hsplit y hy.2, hEpos i y hyi, hQ0 y, add_zero] at e
  have e := hP0 x
  rwa [hP, sub_eq_zero] at e

/-! ### Step 2: the coefficients of one unit -/

/-- A vector is determined by its dot products with all `x`. -/
private lemma eq_smul_of_dot_urg {n : Type*} [Fintype n] {v w : n → ℝ} {l : ℝ}
    (h : ∀ x : n → ℝ, x ⬝ᵥ v = l * (x ⬝ᵥ w)) : v = l • w := by
  classical
  funext o
  have e := h (Pi.single o 1)
  simp only [single_one_dotProduct] at e
  simp only [Pi.smul_apply, smul_eq_mul]
  exact e

/-- If `x ψ = 0` at every `x` of the hyperplane `x c = 0` with `x e ≠ 0`, where `e` is no
multiple of `c ≠ 0`, then `ψ = λ c`: the component `w` of `e` orthogonal to `c` has `w e ≠ 0`,
so `x ψ = 0` on the whole hyperplane (at `x` with `x e = 0`, compare `x + w` and `w`). -/
private lemma eq_smul_of_perp_urg {n : Type*} [Fintype n] {c e ψ : n → ℝ} (hc : c ≠ 0)
    (he : ∀ r : ℝ, e ≠ r • c) (h : ∀ x : n → ℝ, x ⬝ᵥ c = 0 → x ⬝ᵥ e ≠ 0 → x ⬝ᵥ ψ = 0) :
    ∃ lam : ℝ, ψ = lam • c := by
  have hcc : c ⬝ᵥ c ≠ 0 := dotProduct_self_eq_zero.not.2 hc
  -- `w`: the component of `e` orthogonal to `c`; it is nonzero and `w e = w w`
  obtain ⟨w, hw⟩ : ∃ w : n → ℝ, e = w + ((c ⬝ᵥ e) / (c ⬝ᵥ c)) • c :=
    ⟨e - ((c ⬝ᵥ e) / (c ⬝ᵥ c)) • c, (sub_add_cancel _ _).symm⟩
  have hw0 : w ≠ 0 := fun h0 => he _ (by rw [hw, h0, zero_add])
  have hwc : w ⬝ᵥ c = 0 := by
    have e1 : c ⬝ᵥ e = c ⬝ᵥ w + (c ⬝ᵥ e) / (c ⬝ᵥ c) * (c ⬝ᵥ c) := by
      conv_lhs => rw [hw]
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [div_mul_cancel₀ _ hcc] at e1
    rw [dotProduct_comm]
    linarith
  have hwe : w ⬝ᵥ e ≠ 0 := by
    rw [hw, dotProduct_add, dotProduct_smul, hwc, smul_zero, add_zero]
    exact dotProduct_self_eq_zero.not.2 hw0
  -- `x ψ = 0` on the whole hyperplane
  have hψ0 : ∀ x : n → ℝ, x ⬝ᵥ c = 0 → x ⬝ᵥ ψ = 0 := fun x hx => by
    by_cases hxe : x ⬝ᵥ e = 0
    · have h1 := h w hwc hwe
      have h2 := h (x + w) (by rw [add_dotProduct, hx, hwc, add_zero])
        (by rw [add_dotProduct, hxe, zero_add]; exact hwe)
      rwa [add_dotProduct, h1, add_zero] at h2
    · exact h x hx hxe
  -- so `ψ = λ c`
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = (c ⬝ᵥ ψ) / (c ⬝ᵥ c) := ⟨_, rfl⟩
  have hlin : ∀ x : n → ℝ, x ⬝ᵥ ψ = lam * (x ⬝ᵥ c) := fun x => by
    have hx := hψ0 (x - ((x ⬝ᵥ c) / (c ⬝ᵥ c)) • c) (by
      rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, div_mul_cancel₀ _ hcc, sub_self])
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, sub_eq_zero] at hx
    rw [hx, hlam]
    ring
  exact ⟨lam, eq_smul_of_dot_urg hlin⟩

/-- **The coefficients of one unit.** If
`‖x‖² ((x g)(x v) b + (x ψg)(x v) a + (x g)(x ψv) a) = 2 (x X xᵀ)(x g)(x v) a` for every `x`,
with `a ≠ 0`, `g ≠ 0` and `v` no multiple of `g`, then `ψg = λ g`, `ψv = μ v`,
`x X xᵀ = c ‖x‖²` for every `x`, and `b = (2 c − λ − μ) a`. At an output `o` with `a_o ≠ 0`: on
the hyperplane `x g = 0` the identity gives `x ψg = 0` where `x v ≠ 0`, so `ψg = λ g`; on the
hyperplane `x v = 0` it gives `x ψv = 0` where `x g ≠ 0`, so `ψv = μ v`; off both, dividing by
`(x g)(x v)` gives `‖x‖² (b + (λ + μ) a) = 2 (x X xᵀ) a`, so `x X xᵀ = c ‖x‖²` near a point off
both hyperplanes, hence everywhere (the identity theorem), and `b = (2 c − λ − μ) a`. -/
private lemma unit_coeffs_urg {n m : Type*} [Fintype n] [Fintype m]
    {g v ψg ψv : n → ℝ} {a b : m → ℝ} {X : Matrix n n ℝ} (ha : a ≠ 0) (hg : g ≠ 0)
    (hvg : ∀ r : ℝ, v ≠ r • g)
    (h : ∀ x : n → ℝ, (x ⬝ᵥ x) • (((x ⬝ᵥ g) * (x ⬝ᵥ v)) • b + ((x ⬝ᵥ ψg) * (x ⬝ᵥ v)) • a
      + ((x ⬝ᵥ g) * (x ⬝ᵥ ψv)) • a) = (2 * ((x ᵥ* X) ⬝ᵥ x) * (x ⬝ᵥ g) * (x ⬝ᵥ v)) • a) :
    ∃ lam mu c : ℝ, ψg = lam • g ∧ ψv = mu • v ∧
      (∀ x : n → ℝ, (x ᵥ* X) ⬝ᵥ x = c * (x ⬝ᵥ x)) ∧ b = (2 * c - lam - mu) • a := by
  obtain ⟨o, ho⟩ := Function.ne_iff.1 ha
  rw [Pi.zero_apply] at ho
  have hcomp : ∀ (x : n → ℝ) (o' : m), (x ⬝ᵥ x) * ((x ⬝ᵥ g) * (x ⬝ᵥ v) * b o'
      + (x ⬝ᵥ ψg) * (x ⬝ᵥ v) * a o' + (x ⬝ᵥ g) * (x ⬝ᵥ ψv) * a o')
      = 2 * ((x ᵥ* X) ⬝ᵥ x) * (x ⬝ᵥ g) * (x ⬝ᵥ v) * a o' := fun x o' => by
    have e := congrFun (h x) o'
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at e
    linear_combination e
  have hxx : ∀ x : n → ℝ, x ≠ 0 → x ⬝ᵥ x ≠ 0 := fun x hx => dotProduct_self_eq_zero.not.2 hx
  -- `v ≠ 0`, and `g` is no multiple of `v`
  have hv : v ≠ 0 := fun h0 => hvg 0 (by rw [h0, zero_smul])
  have hgv : ∀ r : ℝ, g ≠ r • v := fun r hr => by
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hg (by rw [hr, zero_smul])
    exact hvg r⁻¹ (by rw [hr, smul_smul, inv_mul_cancel₀ hr0, one_smul])
  -- on the hyperplane `x g = 0`: `‖x‖² (x ψg)(x v) a_o = 0`, so `ψg = λ g`
  obtain ⟨lam, hlam⟩ := eq_smul_of_perp_urg hg hvg fun x hx hxv => by
    have hx0 : x ≠ 0 := fun h0 => hxv (by rw [h0, zero_dotProduct])
    have e := hcomp x o
    rw [hx] at e
    have key : (x ⬝ᵥ x) * (x ⬝ᵥ v) * a o * (x ⬝ᵥ ψg) = 0 := by linear_combination e
    exact (mul_eq_zero.1 key).resolve_left (mul_ne_zero (mul_ne_zero (hxx x hx0) hxv) ho)
  -- on the hyperplane `x v = 0`: `‖x‖² (x g)(x ψv) a_o = 0`, so `ψv = μ v`
  obtain ⟨mu, hmu⟩ := eq_smul_of_perp_urg hv hgv fun x hx hxg => by
    have hx0 : x ≠ 0 := fun h0 => hxg (by rw [h0, zero_dotProduct])
    have e := hcomp x o
    rw [hx] at e
    have key : (x ⬝ᵥ x) * (x ⬝ᵥ g) * a o * (x ⬝ᵥ ψv) = 0 := by linear_combination e
    exact (mul_eq_zero.1 key).resolve_left (mul_ne_zero (mul_ne_zero (hxx x hx0) hxg) ho)
  -- off both hyperplanes: `‖x‖² (b_o' + (λ + μ) a_o') = 2 (x X xᵀ) a_o'`
  have hoff : ∀ (x : n → ℝ) (o' : m), x ⬝ᵥ g ≠ 0 → x ⬝ᵥ v ≠ 0 →
      (x ⬝ᵥ x) * (b o' + (lam + mu) * a o') = 2 * ((x ᵥ* X) ⬝ᵥ x) * a o' := by
    intro x o' hxg hxv
    have e := hcomp x o'
    rw [hlam, hmu, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at e
    have key : (x ⬝ᵥ g) * (x ⬝ᵥ v) * ((x ⬝ᵥ x) * (b o' + (lam + mu) * a o')
        - 2 * ((x ᵥ* X) ⬝ᵥ x) * a o') = 0 := by linear_combination e
    exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left (mul_ne_zero hxg hxv))
  -- a point `z` off both hyperplanes
  obtain ⟨z, hzg, hzv⟩ : ∃ z : n → ℝ, z ⬝ᵥ g ≠ 0 ∧ z ⬝ᵥ v ≠ 0 := by
    by_cases hgv0 : g ⬝ᵥ v = 0
    · refine ⟨g + v, ?_, ?_⟩
      · rw [add_dotProduct, dotProduct_comm v g, hgv0, add_zero]; exact hxx g hg
      · rw [add_dotProduct, hgv0, zero_add]; exact hxx v hv
    · exact ⟨g, hxx g hg, hgv0⟩
  have hz0 : z ≠ 0 := fun h0 => hzg (by rw [h0, zero_dotProduct])
  -- `c`, from `2 c a_o = b_o + (λ + μ) a_o`
  have h2ao : 2 * a o ≠ 0 := mul_ne_zero two_ne_zero ho
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c * (2 * a o) = b o + (lam + mu) * a o :=
    ⟨_, div_mul_cancel₀ _ h2ao⟩
  -- `x X xᵀ = c ‖x‖²` off both hyperplanes, so near `z`, hence everywhere
  have hq : ∀ x : n → ℝ, (x ᵥ* X) ⬝ᵥ x = c * (x ⬝ᵥ x) := by
    have hcont : ∀ w : n → ℝ, Continuous fun y : n → ℝ => y ⬝ᵥ w := fun w => by fun_prop
    have hzero := eq_zero_of_eventually_urg
      (f := fun y : n → ℝ => (y ᵥ* X) ⬝ᵥ y - c * (y ⬝ᵥ y)) (fun x => by
        have h1 := analyticAt_quad_urg X x
        have h2 := analyticAt_dotSelf_urg x
        fun_prop) (z := z) (by
        filter_upwards [(hcont g).continuousAt.eventually_ne hzg,
          (hcont v).continuousAt.eventually_ne hzv] with y hyg hyv
        have e := hoff y o hyg hyv
        have key : 2 * a o * ((y ᵥ* X) ⬝ᵥ y - c * (y ⬝ᵥ y)) = 0 := by
          linear_combination -e - (y ⬝ᵥ y) * hc
        exact (mul_eq_zero.1 key).resolve_left h2ao)
    exact fun x => sub_eq_zero.1 (hzero x)
  refine ⟨lam, mu, c, hlam, hmu, hq, funext fun o' => ?_⟩
  -- every output at `x = z`: `‖z‖² (b_o' − (2 c − λ − μ) a_o') = 0`
  have e := hoff z o' hzg hzv
  rw [hq z] at e
  have key : (z ⬝ᵥ z) * (b o' - (2 * c - lam - mu) * a o') = 0 := by linear_combination e
  have := (mul_eq_zero.1 key).resolve_left (hxx z hz0)
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith

/-- A symmetric matrix whose quadratic form is `μ ‖x‖²` is `μ I` (at `e_p` and `e_p + e_r`). -/
private lemma eq_smul_one_of_quad_urg {n : Type*} [Fintype n] [DecidableEq n]
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

/-! ### The theorem -/

/-- **Step 4 of the proof of Theorem B.1 (iii) of the skips paper for `ε = 0`, with Lemma B.3, for
ReGLU units:** for hidden units `relu(x g_i) (x v_i) a_i` (at least one) with nonzero rows `a_i`,
nonzero, pairwise non-collinear gate columns `g_i` and no value column `v_i` proportional to its
gate column, a symmetric matrix `X` and a direction `(ψg, ψv, β)` of the weights: if at every
input `x` with no gate at its kink
`‖x‖² ∑_i [σ(x g_i)(x v_i) β_i + σ'(x g_i)(x ψg_i)(x v_i) a_i + σ(x g_i)(x ψv_i) a_i]
  = 2 (x X xᵀ) ∑_i σ(x g_i)(x v_i) a_i`,
then `X = c₀ I` for a number `c₀`, and `ψg_i = λ_i g_i`, `ψv_i = μ_i v_i`,
`β_i = (2 c₀ − λ_i − μ_i) a_i` for numbers `λ_i`, `μ_i`. -/
theorem reglu_unitsRescaleSphere {n m q : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    [Fintype q] [Nonempty q]
    (g v : q → n → ℝ) (a : q → m → ℝ) (X : Matrix n n ℝ) (ψg ψv : q → n → ℝ) (β : q → m → ℝ)
    (ha : ∀ i, a i ≠ 0) (hg : ∀ i, g i ≠ 0) (hgg : ∀ i j, i ≠ j → ∀ r : ℝ, g i ≠ r • g j)
    (hvg : ∀ i, ∀ r : ℝ, v i ≠ r • g i) (hX : Xᵀ = X)
    (h : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ g i ≠ 0) →
      (x ⬝ᵥ x) • ∑ i, ((relu (x ⬝ᵥ g i) * (x ⬝ᵥ v i)) • β i
          + (reluDeriv (x ⬝ᵥ g i) * (x ⬝ᵥ ψg i) * (x ⬝ᵥ v i)) • a i
          + (relu (x ⬝ᵥ g i) * (x ⬝ᵥ ψv i)) • a i)
        = (2 * ((x ᵥ* X) ⬝ᵥ x)) • ∑ i, (relu (x ⬝ᵥ g i) * (x ⬝ᵥ v i)) • a i) :
    ∃ (c₀ : ℝ) (lam mu : q → ℝ), X = c₀ • (1 : Matrix n n ℝ) ∧
      ∀ i, ψg i = lam i • g i ∧ ψv i = mu i • v i ∧
        β i = (2 * c₀ - lam i - mu i) • a i := by
  obtain ⟨i₀⟩ := ‹Nonempty q›
  -- steps 1 and 2 for every unit
  choose lam mu c hψg hψv hq hβ using fun i =>
    unit_coeffs_urg (ha i) (hg i) (hvg i) (unit_alone_urg hg hgg h i)
  -- the quadratic form of `X` is `c_i ‖x‖²` for every `i`, so all `c_i` are `c_{i₀}`
  have hc : ∀ i, c i = c i₀ := fun i =>
    mul_right_cancel₀ (dotProduct_self_eq_zero.not.2 (hg i))
      ((hq i (g i)).symm.trans (hq i₀ (g i)))
  refine ⟨c i₀, lam, mu, eq_smul_one_of_quad_urg hX (hq i₀), fun i => ⟨hψg i, hψv i, ?_⟩⟩
  rw [hβ i, hc i]

end Skips
