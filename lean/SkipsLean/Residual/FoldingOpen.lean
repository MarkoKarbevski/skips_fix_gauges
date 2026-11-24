import SkipsLean.Residual.Folding

/-!
# An open set of weights on which a block folds and the next block has a dead unit

Paper (skips paper): Appendix A.8, Proposition A.33 (i) and its proof.

"(i) There is a nonempty open set of weights on which block 1 folds and block 2 has a dead unit."

"(i) Let block 1 hold the `d_model` units of the example above, with `W_read = −I` and
`W_write = 2I`. Give its other units zero writes. Let a unit of block 2 have a read `r` whose
entries are all negative. Then `Φ_1(h) r < 0` for every `h ≠ 0`, since `Φ_1(h)` is a nonzero vector
with no negative entry. By compactness of the unit sphere, `max_{‖h‖=1} Φ_1(h) r < 0` persists
under small changes of all the weights. Since the perturbed `Φ_1` is still positively homogeneous,
`Φ_1(h) r < 0` then holds for every `h ≠ 0`. As `h_1(x) = Φ_1(xE)` and `Φ_1(0) = 0`, the unit is
active at no input, so it is dead. And `Φ_1` misses the half-space `{h : hr > 0}`, so it is not
onto, and block 1 folds by Proposition A.32 (i)."

Stated here, for a residual network of ReLU blocks `Fin (L + 1)` without normalization, a block
`ℓ.succ` after the first and a unit `j` of it (the paper's blocks 1 and 2 are `ℓ.castSucc` and
`ℓ.succ`): if block `ℓ.castSucc` has at least `d` units, there is a nonempty open set of weights on
which block `ℓ.castSucc` folds and unit `j` of block `ℓ.succ` is dead.

The statement does not take invariance of domain as a hypothesis: that the block folds at every
parameter of the open set can be shown directly (near the example, `Φ` is close to the identity
around a row with positive entries and close to a reflection around its mirror image, and both
images contain a common ball).
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin (L + 1) → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)]

/-- Helper: `ReLU (c z) = c ReLU z` for `c ≥ 0`. -/
private theorem relu_mul_fopen {c : ℝ} (hc : 0 ≤ c) (z : ℝ) : relu (c * z) = c * relu z := by
  simp only [relu]
  rw [mul_max_of_nonneg _ _ hc, mul_zero]

/-- Helper: ReLU is `1`-Lipschitz. -/
private theorem abs_relu_sub_fopen (a b : ℝ) : |relu a - relu b| ≤ |a - b| :=
  abs_max_sub_max_le_abs a b 0

/-- Helper: `z + 2 ReLU (-z) = |z|`. -/
private theorem add_relu_neg_fopen (z : ℝ) : z + relu (-z) * 2 = |z| := by
  simp only [relu]
  rcases le_total 0 z with h | h
  · rw [max_eq_right (by linarith), abs_of_nonneg h]; ring
  · rw [max_eq_left (by linarith), abs_of_nonpos h]; ring

/-- Helper: ReLU is continuous. -/
private theorem continuous_relu_fopen : Continuous relu :=
  continuous_id.max continuous_const

/-- Helper: `|v ⬝ᵥ w| ≤ ‖v‖ ∑_a |w a|` (sup norm). -/
private theorem abs_dot_le_fopen {n : Type*} [Fintype n] (v w : n → ℝ) :
    |v ⬝ᵥ w| ≤ ‖v‖ * ∑ a, |w a| := by
  rw [Finset.mul_sum]
  simp only [dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [abs_mul]
  have h := norm_le_pi_norm v a
  rw [Real.norm_eq_abs] at h
  exact mul_le_mul_of_nonneg_right h (abs_nonneg _)

/-- Helper: the scalar estimate for one unit. If the reference read `c₀` is `0`, or the unit is
active on all of `S` (`s = 1`), or inactive on all of `S` (`s = 0`), then
`ReLU (x c) - ReLU (y c) - s (x - y) c₀` is at most `‖x - y‖ ‖c - c₀‖₁`. -/
private theorem unit_scalar_fopen {n : Type*} [Fintype n] (c c₀ : n → ℝ) (s : ℝ)
    (S : Set (n → ℝ))
    (hgood : c₀ = 0 ∨ (s = 1 ∧ ∀ h ∈ S, 0 ≤ h ⬝ᵥ c) ∨ (s = 0 ∧ ∀ h ∈ S, h ⬝ᵥ c ≤ 0))
    {x y : n → ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    |relu (x ⬝ᵥ c) - relu (y ⬝ᵥ c) - s * ((x - y) ⬝ᵥ c₀)| ≤ ‖x - y‖ * ∑ a, |c a - c₀ a| := by
  have key : |(x - y) ⬝ᵥ (c - c₀)| ≤ ‖x - y‖ * ∑ a, |c a - c₀ a| :=
    abs_dot_le_fopen (x - y) (c - c₀)
  rcases hgood with h0 | ⟨h1, hS⟩ | ⟨h0', hS⟩
  · subst h0
    rw [dotProduct_zero, mul_zero, sub_zero]
    refine (abs_relu_sub_fopen _ _).trans ?_
    rw [← sub_dotProduct]
    simpa using key
  · subst h1
    simp only [relu]
    rw [max_eq_left (hS x hx), max_eq_left (hS y hy), one_mul, ← sub_dotProduct,
      ← dotProduct_sub]
    exact key
  · subst h0'
    simp only [relu]
    rw [max_eq_right (hS x hx), max_eq_right (hS y hy), zero_mul, sub_self, sub_zero, abs_zero]
    exact mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun a _ => abs_nonneg _)

/-- Helper: the estimate for one unit, with its write `r` and the reference write `r₀`. -/
private theorem unit_vec_fopen {n : Type*} [Fintype n] (c r c₀ r₀ : n → ℝ) (s : ℝ)
    (hs : |s| ≤ 1) (S : Set (n → ℝ))
    (hgood : c₀ = 0 ∨ (s = 1 ∧ ∀ h ∈ S, 0 ≤ h ⬝ᵥ c) ∨ (s = 0 ∧ ∀ h ∈ S, h ⬝ᵥ c ≤ 0))
    {x y : n → ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    ‖relu (x ⬝ᵥ c) • r - relu (y ⬝ᵥ c) • r - (s * ((x - y) ⬝ᵥ c₀)) • r₀‖
      ≤ ‖x - y‖ * ((∑ a, |c a - c₀ a|) * ‖r‖ + (∑ a, |c₀ a|) * ‖r - r₀‖) := by
  have e : relu (x ⬝ᵥ c) • r - relu (y ⬝ᵥ c) • r - (s * ((x - y) ⬝ᵥ c₀)) • r₀
      = (relu (x ⬝ᵥ c) - relu (y ⬝ᵥ c) - s * ((x - y) ⬝ᵥ c₀)) • r
        + (s * ((x - y) ⬝ᵥ c₀)) • (r - r₀) := by
    simp only [sub_smul, smul_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  have h1 := unit_scalar_fopen c c₀ s S hgood hx hy
  have h2 := abs_dot_le_fopen (x - y) c₀
  calc _ ≤ (‖x - y‖ * ∑ a, |c a - c₀ a|) * ‖r‖
        + (1 * (‖x - y‖ * ∑ a, |c₀ a|)) * ‖r - r₀‖ := by
        gcongr
    _ = _ := by ring

/-- Helper: the map `F(h) = h + ∑_i ReLU (h c_i) r_i` of a block. -/
private noncomputable def F_fopen {n ι : Type*} [Fintype n] [Fintype ι] (c r : ι → n → ℝ)
    (h : n → ℝ) : n → ℝ :=
  h + ∑ i, relu (h ⬝ᵥ c i) • r i

/-- Helper: on a set `S` where every unit is good, `F` approximates the linear map
`v ↦ v + ∑_i s_i (v c₀_i) r₀_i` with the constant
`∑_i (‖c_i - c₀_i‖₁ ‖r_i‖ + ‖c₀_i‖₁ ‖r_i - r₀_i‖)`. -/
private theorem approx_fopen {n ι : Type*} [Fintype n] [Fintype ι] (c r c₀ r₀ : ι → n → ℝ)
    (s : ι → ℝ) (hs : ∀ i, |s i| ≤ 1) (S : Set (n → ℝ))
    (hgood : ∀ i, c₀ i = 0 ∨ (s i = 1 ∧ ∀ h ∈ S, 0 ≤ h ⬝ᵥ c i)
      ∨ (s i = 0 ∧ ∀ h ∈ S, h ⬝ᵥ c i ≤ 0))
    (f' : (n → ℝ) →L[ℝ] (n → ℝ)) (hf' : ∀ v, f' v = v + ∑ i, (s i * (v ⬝ᵥ c₀ i)) • r₀ i)
    (κ : NNReal)
    (hκ : ∑ i, ((∑ a, |c i a - c₀ i a|) * ‖r i‖ + (∑ a, |c₀ i a|) * ‖r i - r₀ i‖) ≤ κ) :
    ApproximatesLinearOn (F_fopen c r) f' S κ := by
  intro x hx y hy
  rw [hf']
  have e : F_fopen c r x - F_fopen c r y - ((x - y) + ∑ i, (s i * ((x - y) ⬝ᵥ c₀ i)) • r₀ i)
      = ∑ i, (relu (x ⬝ᵥ c i) • r i - relu (y ⬝ᵥ c i) • r i
        - (s i * ((x - y) ⬝ᵥ c₀ i)) • r₀ i) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [F_fopen]
    abel
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ i, ‖x - y‖ * ((∑ a, |c i a - c₀ i a|) * ‖r i‖
          + (∑ a, |c₀ i a|) * ‖r i - r₀ i‖) :=
        Finset.sum_le_sum fun i _ =>
          unit_vec_fopen (c i) (r i) (c₀ i) (r₀ i) (s i) (hs i) S (hgood i) hx hy
    _ = ‖x - y‖ * ∑ i, ((∑ a, |c i a - c₀ i a|) * ‖r i‖
          + (∑ a, |c₀ i a|) * ‖r i - r₀ i‖) := by rw [Finset.mul_sum]
    _ ≤ ‖x - y‖ * κ := by gcongr
    _ = κ * ‖x - y‖ := mul_comm _ _

/-- Helper: a map that approximates, with the constant `1/2` on the closed ball of radius `1/4`
around `b`, a linear map with a right inverse of norm at most `1`, takes every value within `1/8`
of `F b` on that ball. -/
private theorem exists_eq_fopen {n : Type*} [Fintype n] (F : (n → ℝ) → (n → ℝ))
    (f' : (n → ℝ) →L[ℝ] (n → ℝ)) (g : (n → ℝ) → (n → ℝ)) (hg : ∀ y, f' (g y) = y)
    (hgn : ∀ y, ‖g y‖ ≤ ‖y‖) (b q : n → ℝ)
    (hF : ApproximatesLinearOn F f' (Metric.closedBall b (1 / 4)) ⟨1 / 2, by norm_num⟩)
    (hq : dist q (F b) ≤ 1 / 8) : ∃ h ∈ Metric.closedBall b (1 / 4), F h = q := by
  let G : f'.NonlinearRightInverse := ⟨g, 1, fun y => by simpa using hgn y, hg⟩
  have hs := hF.surjOn_closedBall_of_nonlinearRightInverse G (by norm_num : (0 : ℝ) ≤ 1 / 4)
    le_rfl
  refine hs ?_
  rw [Metric.mem_closedBall]
  have hG : ((G.nnNorm : NNReal) : ℝ) = 1 := rfl
  rw [hG]
  show dist q (F b) ≤ ((1 : ℝ)⁻¹ - 1 / 2) * (1 / 4)
  linarith

/-- Helper: the reflection `R v = v` with the entry `a₀` negated, a linear map. -/
private noncomputable def refl_fopen {n : Type*} [Fintype n] [DecidableEq n] (a₀ : n) :
    (n → ℝ) →L[ℝ] (n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v b => if b = a₀ then -v b else v b
      map_add' := fun v w => by
        ext b
        simp only [Pi.add_apply]
        split_ifs <;> ring
      map_smul' := fun t v => by
        ext b
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> ring }

private theorem refl_apply_fopen {n : Type*} [Fintype n] [DecidableEq n] (a₀ : n) (v : n → ℝ)
    (b : n) : refl_fopen a₀ v b = if b = a₀ then -v b else v b := rfl

private theorem refl_refl_fopen {n : Type*} [Fintype n] [DecidableEq n] (a₀ : n) (v : n → ℝ) :
    refl_fopen a₀ (refl_fopen a₀ v) = v := by
  ext b
  simp only [refl_apply_fopen]
  split_ifs <;> simp

private theorem norm_refl_fopen {n : Type*} [Fintype n] [DecidableEq n] (a₀ : n) (v : n → ℝ) :
    ‖refl_fopen a₀ v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun b => ?_
  rw [refl_apply_fopen]
  split_ifs
  · rw [norm_neg]; exact norm_le_pi_norm v b
  · exact norm_le_pi_norm v b

/-- Helper: the read column of unit `i` at `θ*`: `-e_a` if `i = e a`, else `0`. -/
private def c0_fopen {n ι : Type*} [DecidableEq ι] (e : n ↪ ι) (i : ι) : n → ℝ :=
  fun a => if i = e a then -1 else 0

/-- Helper: the write row of unit `i` at `θ*`: `2 e_a` if `i = e a`, else `0`. -/
private def r0_fopen {n ι : Type*} [DecidableEq ι] (e : n ↪ ι) (i : ι) : n → ℝ :=
  fun b => if i = e b then 2 else 0

/-- Helper: unit `e a` reads `-h a` at `θ*`. -/
private theorem dot_c0_fopen {n ι : Type*} [Fintype n] [DecidableEq ι] (e : n ↪ ι) (a : n)
    (h : n → ℝ) : h ⬝ᵥ c0_fopen e (e a) = -h a := by
  simp only [dotProduct, c0_fopen, mul_ite, mul_neg, mul_one, mul_zero]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [e.injective.ne (Ne.symm hb)])
    (fun ha => absurd (Finset.mem_univ a) ha)]
  simp

/-- Helper: a unit outside the range of `e` reads `0` at `θ*`. -/
private theorem c0_eq_zero_fopen {n ι : Type*} [DecidableEq ι] (e : n ↪ ι) (i : ι)
    (hi : ∀ a, i ≠ e a) : c0_fopen e i = 0 := by
  funext a
  simp [c0_fopen, hi a]

/-- Helper: at `θ*`, `Φ(h) = |h|` entrywise (`h + 2 ReLU (-h) = |h|`). -/
private theorem F_c0_fopen {n ι : Type*} [Fintype n] [Fintype ι] [DecidableEq ι] (e : n ↪ ι)
    (h : n → ℝ) : F_fopen (c0_fopen e) (r0_fopen e) h = fun b => |h b| := by
  funext b
  simp only [F_fopen, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, r0_fopen,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, dot_c0_fopen]
  exact add_relu_neg_fopen (h b)

/-- Helper: the row with all entries `1`. -/
private def P1_fopen {n : Type*} : n → ℝ := fun _ => 1

/-- Helper: the row with the entry `-1` at `a₀` and `1` elsewhere. -/
private def P2_fopen {n : Type*} [DecidableEq n] (a₀ : n) : n → ℝ :=
  fun b => if b = a₀ then -1 else 1

/-- Helper: an entry of a point of a closed ball is within the radius of the center's entry. -/
private theorem abs_sub_le_fopen {n : Type*} [Fintype n] {b h : n → ℝ} {ρ : ℝ}
    (hh : h ∈ Metric.closedBall b ρ) (a : n) : |h a - b a| ≤ ρ := by
  have := (dist_le_pi_dist h b a).trans (Metric.mem_closedBall.1 hh)
  rwa [Real.dist_eq] at this

/-- Helper: a point within `1/4` of a row with entries in `[-1, 1]` has norm at most `5/4`. -/
private theorem norm_le_fopen {n : Type*} [Fintype n] {b h : n → ℝ} (hb : ∀ a, |b a| ≤ 1)
    (hh : h ∈ Metric.closedBall b (1 / 4)) : ‖h‖ ≤ 5 / 4 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun a => ?_
  rw [Real.norm_eq_abs]
  have h1 := abs_sub_le_fopen hh a
  have h2 := abs_sub_abs_le_abs_sub (h a) (b a)
  linarith [hb a]

private theorem abs_P1_fopen {n : Type*} (a : n) : |(P1_fopen : n → ℝ) a| ≤ 1 := by
  simp [P1_fopen]

private theorem abs_P2_fopen {n : Type*} [DecidableEq n] (a₀ a : n) : |P2_fopen a₀ a| ≤ 1 := by
  simp only [P2_fopen]
  split_ifs <;> norm_num

/-- Helper: near a reference read, the read of a row of norm `≤ 5/4` moves by at most `5/8`. -/
private theorem dot_near_fopen {n : Type*} [Fintype n] (h c c₀ : n → ℝ)
    (hc : ∑ a, |c a - c₀ a| ≤ 1 / 2) (hh : ‖h‖ ≤ 5 / 4) : |h ⬝ᵥ c - h ⬝ᵥ c₀| ≤ 5 / 8 := by
  rw [← dotProduct_sub]
  calc |h ⬝ᵥ (c - c₀)| ≤ ‖h‖ * ∑ a, |c a - c₀ a| := abs_dot_le_fopen h (c - c₀)
    _ ≤ 5 / 4 * (1 / 2) :=
        mul_le_mul hh hc (Finset.sum_nonneg fun a _ => abs_nonneg _) (by norm_num)
    _ = 5 / 8 := by norm_num

/-- Helper: on the ball around `P1`, every unit is good with `s = 0`: the units `e a` read
`≈ -h a < 0`, the others have the reference read `0`. -/
private theorem good1_fopen {n ι : Type*} [Fintype n] [DecidableEq ι] (e : n ↪ ι)
    (c : ι → n → ℝ) (hc : ∀ i, ∑ a, |c i a - c0_fopen e i a| ≤ 1 / 2) (i : ι) :
    c0_fopen e i = 0 ∨ ((fun _ => (0 : ℝ)) i = 1 ∧ ∀ h ∈ Metric.closedBall P1_fopen (1 / 4),
      0 ≤ h ⬝ᵥ c i) ∨ ((fun _ => (0 : ℝ)) i = 0 ∧ ∀ h ∈ Metric.closedBall P1_fopen (1 / 4),
      h ⬝ᵥ c i ≤ 0) := by
  by_cases hi : ∃ a, i = e a
  · obtain ⟨a, rfl⟩ := hi
    refine Or.inr (Or.inr ⟨rfl, fun h hh => ?_⟩)
    have h1 := dot_near_fopen h (c (e a)) (c0_fopen e (e a)) (hc _)
      (norm_le_fopen abs_P1_fopen hh)
    rw [dot_c0_fopen] at h1
    have h2 := abs_sub_le_fopen hh a
    simp only [P1_fopen] at h2
    linarith [(abs_le.1 h1).2, (abs_le.1 h2).1]
  · push Not at hi
    exact Or.inl (c0_eq_zero_fopen e i hi)

/-- Helper: on the ball around `P2`, every unit is good with `s = 1` at `e a₀` and `s = 0`
elsewhere: unit `e a₀` reads `≈ -h a₀ > 0`, a unit `e a` with `a ≠ a₀` reads `≈ -h a < 0`. -/
private theorem good2_fopen {n ι : Type*} [Fintype n] [DecidableEq n] [DecidableEq ι]
    (e : n ↪ ι) (a₀ : n) (c : ι → n → ℝ) (hc : ∀ i, ∑ a, |c i a - c0_fopen e i a| ≤ 1 / 2)
    (i : ι) :
    c0_fopen e i = 0 ∨ ((fun i => if i = e a₀ then (1 : ℝ) else 0) i = 1
      ∧ ∀ h ∈ Metric.closedBall (P2_fopen a₀) (1 / 4), 0 ≤ h ⬝ᵥ c i)
      ∨ ((fun i => if i = e a₀ then (1 : ℝ) else 0) i = 0
      ∧ ∀ h ∈ Metric.closedBall (P2_fopen a₀) (1 / 4), h ⬝ᵥ c i ≤ 0) := by
  by_cases hi : ∃ a, i = e a
  · obtain ⟨a, rfl⟩ := hi
    by_cases ha : a = a₀
    · subst ha
      refine Or.inr (Or.inl ⟨by simp, fun h hh => ?_⟩)
      have h1 := dot_near_fopen h (c (e a)) (c0_fopen e (e a)) (hc _)
        (norm_le_fopen (abs_P2_fopen a) hh)
      rw [dot_c0_fopen] at h1
      have h2 := abs_sub_le_fopen hh a
      simp only [P2_fopen, ite_true] at h2
      linarith [(abs_le.1 h1).1, (abs_le.1 h2).2]
    · refine Or.inr (Or.inr ⟨by simp [e.injective.eq_iff, ha], fun h hh => ?_⟩)
      have h1 := dot_near_fopen h (c (e a)) (c0_fopen e (e a)) (hc _)
        (norm_le_fopen (abs_P2_fopen a₀) hh)
      rw [dot_c0_fopen] at h1
      have h2 := abs_sub_le_fopen hh a
      simp only [P2_fopen, ha, ite_false] at h2
      linarith [(abs_le.1 h1).2, (abs_le.1 h2).1]
  · push Not at hi
    exact Or.inl (c0_eq_zero_fopen e i hi)

/-- Helper: the linear part of `Φ` at `θ*` on the ball around `P2` is the reflection. -/
private theorem refl_formula_fopen {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι] (e : n ↪ ι) (a₀ : n) (v : n → ℝ) :
    refl_fopen a₀ v = v + ∑ i, ((fun i => if i = e a₀ then (1 : ℝ) else 0) i
      * (v ⬝ᵥ c0_fopen e i)) • r0_fopen e i := by
  simp only [ite_mul, one_mul, zero_mul, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, dot_c0_fopen]
  funext b
  simp only [refl_apply_fopen, Pi.add_apply, Pi.smul_apply, smul_eq_mul, r0_fopen,
    e.injective.eq_iff]
  by_cases hb : b = a₀
  · subst hb
    simp only [ite_true]
    ring
  · simp only [hb, Ne.symm hb, ite_false]
    ring

/-- Helper (part 2, without weights): if every read column is within `1/2` (in `ℓ¹`) of its
value at `θ*`, the constant `K ≤ 1/2`, and `Φ` sends `P1` and `P2` within `1/8` of `P1`, then
`Φ` is not injective: `P1` has a preimage near `P1` and one near `P2`. -/
private theorem not_injective_fopen {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι] (e : n ↪ ι) (a₀ : n) (c r : ι → n → ℝ)
    (hc : ∀ i, ∑ a, |c i a - c0_fopen e i a| ≤ 1 / 2)
    (hK : ∑ i, ((∑ a, |c i a - c0_fopen e i a|) * ‖r i‖
      + (∑ a, |c0_fopen e i a|) * ‖r i - r0_fopen e i‖) ≤ 1 / 2)
    (hp1 : dist P1_fopen (F_fopen c r P1_fopen) ≤ 1 / 8)
    (hp2 : dist P1_fopen (F_fopen c r (P2_fopen a₀)) ≤ 1 / 8) :
    ¬ Function.Injective (F_fopen c r) := by
  -- near `P1`, `Φ` approximates the identity; near `P2`, the reflection
  have hA1 : ApproximatesLinearOn (F_fopen c r) (ContinuousLinearMap.id ℝ (n → ℝ))
      (Metric.closedBall P1_fopen (1 / 4)) ⟨1 / 2, by norm_num⟩ :=
    approx_fopen c r (c0_fopen e) (r0_fopen e) (fun _ => 0) (fun _ => by norm_num) _
      (good1_fopen e c hc) _ (fun v => by simp) _ hK
  have hA2 : ApproximatesLinearOn (F_fopen c r) (refl_fopen a₀)
      (Metric.closedBall (P2_fopen a₀) (1 / 4)) ⟨1 / 2, by norm_num⟩ :=
    approx_fopen c r (c0_fopen e) (r0_fopen e) (fun i => if i = e a₀ then 1 else 0)
      (fun i => by split_ifs <;> norm_num) _ (good2_fopen e a₀ c hc) _
      (refl_formula_fopen e a₀) _ hK
  -- both balls contain a preimage of `P1`
  obtain ⟨h, hh, hFh⟩ := exists_eq_fopen _ _ id (fun y => rfl) (fun y => le_rfl) P1_fopen
    P1_fopen hA1 hp1
  obtain ⟨h', hh', hFh'⟩ := exists_eq_fopen _ _ (refl_fopen a₀) (refl_refl_fopen a₀)
    (norm_refl_fopen a₀) (P2_fopen a₀) P1_fopen hA2 hp2
  -- and the balls are disjoint: `h a₀ ≥ 3/4 > -3/4 ≥ h' a₀`
  intro hinj
  have heq := hinj (hFh.trans hFh'.symm)
  subst heq
  have h1 := abs_sub_le_fopen hh a₀
  have h2 := abs_sub_le_fopen hh' a₀
  simp only [P1_fopen, P2_fopen, ite_true] at h1 h2
  linarith [(abs_le.1 h1).1, (abs_le.1 h2).2]

/-- **Proposition A.33 (i) of the skips paper:** for `d ≥ 1` and at least `d` units in block
`ℓ.castSucc`, there is a nonempty open set of weights of the residual ReLU network on which block
`ℓ.castSucc` folds and unit `j` of the next block `ℓ.succ` is dead. -/
theorem exists_isOpen_folds_unitInactiveRes_relu [Nonempty d] (ℓ : Fin L) (j : hid ℓ.succ)
    (hq : Fintype.card d ≤ Fintype.card (hid ℓ.castSucc)) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ ∀ θ ∈ U, Folds θ ℓ.castSucc ∧ UnitInactiveRes θ ℓ.succ j := by
  sorry

end Skips
