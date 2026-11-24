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

/-- Helper: the read column of unit `i` of block `m`. -/
private def col_fopen (m : Fin (L + 1))
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (i : hid m) : d → ℝ :=
  fun a => θ.read m a i

/-- Helper: the write row of unit `i` of block `m`. -/
private def row_fopen (m : Fin (L + 1))
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (i : hid m) : d → ℝ :=
  θ.write m i

/-- Helper: the weights `θ*`. In block `ℓ.castSucc`, unit `e a` has the read column `-e_a` and
the write row `2 e_a`, the other units read and write `0`; every read column of block `ℓ.succ`
has all entries `-1`; all other weights are `0`. -/
private noncomputable def star_fopen (ℓ : Fin L) (e : d ↪ hid ℓ.castSucc) :
    Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut where
  E := 0
  read := Function.update
    (Function.update (fun _ => 0) ℓ.succ (Matrix.of fun _ _ => -1))
    ℓ.castSucc (Matrix.of fun a i => c0_fopen e i a)
  write := Function.update (fun _ => 0) ℓ.castSucc (Matrix.of fun i b => r0_fopen e i b)
  D := 0

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read columns of block `ℓ.castSucc` at `θ*`. -/
private theorem col_star_fopen (ℓ : Fin L) (e : d ↪ hid ℓ.castSucc) :
    col_fopen ℓ.castSucc (star_fopen (T := T) (dIn := dIn) (dOut := dOut) ℓ e)
      = c0_fopen e := by
  funext i a
  simp only [col_fopen, star_fopen, Function.update_self, Matrix.of_apply]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write rows of block `ℓ.castSucc` at `θ*`. -/
private theorem row_star_fopen (ℓ : Fin L) (e : d ↪ hid ℓ.castSucc) :
    row_fopen ℓ.castSucc (star_fopen (T := T) (dIn := dIn) (dOut := dOut) ℓ e)
      = r0_fopen e := by
  funext i b
  simp only [row_fopen, star_fopen, Function.update_self, Matrix.of_apply]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read column of unit `j` of block `ℓ.succ` at `θ*` has all entries `-1`. -/
private theorem col_succ_star_fopen (ℓ : Fin L) (e : d ↪ hid ℓ.castSucc) (j : hid ℓ.succ) :
    col_fopen ℓ.succ (star_fopen (T := T) (dIn := dIn) (dOut := dOut) ℓ e) j
      = fun _ => -1 := by
  have hne : ℓ.succ ≠ ℓ.castSucc := Fin.castSucc_lt_succ.ne'
  funext a
  simp only [col_fopen, star_fopen]
  rw [Function.update_of_ne hne, Function.update_self]
  rfl

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper: `Φ_m(h) = h + ∑_i ReLU (h c_i) r_i`. -/
private theorem blockMapRes_eq_fopen (m : Fin (L + 1))
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) :
    blockMapRes θ m = F_fopen (col_fopen m θ) (row_fopen m θ) := by
  funext h b
  simp only [blockMapRes, F_fopen, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: at `θ*`, `Φ(h) = |h|` entrywise. -/
private theorem blockMapRes_star_fopen (ℓ : Fin L) (e : d ↪ hid ℓ.castSucc) (h : d → ℝ) :
    blockMapRes (star_fopen (T := T) (dIn := dIn) (dOut := dOut) ℓ e) ℓ.castSucc h
      = fun b => |h b| := by
  rw [blockMapRes_eq_fopen, col_star_fopen, row_star_fopen, F_c0_fopen]

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper: an entry of a read is a continuous function of the parameters. -/
private theorem continuous_read_fopen (m : Fin (L + 1)) (a : d) (i : hid m) :
    Continuous fun θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut =>
      θ.read m a i :=
  LinearMap.continuous_of_finiteDimensional
    ({ toFun := fun θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut => θ.read m a i
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } :
      Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut →ₗ[ℝ] ℝ)

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper: an entry of a write is a continuous function of the parameters. -/
private theorem continuous_write_fopen (m : Fin (L + 1)) (i : hid m) (b : d) :
    Continuous fun θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut =>
      θ.write m i b :=
  LinearMap.continuous_of_finiteDimensional
    ({ toFun := fun θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut => θ.write m i b
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } :
      Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut →ₗ[ℝ] ℝ)

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper: a read column is continuous in the parameters. -/
private theorem continuous_col_fopen (m : Fin (L + 1)) (i : hid m) :
    Continuous fun θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut =>
      col_fopen m θ i :=
  continuous_pi fun a => continuous_read_fopen m a i

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper: a write row is continuous in the parameters. -/
private theorem continuous_row_fopen (m : Fin (L + 1)) (i : hid m) :
    Continuous fun θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut =>
      row_fopen m θ i :=
  continuous_pi fun b => continuous_write_fopen m i b

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper: `Φ_m(h)` is continuous in the parameters and the row. -/
private theorem continuous_F_fopen (m : Fin (L + 1)) :
    Continuous fun p : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut × (d → ℝ) =>
      F_fopen (col_fopen m p.1) (row_fopen m p.1) p.2 := by
  have hterm : ∀ i : hid m, Continuous fun p : Params (Arch.mlp (T := T) (d := d) relu id hid)
      dIn dOut × (d → ℝ) => relu (p.2 ⬝ᵥ col_fopen m p.1 i) • row_fopen m p.1 i := fun i =>
    (continuous_relu_fopen.comp (continuous_snd.dotProduct
      ((continuous_col_fopen m i).comp continuous_fst))).smul
      ((continuous_row_fopen m i).comp continuous_fst)
  have hsum : Continuous fun p : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut
      × (d → ℝ) => ∑ i, relu (p.2 ⬝ᵥ col_fopen m p.1 i) • row_fopen m p.1 i :=
    continuous_finsetSum _ fun i _ => hterm i
  exact continuous_snd.add hsum

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper: `θ ↦ Φ_m(b)` is continuous for a fixed row `b`. -/
private theorem continuous_blockMapRes_fopen (m : Fin (L + 1)) (b : d → ℝ) :
    Continuous fun θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut =>
      blockMapRes θ m b := by
  simp only [blockMapRes_eq_fopen]
  have h1 : Continuous fun θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut =>
      (θ, b) := continuous_id.prodMk continuous_const
  have hc := (continuous_F_fopen m).comp h1
  exact hc

/-- Helper: `Φ` is positively homogeneous: `Φ(t h) = t Φ(h)` for `t ≥ 0`. -/
private theorem F_smul_fopen {n ι : Type*} [Fintype n] [Fintype ι] (c r : ι → n → ℝ)
    (h : n → ℝ) {t : ℝ} (ht : 0 ≤ t) : F_fopen c r (t • h) = t • F_fopen c r h := by
  simp only [F_fopen, smul_dotProduct, smul_eq_mul, relu_mul_fopen ht, mul_smul, smul_add,
    Finset.smul_sum]

/-- Helper (part 1): the number `Φ(h) r` that unit `j` of block `ℓ.succ` reads when the row `h`
enters block `ℓ.castSucc`. -/
private noncomputable def W_fopen (ℓ : Fin L) (j : hid ℓ.succ)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (h : d → ℝ) : ℝ :=
  blockMapRes θ ℓ.castSucc h ⬝ᵥ col_fopen ℓ.succ θ j

omit [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper (part 1): unit `j` of block `ℓ.succ` reads `W` of the row of the hidden state before
block `ℓ.castSucc`. -/
private theorem read_eq_fopen (ℓ : Fin L) (j : hid ℓ.succ)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (t : T) :
    (hidden (Arch.mlp relu id hid) 1 θ x ℓ.succ.castSucc * θ.read ℓ.succ) t j
      = W_fopen ℓ j θ (hidden (Arch.mlp relu id hid) 1 θ x ℓ.castSucc.castSucc t) := by
  rw [W_fopen, ← hidden_succ_eq_blockMapRes]
  rfl

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper (part 1): `W` is continuous in the parameters and the row. -/
private theorem continuous_W_fopen (ℓ : Fin L) (j : hid ℓ.succ) :
    Continuous fun p : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut × (d → ℝ) =>
      W_fopen ℓ j p.1 p.2 := by
  simp only [W_fopen, blockMapRes_eq_fopen]
  exact (continuous_F_fopen ℓ.castSucc).dotProduct
    ((continuous_col_fopen ℓ.succ j).comp continuous_fst)

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper (part 1): `W` is positively homogeneous in the row. -/
private theorem W_smul_fopen (ℓ : Fin L) (j : hid ℓ.succ)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (h : d → ℝ) {t : ℝ}
    (ht : 0 ≤ t) : W_fopen ℓ j θ (t • h) = t * W_fopen ℓ j θ h := by
  rw [W_fopen, W_fopen, blockMapRes_eq_fopen, F_smul_fopen _ _ _ ht, smul_dotProduct,
    smul_eq_mul]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (part 1): at `θ*`, `W(h) = -∑_b |h b|`, which is `< 0` for `h ≠ 0`. -/
private theorem W_star_neg_fopen (ℓ : Fin L) (j : hid ℓ.succ) (e : d ↪ hid ℓ.castSucc)
    (h : d → ℝ) (hh : h ≠ 0) :
    W_fopen ℓ j (star_fopen (T := T) (dIn := dIn) (dOut := dOut) ℓ e) h < 0 := by
  rw [W_fopen, blockMapRes_star_fopen, col_succ_star_fopen]
  simp only [dotProduct, mul_neg, mul_one, Finset.sum_neg_distrib, Left.neg_neg_iff]
  obtain ⟨b, hb⟩ := Function.ne_iff.1 hh
  exact Finset.sum_pos' (fun b _ => abs_nonneg _) ⟨b, Finset.mem_univ b, abs_pos.2 hb⟩

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper (part 1): `W < 0` on the unit sphere gives `W ≤ 0` at every row, by homogeneity. -/
private theorem W_nonpos_fopen (ℓ : Fin L) (j : hid ℓ.succ)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : ∀ h ∈ Metric.sphere (0 : d → ℝ) 1, W_fopen ℓ j θ h < 0) (h : d → ℝ) :
    W_fopen ℓ j θ h ≤ 0 := by
  by_cases hh : h = 0
  · -- `W(0) = 0 W(0) = 0`
    subst hh
    have h0 := W_smul_fopen ℓ j θ (0 : d → ℝ) (le_refl (0 : ℝ))
    rw [zero_smul, zero_mul] at h0
    exact h0.le
  · -- `h = ‖h‖ (h / ‖h‖)`, and `h / ‖h‖` is on the unit sphere
    have hn : 0 < ‖h‖ := norm_pos_iff.2 hh
    have hmem : ‖h‖⁻¹ • h ∈ Metric.sphere (0 : d → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have he : h = ‖h‖ • (‖h‖⁻¹ • h) := (smul_inv_smul₀ hn.ne' h).symm
    rw [he, W_smul_fopen ℓ j θ _ (norm_nonneg h)]
    exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (hθ _ hmem).le

/-- Helper (part 1): near `θ*`, unit `j` of block `ℓ.succ` is dead. -/
private theorem eventually_inactive_fopen (ℓ : Fin L) (j : hid ℓ.succ)
    (e : d ↪ hid ℓ.castSucc) :
    ∀ᶠ θ in 𝓝 (star_fopen (T := T) (dIn := dIn) (dOut := dOut) ℓ e),
      UnitInactiveRes θ ℓ.succ j := by
  set θs := star_fopen (T := T) (dIn := dIn) (dOut := dOut) ℓ e
  -- the tube lemma: near `θ*`, `W < 0` on the unit sphere
  have hev : ∀ᶠ θ in 𝓝 θs, ∀ h ∈ Metric.sphere (0 : d → ℝ) 1, W_fopen ℓ j θ h < 0 :=
    (isCompact_sphere 0 1).eventually_forall_of_forall_eventually fun h hh =>
      ((continuous_W_fopen ℓ j).tendsto (θs, h)).eventually_lt_const
        (W_star_neg_fopen ℓ j e h (Metric.ne_of_mem_sphere hh one_ne_zero))
  filter_upwards [hev] with θ hθ
  intro x t
  rw [read_eq_fopen]
  exact W_nonpos_fopen ℓ j θ hθ _

/-- Helper (part 2): the distance `‖c_i - c₀_i‖₁` of a read column of block `ℓ.castSucc` from its
value at `θ*`. -/
private noncomputable def dcol_fopen (ℓ : Fin L) (e : d ↪ hid ℓ.castSucc)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) (i : hid ℓ.castSucc) : ℝ :=
  ∑ a, |col_fopen ℓ.castSucc θ i a - c0_fopen e i a|

/-- Helper (part 2): the constant `K(θ)` of the estimates. -/
private noncomputable def K_fopen (ℓ : Fin L) (e : d ↪ hid ℓ.castSucc)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) : ℝ :=
  ∑ i, (dcol_fopen ℓ e θ i * ‖row_fopen ℓ.castSucc θ i‖
    + (∑ a, |c0_fopen e i a|) * ‖row_fopen ℓ.castSucc θ i - r0_fopen e i‖)

omit [Fintype T] [DecidableEq d] in
private theorem continuous_dcol_fopen (ℓ : Fin L) (e : d ↪ hid ℓ.castSucc)
    (i : hid ℓ.castSucc) :
    Continuous fun θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut =>
      dcol_fopen ℓ e θ i :=
  continuous_finsetSum _ fun a _ =>
    (((continuous_apply a).comp (continuous_col_fopen ℓ.castSucc i)).sub continuous_const).abs

omit [Fintype T] [DecidableEq d] in
private theorem continuous_K_fopen (ℓ : Fin L) (e : d ↪ hid ℓ.castSucc) :
    Continuous fun θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut =>
      K_fopen ℓ e θ := by
  have hterm : ∀ i : hid ℓ.castSucc, Continuous fun θ : Params (Arch.mlp (T := T) (d := d)
      relu id hid) dIn dOut => dcol_fopen ℓ e θ i * ‖row_fopen ℓ.castSucc θ i‖
        + (∑ a, |c0_fopen e i a|) * ‖row_fopen ℓ.castSucc θ i - r0_fopen e i‖ := by
    intro i
    have h1 : Continuous fun θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut =>
        ‖row_fopen ℓ.castSucc θ i‖ := (continuous_row_fopen ℓ.castSucc i).norm
    have h2 : Continuous fun θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut =>
        ‖row_fopen ℓ.castSucc θ i - r0_fopen e i‖ :=
      ((continuous_row_fopen ℓ.castSucc i).sub continuous_const).norm
    exact ((continuous_dcol_fopen ℓ e i).mul h1).add (continuous_const.mul h2)
  exact continuous_finsetSum _ fun i _ => hterm i

omit [Fintype T] in
/-- Helper (part 2): near `θ*`, block `ℓ.castSucc` folds. -/
private theorem eventually_folds_fopen (ℓ : Fin L) (e : d ↪ hid ℓ.castSucc) (a₀ : d) :
    ∀ᶠ θ in 𝓝 (star_fopen (T := T) (dIn := dIn) (dOut := dOut) ℓ e), Folds θ ℓ.castSucc := by
  set θs := star_fopen (T := T) (dIn := dIn) (dOut := dOut) ℓ e with hθs
  -- every read column of block `ℓ.castSucc` stays within `1/2` of its value at `θ*`
  have hE1 : ∀ i, ∀ᶠ θ in 𝓝 θs, dcol_fopen ℓ e θ i < 1 / 2 := by
    intro i
    have h0 : dcol_fopen ℓ e θs i = 0 := by
      simp only [dcol_fopen, hθs, col_star_fopen, sub_self, abs_zero, Finset.sum_const_zero]
    exact ((continuous_dcol_fopen ℓ e i).tendsto θs).eventually_lt_const
      (by rw [h0]; norm_num)
  -- the constant `K` tends to `0`
  have hE2 : ∀ᶠ θ in 𝓝 θs, K_fopen ℓ e θ < 1 / 2 := by
    have h0 : K_fopen ℓ e θs = 0 := by
      simp only [K_fopen, dcol_fopen, hθs, col_star_fopen, row_star_fopen, sub_self, abs_zero,
        Finset.sum_const_zero, zero_mul, norm_zero, mul_zero, add_zero]
    exact ((continuous_K_fopen ℓ e).tendsto θs).eventually_lt_const (by rw [h0]; norm_num)
  -- `Φ(P1) → |P1| = P1` and `Φ(P2) → |P2| = P1`
  have hP1 : blockMapRes θs ℓ.castSucc P1_fopen = P1_fopen := by
    rw [blockMapRes_star_fopen]
    funext b
    simp [P1_fopen]
  have hP2 : blockMapRes θs ℓ.castSucc (P2_fopen a₀) = P1_fopen := by
    rw [blockMapRes_star_fopen]
    funext b
    simp only [P2_fopen, P1_fopen]
    split_ifs <;> norm_num
  have hE3 : ∀ᶠ θ in 𝓝 θs, dist (blockMapRes θ ℓ.castSucc P1_fopen) P1_fopen < 1 / 8 := by
    have h := (continuous_blockMapRes_fopen ℓ.castSucc P1_fopen).tendsto θs
    rw [hP1] at h
    exact Metric.tendsto_nhds.1 h _ (by norm_num)
  have hE4 : ∀ᶠ θ in 𝓝 θs,
      dist (blockMapRes θ ℓ.castSucc (P2_fopen a₀)) P1_fopen < 1 / 8 := by
    have h := (continuous_blockMapRes_fopen ℓ.castSucc (P2_fopen a₀)).tendsto θs
    rw [hP2] at h
    exact Metric.tendsto_nhds.1 h _ (by norm_num)
  filter_upwards [Filter.eventually_all.2 hE1, hE2, hE3, hE4] with θ h1 h2 h3 h4
  rw [dist_comm, blockMapRes_eq_fopen] at h3 h4
  unfold Folds
  rw [blockMapRes_eq_fopen]
  exact not_injective_fopen e a₀ _ _ (fun i => (h1 i).le) h2.le h3.le h4.le

/-- **Proposition A.33 (i) of the skips paper:** for `d ≥ 1` and at least `d` units in block
`ℓ.castSucc`, there is a nonempty open set of weights of the residual ReLU network on which block
`ℓ.castSucc` folds and unit `j` of the next block `ℓ.succ` is dead. -/
theorem exists_isOpen_folds_unitInactiveRes_relu [Nonempty d] (ℓ : Fin L) (j : hid ℓ.succ)
    (hq : Fintype.card d ≤ Fintype.card (hid ℓ.castSucc)) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ ∀ θ ∈ U, Folds θ ℓ.castSucc ∧ UnitInactiveRes θ ℓ.succ j := by
  -- an embedding `e` of `d` into the units of block `ℓ.castSucc`, and an index `a₀`
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hq
  obtain ⟨a₀⟩ := ‹Nonempty d›
  set θs := star_fopen (T := T) (dIn := dIn) (dOut := dOut) ℓ e
  -- parts 1 and 2: near `θ*` the block folds and the unit is dead
  have hev : ∀ᶠ θ in 𝓝 θs, Folds θ ℓ.castSucc ∧ UnitInactiveRes θ ℓ.succ j :=
    (eventually_folds_fopen ℓ e a₀).and (eventually_inactive_fopen ℓ j e)
  -- the open set: the interior of the weights at which both hold
  exact ⟨interior {θ | Folds θ ℓ.castSucc ∧ UnitInactiveRes θ ℓ.succ j}, isOpen_interior,
    ⟨θs, mem_interior_iff_mem_nhds.2 hev⟩, fun θ hθ => interior_subset hθ⟩

end Skips
