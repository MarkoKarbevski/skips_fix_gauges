import SkipsLean.OneBlock.UnitsParallelAtSq
import SkipsLean.OneBlock.UnitsGeneralPosition

/-!
# ReLU² units in general position: the conditions on the weights

Paper (skips paper), proof of Theorem B.1 (iv), "The skipless network: equality. Let
`σ(z) = max(z, 0)^k` with `k = 1` or `2`, and write `h_1 = B(xE) = ∑_i σ(x c_i) a_i`, with `c_i`
the columns of `C = E W_read` and `a_i` the rows of `W_write`. The network is defined on the set
`Ω` of inputs at which some unit is active: for generic parameters `h_1 ≠ 0` there, and `h_1 = 0`
elsewhere. […] If `|S| ≥ d_model` and `k = 2`, the entries of `h_1` are `d_model` quadratic forms
in `xE`. A common zero other than `0`, real or complex, makes their resultant vanish." Then
"For generic parameters and `x_0` in an open dense set of such points, `h_1(x_0)` is not parallel
to `a_i`", "for generic parameters two entries `h_a` and `h_b` of `h_1` have no common factor",
and, in the case `ε = 0` of part (iii), "since `h_1` takes all values in an open set".

Here the conditions on `W_read` (columns `w_i`) and `W_write` (rows `a_i`) under which these hold
for a ReLU² block (`k = 2`), as one definition, `UnitsGeneralPositionSq W_read W_write`:

1. the columns `w_i` are pairwise non-collinear (also not opposite);
2. no row `a_i` is zero;
3. `∑_i max(u w_i, 0)² a_i ≠ 0` at every `u` at which a unit is active (for real `u`; the
   paper's resultant also excludes complex zeros, which the proof does not need);
4. for every unit `i` a point `u_0` of its hyperplane, on no other hyperplane, at which
   `∑_j max(u_0 w_j, 0)² a_j` is not a multiple of `a_i`;
5. for every set `S` of at least two units a line `t ↦ u + t v` and two entries `e`, `f` for
   which the polynomials `t ↦ ∑_{i∈S} ((u + t v) w_i)² a_{i e}` and the same with `f` have a
   resultant that is not zero (`quadRes`);
6. a point `u` on no hyperplane at which the derivative `v ↦ ∑_i 2 max(u w_i, 0) (v w_i) a_i` of
   the map of the block is invertible ("`h_1` takes all values in an open set").

All six hold at almost every parameter of a block of width at least `d ≥ 2`
(`OneBlock/SkiplessReluSqWideRMSZero.lean`). From them, for `E` of rank `d`, `d ≥ 2` and at
least `d` units: the hypotheses of `reluSq_unitsParallelAt_of_generic` at the columns of
`E W_read` and the rows of `W_write`, hence `UnitsParallelAt`; a nonempty open set of outputs of
the block at rows off the kinks; and the ranks of `W_read` and `W_write`.
-/

namespace Skips

open Matrix

/-- **ReLU² hidden units in general position** (the conditions "for generic parameters" of the
proof of Theorem B.1 (iv) of the skips paper, "The skipless network: equality", for `k = 2`). -/
def UnitsGeneralPositionSq {d q : Type*} [Fintype d] [DecidableEq d] [Fintype q]
    (Wr : Matrix d q ℝ) (Ww : Matrix q d ℝ) : Prop :=
  (∀ i j, i ≠ j → ∀ r : ℝ, Wrᵀ i ≠ r • Wrᵀ j) ∧
  (∀ i, Ww i ≠ 0) ∧
  (∀ u : d → ℝ, (∃ i, 0 < u ⬝ᵥ Wrᵀ i) → ∑ i, reluSq (u ⬝ᵥ Wrᵀ i) • Ww i ≠ 0) ∧
  (∀ i, ∃ u₀ : d → ℝ, u₀ ⬝ᵥ Wrᵀ i = 0 ∧ (∀ j, j ≠ i → u₀ ⬝ᵥ Wrᵀ j ≠ 0) ∧
    ∀ r : ℝ, ∑ j, reluSq (u₀ ⬝ᵥ Wrᵀ j) • Ww j ≠ r • Ww i) ∧
  (∀ S : Finset q, 2 ≤ S.card → ∃ (u v : d → ℝ) (e f : d),
    quadRes (∑ i ∈ S, (u ⬝ᵥ Wrᵀ i) ^ 2 * Ww i e)
      (2 * ∑ i ∈ S, (u ⬝ᵥ Wrᵀ i) * (v ⬝ᵥ Wrᵀ i) * Ww i e) (∑ i ∈ S, (v ⬝ᵥ Wrᵀ i) ^ 2 * Ww i e)
      (∑ i ∈ S, (u ⬝ᵥ Wrᵀ i) ^ 2 * Ww i f)
      (2 * ∑ i ∈ S, (u ⬝ᵥ Wrᵀ i) * (v ⬝ᵥ Wrᵀ i) * Ww i f)
      (∑ i ∈ S, (v ⬝ᵥ Wrᵀ i) ^ 2 * Ww i f) ≠ 0) ∧
  ∃ u : d → ℝ, (∀ i, u ⬝ᵥ Wrᵀ i ≠ 0) ∧
    IsUnit (∑ i, reluSqDeriv (u ⬝ᵥ Wrᵀ i) • Matrix.vecMulVec (Wrᵀ i) (Ww i)).det

variable {dIn d q : Type*} [Fintype dIn] [Fintype d] [DecidableEq d] [Fintype q]

omit [Fintype d] [DecidableEq d] in
/-- `∑_i s_i w_i a_i = W_read (s_i a_i)_i`. -/
private theorem sum_eq_mul_left_ugq (Wr : Matrix d q ℝ) (Ww : Matrix q d ℝ) (s : q → ℝ) :
    ∑ i, s i • vecMulVec (Wrᵀ i) (Ww i) = Wr * Matrix.of (fun i b => s i * Ww i b) := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, transpose_apply,
    Matrix.mul_apply, of_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [Fintype d] [DecidableEq d] in
/-- `∑_i s_i w_i a_i = (s_i w_i)_i W_write`. -/
private theorem sum_eq_mul_right_ugq (Wr : Matrix d q ℝ) (Ww : Matrix q d ℝ) (s : q → ℝ) :
    ∑ i, s i • vecMulVec (Wrᵀ i) (Ww i) = Matrix.of (fun a i => Wr a i * s i) * Ww := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, transpose_apply,
    Matrix.mul_apply, of_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- ReLU² units in general position, `d ≥ 2`: `W_read` and `W_write` have rank `d`, and no column
of `W_read` is zero. -/
theorem rank_of_unitsGeneralPositionSq {Wr : Matrix d q ℝ} {Ww : Matrix q d ℝ}
    (hd : 2 ≤ Fintype.card d) (hG : UnitsGeneralPositionSq Wr Ww) :
    Wr.rank = Fintype.card d ∧ Ww.rank = Fintype.card d ∧ ∀ i, (fun a => Wr a i) ≠ 0 := by
  -- clause 6: `M = ∑_i 2 max(u w_i, 0) w_i a_i` is invertible, so it has rank `d`
  obtain ⟨u, -, hdet⟩ := hG.2.2.2.2.2
  have hr := rank_of_isUnit _ ((isUnit_iff_isUnit_det _).2 hdet)
  -- `M = W_read N = N' W_write`
  have h1 := rank_mul_le_left Wr (Matrix.of fun i b => reluSqDeriv (u ⬝ᵥ Wrᵀ i) * Ww i b)
  have h2 := rank_mul_le_right (Matrix.of fun a i => Wr a i * reluSqDeriv (u ⬝ᵥ Wrᵀ i)) Ww
  rw [← sum_eq_mul_left_ugq, hr] at h1
  rw [← sum_eq_mul_right_ugq, hr] at h2
  have hWr : Wr.rank = Fintype.card d := le_antisymm (rank_le_card_height Wr) h1
  -- at least `d ≥ 2` units, so two units, and clause 1 excludes a zero column
  have hq2 : 1 < Fintype.card q := by
    have := rank_le_card_width Wr
    omega
  refine ⟨hWr, le_antisymm (rank_le_card_width Ww) h2, fun l h0 => ?_⟩
  obtain ⟨m, hm⟩ := Fintype.exists_ne_of_one_lt_card hq2 l
  refine hG.1 l m hm.symm 0 ?_
  rw [zero_smul]
  funext a
  exact congrFun h0 a

omit [DecidableEq d] [Fintype q] in
/-- `x · c_i = (x E) · w_i` for the columns `c_i` of `E W_read`. -/
private theorem dot_c_ugq (E : Matrix dIn d ℝ) (Wr : Matrix d q ℝ) (x : dIn → ℝ) (i : q) :
    x ⬝ᵥ (E * Wr)ᵀ i = (x ᵥ* E) ⬝ᵥ Wrᵀ i :=
  (congrFun (vecMul_vecMul x E Wr) i).symm

/-- **"The kinks stay" and "One scale" for a ReLU² block whose units are in general position:**
for `E` of rank `d ≥ 2`, `UnitsParallelAt` holds at the columns `c_i` of `E W_read` and the rows
`a_i` of `W_write`. -/
theorem reluSq_unitsParallelAt_of_unitsGeneralPositionSq (E : Matrix dIn d ℝ)
    {Wr : Matrix d q ℝ} {Ww : Matrix q d ℝ} (hd : 2 ≤ Fintype.card d)
    (hE : E.rank = Fintype.card d) (hG : UnitsGeneralPositionSq Wr Ww) :
    UnitsParallelAt reluSq reluSqDeriv 2 (fun i => (E * Wr)ᵀ i) (fun i => Ww i) := by
  -- `x ↦ x E` is onto (`E` has rank `d`), and `x · c_i = (x E) · w_i`
  have hsurj : Function.Surjective fun x : dIn → ℝ => x ᵥ* E :=
    vecMul_surjective_iff_rank_eq_card.2 hE
  refine reluSq_unitsParallelAt_of_generic _ _ (fun i j hij r h => ?_) (fun i => hG.2.1 i)
    (fun x hx => ?_) (fun i => ?_) (fun S hS => ?_)
  · -- the columns `c_i` are pairwise non-collinear: `E` is injective (clause 1)
    refine hG.1 i j hij r (dotProduct_eq _ _ fun u => ?_)
    obtain ⟨x, hx⟩ := hsurj u
    have hx' : x ᵥ* E = u := hx
    have h1 := congrArg (fun c => x ⬝ᵥ c) h
    simp only [dotProduct_smul, dot_c_ugq, hx'] at h1
    rw [dotProduct_comm, h1, dotProduct_comm, smul_dotProduct]
  · -- `h_1 ≠ 0` where a unit is active (clause 3 at `u = x E`)
    simp only [dot_c_ugq] at hx ⊢
    exact hG.2.2.1 _ hx
  · -- "the kinks stay" (clause 4 at a preimage `x₀` of `u₀`)
    obtain ⟨u₀, h1, h2, h3⟩ := hG.2.2.2.1 i
    obtain ⟨x₀, hx₀⟩ := hsurj u₀
    have hx₀' : x₀ ᵥ* E = u₀ := hx₀
    refine ⟨x₀, ?_⟩
    simp only [dot_c_ugq, hx₀']
    exact ⟨h1, h2, h3⟩
  · -- two entries without a common factor (clause 5 at preimages `x`, `y` of `u`, `v`)
    obtain ⟨u, v, e, f, h⟩ := hG.2.2.2.2.1 S hS
    obtain ⟨x, hx⟩ := hsurj u
    obtain ⟨y, hy⟩ := hsurj v
    have hx' : x ᵥ* E = u := hx
    have hy' : y ᵥ* E = v := hy
    refine ⟨x, y, e, f, ?_⟩
    simp only [dot_c_ugq, hx', hy']
    exact h

/-- ReLU² has a strict derivative off its kink. -/
private theorem hasStrictDerivAt_reluSq_ugq {z : ℝ} (hz : z ≠ 0) :
    HasStrictDerivAt reluSq (reluSqDeriv z) z := by
  rcases hz.lt_or_gt with hneg | hpos
  · -- near `z < 0`, `reluSq` is the constant `0`
    have hd : reluSqDeriv z = 0 := by rw [reluSqDeriv, max_eq_right hneg.le, mul_zero]
    rw [hd]
    refine (hasStrictDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_lt_nhds hneg] with y hy
    show 0 = max y 0 ^ 2
    rw [max_eq_right hy.le]; norm_num
  · -- near `z > 0`, `reluSq` is the square
    refine ((hasStrictDerivAt_pow 2 z).congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [eventually_gt_nhds hpos] with y hy
      show y ^ 2 = max y 0 ^ 2
      rw [max_eq_left hy.le]
    · rw [reluSqDeriv, max_eq_left hpos.le]; norm_num

/-- The linear form `u ↦ u · w`. -/
private noncomputable def dotCLM_ugq (w : d → ℝ) : (d → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => u ⬝ᵥ w
      map_add' := fun u v => add_dotProduct u v w
      map_smul' := fun r u => smul_dotProduct r u w }

omit [DecidableEq d] in
private theorem dotCLM_ugq_apply (w u : d → ℝ) : dotCLM_ugq w u = u ⬝ᵥ w := rfl

omit [DecidableEq d] in
/-- **The derivative of the block's map** `g(u) = ∑_i max(u w_i, 0)² a_i` at a point `u₁` on no
hyperplane: `v ↦ ∑_i 2 max(u₁ w_i, 0) (v w_i) a_i`. -/
private theorem hasStrictFDerivAt_g_ugq (Wr : Matrix d q ℝ) (Ww : Matrix q d ℝ) (u₁ : d → ℝ)
    (hu₁ : ∀ i, u₁ ⬝ᵥ Wrᵀ i ≠ 0) :
    HasStrictFDerivAt (fun u : d → ℝ => ∑ i, reluSq (u ⬝ᵥ Wrᵀ i) • Ww i)
      (∑ i, (reluSqDeriv (u₁ ⬝ᵥ Wrᵀ i) • dotCLM_ugq (Wrᵀ i)).smulRight (Ww i)) u₁ := by
  have h : ∀ i ∈ (Finset.univ : Finset q), HasStrictFDerivAt
      (fun u : d → ℝ => reluSq (u ⬝ᵥ Wrᵀ i) • Ww i)
      ((reluSqDeriv (u₁ ⬝ᵥ Wrᵀ i) • dotCLM_ugq (Wrᵀ i)).smulRight (Ww i)) u₁ := fun i _ => by
    have h1 := ((hasStrictDerivAt_reluSq_ugq (hu₁ i)).comp_hasStrictFDerivAt u₁
      (dotCLM_ugq (Wrᵀ i)).hasStrictFDerivAt).smul_const (Ww i)
    exact h1
  exact HasStrictFDerivAt.fun_sum h

/-- **"`h_1` takes all values in an open set", for a ReLU² block whose units are in general
position:** for `E` of rank `d`, the outputs `∑_i max(x c_i, 0)² a_i` of the block at the rows `x`
on no hyperplane `x c_i = 0` contain a nonempty open set. -/
theorem exists_open_reluSq_of_unitsGeneralPositionSq (E : Matrix dIn d ℝ) {Wr : Matrix d q ℝ}
    {Ww : Matrix q d ℝ} (hE : E.rank = Fintype.card d) (hG : UnitsGeneralPositionSq Wr Ww) :
    ∃ O : Set (d → ℝ), IsOpen O ∧ O.Nonempty ∧ ∀ v ∈ O, ∃ x : dIn → ℝ,
      (∀ i, x ⬝ᵥ (E * Wr)ᵀ i ≠ 0) ∧ ∑ i, reluSq (x ⬝ᵥ (E * Wr)ᵀ i) • Ww i = v := by
  have hsurj : Function.Surjective fun x : dIn → ℝ => x ᵥ* E :=
    vecMul_surjective_iff_rank_eq_card.2 hE
  -- clause 6: a point `u₁` on no hyperplane at which the derivative `v ↦ v M` is invertible
  obtain ⟨u₁, hu₁, hdet⟩ := hG.2.2.2.2.2
  obtain ⟨M, hMdef⟩ : ∃ M, M = ∑ i, reluSqDeriv (u₁ ⬝ᵥ Wrᵀ i) • vecMulVec (Wrᵀ i) (Ww i) :=
    ⟨_, rfl⟩
  rw [← hMdef] at hdet
  have hg := hasStrictFDerivAt_g_ugq Wr Ww u₁ hu₁
  -- the derivative is `v ↦ v M`, onto
  have hD : ∀ v : d → ℝ,
      (∑ i, (reluSqDeriv (u₁ ⬝ᵥ Wrᵀ i) • dotCLM_ugq (Wrᵀ i)).smulRight (Ww i)) v = v ᵥ* M := by
    intro v
    rw [hMdef, vecMul_sum, _root_.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.smulRight_apply, _root_.smul_apply, dotCLM_ugq_apply, vecMul_smul,
      vecMul_vecMulVec, smul_eq_mul, smul_smul]
  have hrange : (∑ i, (reluSqDeriv (u₁ ⬝ᵥ Wrᵀ i) • dotCLM_ugq (Wrᵀ i)).smulRight (Ww i)).range
      = ⊤ := by
    refine LinearMap.range_eq_top.2 fun y => ⟨y ᵥ* M⁻¹, (hD _).trans ?_⟩
    rw [vecMul_vecMul, nonsing_inv_mul _ hdet, vecMul_one]
  -- inverse function theorem: the image of a neighbourhood of `u₁` is a neighbourhood of `g u₁`
  have hmap := hg.map_nhds_eq_of_surj hrange
  have hU : (⋂ i, {u : d → ℝ | u ⬝ᵥ Wrᵀ i ≠ 0}) ∈ nhds u₁ :=
    (isOpen_iInter_of_finite fun i => isOpen_ne_fun
      (continuous_id.dotProduct continuous_const) continuous_const).mem_nhds
      (Set.mem_iInter.2 hu₁)
  have himg := Filter.image_mem_map
    (m := fun u : d → ℝ => ∑ i, reluSq (u ⬝ᵥ Wrᵀ i) • Ww i) hU
  rw [hmap] at himg
  refine ⟨interior _, isOpen_interior, ⟨_, mem_interior_iff_mem_nhds.2 himg⟩, fun v hv => ?_⟩
  obtain ⟨u, huU, rfl⟩ := interior_subset hv
  obtain ⟨x, hx⟩ := hsurj u
  have hx' : x ᵥ* E = u := hx
  refine ⟨x, fun i => ?_, ?_⟩
  · rw [dot_c_ugq, hx']
    exact Set.mem_iInter.1 huU i
  · simp only [dot_c_ugq, hx']

end Skips
