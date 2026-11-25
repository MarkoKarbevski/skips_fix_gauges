import SkipsLean.OneBlock.UnitsParallelAt

/-!
# Hidden units in general position, and what follows for a ReLU block of width at least `d`

Paper (skips paper), proof of Theorem B.1 (iv), "The skipless network: equality": "The network is
defined on the set `Ω` of inputs at which some unit is active: for generic parameters `h_1 ≠ 0`
there, and `h_1 = 0` elsewhere. Indeed, let `S` be the set of units active at `x`, and let `w_i`
be the columns of `W_read`. If `|S| < d_model`, the rows `a_i`, `i ∈ S`, are linearly independent.
If `|S| ≥ d_model` and `k = 1`, `h_1 = x E ∑_{i∈S} w_i a_i`, and this `d_model × d_model` matrix
is invertible." Then "For generic parameters and `x_0` in an open dense set of such points,
`h_1(x_0)` is not parallel to `a_i`", "for generic parameters two entries `h_a` and `h_b` of `h_1`
have no common factor", and "the `c_i` are pairwise non-collinear".

Here the conditions on `W_read` (columns `w_i`) and `W_write` (rows `a_i`) under which these hold
for a ReLU block (`k = 1`), as one definition, `UnitsGeneralPosition W_read W_write`:

1. the columns `w_i` are pairwise non-collinear (also not opposite);
2. any at most `d` of the rows `a_i` are linearly independent;
3. for every set `S` of at least `d` units the `d × d` matrix `M_S = ∑_{i∈S} w_i a_i` is
   invertible;
4. for every such `S` and every unit `i` outside it, `(a_i M_S⁻¹) · w_i ≠ 0` (then no nonzero
   point `u` of the hyperplane `u · w_i = 0` has `u M_S` parallel to `a_i`; the paper's "`x_0` in
   an open dense set", which for `d_model = 2` is a condition on the parameters).

All four hold at almost every parameter of a block of width at least `d ≥ 2`
(`OneBlock/SkiplessReluWideRMSZero.lean`). From them, for `E` of rank `d`, `d ≥ 2` and at
least `d` units: the hypotheses of `relu_unitsParallelAt_of_generic` at the columns of
`E W_read` and the rows of `W_write`, hence `UnitsParallelAt`; a nonempty open set of outputs of
the block at rows off the kinks; and the ranks of `W_read` and `W_write`.
-/

namespace Skips

open Matrix

/-- **Hidden units in general position** (the conditions "for generic parameters" of the proof
of Theorem B.1 (iv) of the skips paper, "The skipless network: equality", for `k = 1`): the
columns `w_i` of `W_read` are pairwise non-collinear; any at most `d` rows `a_i` of `W_write` are
linearly independent; for every set `S` of at least `d` units, `M_S = ∑_{i∈S} w_i a_i` is
invertible, and `(a_i M_S⁻¹) · w_i ≠ 0` for every unit `i` outside `S`. -/
def UnitsGeneralPosition {d q : Type*} [Fintype d] [DecidableEq d] (Wr : Matrix d q ℝ)
    (Ww : Matrix q d ℝ) : Prop :=
  (∀ i j, i ≠ j → ∀ r : ℝ, Wrᵀ i ≠ r • Wrᵀ j) ∧
  (∀ S : Finset q, S.card ≤ Fintype.card d → LinearIndependent ℝ fun i : S => Ww i) ∧
  (∀ S : Finset q, Fintype.card d ≤ S.card →
    IsUnit (∑ i ∈ S, Matrix.vecMulVec (Wrᵀ i) (Ww i)).det) ∧
  ∀ (i : q) (S : Finset q), i ∉ S → Fintype.card d ≤ S.card →
    (Ww i ᵥ* (∑ j ∈ S, Matrix.vecMulVec (Wrᵀ j) (Ww j))⁻¹) ⬝ᵥ Wrᵀ i ≠ 0

variable {dIn d q : Type*} [Fintype dIn] [Fintype d] [DecidableEq d] [Fintype q]

omit [Fintype d] [DecidableEq d] in
/-- `∑_i w_i a_i = W_read W_write`. -/
private theorem sum_vecMulVec_ugp (Wr : Matrix d q ℝ) (Ww : Matrix q d ℝ) :
    ∑ i, vecMulVec (Wrᵀ i) (Ww i) = Wr * Ww := by
  ext a b
  simp only [Matrix.sum_apply, vecMulVec_apply, transpose_apply, Matrix.mul_apply]

/-- A column `w_l` of `W_read` is not zero (two units, pairwise non-collinear columns). -/
private theorem col_ne_zero_ugp {Wr : Matrix d q ℝ} {Ww : Matrix q d ℝ}
    (hq2 : 1 < Fintype.card q) (hG : UnitsGeneralPosition Wr Ww) (l : q) : Wrᵀ l ≠ 0 := by
  obtain ⟨m, hm⟩ := Fintype.exists_ne_of_one_lt_card hq2 l
  exact fun h0 => hG.1 l m hm.symm 0 (by rw [h0, zero_smul])

/-- **In general position, `W_read` and `W_write` have rank `d` and no column of `W_read` is
zero** (at least `d ≥ 2` units): `W_read W_write = M_S` for `S` the set of all units. -/
theorem rank_of_unitsGeneralPosition {Wr : Matrix d q ℝ} {Ww : Matrix q d ℝ}
    (hd : 2 ≤ Fintype.card d) (hq : Fintype.card d ≤ Fintype.card q)
    (hG : UnitsGeneralPosition Wr Ww) :
    Wr.rank = Fintype.card d ∧ Ww.rank = Fintype.card d ∧ ∀ i, (fun a => Wr a i) ≠ 0 := by
  -- `W_read W_write = M_S` for `S` the set of all units: invertible (clause 3)
  have hM : IsUnit (Wr * Ww) := by
    have h := hG.2.2.1 Finset.univ (by rw [Finset.card_univ]; exact hq)
    rw [sum_vecMulVec_ugp] at h
    exact (isUnit_iff_isUnit_det _).2 h
  have hr := rank_of_isUnit _ hM
  refine ⟨le_antisymm (rank_le_card_height Wr) (hr.symm.le.trans (rank_mul_le_left Wr Ww)),
    le_antisymm (rank_le_card_width Ww) (hr.symm.le.trans (rank_mul_le_right Wr Ww)),
    fun i h0 => col_ne_zero_ugp (by omega) hG i ?_⟩
  -- a column of `W_read` is zero
  funext a
  exact congrFun h0 a

omit [DecidableEq d] [Fintype q] in
/-- `x · c_i = (x E) · w_i` for the columns `c_i` of `E W_read`. -/
private theorem dot_c_ugp (E : Matrix dIn d ℝ) (Wr : Matrix d q ℝ) (x : dIn → ℝ) (i : q) :
    x ⬝ᵥ (E * Wr)ᵀ i = (x ᵥ* E) ⬝ᵥ Wrᵀ i :=
  (congrFun (vecMul_vecMul x E Wr) i).symm

omit [Fintype d] [DecidableEq d] in
/-- The ReLU output keeps the strictly active units: `∑_i max(z_i, 0) a_i = ∑_{z_i > 0} z_i a_i`. -/
private theorem relu_sum_ugp (z : q → ℝ) (a : Matrix q d ℝ) :
    ∑ i, relu (z i) • a i = ∑ i ∈ Finset.univ.filter (fun i => 0 < z i), z i • a i := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : 0 < z i
  · simp only [relu, max_eq_left h.le, h, ite_true]
  · simp only [relu, max_eq_right (not_lt.1 h), zero_smul, h, ite_false]

omit [Fintype d] [DecidableEq d] in
/-- `∑_i 1[z_i > 0] t_i a_i = ∑_{z_i > 0} t_i a_i`. -/
private theorem reluDeriv_sum_ugp (z t : q → ℝ) (a : Matrix q d ℝ) :
    ∑ i, (reluDeriv (z i) * t i) • a i
      = ∑ i ∈ Finset.univ.filter (fun i => 0 < z i), t i • a i := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : 0 < z i
  · simp only [reluDeriv, h, ite_true, one_mul]
  · simp only [reluDeriv, h, ite_false, zero_mul, zero_smul]

omit [DecidableEq d] [Fintype q] in
/-- `v M_S = ∑_{l∈S} (v · w_l) a_l`. -/
private theorem vecMul_M_ugp (Wr : Matrix d q ℝ) (Ww : Matrix q d ℝ) (S : Finset q)
    (v : d → ℝ) :
    v ᵥ* ∑ l ∈ S, vecMulVec (Wrᵀ l) (Ww l) = ∑ l ∈ S, (v ⬝ᵥ Wrᵀ l) • Ww l := by
  rw [vecMul_sum]
  exact Finset.sum_congr rfl fun l _ => vecMul_vecMulVec _ _ _

omit [Fintype d] [DecidableEq d] [Fintype q] in
/-- Independent rows: equal combinations have equal coefficients. -/
private theorem li_coeff_ugp {Ww : Matrix q d ℝ} {S : Finset q}
    (hli : LinearIndependent ℝ fun i : S => Ww i) (g g' : q → ℝ)
    (h : ∑ l ∈ S, g l • Ww l = ∑ l ∈ S, g' l • Ww l) : ∀ l ∈ S, g l = g' l := by
  have h0 : ∑ l : S, (g l - g' l) • Ww l = 0 := by
    rw [Finset.sum_coe_sort S (fun l => (g l - g' l) • Ww l)]
    simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  intro l hl
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli (fun l : S => g l - g' l) h0 ⟨l, hl⟩)

omit [Fintype q] in
/-- **The coefficients on a set of units are determined by the output** (clause 2 for at most
`d` units, clause 3 for at least `d`): if `∑_{l∈S} (v · w_l) a_l = ∑_{l∈S} (v' · w_l) a_l`,
then `v · w_l = v' · w_l` for every `l ∈ S`. -/
private theorem coeff_eq_ugp {Wr : Matrix d q ℝ} {Ww : Matrix q d ℝ}
    (hG : UnitsGeneralPosition Wr Ww) (S : Finset q) (v v' : d → ℝ)
    (h : ∑ l ∈ S, (v ⬝ᵥ Wrᵀ l) • Ww l = ∑ l ∈ S, (v' ⬝ᵥ Wrᵀ l) • Ww l) :
    ∀ l ∈ S, v ⬝ᵥ Wrᵀ l = v' ⬝ᵥ Wrᵀ l := by
  rcases le_total S.card (Fintype.card d) with hS | hS
  · -- at most `d` units: the rows `a_l`, `l ∈ S`, are independent
    exact li_coeff_ugp (hG.2.1 S hS) _ _ h
  · -- at least `d` units: `v M_S = v' M_S` with `M_S` invertible
    obtain ⟨M, hMdef⟩ : ∃ M, M = ∑ l ∈ S, vecMulVec (Wrᵀ l) (Ww l) := ⟨_, rfl⟩
    have hM : IsUnit M.det := hMdef ▸ hG.2.2.1 S hS
    rw [← vecMul_M_ugp Wr Ww S v, ← vecMul_M_ugp Wr Ww S v', ← hMdef] at h
    have hv : v = v' := by
      calc v = v ᵥ* M ᵥ* M⁻¹ := by rw [vecMul_vecMul, mul_nonsing_inv _ hM, vecMul_one]
        _ = v' ᵥ* M ᵥ* M⁻¹ := by rw [h]
        _ = v' := by rw [vecMul_vecMul, mul_nonsing_inv _ hM, vecMul_one]
    intro l _
    rw [hv]

/-- **`h_1 ≠ 0` where a unit is active.** -/
private theorem ne_zero_ugp {Wr : Matrix d q ℝ} {Ww : Matrix q d ℝ}
    (hG : UnitsGeneralPosition Wr Ww) (u : d → ℝ) (hu : ∃ i, 0 < u ⬝ᵥ Wrᵀ i) :
    ∑ i, relu (u ⬝ᵥ Wrᵀ i) • Ww i ≠ 0 := by
  obtain ⟨i, hi⟩ := hu
  rw [relu_sum_ugp]
  intro h0
  have h1 : ∑ l ∈ Finset.univ.filter (fun l => 0 < u ⬝ᵥ Wrᵀ l), (u ⬝ᵥ Wrᵀ l) • Ww l
      = ∑ l ∈ Finset.univ.filter (fun l => 0 < u ⬝ᵥ Wrᵀ l), ((0 : d → ℝ) ⬝ᵥ Wrᵀ l) • Ww l := by
    rw [h0]
    simp only [zero_dotProduct, zero_smul, Finset.sum_const_zero]
  have h2 := coeff_eq_ugp hG _ u 0 h1 i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
  rw [zero_dotProduct] at h2
  exact hi.ne' h2

omit [DecidableEq d] in
/-- Two non-collinear vectors `w`, `w'` (`w' ≠ 0`): some `u` has `u · w = 1`, `u · w' = 0`
(`u` along the component of `w` orthogonal to `w'`). -/
private theorem exists_dual_ugp (w w' : d → ℝ) (hw' : w' ≠ 0) (h : ∀ r : ℝ, w ≠ r • w') :
    ∃ u : d → ℝ, u ⬝ᵥ w = 1 ∧ u ⬝ᵥ w' = 0 := by
  have hw'w' : w' ⬝ᵥ w' ≠ 0 := fun h0 => hw' (dotProduct_self_eq_zero.1 h0)
  obtain ⟨c, hc⟩ : ∃ c, c = (w ⬝ᵥ w') / (w' ⬝ᵥ w') := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = w - c • w' := ⟨_, rfl⟩
  have hp0 : p ≠ 0 := fun h0 => h c (sub_eq_zero.1 (hp ▸ h0))
  have hpw' : p ⬝ᵥ w' = 0 := by
    rw [hp, sub_dotProduct, smul_dotProduct, smul_eq_mul, hc, div_mul_cancel₀ _ hw'w', sub_self]
  have e : p ⬝ᵥ p = p ⬝ᵥ (w - c • w') := congrArg (fun z => p ⬝ᵥ z) hp
  rw [dotProduct_sub, dotProduct_smul, hpw', smul_zero, sub_zero] at e
  have hpw : p ⬝ᵥ w ≠ 0 := by
    rw [← e]
    exact fun h0 => hp0 (dotProduct_self_eq_zero.1 h0)
  refine ⟨(p ⬝ᵥ w)⁻¹ • p, ?_, ?_⟩
  · rw [smul_dotProduct, smul_eq_mul, inv_mul_cancel₀ hpw]
  · rw [smul_dotProduct, hpw', smul_zero]

/-- **Two active units: rank at least two.** -/
private theorem rank_two_ugp {Wr : Matrix d q ℝ} {Ww : Matrix q d ℝ}
    (hG : UnitsGeneralPosition Wr Ww) (u : d → ℝ) (i j : q) (hij : i ≠ j)
    (hi : 0 < u ⬝ᵥ Wrᵀ i) (hj : 0 < u ⬝ᵥ Wrᵀ j) :
    ∃ u' : d → ℝ, ∀ r : ℝ, ∑ l, (reluDeriv (u ⬝ᵥ Wrᵀ l) * (u' ⬝ᵥ Wrᵀ l)) • Ww l
      ≠ r • ∑ l, relu (u ⬝ᵥ Wrᵀ l) • Ww l := by
  have hwj : Wrᵀ j ≠ 0 := fun h0 => hG.1 j i hij.symm 0 (by rw [h0, zero_smul])
  -- `u' · w_i = 1`, `u' · w_j = 0`
  obtain ⟨u', h1, h0⟩ := exists_dual_ugp (Wrᵀ i) (Wrᵀ j) hwj (hG.1 i j hij)
  refine ⟨u', fun r hr => ?_⟩
  -- both sides are combinations of the `a_l` of the active units
  have hr' : ∑ l ∈ Finset.univ.filter (fun l => 0 < u ⬝ᵥ Wrᵀ l), (u' ⬝ᵥ Wrᵀ l) • Ww l
      = ∑ l ∈ Finset.univ.filter (fun l => 0 < u ⬝ᵥ Wrᵀ l), ((r • u) ⬝ᵥ Wrᵀ l) • Ww l := by
    rw [← reluDeriv_sum_ugp, hr, relu_sum_ugp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul, smul_dotProduct, smul_eq_mul]
  have hci := coeff_eq_ugp hG _ _ _ hr' i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
  have hcj := coeff_eq_ugp hG _ _ _ hr' j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
  rw [smul_dotProduct, smul_eq_mul] at hci hcj
  rw [h0] at hcj
  -- at `j`: `0 = r (u · w_j)`, so `r = 0`; at `i`: `1 = r (u · w_i) = 0`
  have hr0 : r = 0 := (mul_eq_zero.1 hcj.symm).resolve_right hj.ne'
  rw [h1, hr0, zero_mul] at hci
  exact one_ne_zero hci

omit [DecidableEq d] in
/-- The complement of a hyperplane `u · w = 0`, `w ≠ 0`, is dense. -/
private theorem dense_ne_ugp (w : d → ℝ) (hw : w ≠ 0) : Dense {u : d → ℝ | u ⬝ᵥ w ≠ 0} := by
  have hww : w ⬝ᵥ w ≠ 0 := fun h0 => hw (dotProduct_self_eq_zero.1 h0)
  intro x
  by_cases hx : x ⬝ᵥ w = 0
  · -- `x + t w`, `t ≠ 0`, is off the hyperplane and tends to `x`
    have hc : Continuous fun t : ℝ => x + t • w :=
      continuous_const.add (continuous_id.smul continuous_const)
    have ht : Filter.Tendsto (fun t : ℝ => x + t • w) (nhdsWithin 0 {0}ᶜ) (nhds x) := by
      have h := hc.tendsto 0
      simp only [zero_smul, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun t htz => ?_)
    show (x + t • w) ⬝ᵥ w ≠ 0
    rw [add_dotProduct, hx, zero_add, smul_dotProduct, smul_eq_mul]
    exact mul_ne_zero (Set.mem_compl_singleton_iff.1 htz) hww
  · exact subset_closure hx

omit [DecidableEq d] [Fintype q] in
/-- A nonempty open set meets the complement of finitely many hyperplanes `u · v_j = 0`. -/
private theorem exists_avoid_ugp (v : q → d → ℝ) (J : Finset q) (hv : ∀ j ∈ J, v j ≠ 0)
    (U : Set (d → ℝ)) (hU : IsOpen U) (hU0 : U.Nonempty) :
    ∃ u ∈ U, ∀ j ∈ J, u ⬝ᵥ v j ≠ 0 := by
  have hD : Dense (⋂ j ∈ (J : Set q), {u : d → ℝ | u ⬝ᵥ v j ≠ 0}) := by
    refine dense_biInter_of_isOpen (fun j _ => ?_) J.countable_toSet (fun j hj => ?_)
    · exact isOpen_ne_fun (continuous_id.dotProduct continuous_const) continuous_const
    · exact dense_ne_ugp (v j) (hv j hj)
  obtain ⟨u, huU, hu⟩ := hD.inter_open_nonempty U hU hU0
  exact ⟨u, huU, fun j hj => Set.mem_iInter₂.1 hu j hj⟩

omit [DecidableEq d] in
/-- A point of the hyperplane `u · w_i = 0` on no other hyperplane `u · w_j = 0` (`w_i ≠ 0`, no
`w_j` a multiple of `w_i`): the orthogonal projection onto `w_i^⊥` of a point off the
hyperplanes `u · P w_j = 0`. -/
private theorem exists_hyperplane_ugp (w : q → d → ℝ) (i : q) (hwi : w i ≠ 0)
    (hcc : ∀ j, j ≠ i → ∀ r : ℝ, w j ≠ r • w i) :
    ∃ u : d → ℝ, u ⬝ᵥ w i = 0 ∧ ∀ j, j ≠ i → u ⬝ᵥ w j ≠ 0 := by
  classical
  have hii : w i ⬝ᵥ w i ≠ 0 := fun h0 => hwi (dotProduct_self_eq_zero.1 h0)
  -- the orthogonal projection onto the hyperplane `u · w_i = 0`
  let P : (d → ℝ) → d → ℝ := fun v => v - ((v ⬝ᵥ w i) / (w i ⬝ᵥ w i)) • w i
  have hP : ∀ v, P v ⬝ᵥ w i = 0 := fun v => by
    simp only [P, sub_dotProduct, smul_dotProduct, smul_eq_mul, div_mul_cancel₀ _ hii, sub_self]
  have hPs : ∀ v v', P v ⬝ᵥ v' = v ⬝ᵥ P v' := fun v v' => by
    simp only [P, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm v' (w i)]
    ring
  obtain ⟨u, -, hu⟩ := exists_avoid_ugp (fun j => P (w j)) (Finset.univ.erase i)
    (fun j hj h0 => hcc j (Finset.ne_of_mem_erase hj) _ (sub_eq_zero.1 h0)) Set.univ isOpen_univ
    Set.univ_nonempty
  refine ⟨P u, hP u, fun j hj => ?_⟩
  rw [hPs]
  exact hu j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)

/-- **"The kinks stay"**, in the coordinates `u = x E`. -/
private theorem kink_ugp {Wr : Matrix d q ℝ} {Ww : Matrix q d ℝ}
    (hd : 2 ≤ Fintype.card d) (hq : Fintype.card d ≤ Fintype.card q)
    (hG : UnitsGeneralPosition Wr Ww) (i : q) :
    ∃ u₀ : d → ℝ, u₀ ⬝ᵥ Wrᵀ i = 0 ∧ (∀ j, j ≠ i → u₀ ⬝ᵥ Wrᵀ j ≠ 0) ∧
      ∀ r : ℝ, ∑ j, relu (u₀ ⬝ᵥ Wrᵀ j) • Ww j ≠ r • Ww i := by
  classical
  have hq2 : 1 < Fintype.card q := by omega
  obtain ⟨u₁, hu₁i, hu₁j⟩ := exists_hyperplane_ugp (fun l => Wrᵀ l) i
    (col_ne_zero_ugp hq2 hG i) (fun j hj r => hG.1 j i hj r)
  -- choose the sign so that some unit is active
  obtain ⟨u₀, hu₀i, hu₀j, k, hk⟩ : ∃ u₀ : d → ℝ, u₀ ⬝ᵥ Wrᵀ i = 0 ∧
      (∀ j, j ≠ i → u₀ ⬝ᵥ Wrᵀ j ≠ 0) ∧ ∃ k, 0 < u₀ ⬝ᵥ Wrᵀ k := by
    obtain ⟨m, hm⟩ := Fintype.exists_ne_of_one_lt_card hq2 i
    rcases (hu₁j m hm).lt_or_gt with hneg | hpos
    · refine ⟨-u₁, by rw [neg_dotProduct, hu₁i, neg_zero], fun j hj => ?_, m, ?_⟩
      · rw [neg_dotProduct, neg_ne_zero]
        exact hu₁j j hj
      · rw [neg_dotProduct]
        exact neg_pos.2 hneg
    · exact ⟨u₁, hu₁i, hu₁j, m, hpos⟩
  refine ⟨u₀, hu₀i, hu₀j, fun r hr => ?_⟩
  rw [relu_sum_ugp] at hr
  set S := Finset.univ.filter (fun l => 0 < u₀ ⬝ᵥ Wrᵀ l) with hS
  have hiS : i ∉ S := fun h => (Finset.mem_filter.1 h).2.ne' hu₀i
  have hkS : k ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
  rcases Nat.lt_or_ge S.card (Fintype.card d) with hlt | hge
  · -- `S ∪ {i}` has at most `d` units, so their rows are independent (clause 2)
    have hcard : (insert i S).card ≤ Fintype.card d := by
      rw [Finset.card_insert_of_notMem hiS]
      omega
    have hz : ∑ l ∈ S, (if l = i then r else 0) • Ww l = 0 :=
      Finset.sum_eq_zero fun l hl => by
        have hli : l ≠ i := fun h => hiS (h ▸ hl)
        simp only [hli, ite_false, zero_smul]
    have h2 : ∑ l ∈ insert i S, (u₀ ⬝ᵥ Wrᵀ l) • Ww l
        = ∑ l ∈ insert i S, (if l = i then r else 0) • Ww l := by
      rw [Finset.sum_insert hiS, Finset.sum_insert hiS, hu₀i, zero_smul, zero_add, hr, hz,
        add_zero]
      simp only [ite_true]
    have h3 := li_coeff_ugp (hG.2.1 _ hcard) _ _ h2 k (Finset.mem_insert_of_mem hkS)
    have hki : k ≠ i := fun h => hiS (h ▸ hkS)
    simp only [hki, ite_false] at h3
    exact hk.ne' h3
  · -- at least `d` units: `u₀ M_S = r a_i` gives `u₀ = r (a_i M_S⁻¹)`, and clause 4 gives `r = 0`
    obtain ⟨M, hMdef⟩ : ∃ M, M = ∑ l ∈ S, vecMulVec (Wrᵀ l) (Ww l) := ⟨_, rfl⟩
    have hM : IsUnit M.det := hMdef ▸ hG.2.2.1 S hge
    rw [← vecMul_M_ugp Wr Ww S u₀, ← hMdef] at hr
    have hu : u₀ = r • (Ww i ᵥ* M⁻¹) := by
      calc u₀ = u₀ ᵥ* M ᵥ* M⁻¹ := by rw [vecMul_vecMul, mul_nonsing_inv _ hM, vecMul_one]
        _ = r • (Ww i ᵥ* M⁻¹) := by rw [hr, smul_vecMul]
    have h4 : (Ww i ᵥ* M⁻¹) ⬝ᵥ Wrᵀ i ≠ 0 := hMdef ▸ hG.2.2.2 i S hiS hge
    have h5 : r * ((Ww i ᵥ* M⁻¹) ⬝ᵥ Wrᵀ i) = 0 := by
      rw [← smul_eq_mul, ← smul_dotProduct, ← hu, hu₀i]
    have hr0 : r = 0 := (mul_eq_zero.1 h5).resolve_right h4
    rw [hr0, zero_smul] at hu
    rw [hu, zero_dotProduct] at hk
    exact lt_irrefl 0 hk

/-- **"The kinks stay" and "One scale" for a ReLU block of width at least `d` in general
position:** for `E` of rank `d ≥ 2` and at least `d` units in general position, `UnitsParallelAt`
holds at the columns `c_i` of `E W_read` and the rows `a_i` of `W_write`. -/
theorem relu_unitsParallelAt_of_unitsGeneralPosition (E : Matrix dIn d ℝ) {Wr : Matrix d q ℝ}
    {Ww : Matrix q d ℝ} (hd : 2 ≤ Fintype.card d) (hq : Fintype.card d ≤ Fintype.card q)
    (hE : E.rank = Fintype.card d) (hG : UnitsGeneralPosition Wr Ww) :
    UnitsParallelAt relu reluDeriv 1 (fun i => (E * Wr)ᵀ i) (fun i => Ww i) := by
  -- `x ↦ x E` is onto (`E` has rank `d`), and `x · c_i = (x E) · w_i`
  have hsurj : Function.Surjective fun x : dIn → ℝ => x ᵥ* E :=
    vecMul_surjective_iff_rank_eq_card.2 hE
  refine relu_unitsParallelAt_of_generic _ _ (fun i j hij r h => ?_) (fun i => ?_)
    (fun x hx => ?_) (fun i => ?_) (fun x _ hij => ?_)
  · -- the columns `c_i` are pairwise non-collinear: `E` is injective
    refine hG.1 i j hij r (dotProduct_eq _ _ fun u => ?_)
    obtain ⟨x, hx⟩ := hsurj u
    have hx' : x ᵥ* E = u := hx
    have h1 := congrArg (fun c => x ⬝ᵥ c) h
    simp only [dotProduct_smul, dot_c_ugp, hx'] at h1
    rw [dotProduct_comm, h1, dotProduct_comm, smul_dotProduct]
  · -- `a_i ≠ 0` (clause 2 for `S = {i}`)
    exact (hG.2.1 {i} (by rw [Finset.card_singleton]; omega)).ne_zero
      ⟨i, Finset.mem_singleton_self i⟩
  · -- `h_1 ≠ 0` where a unit is active
    simp only [dot_c_ugp] at hx ⊢
    exact ne_zero_ugp hG _ hx
  · -- "the kinks stay"
    obtain ⟨u₀, h1, h2, h3⟩ := kink_ugp hd hq hG i
    obtain ⟨x₀, hx₀⟩ := hsurj u₀
    have hx₀' : x₀ ᵥ* E = u₀ := hx₀
    refine ⟨x₀, ?_⟩
    simp only [dot_c_ugp, hx₀']
    exact ⟨h1, h2, h3⟩
  · -- two active units: rank at least two
    obtain ⟨i, j, hij, hi, hj⟩ := hij
    simp only [dot_c_ugp] at hi hj ⊢
    obtain ⟨u', hu'⟩ := rank_two_ugp hG (x ᵥ* E) i j hij hi hj
    obtain ⟨y, hy⟩ := hsurj u'
    have hy' : y ᵥ* E = u' := hy
    refine ⟨y, ?_⟩
    rw [hy']
    exact hu'

/-- A point `u₁` off the hyperplanes with at least `d` active units. -/
private theorem exists_active_ugp {Wr : Matrix d q ℝ} {Ww : Matrix q d ℝ}
    (hd : 2 ≤ Fintype.card d) (hq : Fintype.card d ≤ Fintype.card q)
    (hG : UnitsGeneralPosition Wr Ww) :
    ∃ u₁ : d → ℝ, (∀ l, u₁ ⬝ᵥ Wrᵀ l ≠ 0) ∧
      Fintype.card d ≤ (Finset.univ.filter fun l => 0 < u₁ ⬝ᵥ Wrᵀ l).card := by
  obtain ⟨D, -, hD⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset q))
    (n := Fintype.card d) (by rw [Finset.card_univ]; exact hq)
  obtain ⟨M, hMdef⟩ : ∃ M, M = ∑ l ∈ D, vecMulVec (Wrᵀ l) (Ww l) := ⟨_, rfl⟩
  have hM : IsUnit M.det := hMdef ▸ hG.2.2.1 D hD.ge
  -- `u₀ = (∑_{l∈D} a_l) M_D⁻¹` has `u₀ · w_l = 1` for `l ∈ D` (clause 2 for `D`)
  have hu₀ : ∀ l ∈ D, ((∑ l ∈ D, Ww l) ᵥ* M⁻¹) ⬝ᵥ Wrᵀ l = 1 := by
    refine li_coeff_ugp (hG.2.1 D hD.le) (fun l => ((∑ l ∈ D, Ww l) ᵥ* M⁻¹) ⬝ᵥ Wrᵀ l)
      (fun _ => 1) ?_
    rw [← vecMul_M_ugp, ← hMdef, vecMul_vecMul, nonsing_inv_mul _ hM, vecMul_one]
    simp only [one_smul]
  -- the open set where the units of `D` are active meets the complement of the hyperplanes
  obtain ⟨u₁, hu₁D, hu₁⟩ := exists_avoid_ugp (fun l => Wrᵀ l) Finset.univ
    (fun l _ => col_ne_zero_ugp (by omega) hG l) (⋂ l ∈ D, {u : d → ℝ | 0 < u ⬝ᵥ Wrᵀ l})
    (isOpen_biInter_finset fun l _ => isOpen_lt continuous_const
      (continuous_id.dotProduct continuous_const))
    ⟨(∑ l ∈ D, Ww l) ᵥ* M⁻¹, Set.mem_iInter₂.2 fun l hl => by
      rw [Set.mem_ofPred_eq, hu₀ l hl]
      exact one_pos⟩
  refine ⟨u₁, fun l => hu₁ l (Finset.mem_univ l), ?_⟩
  rw [← hD]
  exact Finset.card_le_card fun l hl =>
    Finset.mem_filter.2 ⟨Finset.mem_univ l, Set.mem_iInter₂.1 hu₁D l hl⟩

/-- **"`h_1` takes all values in an open set" for a ReLU block of width at least `d` in general
position:** for `E` of rank `d ≥ 2` and at least `d` units in general position, the outputs
`∑_i max(x c_i, 0) a_i` at rows `x` off the kinks fill a nonempty open set (on a region with at
least `d` active units the output is `x E M_S` with `M_S` invertible). -/
theorem exists_open_relu_of_unitsGeneralPosition (E : Matrix dIn d ℝ) {Wr : Matrix d q ℝ}
    {Ww : Matrix q d ℝ} (hd : 2 ≤ Fintype.card d) (hq : Fintype.card d ≤ Fintype.card q)
    (hE : E.rank = Fintype.card d) (hG : UnitsGeneralPosition Wr Ww) :
    ∃ O : Set (d → ℝ), IsOpen O ∧ O.Nonempty ∧ ∀ v ∈ O, ∃ x : dIn → ℝ,
      (∀ i, x ⬝ᵥ (E * Wr)ᵀ i ≠ 0) ∧ ∑ i, relu (x ⬝ᵥ (E * Wr)ᵀ i) • Ww i = v := by
  have hsurj : Function.Surjective fun x : dIn → ℝ => x ᵥ* E :=
    vecMul_surjective_iff_rank_eq_card.2 hE
  -- a region `R` of `u = x E` with the set `S` of active units, `|S| ≥ d`, on no hyperplane
  obtain ⟨u₁, hu₁0, hu₁S⟩ := exists_active_ugp hd hq hG
  set S := Finset.univ.filter (fun l => 0 < u₁ ⬝ᵥ Wrᵀ l) with hS
  obtain ⟨M, hMdef⟩ : ∃ M, M = ∑ l ∈ S, vecMulVec (Wrᵀ l) (Ww l) := ⟨_, rfl⟩
  have hM : IsUnit M.det := hMdef ▸ hG.2.2.1 S hu₁S
  -- `O = R M_S`, the preimage of `R` under `v ↦ v M_S⁻¹`
  refine ⟨⋂ l, {v : d → ℝ | 0 < (u₁ ⬝ᵥ Wrᵀ l) * ((v ᵥ* M⁻¹) ⬝ᵥ Wrᵀ l)}, ?_, ⟨u₁ ᵥ* M, ?_⟩, ?_⟩
  · exact isOpen_iInter_of_finite fun l => isOpen_lt continuous_const
      (continuous_const.mul ((continuous_id.matrix_vecMul continuous_const).dotProduct
        continuous_const))
  · refine Set.mem_iInter.2 fun l => ?_
    show 0 < (u₁ ⬝ᵥ Wrᵀ l) * ((u₁ ᵥ* M ᵥ* M⁻¹) ⬝ᵥ Wrᵀ l)
    rw [vecMul_vecMul, mul_nonsing_inv _ hM, vecMul_one]
    exact mul_self_pos.2 (hu₁0 l)
  · intro v hv
    have hv' : ∀ l, 0 < (u₁ ⬝ᵥ Wrᵀ l) * ((v ᵥ* M⁻¹) ⬝ᵥ Wrᵀ l) := Set.mem_iInter.1 hv
    obtain ⟨x, hx⟩ := hsurj (v ᵥ* M⁻¹)
    have hx' : x ᵥ* E = v ᵥ* M⁻¹ := hx
    refine ⟨x, fun l => ?_, ?_⟩
    · rw [dot_c_ugp, hx']
      exact right_ne_zero_of_mul (hv' l).ne'
    · -- `u = v M_S⁻¹` has the active set `S`, so the output is `u M_S = v`
      simp only [dot_c_ugp, hx']
      rw [relu_sum_ugp]
      have hSS : Finset.univ.filter (fun l => 0 < (v ᵥ* M⁻¹) ⬝ᵥ Wrᵀ l) = S :=
        Finset.filter_congr fun l _ => (pos_iff_pos_of_mul_pos (hv' l)).symm
      rw [hSS, ← vecMul_M_ugp Wr Ww S, ← hMdef, vecMul_vecMul, nonsing_inv_mul _ hM, vecMul_one]

end Skips
