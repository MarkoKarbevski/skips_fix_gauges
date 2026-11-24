import SkipsLean.OneBlock.ResidualRMSZeroReGLU

/-!
# One residual ReGLU block under pre-RMSNorm with `ε = 0`: generic parameters

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`". For ReGLU
`s = 2 d_hidden`.

`OneBlock/ResidualRMSZeroReGLU.lean` has this value at one parameter under the conditions of the
proof, among them: the block turns a dense set of the rows at which some gate is active
(`TurnsActiveRowsGated`), and it turns some row off the kinks of the gates. Here: these two
conditions at almost every parameter for a ReGLU block with `d ≥ 2` (for every nonempty set `S` of
hidden units, the map `v ↦ ∑_{i ∈ S} (v g_i) (v c_i) a_i`, with `g_i` and `c_i` the gate column
and the value column of unit `i` and `a_i` its row of `W_write`, is at almost every parameter not
parallel to `v` for all `v`, and a nonzero polynomial does not vanish on an open set); and
Theorem B.1 (iv) for the residual network at almost every parameter, as the value of Lean's
`funDim` and as a batch of the paper's inputs with this rank. Twin of
`OneBlock/ResidualRMSZeroRescaleGeneric.lean` (ReLU and ReLU² blocks). No width of the block is
asked; for the batch and the value the block has at least one hidden unit.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-! ### Helpers: the polynomial `w_S` and the rows on which the block is `b_S` -/

omit [DecidableEq d] in
/-- Helper: the polynomial `w_S(u) = u_p b_S(u)_q − u_q b_S(u)_p`, with
`b_S(u) = ∑_{i ∈ S} (u g_i) (u c_i) a_i` (`g_i`, `c_i` the columns of `G`, `C`, `a_i` the rows of
`W`). -/
private def wPoly_rgq {m : Type*} [Fintype m] (S : Finset m) (p q : d)
    (G C : Matrix d m ℝ) (W : Matrix m d ℝ) (u : d → ℝ) : ℝ :=
  u p * ∑ i ∈ S, (u ᵥ* G) i * (u ᵥ* C) i * W i q
    - u q * ∑ i ∈ S, (u ᵥ* G) i * (u ᵥ* C) i * W i p

omit [Fintype d] [DecidableEq d] in
/-- Helper: two rows `x`, `y` with a nonzero minor `x_p y_q − x_q y_p` are linearly
independent. -/
private theorem linearIndependent_of_minor_rgq {x y : d → ℝ} {p q : d}
    (h : x p * y q - x q * y p ≠ 0) : LinearIndependent ℝ ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hp : s * x p + t * y p = 0 := by
    have h1 := congrFun hst p
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h1
  have hq : s * x q + t * y q = 0 := by
    have h1 := congrFun hst q
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h1
  -- Cramer's rule: `s` and `t` times the minor vanish
  have h1 : s * (x p * y q - x q * y p) = 0 := by linear_combination y q * hp - y p * hq
  have h2 : t * (x p * y q - x q * y p) = 0 := by linear_combination x p * hq - x q * hp
  exact ⟨(mul_eq_zero.1 h1).resolve_right h, (mul_eq_zero.1 h2).resolve_right h⟩

omit [DecidableEq d] in
/-- Helper: `u ↦ (u R)_i` is analytic (a linear form). -/
private theorem analyticOnNhd_vecMul_rgq {m : Type*} [Fintype m] (R : Matrix d m ℝ) (i : m) :
    AnalyticOnNhd ℝ (fun u : d → ℝ => (u ᵥ* R) i) Set.univ :=
  analyticOnNhd_linear ((LinearMap.proj i).comp (Matrix.vecMulLinear R))

omit [DecidableEq d] in
/-- Helper: `u ↦ (u R)_i` is continuous. -/
private theorem continuous_vecMul_rgq {m : Type*} [Fintype m] (R : Matrix d m ℝ) (i : m) :
    Continuous fun u : d → ℝ => (u ᵥ* R) i :=
  continuousOn_univ.mp (analyticOnNhd_vecMul_rgq R i).continuousOn

omit [DecidableEq d] in
/-- Helper: `u ↦ w_S(u)` is analytic (a polynomial in `u`). -/
private theorem analyticOnNhd_wPoly_rgq {m : Type*} [Fintype m] (S : Finset m)
    (p q : d) (G C : Matrix d m ℝ) (W : Matrix m d ℝ) :
    AnalyticOnNhd ℝ (fun u => wPoly_rgq S p q G C W u) Set.univ := by
  have hc : ∀ o : d, AnalyticOnNhd ℝ (fun u : d → ℝ => u o) Set.univ := fun o =>
    analyticOnNhd_linear (LinearMap.proj (R := ℝ) (φ := fun _ : d => ℝ) o)
  have hs : ∀ o : d, AnalyticOnNhd ℝ
      (fun u : d → ℝ => ∑ i ∈ S, (u ᵥ* G) i * (u ᵥ* C) i * W i o) Set.univ := fun o =>
    Finset.analyticOnNhd_fun_sum _ fun i _ =>
      ((analyticOnNhd_vecMul_rgq G i).mul (analyticOnNhd_vecMul_rgq C i)).mul analyticOnNhd_const
  exact ((hc p).mul (hs q)).sub ((hc q).mul (hs p))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: an entry of the read is analytic in the parameters (it is linear). -/
private theorem analyticOnNhd_read_rgq {σ : ℝ → ℝ} (j : d) (i : hid 0 ⊕ hid 0) :
    AnalyticOnNhd ℝ
      (fun θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut => θ.read 0 j i)
      Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ j i).comp
    (Params.linRead (A := Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) (dIn := dIn)
      (dOut := dOut) 0))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: an entry of the write is analytic in the parameters (it is linear). -/
private theorem analyticOnNhd_write_rgq {σ : ℝ → ℝ} (i : hid 0) (j : d) :
    AnalyticOnNhd ℝ
      (fun θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut => θ.write 0 i j)
      Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ i j).comp
    (Params.linWrite (A := Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) (dIn := dIn)
      (dOut := dOut) 0))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: at a fixed row `u`, `θ ↦ w_S(θ, u)` is analytic (a polynomial in the weights). -/
private theorem analyticOnNhd_wPoly_params_rgq {σ : ℝ → ℝ} (S : Finset (hid 0))
    (p q : d) (u : d → ℝ) :
    AnalyticOnNhd ℝ (fun θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
      wPoly_rgq S p q ((θ.read 0).submatrix id Sum.inl) ((θ.read 0).submatrix id Sum.inr)
        (θ.write 0) u) Set.univ := by
  have hv : ∀ x : hid 0 ⊕ hid 0, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        (u ᵥ* θ.read 0) x) Set.univ := fun x =>
    Finset.analyticOnNhd_fun_sum _ fun j _ =>
      analyticOnNhd_const.mul (analyticOnNhd_read_rgq j x)
  have hs : ∀ o : d, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        ∑ i ∈ S, (u ᵥ* θ.read 0) (Sum.inl i) * (u ᵥ* θ.read 0) (Sum.inr i) * θ.write 0 i o)
      Set.univ := fun o =>
    Finset.analyticOnNhd_fun_sum _ fun i _ =>
      ((hv (Sum.inl i)).mul (hv (Sum.inr i))).mul (analyticOnNhd_write_rgq i o)
  exact (analyticOnNhd_const.mul (hs q)).sub (analyticOnNhd_const.mul (hs p))

omit [Fintype T] [Nonempty T] in
/-- Helper: at almost every parameter, `w_S(θ, 1) ≠ 0` for every nonempty set `S` of hidden
units: it is a polynomial in `θ`, equal to `−|S|` at the weights with `g_i = c_i = e_p`,
`a_i = e_p`. -/
private theorem ae_wPoly_ne_zero_rgq {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] {p q : d} (hpq : p ≠ q) :
    ∀ᵐ θ ∂μ, ∀ S : Finset (hid 0), S.Nonempty →
      wPoly_rgq S p q ((θ.read 0).submatrix id Sum.inl) ((θ.read 0).submatrix id Sum.inr)
        (θ.write 0) (fun _ => 1) ≠ 0 := by
  -- finitely many sets `S`: one at a time
  refine ae_all_iff.2 fun S => ?_
  by_cases hS : S.Nonempty
  · -- the weights with `g_i = c_i = e_p` and `a_i = e_p` for every unit: `b_S(1) = |S| e_p`
    let θ₀ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut :=
      ⟨0, fun _ => Matrix.of fun j _ => if j = p then 1 else 0,
        fun _ => Matrix.of fun _ j => if j = p then 1 else 0, 0⟩
    have h1 : ∀ x : hid 0 ⊕ hid 0, ((fun _ => (1 : ℝ)) ᵥ* θ₀.read 0) x = 1 := fun x => by
      simp [θ₀, Matrix.vecMul, dotProduct]
    have h0 : wPoly_rgq S p q ((θ₀.read 0).submatrix id Sum.inl)
        ((θ₀.read 0).submatrix id Sum.inr) (θ₀.write 0) (fun _ => 1) = -(S.card : ℝ) := by
      have hg : ∀ i, ((fun _ => (1 : ℝ)) ᵥ* (θ₀.read 0).submatrix id Sum.inl) i = 1 :=
        fun i => h1 (Sum.inl i)
      have hc : ∀ i, ((fun _ => (1 : ℝ)) ᵥ* (θ₀.read 0).submatrix id Sum.inr) i = 1 :=
        fun i => h1 (Sum.inr i)
      simp only [wPoly_rgq, hg, hc]
      simp [θ₀, hpq.symm]
    have hne : wPoly_rgq S p q ((θ₀.read 0).submatrix id Sum.inl)
        ((θ₀.read 0).submatrix id Sum.inr) (θ₀.write 0) (fun _ => 1) ≠ 0 := by
      rw [h0]
      exact neg_ne_zero.2 (Nat.cast_ne_zero.2 hS.card_pos.ne')
    -- a polynomial that is not identically zero is nonzero at almost every `θ`
    exact (ae_ne_zero_of_analytic μ (analyticOnNhd_wPoly_params_rgq S p q _)
      ⟨θ₀, hne⟩).mono fun _ h _ => h
  · exact Filter.Eventually.of_forall fun _ h => absurd h hS

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: at almost every parameter, the entries of the gate columns of the read at the
coordinate `p` are nonzero, so no gate column of the read is zero. -/
private theorem ae_read_ne_zero_rgq {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (p : d) :
    ∀ᵐ θ ∂μ, ∀ i : hid 0, θ.read 0 p (Sum.inl i) ≠ 0 := by
  -- the parameters with all entries `1`
  let θ₁ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1,
      Matrix.of fun _ _ => 1⟩
  exact ae_all_iff.2 fun i =>
    ae_ne_zero_of_analytic μ (analyticOnNhd_read_rgq p (Sum.inl i))
      ⟨θ₁, show (1 : ℝ) ≠ 0 from one_ne_zero⟩

/-- Helper: ReLU is the identity on the positive reals. -/
private theorem relu_pos_rgq (z : ℝ) (hz : 0 < z) : relu z = z := by
  rw [relu, max_eq_left hz.le]

/-- Helper: ReLU vanishes on the nonpositive reals. -/
private theorem relu_nonpos_rgq (z : ℝ) (hz : z ≤ 0) : relu z = 0 := by
  rw [relu, max_eq_right hz]

omit [DecidableEq d] in
/-- Helper (the condition at one parameter): if `w_S(1) ≠ 0` for every nonempty `S`, then every
row `v` off the kinks of the gates with an active gate is a limit of rows `u` such that `u` and
`B(u)` are linearly independent. -/
private theorem mem_closure_of_wPoly_rgq {m : Type*} [Fintype m] {p q : d}
    (G C : Matrix d m ℝ) (W : Matrix m d ℝ)
    (hS : ∀ S : Finset m, S.Nonempty → wPoly_rgq S p q G C W (fun _ => 1) ≠ 0)
    (v : d → ℝ) (hv : ∀ i, (v ᵥ* G) i ≠ 0) (hact : ∃ i, relu ((v ᵥ* G) i) ≠ 0) :
    v ∈ closure {u : d → ℝ | LinearIndependent ℝ ![u, gatedBlock relu G C W u]} := by
  classical
  -- the set `S` of the units whose gate is active at `v`; it is nonempty
  obtain ⟨S, hSdef⟩ : ∃ S : Finset m, S = Finset.univ.filter fun i => 0 < (v ᵥ* G) i :=
    ⟨_, rfl⟩
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hact
    refine ⟨i, hSdef ▸ Finset.mem_filter.2 ⟨Finset.mem_univ i, ?_⟩⟩
    by_contra h
    exact hi (relu_nonpos_rgq _ (not_lt.1 h))
  -- the rows `u` with the signs of the gates of `v` form a neighbourhood of `v`
  have hO : ∀ᶠ u in nhds v, ∀ i, 0 < (v ᵥ* G) i * (u ᵥ* G) i := by
    refine Filter.eventually_all.2 fun i => ?_
    have hc : Continuous fun u : d → ℝ => (v ᵥ* G) i * (u ᵥ* G) i :=
      continuous_const.mul (continuous_vecMul_rgq G i)
    exact Filter.Tendsto.eventually_const_lt (mul_self_pos.2 (hv i)) (hc.tendsto v)
  -- on these rows the block is `b_S`, so `w_S(u) ≠ 0` makes `u`, `B(u)` independent
  have hLI : ∀ u : d → ℝ, (∀ i, 0 < (v ᵥ* G) i * (u ᵥ* G) i) → wPoly_rgq S p q G C W u ≠ 0 →
      LinearIndependent ℝ ![u, gatedBlock relu G C W u] := by
    intro u hu hw
    have hb : ∀ o, gatedBlock relu G C W u o = ∑ i ∈ S, (u ᵥ* G) i * (u ᵥ* C) i * W i o := by
      intro o
      show ∑ i, relu ((u ᵥ* G) i) * (u ᵥ* C) i * W i o = _
      rw [hSdef, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · rw [relu_pos_rgq _ ((pos_iff_pos_of_mul_pos (hu i)).1 h)]
      · have hneg : (v ᵥ* G) i < 0 := lt_of_le_of_ne (not_lt.1 h) (hv i)
        rw [relu_nonpos_rgq _ ((neg_iff_neg_of_mul_pos (hu i)).1 hneg).le, zero_mul, zero_mul]
    apply linearIndependent_of_minor_rgq (p := p) (q := q)
    rw [hb p, hb q]
    exact hw
  rw [mem_closure_iff_nhds]
  intro t ht
  by_contra hne
  -- otherwise `w_S` vanishes near `v`, hence everywhere (identity theorem), also at `1`
  have hz : (fun u => wPoly_rgq S p q G C W u) =ᶠ[nhds v] 0 := by
    filter_upwards [ht, hO] with u hut hu
    by_contra hw
    exact hne ⟨u, hut, hLI u hu hw⟩
  have h0 := (analyticOnNhd_wPoly_rgq S p q G C W).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ v) hz
  exact hS S hSne (h0 (Set.mem_univ _))

/-- Helper (some row off the kinks is turned): if no gate column is zero and every row off the
kinks with an active gate is a limit of turned rows, then some row off the kinks and the output of
the block there are linearly independent. -/
private theorem exists_turned_of_closure_rgq {m : Type*} [Fintype m] [Nonempty m] (p : d)
    (G C : Matrix d m ℝ) (W : Matrix m d ℝ) (hR : ∀ i, G p i ≠ 0)
    (hturn : ∀ v : d → ℝ, (∀ i, (v ᵥ* G) i ≠ 0) → (∃ i, relu ((v ᵥ* G) i) ≠ 0) →
      v ∈ closure {u : d → ℝ | LinearIndependent ℝ ![u, gatedBlock relu G C W u]}) :
    ∃ v : d → ℝ, (∀ i, (v ᵥ* G) i ≠ 0) ∧ LinearIndependent ℝ ![v, gatedBlock relu G C W v] := by
  -- almost every row is off the kinks: each `u ↦ (u G)_i` is a nonzero linear form
  have hae : ∀ᵐ u ∂(volume : Measure (d → ℝ)), ∀ i, (u ᵥ* G) i ≠ 0 :=
    ae_all_iff.2 fun i => ae_ne_zero_of_analytic volume (analyticOnNhd_vecMul_rgq G i)
      ⟨Pi.single p 1, by rw [Matrix.single_one_vecMul]; exact hR i⟩
  obtain ⟨u, hu⟩ := hae.exists
  -- `u` or `−u` has a positive gate at a unit `i₀`, so the gate of `i₀` is active there
  obtain ⟨v, hv, hv0⟩ : ∃ v : d → ℝ, (∀ i, (v ᵥ* G) i ≠ 0) ∧
      0 < (v ᵥ* G) (Classical.arbitrary m) := by
    rcases (hu (Classical.arbitrary m)).lt_or_gt with h | h
    · refine ⟨-u, fun i => ?_, ?_⟩
      · rw [Matrix.neg_vecMul, Pi.neg_apply, neg_ne_zero]
        exact hu i
      · rw [Matrix.neg_vecMul, Pi.neg_apply]
        exact neg_pos.2 h
    · exact ⟨u, hu, h⟩
  have hact : relu ((v ᵥ* G) (Classical.arbitrary m)) ≠ 0 := by
    rw [relu_pos_rgq _ hv0]
    exact hv0.ne'
  -- the rows off the kinks form a neighbourhood of `v`, which meets the turned rows
  have hO : ∀ᶠ w in nhds v, ∀ i, (w ᵥ* G) i ≠ 0 :=
    Filter.eventually_all.2 fun i => (continuous_vecMul_rgq G i).continuousAt.eventually_ne (hv i)
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff_nhds.1 (hturn v hv ⟨_, hact⟩) _ hO
  exact ⟨w, hw1, hw2⟩

/-- **A ReGLU block turns a dense set of the rows with an active gate at almost every
parameter,** for `d ≥ 2`. -/
theorem ae_turnsActiveRowsGated_reglu
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, TurnsActiveRowsGated θ := by
  -- two coordinates `p ≠ q` of `d`
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  -- at almost every `θ`, `w_S(θ, 1) ≠ 0` for every nonempty `S`
  filter_upwards [ae_wPoly_ne_zero_rgq μ hpq] with θ hθ
  -- then every row off the kinks with an active gate is a limit of turned rows
  intro v hv hact
  exact mem_closure_of_wPoly_rgq _ _ _ hθ v hv hact

/-- **A ReGLU block with a hidden unit turns some row off the kinks of the gates at almost every
parameter,** for `d ≥ 2`. -/
theorem ae_exists_turned_row_reglu [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v] := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  let p : d := Classical.arbitrary d
  -- at almost every `θ` the block turns a dense set of the rows with an active gate and no gate
  -- column of the read is zero
  filter_upwards [ae_turnsActiveRowsGated_reglu μ hd, ae_read_ne_zero_rgq μ p] with θ hturn hR
  -- a row off the kinks with an active gate, and turned rows near it
  exact exists_turned_of_closure_rgq p _ _ _ hR hturn

/-- **Theorem B.1 (iv) of the skips paper, the residual network, for one ReGLU block:** for
`ε = 0` and `d_in, d_out ≥ d ≥ 2`, at almost every parameter the residual network of one ReGLU
block of any width with at least one hidden unit has `funDim = P − d(d−1)/2 − 1 − 2 d_hidden`. -/
theorem ae_funDim_reglu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  -- the conditions of the proof hold at generic parameters
  filter_upwards [ae_oneBlockGenericReGLURMS μ hd hdIn hdOut, ae_turnsActiveRowsGated_reglu μ hd,
    ae_exists_turned_row_reglu μ hd] with θ hθ hturn hw
  exact funDim_reglu_oneBlock_residual_rmsNorm_zero θ hθ hd hturn hw

/-- **Theorem B.1 (iv) of the skips paper, the residual network, in the paper's own sense, for
one ReGLU block:** at almost every parameter there is a finite batch of inputs at which no
normalized row vanishes and no gate sits at its kink, on which the Jacobian has the rank
`P − d(d−1)/2 − 1 − 2 d_hidden`. -/
theorem ae_exists_jacobianRank_reglu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ residualZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ ∩ noKinkGateRMS θ) ∧
      jacobianRank (Arch.gated relu (rmsNorm 0) hid) 1 X θ
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  -- the conditions of the proof hold at generic parameters
  filter_upwards [ae_oneBlockGenericReGLURMS μ hd hdIn hdOut, ae_turnsActiveRowsGated_reglu μ hd,
    ae_exists_turned_row_reglu μ hd] with θ hθ hturn hw
  exact exists_jacobianRank_reglu_oneBlock_residual_rmsNorm_zero θ hθ hd hturn hw

end Skips
