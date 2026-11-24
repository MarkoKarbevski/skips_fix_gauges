import SkipsLean.OneBlock.ResidualRMSZeroRescale

/-!
# One residual ReLU or ReLU² block under pre-RMSNorm with `ε = 0`: generic parameters

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`".

`OneBlock/ResidualRMSZeroRescale.lean` has this value at one parameter under the conditions of the
proof, among them the condition that the paper does not state: the block turns a dense set of the
rows at which some hidden unit is active (`TurnsActiveRows`). Here: this condition, and "the block
turns some row off the kinks", at almost every parameter for ReLU and ReLU² blocks with `d ≥ 2`
(for every nonempty set `S` of hidden units, the map `v ↦ ∑_{i ∈ S} (v c_i)^k a_i` is at almost
every parameter not parallel to `v` for all `v`, and a nonzero polynomial does not vanish on an
open set); and Theorem B.1 (iv) for the residual network at almost every parameter, as the value
of Lean's `funDim` and as a batch of the paper's inputs with this rank. No width of the block is
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
`b_S(u) = ∑_{i ∈ S} (u c_i)^k a_i` (`c_i` the columns of `R`, `a_i` the rows of `W`). -/
private def wPoly_rzq {m : Type*} [Fintype m] (k : ℕ) (S : Finset m) (p q : d)
    (R : Matrix d m ℝ) (W : Matrix m d ℝ) (u : d → ℝ) : ℝ :=
  u p * ∑ i ∈ S, (u ᵥ* R) i ^ k * W i q - u q * ∑ i ∈ S, (u ᵥ* R) i ^ k * W i p

omit [Fintype d] [DecidableEq d] in
/-- Helper: two rows `x`, `y` with a nonzero minor `x_p y_q − x_q y_p` are linearly
independent. -/
private theorem linearIndependent_of_minor_rzq {x y : d → ℝ} {p q : d}
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
private theorem analyticOnNhd_vecMul_rzq {m : Type*} [Fintype m] (R : Matrix d m ℝ) (i : m) :
    AnalyticOnNhd ℝ (fun u : d → ℝ => (u ᵥ* R) i) Set.univ :=
  analyticOnNhd_linear ((LinearMap.proj i).comp (Matrix.vecMulLinear R))

omit [DecidableEq d] in
/-- Helper: `u ↦ (u R)_i` is continuous. -/
private theorem continuous_vecMul_rzq {m : Type*} [Fintype m] (R : Matrix d m ℝ) (i : m) :
    Continuous fun u : d → ℝ => (u ᵥ* R) i :=
  continuousOn_univ.mp (analyticOnNhd_vecMul_rzq R i).continuousOn

omit [DecidableEq d] in
/-- Helper: `u ↦ w_S(u)` is analytic (a polynomial in `u`). -/
private theorem analyticOnNhd_wPoly_rzq {m : Type*} [Fintype m] (k : ℕ) (S : Finset m)
    (p q : d) (R : Matrix d m ℝ) (W : Matrix m d ℝ) :
    AnalyticOnNhd ℝ (fun u => wPoly_rzq k S p q R W u) Set.univ := by
  have hc : ∀ o : d, AnalyticOnNhd ℝ (fun u : d → ℝ => u o) Set.univ := fun o =>
    analyticOnNhd_linear (LinearMap.proj (R := ℝ) (φ := fun _ : d => ℝ) o)
  have hs : ∀ o : d, AnalyticOnNhd ℝ (fun u : d → ℝ => ∑ i ∈ S, (u ᵥ* R) i ^ k * W i o)
      Set.univ := fun o =>
    Finset.analyticOnNhd_fun_sum _ fun i _ =>
      ((analyticOnNhd_vecMul_rzq R i).pow k).mul analyticOnNhd_const
  exact ((hc p).mul (hs q)).sub ((hc q).mul (hs p))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: an entry of the read is analytic in the parameters (it is linear). -/
private theorem analyticOnNhd_read_rzq {σ : ℝ → ℝ} (j : d) (i : hid 0) :
    AnalyticOnNhd ℝ
      (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut => θ.read 0 j i)
      Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ j i).comp
    (Params.linRead (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) (dIn := dIn)
      (dOut := dOut) 0))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: an entry of the write is analytic in the parameters (it is linear). -/
private theorem analyticOnNhd_write_rzq {σ : ℝ → ℝ} (i : hid 0) (j : d) :
    AnalyticOnNhd ℝ
      (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut => θ.write 0 i j)
      Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ i j).comp
    (Params.linWrite (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) (dIn := dIn)
      (dOut := dOut) 0))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: at a fixed row `u`, `θ ↦ w_S(θ, u)` is analytic (a polynomial in the weights). -/
private theorem analyticOnNhd_wPoly_params_rzq {σ : ℝ → ℝ} (k : ℕ) (S : Finset (hid 0))
    (p q : d) (u : d → ℝ) :
    AnalyticOnNhd ℝ (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
      wPoly_rzq k S p q (θ.read 0) (θ.write 0) u) Set.univ := by
  have hv : ∀ i : hid 0, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        (u ᵥ* θ.read 0) i) Set.univ := fun i =>
    Finset.analyticOnNhd_fun_sum _ fun j _ =>
      analyticOnNhd_const.mul (analyticOnNhd_read_rzq j i)
  have hs : ∀ o : d, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        ∑ i ∈ S, (u ᵥ* θ.read 0) i ^ k * θ.write 0 i o) Set.univ := fun o =>
    Finset.analyticOnNhd_fun_sum _ fun i _ => ((hv i).pow k).mul (analyticOnNhd_write_rzq i o)
  exact (analyticOnNhd_const.mul (hs q)).sub (analyticOnNhd_const.mul (hs p))

omit [Fintype T] [Nonempty T] in
/-- Helper: at almost every parameter, `w_S(θ, 1) ≠ 0` for every nonempty set `S` of hidden
units: it is a polynomial in `θ`, equal to `−|S|` at the weights with `c_i = e_p`, `a_i = e_p`. -/
private theorem ae_wPoly_ne_zero_rzq {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] {p q : d} (hpq : p ≠ q) (k : ℕ) :
    ∀ᵐ θ ∂μ, ∀ S : Finset (hid 0), S.Nonempty →
      wPoly_rzq k S p q (θ.read 0) (θ.write 0) (fun _ => 1) ≠ 0 := by
  -- finitely many sets `S`: one at a time
  refine ae_all_iff.2 fun S => ?_
  by_cases hS : S.Nonempty
  · -- the weights with `c_i = e_p` and `a_i = e_p` for every unit: there `b_S(1) = |S| e_p`
    let θ₀ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut :=
      ⟨0, fun _ => Matrix.of fun j _ => if j = p then 1 else 0,
        fun _ => Matrix.of fun _ j => if j = p then 1 else 0, 0⟩
    have h1 : ∀ i : hid 0, ((fun _ => (1 : ℝ)) ᵥ* θ₀.read 0) i = 1 := fun i => by
      simp [θ₀, Matrix.vecMul, dotProduct]
    have h0 : wPoly_rzq k S p q (θ₀.read 0) (θ₀.write 0) (fun _ => 1) = -(S.card : ℝ) := by
      simp only [wPoly_rzq, h1]
      simp [θ₀, hpq.symm]
    have hne : wPoly_rzq k S p q (θ₀.read 0) (θ₀.write 0) (fun _ => 1) ≠ 0 := by
      rw [h0]
      exact neg_ne_zero.2 (Nat.cast_ne_zero.2 hS.card_pos.ne')
    -- a polynomial that is not identically zero is nonzero at almost every `θ`
    exact (ae_ne_zero_of_analytic μ (analyticOnNhd_wPoly_params_rzq k S p q _)
      ⟨θ₀, hne⟩).mono fun _ h _ => h
  · exact Filter.Eventually.of_forall fun _ h => absurd h hS

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: at almost every parameter, the entries of the read at the coordinate `p` are
nonzero, so no column of the read is zero. -/
private theorem ae_read_ne_zero_rzq {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (p : d) :
    ∀ᵐ θ ∂μ, ∀ i : hid 0, θ.read 0 p i ≠ 0 := by
  -- the parameters with all entries `1`
  let θ₁ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1,
      Matrix.of fun _ _ => 1⟩
  exact ae_all_iff.2 fun i =>
    ae_ne_zero_of_analytic μ (analyticOnNhd_read_rzq p i) ⟨θ₁, show (1 : ℝ) ≠ 0 from one_ne_zero⟩

omit [DecidableEq d] in
/-- Helper (the condition at one parameter): if `σ(z) = z^k` for `z > 0` and `σ(z) = 0` for
`z ≤ 0`, and `w_S(1) ≠ 0` for every nonempty `S`, then every row `v` off the kinks with an
active unit is a limit of rows `u` such that `u` and `B(u)` are linearly independent. -/
private theorem mem_closure_of_wPoly_rzq {m : Type*} [Fintype m] {σ : ℝ → ℝ} {k : ℕ}
    (hpos : ∀ z, 0 < z → σ z = z ^ k) (hnonpos : ∀ z, z ≤ 0 → σ z = 0) {p q : d}
    (R : Matrix d m ℝ) (W : Matrix m d ℝ)
    (hS : ∀ S : Finset m, S.Nonempty → wPoly_rzq k S p q R W (fun _ => 1) ≠ 0)
    (v : d → ℝ) (hv : ∀ i, (v ᵥ* R) i ≠ 0) (hact : ∃ i, σ ((v ᵥ* R) i) ≠ 0) :
    v ∈ closure {u : d → ℝ | LinearIndependent ℝ ![u, vanillaBlock σ R W u]} := by
  classical
  -- the set `S` of the units active at `v`; it is nonempty
  obtain ⟨S, hSdef⟩ : ∃ S : Finset m, S = Finset.univ.filter fun i => 0 < (v ᵥ* R) i :=
    ⟨_, rfl⟩
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hact
    refine ⟨i, hSdef ▸ Finset.mem_filter.2 ⟨Finset.mem_univ i, ?_⟩⟩
    by_contra h
    exact hi (hnonpos _ (not_lt.1 h))
  -- the rows `u` with the signs of `v` (the open set `R_S`) form a neighbourhood of `v`
  have hO : ∀ᶠ u in nhds v, ∀ i, 0 < (v ᵥ* R) i * (u ᵥ* R) i := by
    refine Filter.eventually_all.2 fun i => ?_
    have hc : Continuous fun u : d → ℝ => (v ᵥ* R) i * (u ᵥ* R) i :=
      continuous_const.mul (continuous_vecMul_rzq R i)
    exact Filter.Tendsto.eventually_const_lt (mul_self_pos.2 (hv i)) (hc.tendsto v)
  -- on `R_S` the block is `b_S`, so `w_S(u) ≠ 0` makes `u`, `B(u)` independent
  have hLI : ∀ u : d → ℝ, (∀ i, 0 < (v ᵥ* R) i * (u ᵥ* R) i) → wPoly_rzq k S p q R W u ≠ 0 →
      LinearIndependent ℝ ![u, vanillaBlock σ R W u] := by
    intro u hu hw
    have hb : ∀ o, vanillaBlock σ R W u o = ∑ i ∈ S, (u ᵥ* R) i ^ k * W i o := by
      intro o
      show ∑ i, σ ((u ᵥ* R) i) * W i o = _
      rw [hSdef, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · rw [hpos _ ((pos_iff_pos_of_mul_pos (hu i)).1 h)]
      · have hneg : (v ᵥ* R) i < 0 := lt_of_le_of_ne (not_lt.1 h) (hv i)
        rw [hnonpos _ ((neg_iff_neg_of_mul_pos (hu i)).1 hneg).le, zero_mul]
    apply linearIndependent_of_minor_rzq (p := p) (q := q)
    rw [hb p, hb q]
    exact hw
  rw [mem_closure_iff_nhds]
  intro t ht
  by_contra hne
  -- otherwise `w_S` vanishes near `v`, hence everywhere (identity theorem), also at `1`
  have hz : (fun u => wPoly_rzq k S p q R W u) =ᶠ[nhds v] 0 := by
    filter_upwards [ht, hO] with u hut hu
    by_contra hw
    exact hne ⟨u, hut, hLI u hu hw⟩
  have h0 := (analyticOnNhd_wPoly_rzq k S p q R W).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ v) hz
  exact hS S hSne (h0 (Set.mem_univ _))

/-- Helper (some row off the kinks is turned): if no column of `R` is zero, `σ ≠ 0` on the
positive reals and every active row off the kinks is a limit of turned rows, then some row off the
kinks and the output of the block there are linearly independent. -/
private theorem exists_turned_of_closure_rzq {m : Type*} [Fintype m] [Nonempty m]
    {σ : ℝ → ℝ} (hσ : ∀ z, 0 < z → σ z ≠ 0) (p : d) (R : Matrix d m ℝ) (W : Matrix m d ℝ)
    (hR : ∀ i, R p i ≠ 0)
    (hturn : ∀ v : d → ℝ, (∀ i, (v ᵥ* R) i ≠ 0) → (∃ i, σ ((v ᵥ* R) i) ≠ 0) →
      v ∈ closure {u : d → ℝ | LinearIndependent ℝ ![u, vanillaBlock σ R W u]}) :
    ∃ v : d → ℝ, (∀ i, (v ᵥ* R) i ≠ 0) ∧ LinearIndependent ℝ ![v, vanillaBlock σ R W v] := by
  -- almost every row is off the kinks: each `u ↦ (u R)_i` is a nonzero linear form
  have hae : ∀ᵐ u ∂(volume : Measure (d → ℝ)), ∀ i, (u ᵥ* R) i ≠ 0 :=
    ae_all_iff.2 fun i => ae_ne_zero_of_analytic volume (analyticOnNhd_vecMul_rzq R i)
      ⟨Pi.single p 1, by rw [Matrix.single_one_vecMul]; exact hR i⟩
  obtain ⟨u, hu⟩ := hae.exists
  -- `u` or `−u` has a positive entry at a unit `i₀`, so `i₀` is active there
  obtain ⟨v, hv, hv0⟩ : ∃ v : d → ℝ, (∀ i, (v ᵥ* R) i ≠ 0) ∧
      0 < (v ᵥ* R) (Classical.arbitrary m) := by
    rcases (hu (Classical.arbitrary m)).lt_or_gt with h | h
    · refine ⟨-u, fun i => ?_, ?_⟩
      · rw [Matrix.neg_vecMul, Pi.neg_apply, neg_ne_zero]
        exact hu i
      · rw [Matrix.neg_vecMul, Pi.neg_apply]
        exact neg_pos.2 h
    · exact ⟨u, hu, h⟩
  -- the rows off the kinks form a neighbourhood of `v`, which meets the turned rows
  have hO : ∀ᶠ w in nhds v, ∀ i, (w ᵥ* R) i ≠ 0 :=
    Filter.eventually_all.2 fun i => (continuous_vecMul_rzq R i).continuousAt.eventually_ne (hv i)
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff_nhds.1 (hturn v hv ⟨_, hσ _ hv0⟩) _ hO
  exact ⟨w, hw1, hw2⟩

/-- Helper: ReLU is `z ↦ z^1` on the positive reals. -/
private theorem relu_pos_rzq (z : ℝ) (hz : 0 < z) : relu z = z ^ 1 := by
  rw [relu, max_eq_left hz.le, pow_one]

/-- Helper: ReLU vanishes on the nonpositive reals. -/
private theorem relu_nonpos_rzq (z : ℝ) (hz : z ≤ 0) : relu z = 0 := by
  rw [relu, max_eq_right hz]

/-- Helper: ReLU² is `z ↦ z^2` on the positive reals. -/
private theorem reluSq_pos_rzq (z : ℝ) (hz : 0 < z) : reluSq z = z ^ 2 := by
  rw [reluSq, max_eq_left hz.le]

/-- Helper: ReLU² vanishes on the nonpositive reals. -/
private theorem reluSq_nonpos_rzq (z : ℝ) (hz : z ≤ 0) : reluSq z = 0 := by
  rw [reluSq, max_eq_right hz]
  norm_num

/-- **A ReLU block turns a dense set of the active rows at almost every parameter,** for
`d ≥ 2`. -/
theorem ae_turnsActiveRows_relu
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, TurnsActiveRows θ := by
  -- two coordinates `p ≠ q` of `d`
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  -- at almost every `θ`, `w_S(θ, 1) ≠ 0` for every nonempty `S`
  filter_upwards [ae_wPoly_ne_zero_rzq μ hpq 1] with θ hθ
  -- then every active row off the kinks is a limit of turned rows
  intro v hv hact
  exact mem_closure_of_wPoly_rzq relu_pos_rzq relu_nonpos_rzq _ _ hθ v hv hact

/-- **A ReLU² block turns a dense set of the active rows at almost every parameter,** for
`d ≥ 2`. -/
theorem ae_turnsActiveRows_reluSq
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, TurnsActiveRows θ := by
  -- two coordinates `p ≠ q` of `d`
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  -- at almost every `θ`, `w_S(θ, 1) ≠ 0` for every nonempty `S`
  filter_upwards [ae_wPoly_ne_zero_rzq μ hpq 2] with θ hθ
  -- then every active row off the kinks is a limit of turned rows
  intro v hv hact
  exact mem_closure_of_wPoly_rzq reluSq_pos_rzq reluSq_nonpos_rzq _ _ hθ v hv hact

/-- **A ReLU block with a hidden unit turns some row off the kinks at almost every parameter,**
for `d ≥ 2`. -/
theorem ae_exists_turned_row_relu [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v, vanillaBlock relu (θ.read 0) (θ.write 0) v] := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  let p : d := Classical.arbitrary d
  -- at almost every `θ` the block turns a dense set of the active rows and no column of the read
  -- is zero
  filter_upwards [ae_turnsActiveRows_relu μ hd, ae_read_ne_zero_rzq μ p] with θ hturn hR
  -- a row off the kinks with an active unit, and turned rows near it
  refine exists_turned_of_closure_rzq (fun z hz => ?_) p _ _ hR hturn
  rw [relu_pos_rzq z hz, pow_one]
  exact hz.ne'

/-- **A ReLU² block with a hidden unit turns some row off the kinks at almost every parameter,**
for `d ≥ 2`. -/
theorem ae_exists_turned_row_reluSq [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v, vanillaBlock reluSq (θ.read 0) (θ.write 0) v] := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  let p : d := Classical.arbitrary d
  -- at almost every `θ` the block turns a dense set of the active rows and no column of the read
  -- is zero
  filter_upwards [ae_turnsActiveRows_reluSq μ hd, ae_read_ne_zero_rzq μ p] with θ hturn hR
  -- a row off the kinks with an active unit, and turned rows near it
  refine exists_turned_of_closure_rzq (fun z hz => ?_) p _ _ hR hturn
  rw [reluSq_pos_rzq z hz]
  exact pow_ne_zero 2 hz.ne'

/-- **Theorem B.1 (iv) of the skips paper, the residual network, for one ReLU block with a hidden
unit:** with `d_in, d_out ≥ d ≥ 2` and `ε = 0`, at almost every parameter
`funDim = P − d(d−1)/2 − 1 − s`. -/
theorem ae_funDim_relu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  -- the conditions of the proof at almost every parameter (`ResidualRMSMlp.lean` and above)
  filter_upwards [ae_oneBlockGenericRMS μ hd hdIn hdOut, ae_turnsActiveRows_relu μ hd,
    ae_exists_turned_row_relu μ hd] with θ hθ hturn hw
  exact funDim_mlp_oneBlock_rescale_residual_rmsNorm_zero (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous (relu_unitsRescale d d (hid 0)) θ hθ hd hturn hw

/-- **Theorem B.1 (iv) of the skips paper, the residual network, in the paper's own sense, for
one ReLU block with a hidden unit:** at almost every parameter, a finite batch of inputs at which
no normalized row vanishes and no hidden unit sits at its kink, on which the Jacobian has the rank
`P − d(d−1)/2 − 1 − s`. -/
theorem ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ residualZeroDomain (Arch.mlp relu (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp relu (rmsNorm 0) hid) 1 X θ
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  -- the conditions of the proof at almost every parameter (`ResidualRMSMlp.lean` and above)
  filter_upwards [ae_oneBlockGenericRMS μ hd hdIn hdOut, ae_turnsActiveRows_relu μ hd,
    ae_exists_turned_row_relu μ hd] with θ hθ hturn hw
  exact exists_jacobianRank_mlp_oneBlock_rescale_residual_rmsNorm_zero
    (fun _ hz => hasDerivAt_relu hz) relu_homogeneous (relu_unitsRescale d d (hid 0)) θ hθ hd
    hturn hw

/-- **Theorem B.1 (iv) of the skips paper, the residual network, for one ReLU² block with a
hidden unit:** with `d_in, d_out ≥ d ≥ 2` and `ε = 0`, at almost every parameter
`funDim = P − d(d−1)/2 − 1 − s`. -/
theorem ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  -- the conditions of the proof at almost every parameter (`ResidualRMSMlp.lean` and above)
  filter_upwards [ae_oneBlockGenericRMS μ hd hdIn hdOut, ae_turnsActiveRows_reluSq μ hd,
    ae_exists_turned_row_reluSq μ hd] with θ hθ hturn hw
  exact funDim_mlp_oneBlock_rescale_residual_rmsNorm_zero (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous (reluSq_unitsRescale d d (hid 0)) θ hθ hd hturn hw

/-- **Theorem B.1 (iv) of the skips paper, the residual network, in the paper's own sense, for
one ReLU² block with a hidden unit:** at almost every parameter, a finite batch of inputs at which
no normalized row vanishes and no hidden unit sits at its kink, on which the Jacobian has the rank
`P − d(d−1)/2 − 1 − s`. -/
theorem ae_exists_jacobianRank_reluSq_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ residualZeroDomain (Arch.mlp reluSq (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp reluSq (rmsNorm 0) hid) 1 X θ
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  -- the conditions of the proof at almost every parameter (`ResidualRMSMlp.lean` and above)
  filter_upwards [ae_oneBlockGenericRMS μ hd hdIn hdOut, ae_turnsActiveRows_reluSq μ hd,
    ae_exists_turned_row_reluSq μ hd] with θ hθ hturn hw
  exact exists_jacobianRank_mlp_oneBlock_rescale_residual_rmsNorm_zero
    (fun z _ => hasDerivAt_reluSq z) reluSq_homogeneous (reluSq_unitsRescale d d (hid 0)) θ hθ hd
    hturn hw

end Skips
