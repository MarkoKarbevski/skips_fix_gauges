import SkipsLean.OneBlock.LearnedSkipRMSZeroReGLU

/-!
# One ReGLU block with a full learned skip under pre-RMSNorm with `ε = 0`: generic parameters

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. […] For `ε = 0` it exceeds that of the residual
network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and
ReGLU blocks."

`OneBlock/LearnedSkipRMSZeroReGLU.lean` has the value at one parameter under the conditions of
the proof, among them the condition that the paper does not state (`TurnsActiveRowsGatedSkip`).
Here, for one ReGLU block with `d ≥ 2`:

* this condition, and "the block turns some row off the kinks of the gates", at almost every
  weights and skip `(θ, A)` (the twins for a learned skip of `ae_turnsActiveRowsGated_reglu` and
  `ae_exists_turned_row_reglu`, `OneBlock/ResidualRMSZeroReGLUGeneric.lean`);
* the theorem at almost every `(θ, A)`, for `d_in, d_out ≥ d ≥ 2` and a block of any width with
  a hidden unit: the value `P + d² − (d(d−1) + 2) − 2 d_hidden` of Lean's `funDimLearned`, a batch
  of the paper's inputs with this rank, and the equality with the residual network at the same
  weights, `funDimLearned = funDim + d(d+1)/2 − 1`.

Not stated: the upper triangular skip.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-! ### Helpers: the polynomial `w_S` and the rows on which the block is `b_S` -/

/-- Helper: an analytic function on a finite-dimensional space with the Borel σ-algebra that is
not identically zero is nonzero at almost every point of a Haar measure (`ae_ne_zero_of_analytic`
with the instances passed as arguments). -/
private theorem ae_ne_zero_of_analytic_lzj {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasurableSpace P] (hB : BorelSpace P) (μ : Measure P)
    (hμ : μ.IsAddHaarMeasure) {g : P → ℝ} (hg : AnalyticOnNhd ℝ g Set.univ)
    (hne : ∃ y, g y ≠ 0) : ∀ᵐ y ∂μ, g y ≠ 0 :=
  ae_ne_zero_of_analytic μ hg hne

omit [DecidableEq d] in
/-- Helper: the polynomial `w_S(u) = (u M)_p b_S(u)_q − (u M)_q b_S(u)_p`, with
`b_S(u) = ∑_{i ∈ S} (u g_i) (u c_i) a_i` (`g_i`, `c_i` the columns of `G`, `C`, `a_i` the rows of
`W`, `M` the skip). -/
private def wPoly_lzj {m : Type*} [Fintype m] (S : Finset m) (p q : d) (M : Matrix d d ℝ)
    (G C : Matrix d m ℝ) (W : Matrix m d ℝ) (u : d → ℝ) : ℝ :=
  (u ᵥ* M) p * ∑ i ∈ S, (u ᵥ* G) i * (u ᵥ* C) i * W i q
    - (u ᵥ* M) q * ∑ i ∈ S, (u ᵥ* G) i * (u ᵥ* C) i * W i p

omit [Fintype d] [DecidableEq d] in
/-- Helper: two rows `x`, `y` with a nonzero minor `x_p y_q − x_q y_p` are linearly
independent. -/
private theorem linearIndependent_of_minor_lzj {x y : d → ℝ} {p q : d}
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
private theorem analyticOnNhd_vecMul_lzj {m : Type*} [Fintype m] (R : Matrix d m ℝ) (i : m) :
    AnalyticOnNhd ℝ (fun u : d → ℝ => (u ᵥ* R) i) Set.univ :=
  analyticOnNhd_linear ((LinearMap.proj i).comp (Matrix.vecMulLinear R))

omit [DecidableEq d] in
/-- Helper: `u ↦ (u R)_i` is continuous. -/
private theorem continuous_vecMul_lzj {m : Type*} [Fintype m] (R : Matrix d m ℝ) (i : m) :
    Continuous fun u : d → ℝ => (u ᵥ* R) i :=
  continuousOn_univ.mp (analyticOnNhd_vecMul_lzj R i).continuousOn

omit [DecidableEq d] in
/-- Helper: `u ↦ w_S(u)` is analytic (a polynomial in `u`). -/
private theorem analyticOnNhd_wPoly_lzj {m : Type*} [Fintype m] (S : Finset m) (p q : d)
    (M : Matrix d d ℝ) (G C : Matrix d m ℝ) (W : Matrix m d ℝ) :
    AnalyticOnNhd ℝ (fun u => wPoly_lzj S p q M G C W u) Set.univ := by
  have hs : ∀ o : d, AnalyticOnNhd ℝ
      (fun u : d → ℝ => ∑ i ∈ S, (u ᵥ* G) i * (u ᵥ* C) i * W i o) Set.univ := fun o =>
    Finset.analyticOnNhd_fun_sum _ fun i _ =>
      ((analyticOnNhd_vecMul_lzj G i).mul (analyticOnNhd_vecMul_lzj C i)).mul analyticOnNhd_const
  exact ((analyticOnNhd_vecMul_lzj M p).mul (hs q)).sub
    ((analyticOnNhd_vecMul_lzj M q).mul (hs p))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: an entry of the read is analytic in the weights and the skip (it is linear). -/
private theorem analyticOnNhd_read_lzj (j : d) (i : hid 0 ⊕ hid 0) :
    AnalyticOnNhd ℝ
      (fun x : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ) => x.1.read 0 j i) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ j i).comp
    ((Params.linRead (A := Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) (dIn := dIn)
      (dOut := dOut) 0).comp (LinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: an entry of the write is analytic in the weights and the skip (it is linear). -/
private theorem analyticOnNhd_write_lzj (i : hid 0) (j : d) :
    AnalyticOnNhd ℝ
      (fun x : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ) => x.1.write 0 i j) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ i j).comp
    ((Params.linWrite (A := Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) (dIn := dIn)
      (dOut := dOut) 0).comp (LinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: an entry of the skip `A = x.2 0` is analytic in the weights and the skip (it is
linear). -/
private theorem analyticOnNhd_skip_lzj (j o : d) :
    AnalyticOnNhd ℝ
      (fun x : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ) => x.2 0 j o) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ j o).comp
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix d d ℝ) 0).comp
      (LinearMap.snd ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
        (Fin 1 → Matrix d d ℝ))))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: at a fixed row `u`, `(θ, A) ↦ w_S(θ, A, u)` is analytic (a polynomial in the weights
and the skip). -/
private theorem analyticOnNhd_wPoly_params_lzj (S : Finset (hid 0)) (p q : d) (u : d → ℝ) :
    AnalyticOnNhd ℝ (fun x : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ) =>
      wPoly_lzj S p q (x.2 0) ((x.1.read 0).submatrix id Sum.inl)
        ((x.1.read 0).submatrix id Sum.inr) (x.1.write 0) u) Set.univ := by
  have hm : ∀ o : d, AnalyticOnNhd ℝ
      (fun x : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ) => (u ᵥ* x.2 0) o) Set.univ := fun o =>
    Finset.analyticOnNhd_fun_sum _ fun j _ =>
      analyticOnNhd_const.mul (analyticOnNhd_skip_lzj j o)
  have hv : ∀ i : hid 0 ⊕ hid 0, AnalyticOnNhd ℝ
      (fun x : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ) => (u ᵥ* x.1.read 0) i) Set.univ := fun i =>
    Finset.analyticOnNhd_fun_sum _ fun j _ =>
      analyticOnNhd_const.mul (analyticOnNhd_read_lzj j i)
  have hs : ∀ o : d, AnalyticOnNhd ℝ
      (fun x : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ) => ∑ i ∈ S, (u ᵥ* x.1.read 0) (Sum.inl i)
          * (u ᵥ* x.1.read 0) (Sum.inr i) * x.1.write 0 i o) Set.univ := fun o =>
    Finset.analyticOnNhd_fun_sum _ fun i _ =>
      ((hv (Sum.inl i)).mul (hv (Sum.inr i))).mul (analyticOnNhd_write_lzj i o)
  exact ((hm p).mul (hs q)).sub ((hm q).mul (hs p))

omit [Fintype T] [Nonempty T] in
/-- Helper: at almost every weights and skip `(θ, A)`, `w_S(θ, A, 1) ≠ 0` for every nonempty
set `S` of hidden units: it is a polynomial in `(θ, A)`, equal to `−|S|` at the weights with
`g_i = c_i = e_p`, `a_i = e_p` and the skip `A = I`. -/
private theorem ae_wPoly_ne_zero_lzj
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [hμ : μ.IsAddHaarMeasure] {p q : d} (hpq : p ≠ q) :
    ∀ᵐ x ∂μ, ∀ S : Finset (hid 0), S.Nonempty →
      wPoly_lzj S p q (x.2 0) ((x.1.read 0).submatrix id Sum.inl)
        ((x.1.read 0).submatrix id Sum.inr) (x.1.write 0) (fun _ => 1) ≠ 0 := by
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := inferInstanceAs (BorelSpace (Fin 1 → d → d → ℝ))
  have hBp : BorelSpace (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)) := Prod.borelSpace
  -- finitely many sets `S`: one at a time
  refine ae_all_iff.2 fun S => ?_
  by_cases hS : S.Nonempty
  · -- the weights with `g_i = c_i = e_p` and `a_i = e_p` for every unit and the skip `I`: there
    -- `(1 A)_p = (1 A)_q = 1` and `b_S(1) = |S| e_p`
    let θ₀ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut :=
      ⟨0, fun _ => Matrix.of fun j _ => if j = p then 1 else 0,
        fun _ => Matrix.of fun _ j => if j = p then 1 else 0, 0⟩
    have h1 : ∀ x : hid 0 ⊕ hid 0, ((fun _ => (1 : ℝ)) ᵥ* θ₀.read 0) x = 1 := fun x => by
      simp [θ₀, Matrix.vecMul, dotProduct]
    have hg : ∀ i, ((fun _ => (1 : ℝ)) ᵥ* (θ₀.read 0).submatrix id Sum.inl) i = 1 :=
      fun i => h1 (Sum.inl i)
    have hc : ∀ i, ((fun _ => (1 : ℝ)) ᵥ* (θ₀.read 0).submatrix id Sum.inr) i = 1 :=
      fun i => h1 (Sum.inr i)
    have hM : ∀ o : d, ((fun _ => (1 : ℝ)) ᵥ* (1 : Matrix d d ℝ)) o = 1 := fun o => by
      rw [Matrix.vecMul_one]
    have h0 : wPoly_lzj S p q 1 ((θ₀.read 0).submatrix id Sum.inl)
        ((θ₀.read 0).submatrix id Sum.inr) (θ₀.write 0) (fun _ => 1) = -(S.card : ℝ) := by
      simp only [wPoly_lzj, hg, hc, hM]
      simp [θ₀, hpq.symm]
    have hne : wPoly_lzj S p q 1 ((θ₀.read 0).submatrix id Sum.inl)
        ((θ₀.read 0).submatrix id Sum.inr) (θ₀.write 0) (fun _ => 1) ≠ 0 := by
      rw [h0]
      exact neg_ne_zero.2 (Nat.cast_ne_zero.2 hS.card_pos.ne')
    -- a polynomial that is not identically zero is nonzero at almost every `(θ, A)`
    exact (ae_ne_zero_of_analytic_lzj hBp μ hμ (analyticOnNhd_wPoly_params_lzj S p q _)
      ⟨(θ₀, fun _ => 1), hne⟩).mono fun _ h _ => h
  · exact Filter.Eventually.of_forall fun _ h => absurd h hS

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: at almost every weights and skip `(θ, A)`, the entries of the gate columns of the
read at the coordinate `p` are nonzero, so no gate column of the read is zero. -/
private theorem ae_read_ne_zero_lzj
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [hμ : μ.IsAddHaarMeasure] (p : d) :
    ∀ᵐ x ∂μ, ∀ i : hid 0, x.1.read 0 p (Sum.inl i) ≠ 0 := by
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := inferInstanceAs (BorelSpace (Fin 1 → d → d → ℝ))
  have hBp : BorelSpace (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)) := Prod.borelSpace
  -- the weights with all entries `1`
  let θ₁ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1,
      Matrix.of fun _ _ => 1⟩
  exact ae_all_iff.2 fun i =>
    ae_ne_zero_of_analytic_lzj hBp μ hμ (analyticOnNhd_read_lzj p (Sum.inl i))
      ⟨(θ₁, 0), show (1 : ℝ) ≠ 0 from one_ne_zero⟩

/-- Helper: ReLU is the identity on the positive reals. -/
private theorem relu_pos_lzj (z : ℝ) (hz : 0 < z) : relu z = z := by
  rw [relu, max_eq_left hz.le]

/-- Helper: ReLU vanishes on the nonpositive reals. -/
private theorem relu_nonpos_lzj (z : ℝ) (hz : z ≤ 0) : relu z = 0 := by
  rw [relu, max_eq_right hz]

omit [DecidableEq d] in
/-- Helper (the condition at one weights and skip): if `w_S(1) ≠ 0` for every nonempty `S`, then
every row `v` off the kinks of the gates with an active gate is a limit of rows `u` such that
`u M` and `B(u)` are linearly independent. -/
private theorem mem_closure_of_wPoly_lzj {m : Type*} [Fintype m] {p q : d} (M : Matrix d d ℝ)
    (G C : Matrix d m ℝ) (W : Matrix m d ℝ)
    (hS : ∀ S : Finset m, S.Nonempty → wPoly_lzj S p q M G C W (fun _ => 1) ≠ 0)
    (v : d → ℝ) (hv : ∀ i, (v ᵥ* G) i ≠ 0) (hact : ∃ i, relu ((v ᵥ* G) i) ≠ 0) :
    v ∈ closure {u : d → ℝ | LinearIndependent ℝ ![u ᵥ* M, gatedBlock relu G C W u]} := by
  classical
  -- the set `S` of the units whose gate is active at `v`; it is nonempty
  obtain ⟨S, hSdef⟩ : ∃ S : Finset m, S = Finset.univ.filter fun i => 0 < (v ᵥ* G) i :=
    ⟨_, rfl⟩
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hact
    refine ⟨i, hSdef ▸ Finset.mem_filter.2 ⟨Finset.mem_univ i, ?_⟩⟩
    by_contra h
    exact hi (relu_nonpos_lzj _ (not_lt.1 h))
  -- the rows `u` with the signs of the gates of `v` form a neighbourhood of `v`
  have hO : ∀ᶠ u in nhds v, ∀ i, 0 < (v ᵥ* G) i * (u ᵥ* G) i := by
    refine Filter.eventually_all.2 fun i => ?_
    have hc : Continuous fun u : d → ℝ => (v ᵥ* G) i * (u ᵥ* G) i :=
      continuous_const.mul (continuous_vecMul_lzj G i)
    exact Filter.Tendsto.eventually_const_lt (mul_self_pos.2 (hv i)) (hc.tendsto v)
  -- on these rows the block is `b_S`, so `w_S(u) ≠ 0` makes `u M`, `B(u)` independent
  have hLI : ∀ u : d → ℝ, (∀ i, 0 < (v ᵥ* G) i * (u ᵥ* G) i) →
      wPoly_lzj S p q M G C W u ≠ 0 →
      LinearIndependent ℝ ![u ᵥ* M, gatedBlock relu G C W u] := by
    intro u hu hw
    have hb : ∀ o, gatedBlock relu G C W u o = ∑ i ∈ S, (u ᵥ* G) i * (u ᵥ* C) i * W i o := by
      intro o
      show ∑ i, relu ((u ᵥ* G) i) * (u ᵥ* C) i * W i o = _
      rw [hSdef, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · rw [relu_pos_lzj _ ((pos_iff_pos_of_mul_pos (hu i)).1 h)]
      · have hneg : (v ᵥ* G) i < 0 := lt_of_le_of_ne (not_lt.1 h) (hv i)
        rw [relu_nonpos_lzj _ ((neg_iff_neg_of_mul_pos (hu i)).1 hneg).le, zero_mul, zero_mul]
    apply linearIndependent_of_minor_lzj (p := p) (q := q)
    rw [hb p, hb q]
    exact hw
  rw [mem_closure_iff_nhds]
  intro t ht
  by_contra hne
  -- otherwise `w_S` vanishes near `v`, hence everywhere (identity theorem), also at `1`
  have hz : (fun u => wPoly_lzj S p q M G C W u) =ᶠ[nhds v] 0 := by
    filter_upwards [ht, hO] with u hut hu
    by_contra hw
    exact hne ⟨u, hut, hLI u hu hw⟩
  have h0 :=
    (analyticOnNhd_wPoly_lzj S p q M G C W).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ v) hz
  exact hS S hSne (h0 (Set.mem_univ _))

/-- Helper (some row off the kinks is turned): if no gate column is zero and every row off the
kinks with an active gate is a limit of turned rows, then some row `v` off the kinks has `v M`
and the output of the block there linearly independent. -/
private theorem exists_turned_of_closure_lzj {m : Type*} [Fintype m] [Nonempty m] (p : d)
    (M : Matrix d d ℝ) (G C : Matrix d m ℝ) (W : Matrix m d ℝ) (hR : ∀ i, G p i ≠ 0)
    (hturn : ∀ v : d → ℝ, (∀ i, (v ᵥ* G) i ≠ 0) → (∃ i, relu ((v ᵥ* G) i) ≠ 0) →
      v ∈ closure {u : d → ℝ | LinearIndependent ℝ ![u ᵥ* M, gatedBlock relu G C W u]}) :
    ∃ v : d → ℝ, (∀ i, (v ᵥ* G) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* M, gatedBlock relu G C W v] := by
  -- almost every row is off the kinks: each `u ↦ (u G)_i` is a nonzero linear form
  have hae : ∀ᵐ u ∂(volume : Measure (d → ℝ)), ∀ i, (u ᵥ* G) i ≠ 0 :=
    ae_all_iff.2 fun i => ae_ne_zero_of_analytic volume (analyticOnNhd_vecMul_lzj G i)
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
    rw [relu_pos_lzj _ hv0]
    exact hv0.ne'
  -- the rows off the kinks form a neighbourhood of `v`, which meets the turned rows
  have hO : ∀ᶠ w in nhds v, ∀ i, (w ᵥ* G) i ≠ 0 :=
    Filter.eventually_all.2 fun i => (continuous_vecMul_lzj G i).continuousAt.eventually_ne (hv i)
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff_nhds.1 (hturn v hv ⟨_, hact⟩) _ hO
  exact ⟨w, hw1, hw2⟩

omit [Fintype T] [Nonempty T] in
/-- **A ReGLU block turns a dense set of the rows with an active gate for the skip `A` at almost
every weights and skip `(θ, A)`,** for `d ≥ 2`. -/
theorem ae_turnsActiveRowsGatedSkip_reglu
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, TurnsActiveRowsGatedSkip p.1 (p.2 0) := by
  -- two coordinates `p ≠ q` of `d`
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  -- at almost every `(θ, A)`, `w_S(θ, A, 1) ≠ 0` for every nonempty `S`
  filter_upwards [ae_wPoly_ne_zero_lzj μ hpq] with x hx
  -- then every row off the kinks with an active gate is a limit of turned rows
  intro v hv hact
  exact mem_closure_of_wPoly_lzj _ _ _ _ hx v hv hact

omit [Fintype T] [Nonempty T] in
/-- **A ReGLU block with a hidden unit turns some row off the kinks of the gates, for the skip
`A`, at almost every weights and skip `(θ, A)`,** for `d ≥ 2`. -/
theorem ae_exists_turned_row_skip_reglu [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* p.1.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* p.2 0, gatedBlock relu ((p.1.read 0).submatrix id Sum.inl)
        ((p.1.read 0).submatrix id Sum.inr) (p.1.write 0) v] := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  let p : d := Classical.arbitrary d
  -- at almost every `(θ, A)` the block turns a dense set of the rows with an active gate and no
  -- gate column of the read is zero
  filter_upwards [ae_turnsActiveRowsGatedSkip_reglu μ hd, ae_read_ne_zero_lzj μ p]
    with x hturn hR
  -- a row off the kinks with an active gate, and turned rows near it
  exact exists_turned_of_closure_lzj p _ _ _ _ hR hturn

/-! ### Helpers: almost every `(θ, A)` -/

omit [DecidableEq d] in
/-- Helper: the skips `Fin 1 → Matrix d d ℝ` carry the Borel σ-algebra of their norm topology (a
copy of the private `borelSpace_skips_lsk` of `OneBlock/LearnedSkipKinds.lean`). -/
private theorem borelSpace_skips_lzh : BorelSpace (Fin 1 → Matrix d d ℝ) :=
  inferInstanceAs (BorelSpace (Fin 1 → d → d → ℝ))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: a condition on the weights that holds at almost every `θ` holds at almost every
`(θ, v)` (a copy of the private `ae_fst_lsk` of `OneBlock/LearnedSkipKinds.lean`). -/
private theorem ae_fst_lzh {A : Arch T d 1} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] (hB : BorelSpace V)
    (μ : Measure (Params A dIn dOut × V)) (hμ : μ.IsAddHaarMeasure) {Q : Params A dIn dOut → Prop}
    (h : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), Q θ) :
    ∀ᵐ p ∂μ, Q p.1 := by
  rw [ae_iff] at h
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null h
  have hc : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), θ ∈ Nᶜ :=
    measure_eq_zero_iff_ae_notMem.1 hN0
  have h1 := (ae_comp_linearMap_mem_iff (LinearMap.fst ℝ (Params A dIn dOut) V) μ
    Measure.addHaar (LinearMap.fst_surjective) hN.compl).2 hc
  refine h1.mono fun p hp => ?_
  by_contra hq
  exact hp (hsub hq)

/-- Helper: if a square matrix that depends linearly on a point of `E` is the identity at one
point, it is invertible at almost every point (a copy of the private `ae_isUnit_det_lst` of
`OneBlock/LearnedSkipTriangular.lean`). -/
private theorem ae_isUnit_det_lzh {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] (hB : BorelSpace E) (μ : Measure E)
    (hμ : μ.IsAddHaarMeasure) (Φ : E →ₗ[ℝ] Matrix d d ℝ) (x₀ : E) (h₀ : Φ x₀ = 1) :
    ∀ᵐ x ∂μ, IsUnit (Φ x).det := by
  have hentry : ∀ i j, AnalyticOnNhd ℝ (fun x => Φ x i j) Set.univ := fun i j =>
    (LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℝ ℝ i j) ∘ₗ Φ)).analyticOnNhd _
  have hφ : AnalyticOnNhd ℝ (fun x => (Φ x).det) Set.univ := by
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (σ i) i)
  have hnull := measure_zeroSet_of_analytic μ hφ ⟨x₀, by rw [h₀, Matrix.det_one]; exact one_ne_zero⟩
  rw [ae_iff]
  simpa only [isUnit_iff_ne_zero, not_not] using hnull

/-- Helper: at almost every `(θ, A)` the conditions `OneBlockGenericReGLURMS θ` hold and the skip
`A = R 0` is invertible, for `d_in, d_out ≥ d ≥ 2`. -/
private theorem ae_generic_lzh
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [hμ : μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, OneBlockGenericReGLURMS p.1 ∧ IsUnit (p.2 0).det := by
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := borelSpace_skips_lzh
  have hBp : BorelSpace (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)) := Prod.borelSpace
  have h1 := ae_fst_lzh hBs μ hμ (ae_oneBlockGenericReGLURMS Measure.addHaar hd hdIn hdOut)
  have h2 := ae_isUnit_det_lzh hBp μ hμ
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix d d ℝ) 0)
      ∘ₗ (LinearMap.snd ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
        (Fin 1 → Matrix d d ℝ))) (0, fun _ => 1) rfl
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", for one ReGLU block with
a hidden unit and a full learned skip:** with `d_in, d_out ≥ d ≥ 2`, at almost every weights and
skip `(θ, A)`, `funDimLearned = P + d² − (d(d−1) + 2) − 2 d_hidden`. -/
theorem ae_funDimLearned_reglu_oneBlock_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.gated relu (rmsNorm 0) hid) p
        + ((Fintype.card d * (Fintype.card d - 1) + 2) + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  -- the conditions of the proof at almost every `(θ, A)`
  filter_upwards [ae_generic_lzh μ hd hdIn hdOut, ae_turnsActiveRowsGatedSkip_reglu μ hd,
    ae_exists_turned_row_skip_reglu μ hd] with p hp hturn hw
  exact funDimLearned_reglu_oneBlock_rmsNorm_zero p.1 hp.1 hd p.2 hp.2 hturn hw

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", in the paper's own
sense, for one ReGLU block with a hidden unit and a full learned skip:** at almost every weights
and skip `(θ, A)`, a finite batch of inputs at which no normalized row vanishes and no gate sits
at its kink, on which the Jacobian in the weights and the skip has the rank
`P + d² − (d(d−1) + 2) − 2 d_hidden`. -/
theorem ae_exists_jacobianRankSkips_reglu_oneBlock_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) p.1 p.2
        ∩ noKinkGateRMS p.1) ∧
      jacobianRankSkips (Arch.gated relu (rmsNorm 0) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X p
          + ((Fintype.card d * (Fintype.card d - 1) + 2) + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  -- the conditions of the proof at almost every `(θ, A)`
  filter_upwards [ae_generic_lzh μ hd hdIn hdOut, ae_turnsActiveRowsGatedSkip_reglu μ hd,
    ae_exists_turned_row_skip_reglu μ hd] with p hp hturn hw
  exact exists_jacobianRankSkips_reglu_oneBlock_rmsNorm_zero p.1 hp.1 hd p.2 hp.2 hturn hw

/-- **Theorem B.1 (iii) of the skips paper, "For `ε = 0` it exceeds that of the residual network
with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for […] ReGLU blocks", for
one ReGLU block with a hidden unit:** with `d_in, d_out ≥ d ≥ 2`, at almost every weights and
full learned skip `(θ, A)` the functional dimension exceeds that of the residual network with
the weights `θ` by exactly `d(d+1)/2 − 1`. -/
theorem ae_funDimLearned_reglu_oneBlock_rmsNorm_zero_eq_residual_add [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [hμ : μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.gated relu (rmsNorm 0) hid) p
      = funDim (Arch.gated relu (rmsNorm 0) hid) 1 p.1
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := borelSpace_skips_lzh
  -- `d(d−1)` and `d(d+1)` are even, `d(d+1) + d(d−1) = 2 d²`, and `d(d+1) ≥ 2`
  have e1 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  have e2 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (Fintype.card d))
  have e3 : Fintype.card d * (Fintype.card d + 1) + Fintype.card d * (Fintype.card d - 1)
      = 2 * Fintype.card d ^ 2 := by
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card d = m + 1 := ⟨Fintype.card d - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    ring
  have e4 : 2 ≤ Fintype.card d * (Fintype.card d + 1) := by nlinarith
  filter_upwards [ae_funDimLearned_reglu_oneBlock_rmsNorm_zero μ hd hdIn hdOut,
    ae_fst_lzh hBs μ hμ
      (ae_funDim_reglu_oneBlock_residual_rmsNorm_zero Measure.addHaar hd hdIn hdOut)]
    with p hp hr
  generalize Fintype.card d * (Fintype.card d + 1) = y at e2 e3 e4 ⊢
  generalize Fintype.card d * (Fintype.card d - 1) = x at hp hr e1 e3
  generalize Fintype.card d ^ 2 = q at hp e3
  omega

end Skips
