import SkipsLean.OneBlock.LearnedSkipRMSZeroRescale

/-!
# One ReLU or ReLU² block with a full learned skip under pre-RMSNorm with `ε = 0`: generic
parameters

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. […] For `ε = 0` it exceeds that of the residual
network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and
ReGLU blocks."

`OneBlock/LearnedSkipRMSZeroRescale.lean` has the value at one parameter under the conditions of
the proof, among them the condition that the paper does not state: the block turns a dense set
of the active rows for the skip `A` (`TurnsActiveRowsSkip`). Here, for ReLU and ReLU² blocks
with `d ≥ 2`:

* this condition, and "the block turns some row off the kinks", at almost every weights and skip
  `(θ, A)` (the twins for a learned skip of `ae_turnsActiveRows_relu` and its siblings,
  `OneBlock/ResidualRMSZeroRescaleGeneric.lean`: for every nonempty set `S` of hidden units the
  map `v ↦ ∑_{i ∈ S} (v c_i)^k a_i` is at almost every `(θ, A)` not parallel to `v A` for all
  `v`, and a nonzero polynomial does not vanish on an open set);
* the theorem at almost every `(θ, A)`, for `d_in, d_out ≥ d ≥ 2` and a block of any width with
  a hidden unit: the value `P + d² − (d(d−1) + 2) − d_hidden` of Lean's `funDimLearned`, a batch
  of the paper's inputs with this rank, and the equality with the residual network at the same
  weights, `funDimLearned = funDim + d(d+1)/2 − 1`.

Not stated here: ReGLU blocks (`OneBlock/LearnedSkipRMSZeroReGLU.lean`,
`OneBlock/LearnedSkipRMSZeroReGLUGeneric.lean`); the upper triangular skip
(`OneBlock/LearnedSkipTriangularRMSZeroRescale.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ}

/-! ### Helpers: the polynomial `w_S` and the rows on which the block is `b_S` -/

omit [DecidableEq d] in
/-- Helper: the skips `Fin 1 → Matrix d d ℝ` carry the Borel σ-algebra of their norm topology (a
copy of the private `borelSpace_skips_lsk` of `OneBlock/LearnedSkipKinds.lean`). -/
private theorem borelSpace_skips_lzq : BorelSpace (Fin 1 → Matrix d d ℝ) :=
  inferInstanceAs (BorelSpace (Fin 1 → d → d → ℝ))

/-- Helper: an analytic function on a finite-dimensional space with the Borel σ-algebra that is
not identically zero is nonzero at almost every point of a Haar measure (`ae_ne_zero_of_analytic`
with the instances passed as arguments). -/
private theorem ae_ne_zero_of_analytic_lzg {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasurableSpace P] (hB : BorelSpace P) (μ : Measure P)
    (hμ : μ.IsAddHaarMeasure) {g : P → ℝ} (hg : AnalyticOnNhd ℝ g Set.univ)
    (hne : ∃ y, g y ≠ 0) : ∀ᵐ y ∂μ, g y ≠ 0 :=
  ae_ne_zero_of_analytic μ hg hne

omit [DecidableEq d] in
/-- Helper: the polynomial `w_S(u) = (u M)_p b_S(u)_q − (u M)_q b_S(u)_p`, with
`b_S(u) = ∑_{i ∈ S} (u c_i)^k a_i` (`c_i` the columns of `R`, `a_i` the rows of `W`, `M` the
skip). -/
private def wPoly_lzg {m : Type*} [Fintype m] (k : ℕ) (S : Finset m) (p q : d)
    (M : Matrix d d ℝ) (R : Matrix d m ℝ) (W : Matrix m d ℝ) (u : d → ℝ) : ℝ :=
  (u ᵥ* M) p * ∑ i ∈ S, (u ᵥ* R) i ^ k * W i q - (u ᵥ* M) q * ∑ i ∈ S, (u ᵥ* R) i ^ k * W i p

omit [Fintype d] [DecidableEq d] in
/-- Helper: two rows `x`, `y` with a nonzero minor `x_p y_q − x_q y_p` are linearly
independent. -/
private theorem linearIndependent_of_minor_lzg {x y : d → ℝ} {p q : d}
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
private theorem analyticOnNhd_vecMul_lzg {m : Type*} [Fintype m] (R : Matrix d m ℝ) (i : m) :
    AnalyticOnNhd ℝ (fun u : d → ℝ => (u ᵥ* R) i) Set.univ :=
  analyticOnNhd_linear ((LinearMap.proj i).comp (Matrix.vecMulLinear R))

omit [DecidableEq d] in
/-- Helper: `u ↦ (u R)_i` is continuous. -/
private theorem continuous_vecMul_lzg {m : Type*} [Fintype m] (R : Matrix d m ℝ) (i : m) :
    Continuous fun u : d → ℝ => (u ᵥ* R) i :=
  continuousOn_univ.mp (analyticOnNhd_vecMul_lzg R i).continuousOn

omit [DecidableEq d] in
/-- Helper: `u ↦ w_S(u)` is analytic (a polynomial in `u`). -/
private theorem analyticOnNhd_wPoly_lzg {m : Type*} [Fintype m] (k : ℕ) (S : Finset m)
    (p q : d) (M : Matrix d d ℝ) (R : Matrix d m ℝ) (W : Matrix m d ℝ) :
    AnalyticOnNhd ℝ (fun u => wPoly_lzg k S p q M R W u) Set.univ := by
  have hs : ∀ o : d, AnalyticOnNhd ℝ (fun u : d → ℝ => ∑ i ∈ S, (u ᵥ* R) i ^ k * W i o)
      Set.univ := fun o =>
    Finset.analyticOnNhd_fun_sum _ fun i _ =>
      ((analyticOnNhd_vecMul_lzg R i).pow k).mul analyticOnNhd_const
  exact ((analyticOnNhd_vecMul_lzg M p).mul (hs q)).sub
    ((analyticOnNhd_vecMul_lzg M q).mul (hs p))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: an entry of the read is analytic in the weights and the skip (it is linear). -/
private theorem analyticOnNhd_read_lzg (j : d) (i : hid 0) :
    AnalyticOnNhd ℝ
      (fun x : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ) => x.1.read 0 j i) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ j i).comp
    ((Params.linRead (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) (dIn := dIn)
      (dOut := dOut) 0).comp (LinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: an entry of the write is analytic in the weights and the skip (it is linear). -/
private theorem analyticOnNhd_write_lzg (i : hid 0) (j : d) :
    AnalyticOnNhd ℝ
      (fun x : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ) => x.1.write 0 i j) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ i j).comp
    ((Params.linWrite (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) (dIn := dIn)
      (dOut := dOut) 0).comp (LinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: an entry of the skip `A = x.2 0` is analytic in the weights and the skip (it is
linear). -/
private theorem analyticOnNhd_skip_lzg (j o : d) :
    AnalyticOnNhd ℝ
      (fun x : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ) => x.2 0 j o) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ j o).comp
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix d d ℝ) 0).comp
      (LinearMap.snd ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
        (Fin 1 → Matrix d d ℝ))))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: at a fixed row `u`, `(θ, A) ↦ w_S(θ, A, u)` is analytic (a polynomial in the weights
and the skip). -/
private theorem analyticOnNhd_wPoly_params_lzg (k : ℕ) (S : Finset (hid 0)) (p q : d)
    (u : d → ℝ) :
    AnalyticOnNhd ℝ (fun x : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ) =>
      wPoly_lzg k S p q (x.2 0) (x.1.read 0) (x.1.write 0) u) Set.univ := by
  have hm : ∀ o : d, AnalyticOnNhd ℝ
      (fun x : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ) => (u ᵥ* x.2 0) o) Set.univ := fun o =>
    Finset.analyticOnNhd_fun_sum _ fun j _ =>
      analyticOnNhd_const.mul (analyticOnNhd_skip_lzg j o)
  have hv : ∀ i : hid 0, AnalyticOnNhd ℝ
      (fun x : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ) => (u ᵥ* x.1.read 0) i) Set.univ := fun i =>
    Finset.analyticOnNhd_fun_sum _ fun j _ =>
      analyticOnNhd_const.mul (analyticOnNhd_read_lzg j i)
  have hs : ∀ o : d, AnalyticOnNhd ℝ
      (fun x : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ) => ∑ i ∈ S, (u ᵥ* x.1.read 0) i ^ k * x.1.write 0 i o)
      Set.univ := fun o =>
    Finset.analyticOnNhd_fun_sum _ fun i _ => ((hv i).pow k).mul (analyticOnNhd_write_lzg i o)
  exact ((hm p).mul (hs q)).sub ((hm q).mul (hs p))

omit [Fintype T] [Nonempty T] in
/-- Helper: at almost every weights and skip `(θ, A)`, `w_S(θ, A, 1) ≠ 0` for every nonempty
set `S` of hidden units: it is a polynomial in `(θ, A)`, equal to `−|S|` at the weights with
`c_i = e_p`, `a_i = e_p` and the skip `A = I`. -/
private theorem ae_wPoly_ne_zero_lzg
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [hμ : μ.IsAddHaarMeasure] {p q : d} (hpq : p ≠ q) (k : ℕ) :
    ∀ᵐ x ∂μ, ∀ S : Finset (hid 0), S.Nonempty →
      wPoly_lzg k S p q (x.2 0) (x.1.read 0) (x.1.write 0) (fun _ => 1) ≠ 0 := by
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := borelSpace_skips_lzq
  have hBp : BorelSpace (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)) := Prod.borelSpace
  -- finitely many sets `S`: one at a time
  refine ae_all_iff.2 fun S => ?_
  by_cases hS : S.Nonempty
  · -- the weights with `c_i = e_p` and `a_i = e_p` for every unit and the skip `I`: there
    -- `(1 A)_p = (1 A)_q = 1` and `b_S(1) = |S| e_p`
    let θ₀ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut :=
      ⟨0, fun _ => Matrix.of fun j _ => if j = p then 1 else 0,
        fun _ => Matrix.of fun _ j => if j = p then 1 else 0, 0⟩
    have h1 : ∀ i : hid 0, ((fun _ => (1 : ℝ)) ᵥ* θ₀.read 0) i = 1 := fun i => by
      simp [θ₀, Matrix.vecMul, dotProduct]
    have hM : ∀ o : d, ((fun _ => (1 : ℝ)) ᵥ* (1 : Matrix d d ℝ)) o = 1 := fun o => by
      rw [Matrix.vecMul_one]
    have h0 : wPoly_lzg k S p q 1 (θ₀.read 0) (θ₀.write 0) (fun _ => 1) = -(S.card : ℝ) := by
      simp only [wPoly_lzg, h1, hM]
      simp [θ₀, hpq.symm]
    have hne : wPoly_lzg k S p q 1 (θ₀.read 0) (θ₀.write 0) (fun _ => 1) ≠ 0 := by
      rw [h0]
      exact neg_ne_zero.2 (Nat.cast_ne_zero.2 hS.card_pos.ne')
    -- a polynomial that is not identically zero is nonzero at almost every `(θ, A)`
    exact (ae_ne_zero_of_analytic_lzg hBp μ hμ (analyticOnNhd_wPoly_params_lzg k S p q _)
      ⟨(θ₀, fun _ => 1), hne⟩).mono fun _ h _ => h
  · exact Filter.Eventually.of_forall fun _ h => absurd h hS

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: at almost every weights and skip `(θ, A)`, the entries of the read at the
coordinate `p` are nonzero, so no column of the read is zero. -/
private theorem ae_read_ne_zero_lzg
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [hμ : μ.IsAddHaarMeasure] (p : d) :
    ∀ᵐ x ∂μ, ∀ i : hid 0, x.1.read 0 p i ≠ 0 := by
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := borelSpace_skips_lzq
  have hBp : BorelSpace (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)) := Prod.borelSpace
  -- the weights with all entries `1`
  let θ₁ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1,
      Matrix.of fun _ _ => 1⟩
  exact ae_all_iff.2 fun i =>
    ae_ne_zero_of_analytic_lzg hBp μ hμ (analyticOnNhd_read_lzg p i)
      ⟨(θ₁, 0), show (1 : ℝ) ≠ 0 from one_ne_zero⟩

omit [DecidableEq d] in
/-- Helper (the condition at one weights and skip): if `σ(z) = z^k` for `z > 0` and `σ(z) = 0`
for `z ≤ 0`, and `w_S(1) ≠ 0` for every nonempty `S`, then every row `v` off the kinks with an
active unit is a limit of rows `u` such that `u M` and `B(u)` are linearly independent. -/
private theorem mem_closure_of_wPoly_lzg {m : Type*} [Fintype m] {k : ℕ}
    (hpos : ∀ z, 0 < z → σ z = z ^ k) (hnonpos : ∀ z, z ≤ 0 → σ z = 0) {p q : d}
    (M : Matrix d d ℝ) (R : Matrix d m ℝ) (W : Matrix m d ℝ)
    (hS : ∀ S : Finset m, S.Nonempty → wPoly_lzg k S p q M R W (fun _ => 1) ≠ 0)
    (v : d → ℝ) (hv : ∀ i, (v ᵥ* R) i ≠ 0) (hact : ∃ i, σ ((v ᵥ* R) i) ≠ 0) :
    v ∈ closure {u : d → ℝ | LinearIndependent ℝ ![u ᵥ* M, vanillaBlock σ R W u]} := by
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
      continuous_const.mul (continuous_vecMul_lzg R i)
    exact Filter.Tendsto.eventually_const_lt (mul_self_pos.2 (hv i)) (hc.tendsto v)
  -- on `R_S` the block is `b_S`, so `w_S(u) ≠ 0` makes `u M`, `B(u)` independent
  have hLI : ∀ u : d → ℝ, (∀ i, 0 < (v ᵥ* R) i * (u ᵥ* R) i) → wPoly_lzg k S p q M R W u ≠ 0 →
      LinearIndependent ℝ ![u ᵥ* M, vanillaBlock σ R W u] := by
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
    apply linearIndependent_of_minor_lzg (p := p) (q := q)
    rw [hb p, hb q]
    exact hw
  rw [mem_closure_iff_nhds]
  intro t ht
  by_contra hne
  -- otherwise `w_S` vanishes near `v`, hence everywhere (identity theorem), also at `1`
  have hz : (fun u => wPoly_lzg k S p q M R W u) =ᶠ[nhds v] 0 := by
    filter_upwards [ht, hO] with u hut hu
    by_contra hw
    exact hne ⟨u, hut, hLI u hu hw⟩
  have h0 :=
    (analyticOnNhd_wPoly_lzg k S p q M R W).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ v) hz
  exact hS S hSne (h0 (Set.mem_univ _))

/-- Helper (some row off the kinks is turned): if no column of `R` is zero, `σ ≠ 0` on the
positive reals and every active row off the kinks is a limit of turned rows, then some row `v`
off the kinks has `v M` and the output of the block there linearly independent. -/
private theorem exists_turned_of_closure_lzg {m : Type*} [Fintype m] [Nonempty m]
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (p : d) (M : Matrix d d ℝ) (R : Matrix d m ℝ)
    (W : Matrix m d ℝ) (hR : ∀ i, R p i ≠ 0)
    (hturn : ∀ v : d → ℝ, (∀ i, (v ᵥ* R) i ≠ 0) → (∃ i, σ ((v ᵥ* R) i) ≠ 0) →
      v ∈ closure {u : d → ℝ | LinearIndependent ℝ ![u ᵥ* M, vanillaBlock σ R W u]}) :
    ∃ v : d → ℝ, (∀ i, (v ᵥ* R) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* M, vanillaBlock σ R W v] := by
  -- almost every row is off the kinks: each `u ↦ (u R)_i` is a nonzero linear form
  have hae : ∀ᵐ u ∂(volume : Measure (d → ℝ)), ∀ i, (u ᵥ* R) i ≠ 0 :=
    ae_all_iff.2 fun i => ae_ne_zero_of_analytic volume (analyticOnNhd_vecMul_lzg R i)
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
    Filter.eventually_all.2 fun i => (continuous_vecMul_lzg R i).continuousAt.eventually_ne (hv i)
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff_nhds.1 (hturn v hv ⟨_, hσ _ hv0⟩) _ hO
  exact ⟨w, hw1, hw2⟩

/-- Helper: ReLU is `z ↦ z^1` on the positive reals. -/
private theorem relu_pos_lzg (z : ℝ) (hz : 0 < z) : relu z = z ^ 1 := by
  rw [relu, max_eq_left hz.le, pow_one]

/-- Helper: ReLU vanishes on the nonpositive reals. -/
private theorem relu_nonpos_lzg (z : ℝ) (hz : z ≤ 0) : relu z = 0 := by
  rw [relu, max_eq_right hz]

/-- Helper: ReLU² is `z ↦ z^2` on the positive reals. -/
private theorem reluSq_pos_lzg (z : ℝ) (hz : 0 < z) : reluSq z = z ^ 2 := by
  rw [reluSq, max_eq_left hz.le]

/-- Helper: ReLU² vanishes on the nonpositive reals. -/
private theorem reluSq_nonpos_lzg (z : ℝ) (hz : z ≤ 0) : reluSq z = 0 := by
  rw [reluSq, max_eq_right hz]
  norm_num

omit [Fintype T] [Nonempty T] in
/-- **A ReLU block turns a dense set of the active rows for the skip `A` at almost every weights
and skip `(θ, A)`,** for `d ≥ 2`. -/
theorem ae_turnsActiveRowsSkip_relu
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, TurnsActiveRowsSkip p.1 (p.2 0) := by
  -- two coordinates `p ≠ q` of `d`
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  -- at almost every `(θ, A)`, `w_S(θ, A, 1) ≠ 0` for every nonempty `S`
  filter_upwards [ae_wPoly_ne_zero_lzg μ hpq 1] with x hx
  -- then every active row off the kinks is a limit of turned rows
  intro v hv hact
  exact mem_closure_of_wPoly_lzg relu_pos_lzg relu_nonpos_lzg _ _ _ hx v hv hact

omit [Fintype T] [Nonempty T] in
/-- **A ReLU² block turns a dense set of the active rows for the skip `A` at almost every weights
and skip `(θ, A)`,** for `d ≥ 2`. -/
theorem ae_turnsActiveRowsSkip_reluSq
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, TurnsActiveRowsSkip p.1 (p.2 0) := by
  -- two coordinates `p ≠ q` of `d`
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  -- at almost every `(θ, A)`, `w_S(θ, A, 1) ≠ 0` for every nonempty `S`
  filter_upwards [ae_wPoly_ne_zero_lzg μ hpq 2] with x hx
  -- then every active row off the kinks is a limit of turned rows
  intro v hv hact
  exact mem_closure_of_wPoly_lzg reluSq_pos_lzg reluSq_nonpos_lzg _ _ _ hx v hv hact

omit [Fintype T] [Nonempty T] in
/-- **A ReLU block with a hidden unit turns some row off the kinks, for the skip `A`, at almost
every weights and skip `(θ, A)`,** for `d ≥ 2`. -/
theorem ae_exists_turned_row_skip_relu [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* p.1.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* p.2 0, vanillaBlock relu (p.1.read 0) (p.1.write 0) v] := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  let p : d := Classical.arbitrary d
  -- at almost every `(θ, A)` the block turns a dense set of the active rows and no column of the
  -- read is zero
  filter_upwards [ae_turnsActiveRowsSkip_relu μ hd, ae_read_ne_zero_lzg μ p] with x hturn hR
  -- a row off the kinks with an active unit, and turned rows near it
  refine exists_turned_of_closure_lzg (fun z hz => ?_) p _ _ _ hR hturn
  rw [relu_pos_lzg z hz, pow_one]
  exact hz.ne'

omit [Fintype T] [Nonempty T] in
/-- **A ReLU² block with a hidden unit turns some row off the kinks, for the skip `A`, at almost
every weights and skip `(θ, A)`,** for `d ≥ 2`. -/
theorem ae_exists_turned_row_skip_reluSq [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* p.1.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* p.2 0, vanillaBlock reluSq (p.1.read 0) (p.1.write 0) v] := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  let p : d := Classical.arbitrary d
  -- at almost every `(θ, A)` the block turns a dense set of the active rows and no column of the
  -- read is zero
  filter_upwards [ae_turnsActiveRowsSkip_reluSq μ hd, ae_read_ne_zero_lzg μ p] with x hturn hR
  -- a row off the kinks with an active unit, and turned rows near it
  refine exists_turned_of_closure_lzg (fun z hz => ?_) p _ _ _ hR hturn
  rw [reluSq_pos_lzg z hz]
  exact pow_ne_zero 2 hz.ne'

/-! ### Helpers: almost every `(θ, A)` -/

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: a condition on the weights that holds at almost every `θ` holds at almost every
`(θ, v)` (a copy of the private `ae_fst_lsk` of `OneBlock/LearnedSkipKinds.lean`). -/
private theorem ae_fst_lzq {A : Arch T d 1} {V : Type*} [NormedAddCommGroup V]
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
private theorem ae_isUnit_det_lzq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

/-- Helper: at almost every `(θ, A)` the conditions `OneBlockGenericRMS θ` hold and the skip
`A = R 0` is invertible, for `d_in, d_out ≥ d ≥ 2`. -/
private theorem ae_generic_lzq
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [hμ : μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, OneBlockGenericRMS p.1 ∧ IsUnit (p.2 0).det := by
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := borelSpace_skips_lzq
  have hBp : BorelSpace (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)) := Prod.borelSpace
  have h1 := ae_fst_lzq hBs μ hμ (ae_oneBlockGenericRMS Measure.addHaar hd hdIn hdOut)
  have h2 := ae_isUnit_det_lzq hBp μ hμ
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix d d ℝ) 0)
      ∘ₗ (LinearMap.snd ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
        (Fin 1 → Matrix d d ℝ))) (0, fun _ => 1) rfl
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

omit [Fintype T] [Nonempty T] in
/-- Helper (the equality with the residual network at the same weights): from the value
`fd + (d(d−1) + 2 + s) = P + d²` with the learned skip at almost every `(θ, A)` and the value
`fd₁ + (d(d−1)/2 + 1 + s) = P` of the residual network at almost every `θ`, the difference at
almost every `(θ, A)` is `d² − d(d−1)/2 − 1 = d(d+1)/2 − 1`. -/
private theorem ae_eq_residual_add_lzq {A : Arch T d 1}
    (μ : Measure (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))) [hμ : μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) {s : ℕ}
    (hval : ∀ᵐ p ∂μ, funDimLearned A p
        + ((Fintype.card d * (Fintype.card d - 1) + 2) + s)
      = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2)
    (hres : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), funDim A 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + s)
      = Module.finrank ℝ (Params A dIn dOut)) :
    ∀ᵐ p ∂μ, funDimLearned A p
      = funDim A 1 p.1 + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := borelSpace_skips_lzq
  -- `d(d−1)` and `d(d+1)` are even, `d(d+1) + d(d−1) = 2 d²`, and `d(d+1)/2 ≥ 1`
  have e1 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  have e2 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (Fintype.card d))
  have e3 : Fintype.card d * (Fintype.card d + 1) + Fintype.card d * (Fintype.card d - 1)
      = 2 * Fintype.card d ^ 2 := by
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card d = m + 1 := ⟨Fintype.card d - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    ring
  have e4 : 2 ≤ Fintype.card d * (Fintype.card d + 1) := by nlinarith
  filter_upwards [hval, ae_fst_lzq hBs μ hμ hres] with p hp hr
  generalize Fintype.card d * (Fintype.card d + 1) = y at e2 e3 e4 ⊢
  generalize Fintype.card d * (Fintype.card d - 1) = x at hp hr e1 e3
  generalize Fintype.card d ^ 2 = q at hp e3
  omega

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", for one ReLU block with
a hidden unit and a full learned skip:** with `d_in, d_out ≥ d ≥ 2`, at almost every weights and
skip `(θ, A)`, `funDimLearned = P + d² − (d(d−1) + 2) − d_hidden`. -/
theorem ae_funDimLearned_relu_oneBlock_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp relu (rmsNorm 0) hid) p
        + ((Fintype.card d * (Fintype.card d - 1) + 2) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  -- the conditions of the proof at almost every `(θ, A)`
  filter_upwards [ae_generic_lzq μ hd hdIn hdOut, ae_turnsActiveRowsSkip_relu μ hd,
    ae_exists_turned_row_skip_relu μ hd] with p hp hturn hw
  exact funDimLearned_mlp_oneBlock_rescale_rmsNorm_zero (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous (relu_unitsRescaleSphere d d (hid 0)) p.1 hp.1 hd p.2 hp.2 hturn hw

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", in the paper's own
sense, for one ReLU block with a hidden unit and a full learned skip:** at almost every weights
and skip `(θ, A)`, a finite batch of inputs at which no normalized row vanishes and no hidden
unit sits at its kink, on which the Jacobian in the weights and the skip has the rank
`P + d² − (d(d−1) + 2) − d_hidden`. -/
theorem ae_exists_jacobianRankSkips_relu_oneBlock_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ learnedZeroDomain (Arch.mlp relu (rmsNorm 0) hid) p.1 p.2 ∩ noKinkRMS p.1) ∧
      jacobianRankSkips (Arch.mlp relu (rmsNorm 0) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X p
          + ((Fintype.card d * (Fintype.card d - 1) + 2) + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  -- the conditions of the proof at almost every `(θ, A)`
  filter_upwards [ae_generic_lzq μ hd hdIn hdOut, ae_turnsActiveRowsSkip_relu μ hd,
    ae_exists_turned_row_skip_relu μ hd] with p hp hturn hw
  exact exists_jacobianRankSkips_mlp_oneBlock_rescale_rmsNorm_zero
    (fun _ hz => hasDerivAt_relu hz) relu_homogeneous (relu_unitsRescaleSphere d d (hid 0)) p.1
    hp.1 hd p.2 hp.2 hturn hw

/-- **Theorem B.1 (iii) of the skips paper, "For `ε = 0` it exceeds that of the residual network
with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU […] blocks", for
one ReLU block with a hidden unit:** with `d_in, d_out ≥ d ≥ 2`, at almost every weights and
full learned skip `(θ, A)` the functional dimension exceeds that of the residual network with
the weights `θ` by exactly `d(d+1)/2 − 1`. -/
theorem ae_funDimLearned_relu_oneBlock_rmsNorm_zero_eq_residual_add [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp relu (rmsNorm 0) hid) p
      = funDim (Arch.mlp relu (rmsNorm 0) hid) 1 p.1
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) :=
  ae_eq_residual_add_lzq μ hd (ae_funDimLearned_relu_oneBlock_rmsNorm_zero μ hd hdIn hdOut)
    (ae_funDim_relu_oneBlock_residual_rmsNorm_zero Measure.addHaar hd hdIn hdOut)

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", for one ReLU² block with
a hidden unit and a full learned skip:** with `d_in, d_out ≥ d ≥ 2`, at almost every weights and
skip `(θ, A)`, `funDimLearned = P + d² − (d(d−1) + 2) − d_hidden`. -/
theorem ae_funDimLearned_reluSq_oneBlock_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp reluSq (rmsNorm 0) hid) p
        + ((Fintype.card d * (Fintype.card d - 1) + 2) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  -- the conditions of the proof at almost every `(θ, A)`
  filter_upwards [ae_generic_lzq μ hd hdIn hdOut, ae_turnsActiveRowsSkip_reluSq μ hd,
    ae_exists_turned_row_skip_reluSq μ hd] with p hp hturn hw
  exact funDimLearned_mlp_oneBlock_rescale_rmsNorm_zero (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous (reluSq_unitsRescaleSphere d d (hid 0)) p.1 hp.1 hd p.2 hp.2 hturn hw

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", in the paper's own
sense, for one ReLU² block with a hidden unit and a full learned skip:** at almost every weights
and skip `(θ, A)`, a finite batch of inputs at which no normalized row vanishes and no hidden
unit sits at its kink, on which the Jacobian in the weights and the skip has the rank
`P + d² − (d(d−1) + 2) − d_hidden`. -/
theorem ae_exists_jacobianRankSkips_reluSq_oneBlock_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ learnedZeroDomain (Arch.mlp reluSq (rmsNorm 0) hid) p.1 p.2 ∩ noKinkRMS p.1) ∧
      jacobianRankSkips (Arch.mlp reluSq (rmsNorm 0) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X p
          + ((Fintype.card d * (Fintype.card d - 1) + 2) + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  -- the conditions of the proof at almost every `(θ, A)`
  filter_upwards [ae_generic_lzq μ hd hdIn hdOut, ae_turnsActiveRowsSkip_reluSq μ hd,
    ae_exists_turned_row_skip_reluSq μ hd] with p hp hturn hw
  exact exists_jacobianRankSkips_mlp_oneBlock_rescale_rmsNorm_zero
    (fun z _ => hasDerivAt_reluSq z) reluSq_homogeneous (reluSq_unitsRescaleSphere d d (hid 0))
    p.1 hp.1 hd p.2 hp.2 hturn hw

/-- **Theorem B.1 (iii) of the skips paper, "For `ε = 0` it exceeds that of the residual network
with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for […] ReLU² […] blocks",
for one ReLU² block with a hidden unit:** with `d_in, d_out ≥ d ≥ 2`, at almost every weights and
full learned skip `(θ, A)` the functional dimension exceeds that of the residual network with
the weights `θ` by exactly `d(d+1)/2 − 1`. -/
theorem ae_funDimLearned_reluSq_oneBlock_rmsNorm_zero_eq_residual_add [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp reluSq (rmsNorm 0) hid) p
      = funDim (Arch.mlp reluSq (rmsNorm 0) hid) 1 p.1
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) :=
  ae_eq_residual_add_lzq μ hd (ae_funDimLearned_reluSq_oneBlock_rmsNorm_zero μ hd hdIn hdOut)
    (ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero Measure.addHaar hd hdIn hdOut)

end Skips
