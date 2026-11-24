import SkipsLean.OneBlock.LearnedSkipRMSZeroRescaleGeneric
import SkipsLean.OneBlock.LearnedSkipRMSZeroReGLUGeneric

/-!
# The block turns a dense set of the active rows, for a skip that depends linearly on parameters

`OneBlock/LearnedSkipRMSZeroRescale.lean` and `OneBlock/LearnedSkipRMSZeroReGLU.lean` state the
condition that the proof of Theorem B.1 (iii) of the skips paper for `ε = 0` needs and the paper
does not state: the rows `u` at which `u A` and the output of the block are linearly independent
are dense among the rows off the kinks with an active unit (`TurnsActiveRowsSkip`,
`TurnsActiveRowsGatedSkip`). Their files of generic parameters prove it at almost every weights
and full skip `(θ, A)`.

The theorem is for a learned skip that is "full or upper triangular". Here the same statements
once, for a skip `ι v` that depends linearly on a parameter `v` of a finite-dimensional space and
is the identity at one `v₀` (the full skip: `ι` the identity; the upper triangular skip: `ι` the
inclusion of the upper triangular matrices): at almost every `(θ, v)` the block turns a dense set
of the active rows for the skip `ι v`, and turns some row off the kinks. The proofs are those for
the full skip: for every nonempty set `S` of hidden units, a polynomial in `(θ, v)` that is not
zero at one point with the skip `1`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Helpers: the polynomial `w_S` and the rows on which the block is `b_S` -/

/-- Helper: an analytic function on a finite-dimensional space with the Borel σ-algebra that is
not identically zero is nonzero at almost every point of a Haar measure (`ae_ne_zero_of_analytic`
with the instances passed as arguments). -/
private theorem ae_ne_zero_of_analytic_tsl {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasurableSpace P] (hB : BorelSpace P) (μ : Measure P)
    (hμ : μ.IsAddHaarMeasure) {g : P → ℝ} (hg : AnalyticOnNhd ℝ g Set.univ)
    (hne : ∃ y, g y ≠ 0) : ∀ᵐ y ∂μ, g y ≠ 0 :=
  ae_ne_zero_of_analytic μ hg hne

omit [DecidableEq d] in
/-- Helper: the polynomial `w_S(u) = (u M)_p b_S(u)_q − (u M)_q b_S(u)_p`, with
`b_S(u) = ∑_{i ∈ S} (u c_i)^k a_i` (`c_i` the columns of `R`, `a_i` the rows of `W`, `M` the
skip). -/
private def wPoly_tsl {m : Type*} [Fintype m] (k : ℕ) (S : Finset m) (p q : d)
    (M : Matrix d d ℝ) (R : Matrix d m ℝ) (W : Matrix m d ℝ) (u : d → ℝ) : ℝ :=
  (u ᵥ* M) p * ∑ i ∈ S, (u ᵥ* R) i ^ k * W i q - (u ᵥ* M) q * ∑ i ∈ S, (u ᵥ* R) i ^ k * W i p

omit [Fintype d] [DecidableEq d] in
/-- Helper: two rows `x`, `y` with a nonzero minor `x_p y_q − x_q y_p` are linearly
independent. -/
private theorem linearIndependent_of_minor_tsl {x y : d → ℝ} {p q : d}
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
private theorem analyticOnNhd_vecMul_tsl {m : Type*} [Fintype m] (R : Matrix d m ℝ) (i : m) :
    AnalyticOnNhd ℝ (fun u : d → ℝ => (u ᵥ* R) i) Set.univ :=
  analyticOnNhd_linear ((LinearMap.proj i).comp (Matrix.vecMulLinear R))

omit [DecidableEq d] in
/-- Helper: `u ↦ (u R)_i` is continuous. -/
private theorem continuous_vecMul_tsl {m : Type*} [Fintype m] (R : Matrix d m ℝ) (i : m) :
    Continuous fun u : d → ℝ => (u ᵥ* R) i :=
  continuousOn_univ.mp (analyticOnNhd_vecMul_tsl R i).continuousOn

omit [DecidableEq d] in
/-- Helper: `u ↦ w_S(u)` is analytic (a polynomial in `u`). -/
private theorem analyticOnNhd_wPoly_tsl {m : Type*} [Fintype m] (k : ℕ) (S : Finset m)
    (p q : d) (M : Matrix d d ℝ) (R : Matrix d m ℝ) (W : Matrix m d ℝ) :
    AnalyticOnNhd ℝ (fun u => wPoly_tsl k S p q M R W u) Set.univ := by
  have hs : ∀ o : d, AnalyticOnNhd ℝ (fun u : d → ℝ => ∑ i ∈ S, (u ᵥ* R) i ^ k * W i o)
      Set.univ := fun o =>
    Finset.analyticOnNhd_fun_sum _ fun i _ =>
      ((analyticOnNhd_vecMul_tsl R i).pow k).mul analyticOnNhd_const
  exact ((analyticOnNhd_vecMul_tsl M p).mul (hs q)).sub
    ((analyticOnNhd_vecMul_tsl M q).mul (hs p))

omit [Fintype T] [Nonempty T] [DecidableEq d] [MeasurableSpace V] [BorelSpace V] in
/-- Helper: an entry of the read is analytic in the weights and the parameter `v` of the skip (it
is linear). -/
private theorem analyticOnNhd_read_tsl {A : Arch T d 1} (j : d) (i : A.r 0) :
    AnalyticOnNhd ℝ (fun x : Params A dIn dOut × V => x.1.read 0 j i) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ j i).comp
    ((Params.linRead (A := A) (dIn := dIn) (dOut := dOut) 0).comp (LinearMap.fst ℝ _ V)))

omit [Fintype T] [Nonempty T] [DecidableEq d] [MeasurableSpace V] [BorelSpace V] in
/-- Helper: an entry of the write is analytic in the weights and the parameter `v` of the skip
(it is linear). -/
private theorem analyticOnNhd_write_tsl {A : Arch T d 1} (i : A.w 0) (j : d) :
    AnalyticOnNhd ℝ (fun x : Params A dIn dOut × V => x.1.write 0 i j) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ i j).comp
    ((Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) 0).comp (LinearMap.fst ℝ _ V)))

omit [Fintype T] [Nonempty T] [DecidableEq d] [MeasurableSpace V] [BorelSpace V] in
/-- Helper: an entry of the skip `ι v` is analytic in the weights and the parameter `v` (it is
linear). -/
private theorem analyticOnNhd_skip_tsl {A : Arch T d 1} (ι : V →ₗ[ℝ] Matrix d d ℝ) (j o : d) :
    AnalyticOnNhd ℝ (fun x : Params A dIn dOut × V => ι x.2 j o) Set.univ :=
  analyticOnNhd_linear
    ((Matrix.entryLinearMap ℝ ℝ j o) ∘ₗ ι ∘ₗ LinearMap.snd ℝ (Params A dIn dOut) V)

omit [Fintype T] [Nonempty T] [DecidableEq d] [MeasurableSpace V] [BorelSpace V] in
/-- Helper: at a fixed row `u`, `(θ, v) ↦ w_S(θ, ι v, u)` is analytic (a polynomial in the
weights and `v`). -/
private theorem analyticOnNhd_wPoly_params_tsl {σ : ℝ → ℝ} (ι : V →ₗ[ℝ] Matrix d d ℝ) (k : ℕ)
    (S : Finset (hid 0)) (p q : d) (u : d → ℝ) :
    AnalyticOnNhd ℝ (fun x : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × V =>
      wPoly_tsl k S p q (ι x.2) (x.1.read 0) (x.1.write 0) u) Set.univ := by
  have hm : ∀ o : d, AnalyticOnNhd ℝ
      (fun x : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × V =>
        (u ᵥ* ι x.2) o) Set.univ := fun o =>
    Finset.analyticOnNhd_fun_sum _ fun j _ => analyticOnNhd_const.mul
      (analyticOnNhd_skip_tsl (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) ι j o)
  have hv : ∀ i : hid 0, AnalyticOnNhd ℝ
      (fun x : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × V =>
        (u ᵥ* x.1.read 0) i) Set.univ := fun i =>
    Finset.analyticOnNhd_fun_sum _ fun j _ => analyticOnNhd_const.mul
      (analyticOnNhd_read_tsl (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) j i)
  have hs : ∀ o : d, AnalyticOnNhd ℝ
      (fun x : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × V =>
        ∑ i ∈ S, (u ᵥ* x.1.read 0) i ^ k * x.1.write 0 i o) Set.univ := fun o =>
    Finset.analyticOnNhd_fun_sum _ fun i _ => ((hv i).pow k).mul
      (analyticOnNhd_write_tsl (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) i o)
  exact ((hm p).mul (hs q)).sub ((hm q).mul (hs p))

omit [Fintype T] [Nonempty T] in
/-- Helper: at almost every `(θ, v)`, `w_S(θ, ι v, 1) ≠ 0` for every nonempty set `S` of hidden
units: it is a polynomial in `(θ, v)`, equal to `−|S|` at the weights with `c_i = e_p`,
`a_i = e_p` and `v = v₀`, where the skip is `ι v₀ = I`. -/
private theorem ae_wPoly_ne_zero_tsl {σ : ℝ → ℝ} (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V)
    (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × V))
    [hμ : μ.IsAddHaarMeasure] {p q : d} (hpq : p ≠ q) (k : ℕ) :
    ∀ᵐ x ∂μ, ∀ S : Finset (hid 0), S.Nonempty →
      wPoly_tsl k S p q (ι x.2) (x.1.read 0) (x.1.write 0) (fun _ => 1) ≠ 0 := by
  have hBp : BorelSpace (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × V) :=
    Prod.borelSpace
  -- finitely many sets `S`: one at a time
  refine ae_all_iff.2 fun S => ?_
  by_cases hS : S.Nonempty
  · -- the weights with `c_i = e_p` and `a_i = e_p` for every unit and the skip `ι v₀ = I`:
    -- there `(1 I)_p = (1 I)_q = 1` and `b_S(1) = |S| e_p`
    let θ₀ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut :=
      ⟨0, fun _ => Matrix.of fun j _ => if j = p then 1 else 0,
        fun _ => Matrix.of fun _ j => if j = p then 1 else 0, 0⟩
    have h1 : ∀ i : hid 0, ((fun _ => (1 : ℝ)) ᵥ* θ₀.read 0) i = 1 := fun i => by
      simp [θ₀, Matrix.vecMul, dotProduct]
    have hM : ∀ o : d, ((fun _ => (1 : ℝ)) ᵥ* (1 : Matrix d d ℝ)) o = 1 := fun o => by
      rw [Matrix.vecMul_one]
    have h0 : wPoly_tsl k S p q 1 (θ₀.read 0) (θ₀.write 0) (fun _ => 1) = -(S.card : ℝ) := by
      simp only [wPoly_tsl, h1, hM]
      simp [θ₀, hpq.symm]
    have hne : wPoly_tsl k S p q (ι v₀) (θ₀.read 0) (θ₀.write 0) (fun _ => 1) ≠ 0 := by
      rw [hι, h0]
      exact neg_ne_zero.2 (Nat.cast_ne_zero.2 hS.card_pos.ne')
    -- a polynomial that is not identically zero is nonzero at almost every `(θ, v)`
    exact (ae_ne_zero_of_analytic_tsl hBp μ hμ (analyticOnNhd_wPoly_params_tsl ι k S p q _)
      ⟨(θ₀, v₀), hne⟩).mono fun _ h _ => h
  · exact Filter.Eventually.of_forall fun _ h => absurd h hS

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: at almost every `(θ, v)`, the entries of the read at the coordinate `p` are nonzero,
so no column of the read is zero. -/
private theorem ae_read_ne_zero_tsl {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × V))
    [hμ : μ.IsAddHaarMeasure] (p : d) :
    ∀ᵐ x ∂μ, ∀ i : hid 0, x.1.read 0 p i ≠ 0 := by
  have hBp : BorelSpace (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × V) :=
    Prod.borelSpace
  -- the weights with all entries `1`
  let θ₁ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1,
      Matrix.of fun _ _ => 1⟩
  exact ae_all_iff.2 fun i =>
    ae_ne_zero_of_analytic_tsl hBp μ hμ
      (analyticOnNhd_read_tsl (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) p i)
      ⟨(θ₁, 0), show (1 : ℝ) ≠ 0 from one_ne_zero⟩

omit [DecidableEq d] in
/-- Helper (the condition at one weights and skip): if `σ(z) = z^k` for `z > 0` and `σ(z) = 0`
for `z ≤ 0`, and `w_S(1) ≠ 0` for every nonempty `S`, then every row `v` off the kinks with an
active unit is a limit of rows `u` such that `u M` and `B(u)` are linearly independent. -/
private theorem mem_closure_of_wPoly_tsl {σ : ℝ → ℝ} {m : Type*} [Fintype m] {k : ℕ}
    (hpos : ∀ z, 0 < z → σ z = z ^ k) (hnonpos : ∀ z, z ≤ 0 → σ z = 0) {p q : d}
    (M : Matrix d d ℝ) (R : Matrix d m ℝ) (W : Matrix m d ℝ)
    (hS : ∀ S : Finset m, S.Nonempty → wPoly_tsl k S p q M R W (fun _ => 1) ≠ 0)
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
      continuous_const.mul (continuous_vecMul_tsl R i)
    exact Filter.Tendsto.eventually_const_lt (mul_self_pos.2 (hv i)) (hc.tendsto v)
  -- on `R_S` the block is `b_S`, so `w_S(u) ≠ 0` makes `u M`, `B(u)` independent
  have hLI : ∀ u : d → ℝ, (∀ i, 0 < (v ᵥ* R) i * (u ᵥ* R) i) → wPoly_tsl k S p q M R W u ≠ 0 →
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
    apply linearIndependent_of_minor_tsl (p := p) (q := q)
    rw [hb p, hb q]
    exact hw
  rw [mem_closure_iff_nhds]
  intro t ht
  by_contra hne
  -- otherwise `w_S` vanishes near `v`, hence everywhere (identity theorem), also at `1`
  have hz : (fun u => wPoly_tsl k S p q M R W u) =ᶠ[nhds v] 0 := by
    filter_upwards [ht, hO] with u hut hu
    by_contra hw
    exact hne ⟨u, hut, hLI u hu hw⟩
  have h0 :=
    (analyticOnNhd_wPoly_tsl k S p q M R W).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ v) hz
  exact hS S hSne (h0 (Set.mem_univ _))

/-- Helper (some row off the kinks is turned): if no column of `R` is zero, `σ ≠ 0` on the
positive reals and every active row off the kinks is a limit of turned rows, then some row `v`
off the kinks has `v M` and the output of the block there linearly independent. -/
private theorem exists_turned_of_closure_tsl {σ : ℝ → ℝ} {m : Type*} [Fintype m] [Nonempty m]
    (hσ : ∀ z, 0 < z → σ z ≠ 0) (p : d) (M : Matrix d d ℝ) (R : Matrix d m ℝ)
    (W : Matrix m d ℝ) (hR : ∀ i, R p i ≠ 0)
    (hturn : ∀ v : d → ℝ, (∀ i, (v ᵥ* R) i ≠ 0) → (∃ i, σ ((v ᵥ* R) i) ≠ 0) →
      v ∈ closure {u : d → ℝ | LinearIndependent ℝ ![u ᵥ* M, vanillaBlock σ R W u]}) :
    ∃ v : d → ℝ, (∀ i, (v ᵥ* R) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* M, vanillaBlock σ R W v] := by
  -- almost every row is off the kinks: each `u ↦ (u R)_i` is a nonzero linear form
  have hae : ∀ᵐ u ∂(volume : Measure (d → ℝ)), ∀ i, (u ᵥ* R) i ≠ 0 :=
    ae_all_iff.2 fun i => ae_ne_zero_of_analytic volume (analyticOnNhd_vecMul_tsl R i)
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
    Filter.eventually_all.2 fun i => (continuous_vecMul_tsl R i).continuousAt.eventually_ne (hv i)
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff_nhds.1 (hturn v hv ⟨_, hσ _ hv0⟩) _ hO
  exact ⟨w, hw1, hw2⟩

/-- Helper: ReLU is `z ↦ z^1` on the positive reals. -/
private theorem relu_pos_tsl (z : ℝ) (hz : 0 < z) : relu z = z ^ 1 := by
  rw [relu, max_eq_left hz.le, pow_one]

/-- Helper: ReLU vanishes on the nonpositive reals. -/
private theorem relu_nonpos_tsl (z : ℝ) (hz : z ≤ 0) : relu z = 0 := by
  rw [relu, max_eq_right hz]

/-- Helper: ReLU² is `z ↦ z^2` on the positive reals. -/
private theorem reluSq_pos_tsl (z : ℝ) (hz : 0 < z) : reluSq z = z ^ 2 := by
  rw [reluSq, max_eq_left hz.le]

/-- Helper: ReLU² vanishes on the nonpositive reals. -/
private theorem reluSq_nonpos_tsl (z : ℝ) (hz : z ≤ 0) : reluSq z = 0 := by
  rw [reluSq, max_eq_right hz]
  norm_num

omit [Fintype T] [Nonempty T] in
/-- Helper (both MLP activations at once): if `σ(z) = z^k` for `z > 0` and `σ(z) = 0` for
`z ≤ 0`, the block turns a dense set of the active rows for the skip `ι v` at almost every
`(θ, v)`. -/
private theorem ae_turnsActiveRowsSkip_tsl {σ : ℝ → ℝ} {k : ℕ}
    (hpos : ∀ z, 0 < z → σ z = z ^ k) (hnonpos : ∀ z, z ≤ 0 → σ z = 0)
    (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V) (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × V))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, TurnsActiveRowsSkip p.1 (ι p.2) := by
  -- two coordinates `p ≠ q` of `d`
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  -- at almost every `(θ, v)`, `w_S(θ, ι v, 1) ≠ 0` for every nonempty `S`
  filter_upwards [ae_wPoly_ne_zero_tsl ι v₀ hι μ hpq k] with x hx
  -- then every active row off the kinks is a limit of turned rows
  intro v hv hact
  exact mem_closure_of_wPoly_tsl hpos hnonpos _ _ _ hx v hv hact

omit [Fintype T] [Nonempty T] in
/-- Helper (both MLP activations at once): if `σ(z) = z^k` for `z > 0` and `σ(z) = 0` for
`z ≤ 0`, a block with a hidden unit turns some row off the kinks, for the skip `ι v`, at almost
every `(θ, v)`. -/
private theorem ae_exists_turned_row_skip_tsl [Nonempty (hid 0)] {σ : ℝ → ℝ} {k : ℕ}
    (hpos : ∀ z, 0 < z → σ z = z ^ k) (hnonpos : ∀ z, z ≤ 0 → σ z = 0)
    (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V) (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut × V))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* p.1.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* ι p.2, vanillaBlock σ (p.1.read 0) (p.1.write 0) v] := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  let p : d := Classical.arbitrary d
  -- at almost every `(θ, v)` the block turns a dense set of the active rows and no column of the
  -- read is zero
  filter_upwards [ae_turnsActiveRowsSkip_tsl hpos hnonpos ι v₀ hι μ hd, ae_read_ne_zero_tsl μ p]
    with x hturn hR
  -- a row off the kinks with an active unit, and turned rows near it
  refine exists_turned_of_closure_tsl (fun z hz => ?_) p _ _ _ hR hturn
  rw [hpos z hz]
  exact pow_ne_zero k hz.ne'

omit [Fintype T] [Nonempty T] in
/-- **A ReLU block turns a dense set of the active rows for the skip `ι v`, at almost every
`(θ, v)`,** for `d ≥ 2` and a skip that depends linearly on `v` and is the identity at one
point. -/
theorem ae_turnsActiveRowsSkip_relu_of_linear (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V)
    (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, TurnsActiveRowsSkip p.1 (ι p.2) := by
  exact ae_turnsActiveRowsSkip_tsl relu_pos_tsl relu_nonpos_tsl ι v₀ hι μ hd

omit [Fintype T] [Nonempty T] in
/-- **A ReLU² block turns a dense set of the active rows for the skip `ι v`, at almost every
`(θ, v)`,** for `d ≥ 2` and a skip that depends linearly on `v` and is the identity at one
point. -/
theorem ae_turnsActiveRowsSkip_reluSq_of_linear (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V)
    (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut × V))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, TurnsActiveRowsSkip p.1 (ι p.2) := by
  exact ae_turnsActiveRowsSkip_tsl reluSq_pos_tsl reluSq_nonpos_tsl ι v₀ hι μ hd

/-! ### Helpers for ReGLU: the polynomial `w_S` of the gated block -/

omit [DecidableEq d] in
/-- Helper: the polynomial `w_S(u) = (u M)_p b_S(u)_q − (u M)_q b_S(u)_p`, with
`b_S(u) = ∑_{i ∈ S} (u g_i) (u c_i) a_i` (`g_i`, `c_i` the columns of `G`, `C`, `a_i` the rows of
`W`, `M` the skip). -/
private def wPolyGated_tsl {m : Type*} [Fintype m] (S : Finset m) (p q : d) (M : Matrix d d ℝ)
    (G C : Matrix d m ℝ) (W : Matrix m d ℝ) (u : d → ℝ) : ℝ :=
  (u ᵥ* M) p * ∑ i ∈ S, (u ᵥ* G) i * (u ᵥ* C) i * W i q
    - (u ᵥ* M) q * ∑ i ∈ S, (u ᵥ* G) i * (u ᵥ* C) i * W i p

omit [DecidableEq d] in
/-- Helper: `u ↦ w_S(u)` of the gated block is analytic (a polynomial in `u`). -/
private theorem analyticOnNhd_wPolyGated_tsl {m : Type*} [Fintype m] (S : Finset m) (p q : d)
    (M : Matrix d d ℝ) (G C : Matrix d m ℝ) (W : Matrix m d ℝ) :
    AnalyticOnNhd ℝ (fun u => wPolyGated_tsl S p q M G C W u) Set.univ := by
  have hs : ∀ o : d, AnalyticOnNhd ℝ
      (fun u : d → ℝ => ∑ i ∈ S, (u ᵥ* G) i * (u ᵥ* C) i * W i o) Set.univ := fun o =>
    Finset.analyticOnNhd_fun_sum _ fun i _ =>
      ((analyticOnNhd_vecMul_tsl G i).mul (analyticOnNhd_vecMul_tsl C i)).mul analyticOnNhd_const
  exact ((analyticOnNhd_vecMul_tsl M p).mul (hs q)).sub
    ((analyticOnNhd_vecMul_tsl M q).mul (hs p))

omit [Fintype T] [Nonempty T] [DecidableEq d] [MeasurableSpace V] [BorelSpace V] in
/-- Helper: at a fixed row `u`, `(θ, v) ↦ w_S(θ, ι v, u)` of the gated block is analytic (a
polynomial in the weights and `v`). -/
private theorem analyticOnNhd_wPolyGated_params_tsl (ι : V →ₗ[ℝ] Matrix d d ℝ)
    (S : Finset (hid 0)) (p q : d) (u : d → ℝ) :
    AnalyticOnNhd ℝ
      (fun x : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V =>
        wPolyGated_tsl S p q (ι x.2) ((x.1.read 0).submatrix id Sum.inl)
          ((x.1.read 0).submatrix id Sum.inr) (x.1.write 0) u) Set.univ := by
  have hm : ∀ o : d, AnalyticOnNhd ℝ
      (fun x : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V =>
        (u ᵥ* ι x.2) o) Set.univ := fun o =>
    Finset.analyticOnNhd_fun_sum _ fun j _ => analyticOnNhd_const.mul
      (analyticOnNhd_skip_tsl (A := Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) ι j o)
  have hv : ∀ i : hid 0 ⊕ hid 0, AnalyticOnNhd ℝ
      (fun x : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V =>
        (u ᵥ* x.1.read 0) i) Set.univ := fun i =>
    Finset.analyticOnNhd_fun_sum _ fun j _ => analyticOnNhd_const.mul
      (analyticOnNhd_read_tsl (A := Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) j i)
  have hs : ∀ o : d, AnalyticOnNhd ℝ
      (fun x : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V =>
        ∑ i ∈ S, (u ᵥ* x.1.read 0) (Sum.inl i) * (u ᵥ* x.1.read 0) (Sum.inr i)
          * x.1.write 0 i o) Set.univ := fun o =>
    Finset.analyticOnNhd_fun_sum _ fun i _ => ((hv (Sum.inl i)).mul (hv (Sum.inr i))).mul
      (analyticOnNhd_write_tsl (A := Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) i o)
  exact ((hm p).mul (hs q)).sub ((hm q).mul (hs p))

omit [Fintype T] [Nonempty T] in
/-- Helper: at almost every `(θ, v)`, `w_S(θ, ι v, 1) ≠ 0` of the gated block for every nonempty
set `S` of hidden units: it is a polynomial in `(θ, v)`, equal to `−|S|` at the weights with
`g_i = c_i = e_p`, `a_i = e_p` and `v = v₀`, where the skip is `ι v₀ = I`. -/
private theorem ae_wPolyGated_ne_zero_tsl (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V) (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V))
    [hμ : μ.IsAddHaarMeasure] {p q : d} (hpq : p ≠ q) :
    ∀ᵐ x ∂μ, ∀ S : Finset (hid 0), S.Nonempty →
      wPolyGated_tsl S p q (ι x.2) ((x.1.read 0).submatrix id Sum.inl)
        ((x.1.read 0).submatrix id Sum.inr) (x.1.write 0) (fun _ => 1) ≠ 0 := by
  have hBp : BorelSpace
      (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V) :=
    Prod.borelSpace
  -- finitely many sets `S`: one at a time
  refine ae_all_iff.2 fun S => ?_
  by_cases hS : S.Nonempty
  · -- the weights with `g_i = c_i = e_p` and `a_i = e_p` for every unit and the skip
    -- `ι v₀ = I`: there `(1 I)_p = (1 I)_q = 1` and `b_S(1) = |S| e_p`
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
    have h0 : wPolyGated_tsl S p q 1 ((θ₀.read 0).submatrix id Sum.inl)
        ((θ₀.read 0).submatrix id Sum.inr) (θ₀.write 0) (fun _ => 1) = -(S.card : ℝ) := by
      simp only [wPolyGated_tsl, hg, hc, hM]
      simp [θ₀, hpq.symm]
    have hne : wPolyGated_tsl S p q (ι v₀) ((θ₀.read 0).submatrix id Sum.inl)
        ((θ₀.read 0).submatrix id Sum.inr) (θ₀.write 0) (fun _ => 1) ≠ 0 := by
      rw [hι, h0]
      exact neg_ne_zero.2 (Nat.cast_ne_zero.2 hS.card_pos.ne')
    -- a polynomial that is not identically zero is nonzero at almost every `(θ, v)`
    exact (ae_ne_zero_of_analytic_tsl hBp μ hμ (analyticOnNhd_wPolyGated_params_tsl ι S p q _)
      ⟨(θ₀, v₀), hne⟩).mono fun _ h _ => h
  · exact Filter.Eventually.of_forall fun _ h => absurd h hS

omit [DecidableEq d] in
/-- Helper (the condition at one weights and skip): if `w_S(1) ≠ 0` for every nonempty `S`, then
every row `v` off the kinks of the gates with an active gate is a limit of rows `u` such that
`u M` and `B(u)` are linearly independent. -/
private theorem mem_closure_of_wPolyGated_tsl {m : Type*} [Fintype m] {p q : d}
    (M : Matrix d d ℝ) (G C : Matrix d m ℝ) (W : Matrix m d ℝ)
    (hS : ∀ S : Finset m, S.Nonempty → wPolyGated_tsl S p q M G C W (fun _ => 1) ≠ 0)
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
    exact hi (relu_nonpos_tsl _ (not_lt.1 h))
  -- the rows `u` with the signs of the gates of `v` form a neighbourhood of `v`
  have hO : ∀ᶠ u in nhds v, ∀ i, 0 < (v ᵥ* G) i * (u ᵥ* G) i := by
    refine Filter.eventually_all.2 fun i => ?_
    have hc : Continuous fun u : d → ℝ => (v ᵥ* G) i * (u ᵥ* G) i :=
      continuous_const.mul (continuous_vecMul_tsl G i)
    exact Filter.Tendsto.eventually_const_lt (mul_self_pos.2 (hv i)) (hc.tendsto v)
  -- on these rows the block is `b_S`, so `w_S(u) ≠ 0` makes `u M`, `B(u)` independent
  have hLI : ∀ u : d → ℝ, (∀ i, 0 < (v ᵥ* G) i * (u ᵥ* G) i) →
      wPolyGated_tsl S p q M G C W u ≠ 0 →
      LinearIndependent ℝ ![u ᵥ* M, gatedBlock relu G C W u] := by
    intro u hu hw
    have hb : ∀ o, gatedBlock relu G C W u o = ∑ i ∈ S, (u ᵥ* G) i * (u ᵥ* C) i * W i o := by
      intro o
      show ∑ i, relu ((u ᵥ* G) i) * (u ᵥ* C) i * W i o = _
      rw [hSdef, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · rw [relu_pos_tsl _ ((pos_iff_pos_of_mul_pos (hu i)).1 h), pow_one]
      · have hneg : (v ᵥ* G) i < 0 := lt_of_le_of_ne (not_lt.1 h) (hv i)
        rw [relu_nonpos_tsl _ ((neg_iff_neg_of_mul_pos (hu i)).1 hneg).le, zero_mul, zero_mul]
    apply linearIndependent_of_minor_tsl (p := p) (q := q)
    rw [hb p, hb q]
    exact hw
  rw [mem_closure_iff_nhds]
  intro t ht
  by_contra hne
  -- otherwise `w_S` vanishes near `v`, hence everywhere (identity theorem), also at `1`
  have hz : (fun u => wPolyGated_tsl S p q M G C W u) =ᶠ[nhds v] 0 := by
    filter_upwards [ht, hO] with u hut hu
    by_contra hw
    exact hne ⟨u, hut, hLI u hu hw⟩
  have h0 :=
    (analyticOnNhd_wPolyGated_tsl S p q M G C W).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ v) hz
  exact hS S hSne (h0 (Set.mem_univ _))

omit [Fintype T] [Nonempty T] in
/-- **A ReGLU block turns a dense set of the rows with an active gate for the skip `ι v`, at
almost every `(θ, v)`,** for `d ≥ 2` and a skip that depends linearly on `v` and is the identity
at one point. -/
theorem ae_turnsActiveRowsGatedSkip_reglu_of_linear (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V)
    (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, TurnsActiveRowsGatedSkip p.1 (ι p.2) := by
  -- two coordinates `p ≠ q` of `d`
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  -- at almost every `(θ, v)`, `w_S(θ, ι v, 1) ≠ 0` for every nonempty `S`
  filter_upwards [ae_wPolyGated_ne_zero_tsl ι v₀ hι μ hpq] with x hx
  -- then every row off the kinks with an active gate is a limit of turned rows
  intro v hv hact
  exact mem_closure_of_wPolyGated_tsl _ _ _ _ hx v hv hact

omit [Fintype T] [Nonempty T] in
/-- **A ReLU block with a hidden unit turns some row off the kinks, for the skip `ι v`, at almost
every `(θ, v)`,** for `d ≥ 2`. -/
theorem ae_exists_turned_row_skip_relu_of_linear [Nonempty (hid 0)] (ι : V →ₗ[ℝ] Matrix d d ℝ)
    (v₀ : V) (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* p.1.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* ι p.2, vanillaBlock relu (p.1.read 0) (p.1.write 0) v] := by
  exact ae_exists_turned_row_skip_tsl relu_pos_tsl relu_nonpos_tsl ι v₀ hι μ hd

omit [Fintype T] [Nonempty T] in
/-- **A ReLU² block with a hidden unit turns some row off the kinks, for the skip `ι v`, at
almost every `(θ, v)`,** for `d ≥ 2`. -/
theorem ae_exists_turned_row_skip_reluSq_of_linear [Nonempty (hid 0)]
    (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V) (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut × V))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* p.1.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* ι p.2, vanillaBlock reluSq (p.1.read 0) (p.1.write 0) v] := by
  exact ae_exists_turned_row_skip_tsl reluSq_pos_tsl reluSq_nonpos_tsl ι v₀ hι μ hd

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: at almost every `(θ, v)`, the entries of the gate columns of the read at the
coordinate `p` are nonzero, so no gate column of the read is zero. -/
private theorem ae_readGate_ne_zero_tsl
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V))
    [hμ : μ.IsAddHaarMeasure] (p : d) :
    ∀ᵐ x ∂μ, ∀ i : hid 0, x.1.read 0 p (Sum.inl i) ≠ 0 := by
  have hBp : BorelSpace
      (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V) :=
    Prod.borelSpace
  -- the weights with all entries `1`
  let θ₁ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1,
      Matrix.of fun _ _ => 1⟩
  exact ae_all_iff.2 fun i =>
    ae_ne_zero_of_analytic_tsl hBp μ hμ
      (analyticOnNhd_read_tsl (A := Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) p
        (Sum.inl i))
      ⟨(θ₁, 0), show (1 : ℝ) ≠ 0 from one_ne_zero⟩

/-- Helper (some row off the kinks of the gates is turned): if no gate column is zero and every
row off the kinks with an active gate is a limit of turned rows, then some row `v` off the kinks
has `v M` and the output of the block there linearly independent. -/
private theorem exists_turned_gated_of_closure_tsl {m : Type*} [Fintype m] [Nonempty m] (p : d)
    (M : Matrix d d ℝ) (G C : Matrix d m ℝ) (W : Matrix m d ℝ) (hR : ∀ i, G p i ≠ 0)
    (hturn : ∀ v : d → ℝ, (∀ i, (v ᵥ* G) i ≠ 0) → (∃ i, relu ((v ᵥ* G) i) ≠ 0) →
      v ∈ closure {u : d → ℝ | LinearIndependent ℝ ![u ᵥ* M, gatedBlock relu G C W u]}) :
    ∃ v : d → ℝ, (∀ i, (v ᵥ* G) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* M, gatedBlock relu G C W v] := by
  -- almost every row is off the kinks: each `u ↦ (u G)_i` is a nonzero linear form
  have hae : ∀ᵐ u ∂(volume : Measure (d → ℝ)), ∀ i, (u ᵥ* G) i ≠ 0 :=
    ae_all_iff.2 fun i => ae_ne_zero_of_analytic volume (analyticOnNhd_vecMul_tsl G i)
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
    rw [relu_pos_tsl _ hv0, pow_one]
    exact hv0.ne'
  -- the rows off the kinks form a neighbourhood of `v`, which meets the turned rows
  have hO : ∀ᶠ w in nhds v, ∀ i, (w ᵥ* G) i ≠ 0 :=
    Filter.eventually_all.2 fun i => (continuous_vecMul_tsl G i).continuousAt.eventually_ne (hv i)
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff_nhds.1 (hturn v hv ⟨_, hact⟩) _ hO
  exact ⟨w, hw1, hw2⟩

omit [Fintype T] [Nonempty T] in
/-- **A ReGLU block with a hidden unit turns some row off the kinks of the gates, for the skip
`ι v`, at almost every `(θ, v)`,** for `d ≥ 2`. -/
theorem ae_exists_turned_row_skip_reglu_of_linear [Nonempty (hid 0)]
    (ι : V →ₗ[ℝ] Matrix d d ℝ) (v₀ : V) (hι : ι v₀ = 1)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut × V))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ p ∂μ, ∃ v : d → ℝ, (∀ i, (v ᵥ* p.1.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* ι p.2, gatedBlock relu ((p.1.read 0).submatrix id Sum.inl)
        ((p.1.read 0).submatrix id Sum.inr) (p.1.write 0) v] := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  let p : d := Classical.arbitrary d
  -- at almost every `(θ, v)` the block turns a dense set of the rows with an active gate and no
  -- gate column of the read is zero
  filter_upwards [ae_turnsActiveRowsGatedSkip_reglu_of_linear ι v₀ hι μ hd,
    ae_readGate_ne_zero_tsl μ p] with x hturn hR
  -- a row off the kinks with an active gate, and turned rows near it
  exact exists_turned_gated_of_closure_tsl p _ _ _ _ hR hturn

end Skips
