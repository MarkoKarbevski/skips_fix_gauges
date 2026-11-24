import SkipsLean.OneBlock.ResidualRMSStepsOn
import SkipsLean.OneBlock.ResidualRMSGated
import SkipsLean.OneBlock.ReGLU

/-!
# One residual ReGLU block under pre-RMSNorm

Paper (skips paper): Theorem 4.6 (ii), first sentence (Theorem B.1 (ii) in the appendix), for
`ε > 0` and no biases, for a ReGLU block: "For generic parameters the residual network has
functional dimension `P − d_model (d_model − 1)/2 − s`, which is the equality condition. If the
block has width at least `d_model`, the skip raises the functional dimension by at least
`d_model (d_model − 1)/2`." For ReGLU `s = 2 d_hidden`: one rescaling of the gate and one of the
value for each hidden unit.

Its proof, Step 4: "For the ReLU-type activations without biases the kinks lie on hyperplanes
through the center of the ball, and the arguments of Lemma B.3 are local. So Lemma B.3, with `E`
and `D` replaced by the identity and `M = 0`, makes the entries of `η'` at each hidden unit a
rescaling." Step 5: "The flat directions are thus those of the orthogonal change of basis and of
the symmetries inside the block. […] so `dim K(θ) = d_model (d_model − 1)/2 + s`."

Stated here as in `OneBlock/ReGLU.lean` (the same block without normalization),
`OneBlock/ResidualRMSGated.lean` (SwiGLU and GeGLU blocks under pre-RMSNorm) and
`OneBlock/ResidualRMSRescale.lean` (ReLU and ReLU² blocks under pre-RMSNorm):

* `OneBlockGenericReGLURMS θ`: the conditions of the other gated blocks under pre-RMSNorm, and
  no value column of `W_read` is proportional to the gate column of the same hidden unit (the
  hypothesis of Lemma B.3 that only ReGLU uses, "with `E` and `D` replaced by the identity").
* `noKinkGateRMS θ`: the inputs at which no gate sits at its kink (every entry of the gate
  columns of `x E W_read` is nonzero; under pre-RMSNorm with `ε > 0` the block reads a positive
  multiple of each row of `x E`).
* A direction that is flat at these inputs is
  `cobDir θ (fun _ => Y) + rescaleDir θ α + rescaleDirGate 1 θ β` with `Y` antisymmetric.
* The value: `funDim + d(d−1)/2 + 2 d_hidden = P`, and a batch of inputs of `noKinkGateRMS θ`
  with this rank (the paper's functional dimension for these blocks), under the conditions
  `OneBlockGenericReGLURMS` and at almost every parameter, for a block of any width.
* The gain: for a block of at least `d` hidden units the skip raises `funDim` by at least
  `d(d−1)/2`.

Steps 1 to 3 at the inputs of `noKinkGateRMS θ` are `exists_antisymm_of_flatOn_residual_rmsNorm`
(`OneBlock/ResidualRMSStepsOn.lean`); Lemma B.3 for ReGLU is `relu_gated_units_flat`
(`OneBlock/UnitsReGLU.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ} {ε : ℝ}

/-- **The conditions on `θ` in the proof of Theorem B.1 (ii), for one ReGLU block:** those of
the other gated blocks under pre-RMSNorm, and no value column of `W_read` is proportional to the
gate column of the same hidden unit. They do not involve the gate activation. -/
structure OneBlockGenericReGLURMS
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) : Prop where
  /-- the conditions of the other gated blocks under pre-RMSNorm -/
  gated : OneBlockGenericGatedRMS θ
  /-- no value column of `W_read` is proportional to the gate column of the same unit -/
  value_not_gate : ∀ (i : hid 0) (r : ℝ),
    (θ.read 0)ᵀ (Sum.inr i) ≠ r • (θ.read 0)ᵀ (Sum.inl i)

/-- The inputs at which no gate of the block sits at its kink, under pre-RMSNorm: every entry of
the gate columns of `x E W_read` (one per token and hidden unit) is nonzero. -/
def noKinkGateRMS (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) :
    Set (Matrix T dIn ℝ) :=
  {x | ∀ (t : T) (i : hid 0), (x * θ.E * θ.read 0) t (Sum.inl i) ≠ 0}

/-- The conditions of the proof hold at generic parameters, for `d_in, d_out ≥ d ≥ 2` and a
block of any width: each is the nonvanishing of polynomials in the weights that do not vanish
identically. -/
theorem ae_oneBlockGenericReGLURMS
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, OneBlockGenericReGLURMS θ := by
  classical
  -- two distinct coordinates `k₁ ≠ k₂` of the hidden states
  obtain ⟨k₁, k₂, hk⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  -- an entry of the read is a linear functional of the parameters
  have hr : ∀ (k : d) (j : hid 0 ⊕ hid 0), AnalyticOnNhd ℝ
      (fun θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut =>
        θ.read 0 k j) Set.univ := fun k j =>
    analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ k j).comp
      (Params.linRead (A := Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) (dIn := dIn)
        (dOut := dOut) 0))
  -- the value column and the gate column of one unit are not proportional: a `2 × 2` minor
  -- does not vanish (it is `1` for a read `E₀ W₀` of `exists_minor_ne_zero`)
  have h5 : ∀ᵐ θ ∂μ, ∀ i : hid 0,
      θ.read 0 k₁ (Sum.inr i) * θ.read 0 k₂ (Sum.inl i)
        - θ.read 0 k₁ (Sum.inl i) * θ.read 0 k₂ (Sum.inr i) ≠ 0 := by
    refine ae_all_iff.2 fun i => ?_
    obtain ⟨E₀, W₀, hEW⟩ := exists_minor_ne_zero (q := hid 0 ⊕ hid 0) (i := Sum.inr i)
      (j := Sum.inl i) hk hk Sum.inr_ne_inl
    let θ₀ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
      ⟨0, fun ℓ => Fin.cases (E₀ * W₀) (fun l => l.elim0) ℓ, 0, 0⟩
    have hg := ((hr k₁ (Sum.inr i)).mul (hr k₂ (Sum.inl i))).sub
      ((hr k₁ (Sum.inl i)).mul (hr k₂ (Sum.inr i)))
    exact ae_ne_zero_of_analytic μ hg ⟨θ₀, hEW⟩
  -- the conditions of the other gated blocks hold at generic parameters
  filter_upwards [ae_oneBlockGenericGatedRMS μ hd hdIn hdOut, h5] with θ hg h5
  refine ⟨hg, fun i r hr => h5 i ?_⟩
  -- if `e_i = r c_i`, the minor vanishes
  have e1 : θ.read 0 k₁ (Sum.inr i) = r * θ.read 0 k₁ (Sum.inl i) := congrFun hr k₁
  have e2 : θ.read 0 k₂ (Sum.inr i) = r * θ.read 0 k₂ (Sum.inl i) := congrFun hr k₂
  rw [e1, e2]
  ring

/-! ### Helpers: the block map near pre-activations with no gate at its kink -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `hasDerivAt_affine_rg` of `ResidualRMSGated.lean`): `τ ↦ a + τ b` has the
derivative `b` at `0`. -/
private theorem hasDerivAt_affine_rglu (a b : ℝ) : HasDerivAt (fun τ : ℝ => a + τ * b) b 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const b).const_add a
  rw [one_mul] at h
  exact h

/-- Helper: `relu` is `C¹` away from its kink (it is `0` or the identity near `z ≠ 0`). -/
private theorem contDiffAt_relu_rglu {z : ℝ} (hz : z ≠ 0) : ContDiffAt ℝ 1 relu z := by
  rcases hz.lt_or_gt with hneg | hpos
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [eventually_lt_nhds hneg] with y hy
    exact max_eq_right hy.le
  · refine contDiffAt_id.congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds hpos] with y hy
    exact max_eq_left hy.le

omit [Nonempty T] in
/-- Helper: the pre-activations with no gate at its kink form an open set (a finite
intersection of open sets). -/
private theorem isOpen_gateSet_rglu :
    IsOpen {M : Matrix T (hid 0 ⊕ hid 0) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0} := by
  have h : {M : Matrix T (hid 0 ⊕ hid 0) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0}
      = ⋂ t, ⋂ i, {M : Matrix T (hid 0 ⊕ hid 0) ℝ | M t (Sum.inl i) ≠ 0} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun t => isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun (continuous_id.matrix_elem t (Sum.inl i)) continuous_const

omit [Nonempty T] [DecidableEq d] in
/-- Helper: at a pre-activation with no gate at its kink, the map of the ReGLU block is `C¹`
(entry by entry, `relu` is `C¹` away from `0`). -/
private theorem contDiffAt_f_rglu (M : Matrix T (hid 0 ⊕ hid 0) ℝ)
    (hM : ∀ t i, M t (Sum.inl i) ≠ 0) :
    ContDiffAt ℝ 1 ((Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0) M := by
  refine contDiffAt_pi.2 fun t => contDiffAt_pi.2 fun i => ?_
  have he : ∀ j, ContDiffAt ℝ 1 (fun N : Matrix T (hid 0 ⊕ hid 0) ℝ => N t j) M := fun j =>
    (contDiff_apply_apply ℝ t j).contDiffAt
  have h := ((contDiffAt_relu_rglu (hM t i)).comp M (he (Sum.inl i))).mul (he (Sum.inr i))
  exact h

omit [Nonempty T] [DecidableEq d] in
/-- Helper: the map of the ReGLU block is `C¹` on the pre-activations with no gate at its
kink. -/
private theorem contDiffOn_f_rglu :
    ContDiffOn ℝ 1 ((Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0)
      {M : Matrix T (hid 0 ⊕ hid 0) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0} := by
  intro M hM
  exact (contDiffAt_f_rglu M hM).contDiffWithinAt

omit [Nonempty T] [DecidableEq d] in
/-- Helper (as `fderiv_f_gated_apply_rg` of `ResidualRMSGated.lean`, at a pre-activation with no
gate at its kink): the derivative of the map of the ReGLU block at `M` along `N`, entry `(t, i)`:
`1[M_{t, g i} > 0] N_{t, g i} M_{t, v i} + relu(M_{t, g i}) N_{t, v i}`. -/
private theorem fderiv_f_apply_rglu (M N : Matrix T (hid 0 ⊕ hid 0) ℝ)
    (hM : ∀ t i, M t (Sum.inl i) ≠ 0) (t : T) (i : hid 0) :
    fderiv ℝ ((Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0) M N t i
      = reluDeriv (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + relu (M t (Sum.inl i)) * N t (Sum.inr i) := by
  have hd := (contDiffAt_f_rglu (d := d) (ε := ε) M hM).differentiableAt_one
  -- the chain rule along the line `τ ↦ M + τ N`
  have hline : HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
    rw [one_smul] at h
    exact h
  have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by rw [zero_smul, add_zero])
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) i
  -- the same derivative computed on the entry `(t, i)`; `relu` is differentiable at
  -- `M_{t, g i} ≠ 0`
  have h3 : HasDerivAt (fun τ : ℝ => relu (M t (Sum.inl i) + τ * N t (Sum.inl i))
      * (M t (Sum.inr i) + τ * N t (Sum.inr i)))
      (reluDeriv (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + relu (M t (Sum.inl i)) * N t (Sum.inr i)) 0 := by
    have hu := hasDerivAt_affine_rglu (M t (Sum.inl i)) (N t (Sum.inl i))
    have hw := hasDerivAt_affine_rglu (M t (Sum.inr i)) (N t (Sum.inr i))
    have h := ((hasDerivAt_relu (hM t i)).comp_of_eq (0 : ℝ) hu
      (by simp only [zero_mul, add_zero])).mul hw
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, add_zero]
  exact h2.unique h3

/-! ### Helpers: Step 4, the identity of Lemma B.3 at one row -/

/-- Helper: the entry `k` of the derivative of the block along `R'`, `W'` at one row `u` of the
hidden state (the order of the terms of Lemma B.3): `∑_i [relu(u c_i) (u e_i) W'_{i k}
+ 1[u c_i > 0] (u ψc_i) (u e_i) W_{i k} + relu(u c_i) (u ψe_i) W_{i k}]`, with `c_i`, `e_i` the
gate and value columns of `R` and `ψc_i`, `ψe_i` those of `R'`. -/
private noncomputable def unitSum_rglu {q : Type*} [Fintype q] (R R' : Matrix d (q ⊕ q) ℝ)
    (W W' : Matrix q d ℝ) (u : d → ℝ) (k : d) : ℝ :=
  ∑ i, (relu (u ⬝ᵥ Rᵀ (Sum.inl i)) * (u ⬝ᵥ Rᵀ (Sum.inr i)) * W' i k
    + reluDeriv (u ⬝ᵥ Rᵀ (Sum.inl i)) * (u ⬝ᵥ R'ᵀ (Sum.inl i)) * (u ⬝ᵥ Rᵀ (Sum.inr i)) * W i k
    + relu (u ⬝ᵥ Rᵀ (Sum.inl i)) * (u ⬝ᵥ R'ᵀ (Sum.inr i)) * W i k)

omit [Nonempty T] [DecidableEq d] in
/-- Helper: the derivative of `n ↦ f(n R) W` along `R'`, `W'`, entry `(t, k)`, is `unitSum_rglu`
at the row `n_t`, when no gate of `n R` sits at its kink. -/
private theorem fderiv_add_apply_rglu (n : Matrix T d ℝ) (R R' : Matrix d (hid 0 ⊕ hid 0) ℝ)
    (W W' : Matrix (hid 0) d ℝ) (hn : ∀ t i, (n * R) t (Sum.inl i) ≠ 0) (t : T) (k : d) :
    (fderiv ℝ ((Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0) (n * R) (n * R') * W
        + (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0 (n * R) * W') t k
      = unitSum_rglu R R' W W' (n t) k := by
  rw [unitSum_rglu, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_apply_rglu _ _ hn]
  have hf : (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0 (n * R) t i
      = relu ((n * R) t (Sum.inl i)) * (n * R) t (Sum.inr i) := rfl
  -- `(n S)_{t j} = n_t ⬝ S_j`
  have hc : ∀ (S : Matrix d (hid 0 ⊕ hid 0) ℝ) (j : hid 0 ⊕ hid 0), (n * S) t j = n t ⬝ᵥ Sᵀ j :=
    fun _ _ => rfl
  rw [hf]
  simp only [hc]
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `relu (λ z) = λ relu z` for `λ > 0`. -/
private theorem relu_mul_rglu {lam : ℝ} (hlam : 0 < lam) (z : ℝ) :
    relu (lam * z) = lam * relu z := by
  rw [relu_homogeneous lam z hlam, pow_one]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `relu' (λ z) = relu' z` for `λ > 0`. -/
private theorem reluDeriv_mul_rglu {lam : ℝ} (hlam : 0 < lam) (z : ℝ) :
    reluDeriv (lam * z) = reluDeriv z := by
  simp only [reluDeriv, mul_pos_iff_of_pos_left hlam]

omit [DecidableEq d] in
/-- Helper: `unitSum_rglu` is homogeneous of degree `2` in the row, for positive factors. -/
private theorem unitSum_smul_rglu {q : Type*} [Fintype q] (R R' : Matrix d (q ⊕ q) ℝ)
    (W W' : Matrix q d ℝ) {lam : ℝ} (hlam : 0 < lam) (u : d → ℝ) (k : d) :
    unitSum_rglu R R' W W' (lam • u) k = lam ^ 2 * unitSum_rglu R R' W W' u k := by
  simp only [unitSum_rglu, smul_dotProduct, smul_eq_mul, Finset.mul_sum, relu_mul_rglu hlam,
    reluDeriv_mul_rglu hlam]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [DecidableEq d] in
/-- Helper: the factor of RMSNorm on one row is positive for `ε > 0`. -/
private theorem scale_pos_rglu (hε : 0 < ε) (v : d → ℝ) :
    0 < (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹ := by
  apply inv_pos.2
  apply Real.sqrt_pos.2
  have h1 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun k _ => mul_self_nonneg _
  have h2 : 0 ≤ (v ⬝ᵥ v) / (Fintype.card d : ℝ) := div_nonneg h1 (Nat.cast_nonneg _)
  linarith

/-- Helper: a finite family of nonzero vectors has a vector with no zero dot product with them (a
real vector space is not a finite union of proper subspaces). -/
private theorem exists_dotProduct_ne_zero_rglu {n q : Type*} [Fintype n] [Finite q]
    (c : q → n → ℝ) (hc : ∀ i, c i ≠ 0) : ∃ v : n → ℝ, ∀ i, v ⬝ᵥ c i ≠ 0 := by
  let K : q → Submodule ℝ (n → ℝ) := fun i =>
    { carrier := {v | v ⬝ᵥ c i = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢; rw [add_dotProduct, hx, hy, add_zero]
      zero_mem' := by simp only [Set.mem_ofPred_eq, zero_dotProduct]
      smul_mem' := fun s x hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢; rw [smul_dotProduct, hx, smul_zero] }
  by_contra hcon
  push Not at hcon
  obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ (p := K) (by
    ext v
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, h0⟩ := hcon v
    exact ⟨i, h0⟩)
  have hmem : c i ∈ K i := hi ▸ Submodule.mem_top
  exact hc i (dotProduct_self_eq_zero.1 hmem)

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: some input with equal rows has no gate at its kink (`E` has rank `d`, so `x ↦ x E` is
onto, and the gate columns of `W_read` are nonzero). -/
private theorem exists_input_rglu
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericGatedRMS θ) :
    ∃ w : dIn → ℝ, (Matrix.of fun _ : T => w) * θ.E * θ.read 0
      ∈ {M : Matrix T (hid 0 ⊕ hid 0) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0} := by
  obtain ⟨v, hv⟩ := exists_dotProduct_ne_zero_rglu (fun i => (θ.read 0)ᵀ (Sum.inl i))
    hθ.gate_ne_zero
  obtain ⟨w, hw⟩ := (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hθ.rank_E) v
  refine ⟨w, fun t i => ?_⟩
  have h : ((Matrix.of fun _ : T => w) * θ.E * θ.read 0) t (Sum.inl i)
      = (w ᵥ* θ.E) ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) := rfl
  have hw' : w ᵥ* θ.E = v := hw
  rw [h, hw']
  exact hv i

/-- **Proof of Theorem B.1 (ii), Steps 1 to 4, for a ReGLU block:** under the conditions
`OneBlockGenericReGLURMS`, a direction that is flat at every input with no gate at its kink is
the direction of an orthogonal change of basis shared by `h_0` and `h_1` plus a rescaling of the
values and a rescaling of the gates of the hidden units. -/
theorem flatOn_noKinkGateRMS_le_reglu_residual_rmsNorm (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ)
    (η : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.gated relu (rmsNorm ε) hid) 1 θ (noKinkGateRMS θ)) :
    ∃ (Y : Matrix d d ℝ) (α β : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
      η = cobDir θ (fun _ => Y) + rescaleDir θ α + rescaleDirGate 1 θ β := by
  -- Steps 1 to 3 (`OneBlock/ResidualRMSStepsOn.lean`) on the open cone `V` of pre-activations
  -- with no gate at its kink: `Y` antisymmetric, `η_E = E Y`, `η_D = -Y D`, and the derivative
  -- of the block along `η'` vanishes at `n = N_ε(x E)` for every input `x` of `noKinkGateRMS θ`
  obtain ⟨Y, hY, hYE, hYD, hF⟩ := exists_antisymm_of_flatOn_residual_rmsNorm
    (A := Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) hε rfl
    {M | ∀ t i, M t (Sum.inl i) ≠ 0} isOpen_gateSet_rglu
    (fun M hM c hc t i => mul_ne_zero (hc t).ne' (hM t i)) contDiffOn_f_rglu θ
    hθ.gated.rank_E hθ.gated.rank_D (exists_input_rglu θ hθ.gated) η hη
  -- Step 4 (a): at every row `v` with no gate at its kink the identity of Lemma B.3 holds: take
  -- the input `x` with all rows `w`, `w E = v`; `N_ε(x E)` has all rows `λ v` with `λ > 0`, and
  -- the identity at `λ v` is `λ²` times the identity at `v`
  have hsurj := Matrix.vecMul_surjective_iff_rank_eq_card.mpr hθ.gated.rank_E
  have hzero : ∀ v : d → ℝ, (∀ i, v ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0) → ∀ k,
      unitSum_rglu (θ.read 0) (η.read 0 + Y * θ.read 0) (θ.write 0)
        (η.write 0 - θ.write 0 * Y) v k = 0 := by
    intro v hv k
    obtain ⟨w, hw⟩ := hsurj v
    have hw' : w ᵥ* θ.E = v := hw
    have hxE : (Matrix.of fun _ : T => w) * θ.E = Matrix.of fun _ : T => v := by
      ext t l
      rw [← hw']
      rfl
    have hx : (Matrix.of fun _ : T => w) * θ.E * θ.read 0
        ∈ {M : Matrix T (hid 0 ⊕ hid 0) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0} := by
      rw [hxE]
      exact fun t i => hv i
    have h := hF _ hx
    rw [hxE] at h
    obtain ⟨c, hc, hrow⟩ : ∃ c : ℝ, 0 < c ∧
        ∀ t, rmsNorm ε (Matrix.of fun _ : T => v) t = c • v :=
      ⟨(Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹, scale_pos_rglu hε v, fun t => rfl⟩
    have hn : ∀ t i,
        (rmsNorm ε (Matrix.of fun _ : T => v) * θ.read 0) t (Sum.inl i) ≠ 0 := by
      intro t i
      show rmsNorm ε (Matrix.of fun _ : T => v) t ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0
      rw [hrow, smul_dotProduct, smul_eq_mul]
      exact mul_ne_zero hc.ne' (hv i)
    have h2 := congrFun (congrFun h (Classical.arbitrary T)) k
    rw [fderiv_add_apply_rglu _ _ _ _ _ hn, hrow, unitSum_smul_rglu _ _ _ _ hc,
      Matrix.zero_apply] at h2
    exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero 2 hc.ne')
  -- Step 4 (b): Lemma B.3 for ReGLU with `E` and `D` replaced by the identity and `M = 0`: the
  -- gate column `c_i` moves by `λ_i c_i`, the value column `e_i` by `-α_i e_i` and the write row
  -- `a_i` by `(α_i - λ_i) a_i`
  obtain ⟨-, -, lam, α, hlam⟩ := relu_gated_units_flat
    (fun i => (θ.read 0)ᵀ (Sum.inl i)) 0 (fun i => (θ.read 0)ᵀ (Sum.inr i)) 0
    (fun i => θ.write 0 i) 0 0 (fun i => (η.read 0 + Y * θ.read 0)ᵀ (Sum.inl i)) 0
    (fun i => (η.read 0 + Y * θ.read 0)ᵀ (Sum.inr i)) 0 (fun i => (η.write 0 - θ.write 0 * Y) i)
    (fun i => hθ.gated.row_ne_zero i) (fun i => hθ.gated.gate_ne_zero i)
    (fun i j hij => hθ.gated.gate_not_collinear i j hij) (fun i => hθ.gated.value_ne_zero i)
    (fun i r h => hθ.value_not_gate i r (by have h1 := congrArg Prod.fst h; exact h1)) (by
      intro v hv
      have hv' : ∀ i, v ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0 := fun i => by
        have h := hv i
        simp only [Pi.zero_apply, add_zero] at h
        exact h
      funext k
      have h := hzero v hv' k
      simp only [Matrix.vecMul_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, add_zero, zero_add]
      exact h)
  -- Step 4 (c): `η = cobDir θ (Y, Y) + rescaleDir θ α + rescaleDirGate 1 θ λ`, component by
  -- component (one block)
  obtain ⟨α', hα'⟩ : ∃ α' : ∀ ℓ : Fin 1, hid ℓ → ℝ, α' 0 = α :=
    ⟨fun ℓ => Fin.cases α (fun l => l.elim0) ℓ, rfl⟩
  obtain ⟨β', hβ'⟩ : ∃ β' : ∀ ℓ : Fin 1, hid ℓ → ℝ, β' 0 = lam :=
    ⟨fun ℓ => Fin.cases lam (fun l => l.elim0) ℓ, rfl⟩
  refine ⟨Y, α', β', hY, Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_⟩
  · show η.E = θ.E * Y + 0 + 0
    rw [add_zero, add_zero]
    exact hYE
  · obtain rfl := Subsingleton.elim ℓ 0
    ext k j
    rcases j with i | i
    · have h1 : η.read 0 k (Sum.inl i) + (Y * θ.read 0) k (Sum.inl i)
          = lam i * θ.read 0 k (Sum.inl i) := congrFun (hlam i).1 k
      show η.read 0 k (Sum.inl i)
        = -((Y * θ.read 0) k (Sum.inl i)) + 0 + β' 0 i * θ.read 0 k (Sum.inl i)
      rw [hβ']
      linarith
    · have h1 : η.read 0 k (Sum.inr i) + (Y * θ.read 0) k (Sum.inr i)
          = -(α i) * θ.read 0 k (Sum.inr i) := congrFun (hlam i).2.2.1 k
      show η.read 0 k (Sum.inr i)
        = -((Y * θ.read 0) k (Sum.inr i)) + -(α' 0 i) * θ.read 0 k (Sum.inr i) + 0
      rw [hα']
      linarith
  · obtain rfl := Subsingleton.elim ℓ 0
    ext i k
    have h1 : η.write 0 i k - (θ.write 0 * Y) i k = (α i - lam i) * θ.write 0 i k :=
      congrFun (hlam i).2.2.2.2 k
    show η.write 0 i k = (θ.write 0 * Y) i k + α' 0 i * θ.write 0 i k
      + -(((1 : ℕ) : ℝ) * β' 0 i) * θ.write 0 i k
    rw [hα', hβ', Nat.cast_one]
    linarith
  · show η.D = -(Y * θ.D) + 0 + 0
    rw [add_zero, add_zero]
    exact hYD

/-- **Theorem B.1 (ii), first sentence, for a ReGLU block, at one parameter:** under the
conditions `OneBlockGenericReGLURMS`, `funDim = P − d(d−1)/2 − 2 d_hidden`. -/
theorem funDim_reglu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) :
    funDim (Arch.gated relu (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii) in the paper's own sense, for a ReGLU block, at one parameter:** a
finite batch of inputs with no gate at its kink on which the Jacobian has the rank
`P − d(d−1)/2 − 2 d_hidden`. -/
theorem exists_jacobianRank_reglu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateRMS θ) ∧
      jacobianRank (Arch.gated relu (rmsNorm ε) hid) 1 X θ
          + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii), first sentence, for one ReGLU block:** for `ε > 0` and
`d_in, d_out ≥ d ≥ 2`, at almost every parameter the residual network of one ReGLU block of any
width has `funDim = P − d(d−1)/2 − 2 d_hidden`. -/
theorem ae_funDim_reglu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii) in the paper's own sense, for one ReGLU block:** at almost every
parameter there is a finite batch of inputs with no gate at its kink on which the Jacobian has
the rank `P − d(d−1)/2 − 2 d_hidden`. -/
theorem ae_exists_jacobianRank_reglu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateRMS θ) ∧
      jacobianRank (Arch.gated relu (rmsNorm ε) hid) 1 X θ
          + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii), second sentence, for one ReGLU block:** if the block has at least `d`
hidden units, at almost every parameter the skip raises `funDim` by at least `d(d−1)/2`. -/
theorem ae_funDim_skipless_add_le_reglu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm ε) hid) 0 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ funDim (Arch.gated relu (rmsNorm ε) hid) 1 θ := by
  sorry

end Skips
