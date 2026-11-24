import SkipsLean.OneBlock.LearnedSkipRMSZeroSteps
import SkipsLean.OneBlock.UnitsRescaleSphereReGLU
import SkipsLean.OneBlock.LearnedSkipRMSZeroRescaleBound

/-!
# One ReGLU block with a full learned skip under pre-RMSNorm with `ε = 0`: the equality

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. […] For `ε = 0` it exceeds that of the residual
network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and
ReGLU blocks."

Its proof, "The case `ε = 0`": "Steps 3 and 4 run with `Y + c I` in place of `Y` and with
`X_s = c_0 I + X_0`, where `X_0` has trace zero; the scalings, with the derivatives `c_0` at `h_0`
and `c` at `h_1`, join the rotations in `η^rot`; and (17) holds with `X_0` in place of `X_s` on
the sphere. […] For ReLU, ReLU² and ReGLU, both sides of (17) are positively homogeneous, of
degrees `k` and `k + 2`, so `‖n‖² ∂_ψ B(n) = k d_model q(n) B(n)` for all `n ≠ 0`. […] Since
`‖n‖²` has no real linear factor, it divides `q(n)`, so `X_0` is a multiple of `I`, and `X_0 = 0`
because its trace vanishes. Then Step 5 gives equality."

The twin for a ReGLU block of `OneBlock/LearnedSkipRMSZeroRescale.lean` (ReLU and ReLU² blocks),
and for a learned skip of `OneBlock/ResidualRMSZeroReGLU.lean`. As there, the proof needs a
condition on the parameters that the paper does not state: the rows `u` at which `u A` and the
output of the block are linearly independent are dense among the rows with an active gate
(`TurnsActiveRowsGatedSkip`; at almost every weights and skip:
`OneBlock/LearnedSkipRMSZeroReGLUGeneric.lean`). Here, at one parameter under the conditions of
the proof:

* the directions of the weights and the skip that are flat at the paper's inputs (no normalized
  row vanishes, no gate at its kink) are a rotation and a scaling of `h_0`, a rotation and a
  scaling of `h_1`, a rescaling of the values and a rescaling of the gates of the hidden units;
* the value of Lean's `funDimLearned`: `P + d² − (d(d−1) + 2) − 2 d_hidden` (the bound "at most" is
  `funDimLearned_add_le_rmsNorm_zero'`, `OneBlock/LearnedSkipRMSZeroRescaleBound.lean`);
* a finite batch of the paper's inputs on which the Jacobian in the weights and the skip has
  this rank.

The step "`X_0` is a multiple of `I`", with Lemma B.3, is `reglu_unitsRescaleSphere`
(`OneBlock/UnitsRescaleSphereReGLU.lean`). No width of the block is asked. Numeric check of the
values: `learned_skip_zero_relu_check_2026-11-24.py`. Not stated: the upper triangular skip.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ}

/-- **A gated block turns a dense set of the rows with an active gate, for the skip `S`:** every
row `v` with no gate at its kink and with some active gate is a limit of rows `u` such that `u S`
and the output of the block at `u` are linearly independent. For `S = 1` this is
`TurnsActiveRowsGated`. -/
def TurnsActiveRowsGatedSkip
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (S : Matrix d d ℝ) :
    Prop :=
  ∀ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) →
    (∃ i, σ ((v ᵥ* θ.read 0) (Sum.inl i)) ≠ 0) →
    v ∈ closure {u : d → ℝ | LinearIndependent ℝ ![u ᵥ* S, gatedBlock σ
      ((θ.read 0).submatrix id Sum.inl) ((θ.read 0).submatrix id Sum.inr) (θ.write 0) u]}


section HelpersLrg

open Filter
open scoped Topology

/-! ### The ReGLU block away from the kinks of its gates (copies of the `_rgz` helpers of
`OneBlock/ResidualRMSZeroReGLU.lean`) -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `τ ↦ a + τ b` has the derivative `b` at `0`. -/
private theorem hasDerivAt_affine_lrg (a b : ℝ) : HasDerivAt (fun τ : ℝ => a + τ * b) b 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const b).const_add a
  rw [one_mul] at h
  exact h

/-- Helper: `relu` is `C¹` away from its kink (it is `0` or the identity near `z ≠ 0`). -/
private theorem contDiffAt_relu_lrg {z : ℝ} (hz : z ≠ 0) : ContDiffAt ℝ 1 relu z := by
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
private theorem isOpen_gateSet_lrg :
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
private theorem contDiffAt_f_lrg (M : Matrix T (hid 0 ⊕ hid 0) ℝ)
    (hM : ∀ t i, M t (Sum.inl i) ≠ 0) :
    ContDiffAt ℝ 1 ((Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0) M := by
  refine contDiffAt_pi.2 fun t => contDiffAt_pi.2 fun i => ?_
  have he : ∀ j, ContDiffAt ℝ 1 (fun N : Matrix T (hid 0 ⊕ hid 0) ℝ => N t j) M := fun j =>
    (contDiff_apply_apply ℝ t j).contDiffAt
  have h := ((contDiffAt_relu_lrg (hM t i)).comp M (he (Sum.inl i))).mul (he (Sum.inr i))
  exact h

omit [Nonempty T] [DecidableEq d] in
/-- Helper: the map of the ReGLU block is `C¹` on the pre-activations with no gate at its
kink. -/
private theorem contDiffOn_f_lrg :
    ContDiffOn ℝ 1 ((Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0)
      {M : Matrix T (hid 0 ⊕ hid 0) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0} := by
  intro M hM
  exact (contDiffAt_f_lrg M hM).contDiffWithinAt

omit [Nonempty T] [DecidableEq d] in
/-- Helper: the derivative of the map of the ReGLU block at `M` (no gate at its kink) along `N`,
entry `(t, i)`: `1[M_{t, g i} > 0] N_{t, g i} M_{t, v i} + relu(M_{t, g i}) N_{t, v i}`. -/
private theorem fderiv_f_apply_lrg (M N : Matrix T (hid 0 ⊕ hid 0) ℝ)
    (hM : ∀ t i, M t (Sum.inl i) ≠ 0) (t : T) (i : hid 0) :
    fderiv ℝ ((Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0) M N t i
      = reluDeriv (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + relu (M t (Sum.inl i)) * N t (Sum.inr i) := by
  have hd := (contDiffAt_f_lrg (d := d) M hM).differentiableAt_one
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
    have hu := hasDerivAt_affine_lrg (M t (Sum.inl i)) (N t (Sum.inl i))
    have hw := hasDerivAt_affine_lrg (M t (Sum.inr i)) (N t (Sum.inr i))
    have h := ((hasDerivAt_relu (hM t i)).comp_of_eq (0 : ℝ) hu
      (by simp only [zero_mul, add_zero])).mul hw
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, add_zero]
  exact h2.unique h3

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `relu (λ z) = λ relu z` for `λ > 0`. -/
private theorem relu_mul_lrg {lam : ℝ} (hlam : 0 < lam) (z : ℝ) :
    relu (lam * z) = lam * relu z := by
  rw [relu_homogeneous lam z hlam, pow_one]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `relu' (λ z) = relu' z` for `λ > 0`. -/
private theorem reluDeriv_mul_lrg {lam : ℝ} (hlam : 0 < lam) (z : ℝ) :
    reluDeriv (lam * z) = reluDeriv z := by
  simp only [reluDeriv, mul_pos_iff_of_pos_left hlam]

/-- Helper: Euler's identity for `relu`, `relu'(z) z = relu z` (also at the kink). -/
private theorem reluDeriv_mul_self_lrg (z : ℝ) : reluDeriv z * z = relu z := by
  unfold reluDeriv relu
  split_ifs with h
  · rw [one_mul, max_eq_left h.le]
  · rw [zero_mul, max_eq_right (not_lt.1 h)]

/-- Helper: `relu'` is continuous away from the kink (it is constant near `z ≠ 0`). -/
private theorem continuousAt_reluDeriv_lrg {z : ℝ} (hz : z ≠ 0) : ContinuousAt reluDeriv z := by
  rcases hz.lt_or_gt with hneg | hpos
  · refine ContinuousAt.congr (f := fun _ : ℝ => (0 : ℝ)) continuousAt_const ?_
    filter_upwards [eventually_lt_nhds hneg] with y hy
    simp only [reluDeriv, not_lt.2 hy.le, ite_false]
  · refine ContinuousAt.congr (f := fun _ : ℝ => (1 : ℝ)) continuousAt_const ?_
    filter_upwards [eventually_gt_nhds hpos] with y hy
    simp only [reluDeriv, hy, ite_true]

/-- Helper: at `z` with `relu z = 0` (an inactive gate), `relu' z = 0`. -/
private theorem reluDeriv_eq_zero_lrg {z : ℝ} (h0 : relu z = 0) : reluDeriv z = 0 := by
  have hz : ¬ 0 < z := fun hz => by
    rw [relu, max_eq_left hz.le] at h0
    exact hz.ne' h0
  simp only [reluDeriv, hz, ite_false]

/-! ### The two sides of the equation of `reglu_unitsRescaleSphere` on one row -/

/-- Helper: the entry `k` of the derivative of the block along `R'`, `W'` at one row `u` (the
order of the terms of `reglu_unitsRescaleSphere`): `∑_i [relu(u g_i) (u v_i) W'_{i k}
+ 1[u g_i > 0] (u ψg_i) (u v_i) W_{i k} + relu(u g_i) (u ψv_i) W_{i k}]`, with `g_i`, `v_i` the
gate and value columns of `R` and `ψg_i`, `ψv_i` those of `R'`. -/
private noncomputable def unitSum_lrg {q : Type*} [Fintype q] (R R' : Matrix d (q ⊕ q) ℝ)
    (W W' : Matrix q d ℝ) (u : d → ℝ) (k : d) : ℝ :=
  ∑ i, (relu (u ⬝ᵥ Rᵀ (Sum.inl i)) * (u ⬝ᵥ Rᵀ (Sum.inr i)) * W' i k
    + reluDeriv (u ⬝ᵥ Rᵀ (Sum.inl i)) * (u ⬝ᵥ R'ᵀ (Sum.inl i)) * (u ⬝ᵥ Rᵀ (Sum.inr i)) * W i k
    + relu (u ⬝ᵥ Rᵀ (Sum.inl i)) * (u ⬝ᵥ R'ᵀ (Sum.inr i)) * W i k)

/-- Helper: the block on the row `u`, `B(u) = ∑_i relu(u g_i) (u v_i) a_i`, at the coordinate
`k`. -/
private noncomputable def block_lrg {q : Type*} [Fintype q] (R : Matrix d (q ⊕ q) ℝ)
    (W : Matrix q d ℝ) (u : d → ℝ) (k : d) : ℝ :=
  ∑ i, relu (u ⬝ᵥ Rᵀ (Sum.inl i)) * (u ⬝ᵥ Rᵀ (Sum.inr i)) * W i k

omit [DecidableEq d] in
/-- Helper: `‖v‖² ∂_ψ B(v)_k − 2 (v X vᵀ) B(v)_k` is continuous in the row `v` at a row with no
gate at its kink. -/
private theorem continuousAt_eq_lrg {q : Type*} [Fintype q] (R R' : Matrix d (q ⊕ q) ℝ)
    (W W' : Matrix q d ℝ) (X : Matrix d d ℝ) (k : d) {u : d → ℝ}
    (hu : ∀ i, u ⬝ᵥ Rᵀ (Sum.inl i) ≠ 0) :
    ContinuousAt (fun v : d → ℝ => (v ⬝ᵥ v) * unitSum_lrg R R' W W' v k
      - 2 * ((v ᵥ* X) ⬝ᵥ v) * block_lrg R W v k) u := by
  have hdot : ∀ c : d → ℝ, Continuous fun v : d → ℝ => v ⬝ᵥ c := fun c =>
    continuous_id.dotProduct continuous_const
  have h1 : ∀ i, ContinuousAt (fun v : d → ℝ => relu (v ⬝ᵥ Rᵀ (Sum.inl i))) u := fun i =>
    ContinuousAt.comp (f := fun v : d → ℝ => v ⬝ᵥ Rᵀ (Sum.inl i)) (x := u)
      (hasDerivAt_relu (hu i)).continuousAt (hdot _).continuousAt
  have h2 : ∀ i, ContinuousAt (fun v : d → ℝ => reluDeriv (v ⬝ᵥ Rᵀ (Sum.inl i))) u := fun i =>
    ContinuousAt.comp (f := fun v : d → ℝ => v ⬝ᵥ Rᵀ (Sum.inl i)) (x := u)
      (continuousAt_reluDeriv_lrg (hu i)) (hdot _).continuousAt
  have hterm : ∀ i, ContinuousAt (fun v : d → ℝ =>
      relu (v ⬝ᵥ Rᵀ (Sum.inl i)) * (v ⬝ᵥ Rᵀ (Sum.inr i)) * W' i k
        + reluDeriv (v ⬝ᵥ Rᵀ (Sum.inl i)) * (v ⬝ᵥ R'ᵀ (Sum.inl i)) * (v ⬝ᵥ Rᵀ (Sum.inr i))
          * W i k
        + relu (v ⬝ᵥ Rᵀ (Sum.inl i)) * (v ⬝ᵥ R'ᵀ (Sum.inr i)) * W i k) u := by
    intro i
    have h3 := (hdot (Rᵀ (Sum.inr i))).continuousAt (x := u)
    have h4 := (hdot (R'ᵀ (Sum.inl i))).continuousAt (x := u)
    have h5 := (hdot (R'ᵀ (Sum.inr i))).continuousAt (x := u)
    exact ((((h1 i).mul h3).mul continuousAt_const).add
      ((((h2 i).mul h4).mul h3).mul continuousAt_const)).add
        (((h1 i).mul h5).mul continuousAt_const)
  have hU : ContinuousAt (fun v : d → ℝ => unitSum_lrg R R' W W' v k) u := by
    have h := tendsto_finsetSum (f := fun (i : q) (v : d → ℝ) =>
      relu (v ⬝ᵥ Rᵀ (Sum.inl i)) * (v ⬝ᵥ Rᵀ (Sum.inr i)) * W' i k
        + reluDeriv (v ⬝ᵥ Rᵀ (Sum.inl i)) * (v ⬝ᵥ R'ᵀ (Sum.inl i)) * (v ⬝ᵥ Rᵀ (Sum.inr i))
          * W i k
        + relu (v ⬝ᵥ Rᵀ (Sum.inl i)) * (v ⬝ᵥ R'ᵀ (Sum.inr i)) * W i k) Finset.univ
      fun i _ => hterm i
    exact h
  have hB : ContinuousAt (fun v : d → ℝ => block_lrg R W v k) u := by
    have h := tendsto_finsetSum (f := fun (i : q) (v : d → ℝ) =>
      relu (v ⬝ᵥ Rᵀ (Sum.inl i)) * (v ⬝ᵥ Rᵀ (Sum.inr i)) * W i k) Finset.univ
      fun i _ => ((h1 i).mul (hdot (Rᵀ (Sum.inr i))).continuousAt).mul continuousAt_const
    exact h
  have hq : Continuous fun v : d → ℝ => (v ᵥ* X) ⬝ᵥ v :=
    (continuous_id.matrix_vecMul continuous_const).dotProduct continuous_id
  exact ((continuous_id.dotProduct continuous_id).continuousAt.mul hU).sub
    ((continuousAt_const.mul hq.continuousAt).mul hB)

/-- Helper: a function continuous at a point `u` of the closure of `S` that vanishes at the
points of `S` with a property `P` holding near `u` vanishes at `u`. -/
private theorem eq_zero_of_mem_closure_lrg {X : Type*} [TopologicalSpace X] {F : X → ℝ} {u : X}
    {S : Set X} {P : X → Prop} (hF : ContinuousAt F u) (hu : u ∈ closure S)
    (hP : ∀ᶠ v in 𝓝 u, P v) (h0 : ∀ v ∈ S, P v → F v = 0) : F u = 0 := by
  by_contra hne
  obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ := mem_closure_iff_nhds.1 hu _ ((hF.eventually_ne hne).and hP)
  exact hv1 (h0 v hv3 hv2)

/-! ### The normalized rows and the block on one row (copies of the `_lzf` and `_rgz`
helpers) -/

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `N_0` scales every row: `(N_0(h) W)_{t i} = (‖h_t‖²/d)^{-1/2} (h W)_{t i}`. -/
private theorem rmsNorm_mul_apply_lrg {n : Type*} [Fintype n] (h : Matrix T d ℝ)
    (W : Matrix d n ℝ) (t : T) (i : n) :
    (rmsNorm 0 h * W) t i
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ * (h * W) t i := by
  simp only [Matrix.mul_apply, Finset.mul_sum, rmsNorm, rmsRow, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul, mul_assoc, add_zero]

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: the same at the input whose rows are all `v`. -/
private theorem rmsNorm_const_mul_lrg {n : Type*} [Fintype n] (v : d → ℝ) (W : Matrix d n ℝ)
    (t : T) (i : n) :
    (rmsNorm 0 (Matrix.of fun _ : T => v) * W) t i
      = (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ)))⁻¹ * (v ⬝ᵥ Wᵀ i) := by
  rw [rmsNorm_mul_apply_lrg]
  rfl

omit [DecidableEq d] in
/-- Helper: the factor of `N_0` at a row `v ≠ 0` is positive. -/
private theorem inv_sqrt_pos_lrg {v : d → ℝ} (hv : v ≠ 0) :
    0 < (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ)))⁻¹ := by
  have h1 : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j))
      (fun h => hv (dotProduct_self_eq_zero.1 h.symm))
  obtain ⟨j, -⟩ := Function.ne_iff.1 hv
  have h2 : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩)
  exact inv_pos.2 (Real.sqrt_pos.2 (div_pos h1 h2))

omit [DecidableEq d] in
/-- Helper: the ReGLU block on one row is positively homogeneous of degree `2`:
`b(s u) = s² b(u)` for `s > 0`. -/
private theorem gatedBlock_smul_lrg {q : Type*} [Fintype q] (Wg Wv : Matrix d q ℝ)
    (W : Matrix q d ℝ) (u : d → ℝ) {s : ℝ} (hs : 0 < s) :
    gatedBlock relu Wg Wv W (s • u) = s ^ 2 • gatedBlock relu Wg Wv W u := by
  unfold gatedBlock
  have e : (fun i => relu (((s • u) ᵥ* Wg) i) * ((s • u) ᵥ* Wv) i)
      = s ^ 2 • fun i => relu ((u ᵥ* Wg) i) * (u ᵥ* Wv) i := by
    funext i
    simp only [Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul, relu_mul_lrg hs]
    ring
  rw [e, Matrix.smul_vecMul]

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: at a row `h_t ≠ 0`, the row `t` of the block `f(N_0(h) W_read) W_write` is a
nonzero multiple of `b(h_t)` (the multiple `s²`, with `s = (‖h_t‖²/d)^{-1/2} > 0`). -/
private theorem row_block_lrg (Rd : Matrix d (hid 0 ⊕ hid 0) ℝ) (W : Matrix (hid 0) d ℝ)
    (h : Matrix T d ℝ) (t : T) (ht : h t ≠ 0) :
    ∃ r : ℝ, r ≠ 0 ∧
      ((Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0 (rmsNorm 0 h * Rd) * W) t
        = r • gatedBlock relu (Rd.submatrix id Sum.inl) (Rd.submatrix id Sum.inr) W (h t) := by
  have hpos : 0 < (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + 0))⁻¹ := by
    rw [add_zero]
    exact inv_sqrt_pos_lrg ht
  refine ⟨_, pow_ne_zero 2 hpos.ne', ?_⟩
  have e1 : ((Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0 (rmsNorm 0 h * Rd) * W) t
      = gatedBlock relu (Rd.submatrix id Sum.inl) (Rd.submatrix id Sum.inr) W (rmsNorm 0 h t) :=
    rfl
  have e2 : rmsNorm 0 h t = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + 0))⁻¹ • h t := rfl
  rw [e1, e2]
  exact gatedBlock_smul_lrg _ _ W (h t) hpos

/-- Helper: scaling the second vector of an independent pair by `r ≠ 0` keeps it independent. -/
private theorem linearIndependent_pair_smul_lrg {V : Type*} [AddCommGroup V] [Module ℝ V]
    {a b : V} (h : LinearIndependent ℝ ![a, b]) {r : ℝ} (hr : r ≠ 0) :
    LinearIndependent ℝ ![a, r • b] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  obtain ⟨h1, h2⟩ := h s (t * r) (by rw [mul_smul]; exact hst)
  exact ⟨h1, (mul_eq_zero.1 h2).resolve_right hr⟩

omit [Nonempty T] [DecidableEq d] in
/-- Helper: at the input whose rows are all `v ≠ 0`, with `s = (‖v‖²/d)^{-1/2}`,
`(𝐃N_0(h)(h X) W)_{t i} = s (v X) c_i − (v·vX/d) s³ (v c_i)`, `c_i` the column `i` of `W`. -/
private theorem fderiv_rmsNorm_const_mul_lrg {n : Type*} [Fintype n] {v : d → ℝ} (hv : v ≠ 0)
    (X : Matrix d d ℝ) (W : Matrix d n ℝ) (t : T) (i : n) :
    (fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (Matrix.of fun _ : T => v)
        ((Matrix.of fun _ : T => v) * X) * W) t i
      = (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ)))⁻¹ * ((v ᵥ* X) ⬝ᵥ Wᵀ i)
        - (v ⬝ᵥ (v ᵥ* X)) / (Fintype.card d : ℝ)
          * (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ)))⁻¹ ^ 3 * (v ⬝ᵥ Wᵀ i) := by
  rw [fderiv_rmsNorm_zero_apply (Matrix.of fun _ : T => v) _ fun _ => hv]
  show ((Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ)))⁻¹ • (v ᵥ* X)
      - ((v ⬝ᵥ (v ᵥ* X)) / (Fintype.card d : ℝ)
        * (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ)))⁻¹ ^ 3) • v) ⬝ᵥ Wᵀ i = _
  rw [sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]

omit [DecidableEq d] in
/-- Helper (Step 4 at one row): if the derivative of the block along the direction
`(X, η_read, W')` vanishes at the input whose rows are all `v` (a row with no gate at its kink),
then `‖v‖² ∂_ψ B(v) = 2 (v X vᵀ) B(v)` with `ψ = X W_read + η_read`: the normalization scales
`v` by `s = (‖v‖²/d)^{-1/2}`, its derivative along `v X` is `s (v X) − (v·vX/d) s³ v`, and by
homogeneity and Euler's identity `relu'(z) z = relu z` the equation is `s²` times
`∂_ψ B(v) − 2 (v·vX/d) s² B(v)`, with `s² ‖v‖² = d`. -/
private theorem row_eq_lrg (Wr ηr : Matrix d (hid 0 ⊕ hid 0) ℝ) (Ww W' : Matrix (hid 0) d ℝ)
    (X : Matrix d d ℝ) {v : d → ℝ} (hv0 : v ≠ 0) (hv : ∀ i, v ⬝ᵥ Wrᵀ (Sum.inl i) ≠ 0) (j : d)
    (e : fderiv ℝ ((Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0)
          (rmsNorm 0 (Matrix.of fun _ : T => v) * Wr)
          (fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (Matrix.of fun _ : T => v)
              ((Matrix.of fun _ : T => v) * X) * Wr
            + rmsNorm 0 (Matrix.of fun _ : T => v) * ηr) * Ww
        + (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0
          (rmsNorm 0 (Matrix.of fun _ : T => v) * Wr) * W' = 0) :
    (v ⬝ᵥ v) * unitSum_lrg Wr (X * Wr + ηr) Ww W' v j
      = 2 * ((v ᵥ* X) ⬝ᵥ v) * block_lrg Wr Ww v j := by
  -- the normalization scales the row `v` by `s = (‖v‖²/d)^{-1/2} > 0`, and `s² ‖v‖² = d`
  obtain ⟨s, hs_def⟩ : ∃ s, s = (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ)))⁻¹ := ⟨_, rfl⟩
  have hs : 0 < s := hs_def ▸ inv_sqrt_pos_lrg hv0
  have hvv : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j))
      (fun h => hv0 (dotProduct_self_eq_zero.1 h.symm))
  obtain ⟨j₀, -⟩ := Function.ne_iff.1 hv0
  have hd0 : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j₀⟩)
  have hs2 : s ^ 2 * (v ⬝ᵥ v) = Fintype.card d := by
    rw [hs_def, inv_pow, Real.sq_sqrt (div_nonneg hvv.le hd0.le)]
    field_simp
  -- the entries of the normalized rows and of the derivative of the normalization
  obtain ⟨t₀⟩ : Nonempty T := inferInstance
  have hN : ∀ (W : Matrix d (hid 0 ⊕ hid 0) ℝ) (c : hid 0 ⊕ hid 0),
      (rmsNorm 0 (Matrix.of fun _ : T => v) * W) t₀ c = s * (v ⬝ᵥ Wᵀ c) := fun W c => by
    rw [rmsNorm_const_mul_lrg, ← hs_def]
  have hdN : ∀ c : hid 0 ⊕ hid 0,
      (fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (Matrix.of fun _ : T => v)
        ((Matrix.of fun _ : T => v) * X) * Wr) t₀ c
      = s * ((v ᵥ* X) ⬝ᵥ Wrᵀ c) - (v ⬝ᵥ (v ᵥ* X)) / Fintype.card d * s ^ 3 * (v ⬝ᵥ Wrᵀ c) :=
    fun c => by rw [fderiv_rmsNorm_const_mul_lrg hv0, ← hs_def]
  -- no gate of the normalized row is at its kink
  have hP : ∀ t i, (rmsNorm 0 (Matrix.of fun _ : T => v) * Wr) t (Sum.inl i) ≠ 0 := fun t i => by
    rw [rmsNorm_const_mul_lrg, ← hs_def]
    exact mul_ne_zero hs.ne' (hv i)
  -- the entry `(t₀, j)` of the equation, unit by unit
  have e2 := congrFun (congrFun e t₀) j
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib,
    Matrix.zero_apply] at e2
  have key : ∀ i : hid 0, fderiv ℝ ((Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0)
        (rmsNorm 0 (Matrix.of fun _ : T => v) * Wr)
        (fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (Matrix.of fun _ : T => v)
            ((Matrix.of fun _ : T => v) * X) * Wr
          + rmsNorm 0 (Matrix.of fun _ : T => v) * ηr) t₀ i * Ww i j
      + (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0
          (rmsNorm 0 (Matrix.of fun _ : T => v) * Wr) t₀ i * W' i j
      = s ^ 2 * (relu (v ⬝ᵥ Wrᵀ (Sum.inl i)) * (v ⬝ᵥ Wrᵀ (Sum.inr i)) * W' i j
          + reluDeriv (v ⬝ᵥ Wrᵀ (Sum.inl i)) * (v ⬝ᵥ (X * Wr + ηr)ᵀ (Sum.inl i))
            * (v ⬝ᵥ Wrᵀ (Sum.inr i)) * Ww i j
          + relu (v ⬝ᵥ Wrᵀ (Sum.inl i)) * (v ⬝ᵥ (X * Wr + ηr)ᵀ (Sum.inr i)) * Ww i j)
        - s ^ 2 * (2 * ((v ⬝ᵥ (v ᵥ* X)) / Fintype.card d) * s ^ 2)
          * (relu (v ⬝ᵥ Wrᵀ (Sum.inl i)) * (v ⬝ᵥ Wrᵀ (Sum.inr i)) * Ww i j) := by
    intro i
    have hf : (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0
          (rmsNorm 0 (Matrix.of fun _ : T => v) * Wr) t₀ i
        = relu ((rmsNorm 0 (Matrix.of fun _ : T => v) * Wr) t₀ (Sum.inl i))
          * (rmsNorm 0 (Matrix.of fun _ : T => v) * Wr) t₀ (Sum.inr i) := rfl
    rw [fderiv_f_apply_lrg _ _ hP, hf, Matrix.add_apply, Matrix.add_apply, hdN, hdN, hN, hN, hN,
      hN, relu_mul_lrg hs, reluDeriv_mul_lrg hs]
    have hψg : v ⬝ᵥ (X * Wr + ηr)ᵀ (Sum.inl i)
        = (v ᵥ* X) ⬝ᵥ Wrᵀ (Sum.inl i) + v ⬝ᵥ ηrᵀ (Sum.inl i) := by
      show v ⬝ᵥ (X *ᵥ Wrᵀ (Sum.inl i) + ηrᵀ (Sum.inl i)) = _
      rw [dotProduct_add, Matrix.dotProduct_mulVec]
    have hψv : v ⬝ᵥ (X * Wr + ηr)ᵀ (Sum.inr i)
        = (v ᵥ* X) ⬝ᵥ Wrᵀ (Sum.inr i) + v ⬝ᵥ ηrᵀ (Sum.inr i) := by
      show v ⬝ᵥ (X *ᵥ Wrᵀ (Sum.inr i) + ηrᵀ (Sum.inr i)) = _
      rw [dotProduct_add, Matrix.dotProduct_mulVec]
    have he := reluDeriv_mul_self_lrg (v ⬝ᵥ Wrᵀ (Sum.inl i))
    linear_combination (-s ^ 2 * reluDeriv (v ⬝ᵥ Wrᵀ (Sum.inl i)) * (v ⬝ᵥ Wrᵀ (Sum.inr i))
        * Ww i j) * hψg
      + (-s ^ 2 * relu (v ⬝ᵥ Wrᵀ (Sum.inl i)) * Ww i j) * hψv
      + (-((v ⬝ᵥ (v ᵥ* X)) / Fintype.card d) * s ^ 4 * (v ⬝ᵥ Wrᵀ (Sum.inr i)) * Ww i j) * he
  -- the sum over the units: `s² (∂_ψ B(v) − 2 (v·vX/d) s² B(v)) = 0`
  have e3 := (Finset.sum_congr rfl fun i _ => (key i).symm).trans e2
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at e3
  have hq : (v ⬝ᵥ (v ᵥ* X)) / Fintype.card d * (s ^ 2 * (v ⬝ᵥ v)) = (v ᵥ* X) ⬝ᵥ v := by
    rw [hs2, div_mul_cancel₀ _ hd0.ne', dotProduct_comm]
  unfold unitSum_lrg block_lrg
  refine sub_eq_zero.1 ((mul_eq_zero.1 ?_).resolve_left (pow_ne_zero 2 hs.ne'))
  linear_combination (v ⬝ᵥ v) * e3
    + s ^ 2 * 2 * (∑ i, relu (v ⬝ᵥ Wrᵀ (Sum.inl i)) * (v ⬝ᵥ Wrᵀ (Sum.inr i)) * Ww i j) * hq

end HelpersLrg

/-- **Proof of Theorem B.1 (iii) of the skips paper, "The case `ε = 0`", the flat directions for
one ReGLU block with a full learned skip:** under the conditions `OneBlockGenericReGLURMS`, for
`d ≥ 2`, an invertible skip `A = R 0`, a block that turns a dense set of the rows with an active
gate and one turned row off the kinks of the gates, a direction `(η, η_A)` of the weights and the
skip that is flat at every input at which no normalized row vanishes and no gate sits at its kink
is the sum of the rotations of `h_0` and `h_1` (antisymmetric `X₀`, `Y`), the scalings of `h_0`
and `h_1` (numbers `c₀`, `c₁`), a rescaling of the values and a rescaling of the gates of the
hidden units, with `η_A = A (Y + c₁ I) − (X₀ + c₀ I) A`. -/
theorem flatSkipsOn_noKinkGate_le_reglu_learned_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det)
    (hturn : TurnsActiveRowsGatedSkip θ (R 0))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* R 0, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v])
    (η : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (ρ : Fin 1 → Matrix d d ℝ)
    (hη : (η, ρ) ∈ flatSkipsOn (Arch.gated relu (rmsNorm 0) hid)
      (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
      (learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ R ∩ noKinkGateRMS θ)) :
    ∃ (X₀ Y : Matrix d d ℝ) (c₀ c₁ : ℝ) (α β : ∀ ℓ, hid ℓ → ℝ), X₀ᵀ = -X₀ ∧ Yᵀ = -Y ∧
      η = cobDir θ ![X₀, Y] + scaleDir θ ![c₀, c₁] + rescaleDir θ α + rescaleDirGate 1 θ β ∧
      ρ 0 = R 0 * (Y + c₁ • 1) - (X₀ + c₀ • 1) * R 0 := by
  classical
  -- `x ↦ x E` is onto, through a left inverse `Ep` of `E`
  obtain ⟨Ep, hEp⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hθ.gated.rank_E)
  have hxE : ∀ u : d → ℝ, (Matrix.of fun _ : T => u) * Ep * θ.E = Matrix.of fun _ : T => u :=
    fun u => by rw [Matrix.mul_assoc, hEp, Matrix.mul_one]
  -- the input with every row `u'`, `u' E = u`, for a row `u` with no gate at its kink and with
  -- `u A`, `b(u)` independent: no gate of `x E W_read` is at its kink, and for every token the
  -- rows `u A` of `x E A` and `b(N_0(u)) = s² b(u)` (`s > 0`) of `g(x)` are independent
  have hgood : ∀ u : d → ℝ, (∀ i, (u ᵥ* θ.read 0) (Sum.inl i) ≠ 0) →
      LinearIndependent ℝ ![u ᵥ* R 0, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) u] →
      (Matrix.of fun _ : T => u) * Ep * θ.E * θ.read 0
          ∈ {M : Matrix T (hid 0 ⊕ hid 0) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0} ∧
      ∀ t, LinearIndependent ℝ ![((Matrix.of fun _ : T => u) * Ep * θ.E * R 0) t,
        ((Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0
          (rmsNorm 0 ((Matrix.of fun _ : T => u) * Ep * θ.E) * θ.read 0) * θ.write 0) t] := by
    intro u hu hli
    rw [hxE]
    refine ⟨fun t i => hu i, fun t => ?_⟩
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact hli.ne_zero 0 (by simp)
    obtain ⟨r, hr, e⟩ := row_block_lrg (θ.read 0) (θ.write 0) (Matrix.of fun _ : T => u) t hu0
    have e' : ((Matrix.of fun _ : T => u) * R 0) t = u ᵥ* R 0 := rfl
    rw [e, e']
    exact linearIndependent_pair_smul_lrg hli hr
  -- there is a hidden unit: the block does not vanish at the turned row `v₀`
  obtain ⟨v₀, hv₀, hli₀⟩ := hw
  have hne : Nonempty (hid 0) := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    apply hli₀.ne_zero 1
    funext j
    simp [gatedBlock, Matrix.vecMul, dotProduct, Finset.univ_eq_empty]
  -- Steps 1 to 3 (the case `ε = 0` of part (iii), with the learned skip) on the cone of
  -- pre-activations with no gate at its kink, which is open and invariant under positive
  -- scalings of the rows, and on which the block map is `C¹`: `η_E = E X`,
  -- `η_A = A (Y + c I) − X A`, `η_D = −Y D`, and the derivative of the block along `η` is
  -- `g(x) (Y + c I)` at every input whose rows of `x E A` and `g(x)` are independent
  obtain ⟨X, Y, c, hYa, hEX, hρ, hDY, hF⟩ := exists_of_flatSkipsOn_learned_rmsNorm_zero_on
    (A := Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) rfl hd
    {M | ∀ t i, M t (Sum.inl i) ≠ 0} isOpen_gateSet_lrg
    (fun M hM c hc t i => mul_ne_zero (hc t).ne' (hM t i)) contDiffOn_f_lrg θ R
    hθ.gated.rank_E hθ.gated.rank_D hR ⟨_, hgood v₀ hv₀ hli₀⟩ η ρ hη
  obtain ⟨W', hW'⟩ : ∃ W', W' = η.write 0 - θ.write 0 * (Y + c • 1) := ⟨_, rfl⟩
  -- Step 4 (a), one row: at a row `v` with no gate at its kink and with `v A`, `b(v)`
  -- independent, the block equation at the input with every row `v'`, `v' E = v`, gives
  -- `‖v‖² ∂_ψ B(v) = 2 (v X vᵀ) B(v)`, with `ψ = X W_read + η_read`,
  -- `β_i = (η_write)_i − a_i (Y + c I)`
  have hind : ∀ v : d → ℝ, (∀ i, v ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0) →
      LinearIndependent ℝ ![v ᵥ* R 0, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v] → ∀ j : d,
      (v ⬝ᵥ v) * unitSum_lrg (θ.read 0) (X * θ.read 0 + η.read 0) (θ.write 0) W' v j
        = 2 * ((v ᵥ* X) ⬝ᵥ v) * block_lrg (θ.read 0) (θ.write 0) v j := by
    intro v hv hli j
    obtain ⟨hx, hxi⟩ := hgood v hv hli
    have e := hF _ hx hxi
    rw [hxE] at e
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hli.ne_zero 0 (by simp)
    refine row_eq_lrg (T := T) (θ.read 0) (η.read 0) (θ.write 0) W' X hv0 hv j ?_
    rw [hW', Matrix.mul_sub, ← Matrix.mul_assoc, ← e]
    abel
  -- Step 4 (a), every row with no gate at its kink: if some gate is active at `v`, then `v` is a
  -- limit of rows `u` with `u A`, `b(u)` independent (`hturn`), and both sides are continuous
  -- off the kinks; if no gate is active, `relu` and `relu'` vanish at every gate of `v`
  have hall : ∀ v : d → ℝ, (∀ i, v ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0) → ∀ j : d,
      (v ⬝ᵥ v) * unitSum_lrg (θ.read 0) (X * θ.read 0 + η.read 0) (θ.write 0) W' v j
        - 2 * ((v ᵥ* X) ⬝ᵥ v) * block_lrg (θ.read 0) (θ.write 0) v j = 0 := by
    intro v hv j
    by_cases hact : ∃ i, relu (v ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i)) ≠ 0
    · have hnear : ∀ᶠ u in nhds v, ∀ i, u ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0 :=
        Filter.eventually_all.2 fun i =>
          ContinuousAt.eventually_ne (g := fun u : d → ℝ => u ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i))
            (continuous_id.dotProduct continuous_const).continuousAt (hv i)
      have hc := continuousAt_eq_lrg (θ.read 0) (X * θ.read 0 + η.read 0) (θ.write 0) W' X j hv
      have h := eq_zero_of_mem_closure_lrg hc (hturn v hv hact) hnear
        fun u hu huk => sub_eq_zero.2 (hind u huk hu j)
      exact h
    · push Not at hact
      have h1 : unitSum_lrg (θ.read 0) (X * θ.read 0 + η.read 0) (θ.write 0) W' v j = 0 := by
        rw [unitSum_lrg]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [reluDeriv_eq_zero_lrg (hact i), hact i]
        ring
      have h2 : block_lrg (θ.read 0) (θ.write 0) v j = 0 := by
        rw [block_lrg]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hact i]
        ring
      rw [h1, h2]
      ring
  -- Step 4 (b): `reglu_unitsRescaleSphere` with the symmetric part `X_s = (X + Xᵀ)/2` of `X` (the
  -- same quadratic form): `X_s = c₀ I`, `ψg_i = λ_i g_i`, `ψv_i = μ_i v_i`,
  -- `β_i = (2 c₀ − λ_i − μ_i) a_i`
  have hsymm : ((1 / 2 : ℝ) • (X + Xᵀ))ᵀ = (1 / 2 : ℝ) • (X + Xᵀ) := by
    rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  obtain ⟨c₀, lam, mu, hXs, hlam⟩ := reglu_unitsRescaleSphere
    (fun i => (θ.read 0)ᵀ (Sum.inl i)) (fun i => (θ.read 0)ᵀ (Sum.inr i))
    (fun i => θ.write 0 i) ((1 / 2 : ℝ) • (X + Xᵀ))
    (fun i => (X * θ.read 0 + η.read 0)ᵀ (Sum.inl i))
    (fun i => (X * θ.read 0 + η.read 0)ᵀ (Sum.inr i)) (fun i => W' i)
    hθ.gated.row_ne_zero hθ.gated.gate_ne_zero hθ.gated.gate_not_collinear hθ.value_not_gate
    hsymm (by
      intro v hv
      have hq : (v ᵥ* ((1 / 2 : ℝ) • (X + Xᵀ))) ⬝ᵥ v = (v ᵥ* X) ⬝ᵥ v := by
        rw [Matrix.vecMul_smul, Matrix.vecMul_add, Matrix.vecMul_transpose, smul_dotProduct,
          add_dotProduct, dotProduct_comm (X *ᵥ v) v, Matrix.dotProduct_mulVec, smul_eq_mul]
        ring
      funext j
      have h := hall v hv j
      unfold unitSum_lrg block_lrg at h
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hq]
      linear_combination h)
  -- Step 4 (c): with `X₀ = X − c₀ I` (antisymmetric), `β_i = λ_i − c₀` (gates) and
  -- `α_i = c₀ − μ_i` (values), the direction is
  -- `cobDir θ (X₀, Y) + scaleDir θ (c₀, c) + rescaleDir θ α + rescaleDirGate 1 θ β`
  have hX₀ : (X - c₀ • 1)ᵀ = -(X - c₀ • 1) := by
    ext a b
    have h := congrFun (congrFun hXs a) b
    have h1 : (1 : Matrix d d ℝ) b a = (1 : Matrix d d ℝ) a b :=
      congrFun (congrFun (Matrix.transpose_one (n := d) (α := ℝ)) a) b
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul] at h
    simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
      smul_eq_mul, h1]
    linear_combination 2 * h
  obtain ⟨α, hα⟩ : ∃ α : ∀ ℓ : Fin 1, hid ℓ → ℝ, ∀ i, α 0 i = c₀ - mu i :=
    ⟨fun ℓ => Fin.cases (fun i => c₀ - mu i) (fun l => l.elim0) ℓ, fun i => rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ∀ ℓ : Fin 1, hid ℓ → ℝ, ∀ i, β 0 i = lam i - c₀ :=
    ⟨fun ℓ => Fin.cases (fun i => lam i - c₀) (fun l => l.elim0) ℓ, fun i => rfl⟩
  refine ⟨X - c₀ • 1, Y, c₀, c, α, β, hX₀, hYa,
    Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_, ?_⟩
  · show η.E = θ.E * (X - c₀ • 1) + c₀ • θ.E + 0 + 0
    rw [hEX, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, add_zero, add_zero, sub_add_cancel]
  · obtain rfl := Subsingleton.elim ℓ 0
    ext a j
    have h2 : ∀ j', ((X - c₀ • 1) * θ.read 0 : Matrix d (hid 0 ⊕ hid 0) ℝ) a j'
        = (X * θ.read 0) a j' - c₀ * θ.read 0 a j' := fun j' => by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul]
    rcases j with i | i
    · have h1 : (X * θ.read 0) a (Sum.inl i) + η.read 0 a (Sum.inl i)
          = lam i * θ.read 0 a (Sum.inl i) :=
        congrFun (hlam i).1 a
      show η.read 0 a (Sum.inl i)
        = -(((X - c₀ • 1) * θ.read 0 : Matrix d (hid 0 ⊕ hid 0) ℝ) a (Sum.inl i)) + 0 + 0
          + β 0 i * θ.read 0 a (Sum.inl i)
      rw [h2, hβ i]
      linear_combination h1
    · have h1 : (X * θ.read 0) a (Sum.inr i) + η.read 0 a (Sum.inr i)
          = mu i * θ.read 0 a (Sum.inr i) :=
        congrFun (hlam i).2.1 a
      show η.read 0 a (Sum.inr i)
        = -(((X - c₀ • 1) * θ.read 0 : Matrix d (hid 0 ⊕ hid 0) ℝ) a (Sum.inr i)) + 0
          + -(α 0 i) * θ.read 0 a (Sum.inr i) + 0
      rw [h2, hα i]
      linear_combination h1
  · obtain rfl := Subsingleton.elim ℓ 0
    ext i a
    have h1 : η.write 0 i a - (θ.write 0 * (Y + c • 1) : Matrix (hid 0) d ℝ) i a
        = (2 * c₀ - lam i - mu i) * θ.write 0 i a := by
      rw [← Matrix.sub_apply, ← hW']
      exact congrFun (hlam i).2.2 a
    have h2 : (θ.write 0 * (Y + c • 1) : Matrix (hid 0) d ℝ) i a
        = (θ.write 0 * Y) i a + c * θ.write 0 i a := by
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul]
    show η.write 0 i a = (θ.write 0 * Y) i a + c * θ.write 0 i a + α 0 i * θ.write 0 i a
      + -(((1 : ℕ) : ℝ) * β 0 i) * θ.write 0 i a
    rw [hα i, hβ i, Nat.cast_one]
    linear_combination h1 + h2
  · show η.D = -(Y * θ.D) + 0 + 0 + 0
    rw [hDY, add_zero, add_zero, add_zero]
  · rw [hρ, sub_add_cancel]

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", for one ReGLU block with
a full learned skip, at one parameter:** under the conditions of the proof,
`funDimLearned = P + d² − (d(d−1) + 2) − 2 d_hidden`, with `P` the number of weights without the
skip. -/
theorem funDimLearned_reglu_oneBlock_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det)
    (hturn : TurnsActiveRowsGatedSkip θ (R 0))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* R 0, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v]) :
    funDimLearned (Arch.gated relu (rmsNorm 0) hid) (θ, R)
        + ((Fintype.card d * (Fintype.card d - 1) + 2) + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", in the paper's own
sense, for one ReGLU block with a full learned skip, at one parameter:** a finite batch of inputs
at which no normalized row vanishes and no gate sits at its kink, on which the Jacobian in the
weights and the skip has the rank `P + d² − (d(d−1) + 2) − 2 d_hidden`. -/
theorem exists_jacobianRankSkips_reglu_oneBlock_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det)
    (hturn : TurnsActiveRowsGatedSkip θ (R 0))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* R 0, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v]) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ R ∩ noKinkGateRMS θ) ∧
      jacobianRankSkips (Arch.gated relu (rmsNorm 0) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X (θ, R)
          + ((Fintype.card d * (Fintype.card d - 1) + 2) + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  sorry

end Skips
