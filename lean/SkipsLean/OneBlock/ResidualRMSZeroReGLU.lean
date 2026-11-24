import SkipsLean.OneBlock.ResidualRMSZeroStepsOn
import SkipsLean.OneBlock.ResidualRMSReGLU
import SkipsLean.Residual.UpperBoundRescaleRMSNormZero
import SkipsLean.Absorb.Block

/-!
# One residual ReGLU block under pre-RMSNorm with `ε = 0`: the functional dimension

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`". For ReGLU
`s = 2 d_hidden`: one rescaling of the gate and one of the value for each hidden unit.

Its proof, "The residual network": "The case `ε = 0` of part (iii), with `A = I`, shows that a
flat direction is the sum of a direction of the rotation and scaling of all hidden states and a
direction `ψ` of the weights of the block along which `B` has derivative zero on the sphere of
radius `√d_model`. This derivative is positively homogeneous of degree `k` in `n`, so it vanishes
for all `n ≠ 0`, and Lemma B.3, with `E` and `D` replaced by the identity and `M = 0`, makes `ψ` a
rescaling of the units. So `dim K(θ) = d_model (d_model − 1)/2 + 1 + s`."

This file is the twin, for a ReGLU block, of `OneBlock/ResidualRMSZeroRescale.lean` (ReLU and
ReLU² blocks, `ε = 0`) and, for `ε = 0`, of `OneBlock/ResidualRMSReGLU.lean` (a ReGLU block,
`ε > 0`). As there, the case `ε = 0` of part (iii) gives the zero derivative only at the inputs
`w` at which `w E` and `g(w)` are linearly independent (`OneBlock/ResidualRMSZeroStepsOn.lean`),
and the step to all inputs off the kinks uses that the block turns a dense set of the rows at
which some gate is active (`TurnsActiveRowsGated`): at a row where no gate is active the
derivative of the block along any direction is zero; elsewhere the derivative is continuous off
the kinks of the gates and vanishes on a dense set. The condition holds at almost every parameter
(`OneBlock/ResidualRMSZeroReGLUGeneric.lean`).

Here, at one parameter under the conditions of the proof (`OneBlockGenericReGLURMS`, the two
conditions on turned rows): the flat directions at the paper's inputs (no normalized row
vanishes, no gate at its kink) are a rotation and a scaling of both hidden states plus a rescaling
of the values and a rescaling of the gates of the hidden units; the value of Lean's `funDim`; a
finite batch of the paper's inputs on which the Jacobian has this rank. No width of the block is
asked.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ}

/-- **A gated block turns a dense set of the rows at which some gate is active:** every row `v`
with no gate at its kink (no entry of the gate columns of `v W_read` is zero) and with some
active gate (`σ` of such an entry is not zero) is a limit of rows `u` such that `u` and the
output of the block at `u` are linearly independent. The output at `u` is
`gatedBlock σ W_gate W_value W_write u`, with `W_gate` and `W_value` the gate columns and the
value columns of `W_read`. -/
def TurnsActiveRowsGated
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) : Prop :=
  ∀ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) →
    (∃ i, σ ((v ᵥ* θ.read 0) (Sum.inl i)) ≠ 0) →
    v ∈ closure {u : d → ℝ | LinearIndependent ℝ ![u, gatedBlock σ
      ((θ.read 0).submatrix id Sum.inl) ((θ.read 0).submatrix id Sum.inr) (θ.write 0) u]}

section HelpersRgz

open Filter
open scoped Topology

/-! ### The ReGLU block away from the kinks of its gates (copies of the `_rglu` helpers of
`OneBlock/ResidualRMSReGLU.lean`, for `ε = 0`) -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `τ ↦ a + τ b` has the derivative `b` at `0`. -/
private theorem hasDerivAt_affine_rgz (a b : ℝ) : HasDerivAt (fun τ : ℝ => a + τ * b) b 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const b).const_add a
  rw [one_mul] at h
  exact h

/-- Helper: `relu` is `C¹` away from its kink (it is `0` or the identity near `z ≠ 0`). -/
private theorem contDiffAt_relu_rgz {z : ℝ} (hz : z ≠ 0) : ContDiffAt ℝ 1 relu z := by
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
private theorem isOpen_gateSet_rgz :
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
private theorem contDiffAt_f_rgz (M : Matrix T (hid 0 ⊕ hid 0) ℝ)
    (hM : ∀ t i, M t (Sum.inl i) ≠ 0) :
    ContDiffAt ℝ 1 ((Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0) M := by
  refine contDiffAt_pi.2 fun t => contDiffAt_pi.2 fun i => ?_
  have he : ∀ j, ContDiffAt ℝ 1 (fun N : Matrix T (hid 0 ⊕ hid 0) ℝ => N t j) M := fun j =>
    (contDiff_apply_apply ℝ t j).contDiffAt
  have h := ((contDiffAt_relu_rgz (hM t i)).comp M (he (Sum.inl i))).mul (he (Sum.inr i))
  exact h

omit [Nonempty T] [DecidableEq d] in
/-- Helper: the map of the ReGLU block is `C¹` on the pre-activations with no gate at its
kink. -/
private theorem contDiffOn_f_rgz :
    ContDiffOn ℝ 1 ((Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0)
      {M : Matrix T (hid 0 ⊕ hid 0) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0} := by
  intro M hM
  exact (contDiffAt_f_rgz M hM).contDiffWithinAt

omit [Nonempty T] [DecidableEq d] in
/-- Helper: the derivative of the map of the ReGLU block at `M` (no gate at its kink) along `N`,
entry `(t, i)`: `1[M_{t, g i} > 0] N_{t, g i} M_{t, v i} + relu(M_{t, g i}) N_{t, v i}`. -/
private theorem fderiv_f_apply_rgz (M N : Matrix T (hid 0 ⊕ hid 0) ℝ)
    (hM : ∀ t i, M t (Sum.inl i) ≠ 0) (t : T) (i : hid 0) :
    fderiv ℝ ((Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0) M N t i
      = reluDeriv (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + relu (M t (Sum.inl i)) * N t (Sum.inr i) := by
  have hd := (contDiffAt_f_rgz (d := d) M hM).differentiableAt_one
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
    have hu := hasDerivAt_affine_rgz (M t (Sum.inl i)) (N t (Sum.inl i))
    have hw := hasDerivAt_affine_rgz (M t (Sum.inr i)) (N t (Sum.inr i))
    have h := ((hasDerivAt_relu (hM t i)).comp_of_eq (0 : ℝ) hu
      (by simp only [zero_mul, add_zero])).mul hw
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, add_zero]
  exact h2.unique h3

/-! ### The derivative of the block along a direction, at one row -/

/-- Helper: the entry `k` of the derivative of the block along `R'`, `W'` at one row `u` of the
hidden state (the order of the terms of Lemma B.3): `∑_i [relu(u c_i) (u e_i) W'_{i k}
+ 1[u c_i > 0] (u ψc_i) (u e_i) W_{i k} + relu(u c_i) (u ψe_i) W_{i k}]`, with `c_i`, `e_i` the
gate and value columns of `R` and `ψc_i`, `ψe_i` those of `R'`. -/
private noncomputable def unitSum_rgz {q : Type*} [Fintype q] (R R' : Matrix d (q ⊕ q) ℝ)
    (W W' : Matrix q d ℝ) (u : d → ℝ) (k : d) : ℝ :=
  ∑ i, (relu (u ⬝ᵥ Rᵀ (Sum.inl i)) * (u ⬝ᵥ Rᵀ (Sum.inr i)) * W' i k
    + reluDeriv (u ⬝ᵥ Rᵀ (Sum.inl i)) * (u ⬝ᵥ R'ᵀ (Sum.inl i)) * (u ⬝ᵥ Rᵀ (Sum.inr i)) * W i k
    + relu (u ⬝ᵥ Rᵀ (Sum.inl i)) * (u ⬝ᵥ R'ᵀ (Sum.inr i)) * W i k)

omit [Nonempty T] [DecidableEq d] in
/-- Helper: the derivative of `n ↦ f(n R) W` along `R'`, `W'`, entry `(t, k)`, is `unitSum_rgz`
at the row `n_t`, when no gate of `n R` sits at its kink. -/
private theorem fderiv_add_apply_rgz (n : Matrix T d ℝ) (R R' : Matrix d (hid 0 ⊕ hid 0) ℝ)
    (W W' : Matrix (hid 0) d ℝ) (hn : ∀ t i, (n * R) t (Sum.inl i) ≠ 0) (t : T) (k : d) :
    (fderiv ℝ ((Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0) (n * R) (n * R') * W
        + (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0 (n * R) * W') t k
      = unitSum_rgz R R' W W' (n t) k := by
  rw [unitSum_rgz, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_apply_rgz _ _ hn]
  have hf : (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0 (n * R) t i
      = relu ((n * R) t (Sum.inl i)) * (n * R) t (Sum.inr i) := rfl
  -- `(n S)_{t j} = n_t ⬝ S_j`
  have hc : ∀ (S : Matrix d (hid 0 ⊕ hid 0) ℝ) (j : hid 0 ⊕ hid 0), (n * S) t j = n t ⬝ᵥ Sᵀ j :=
    fun _ _ => rfl
  rw [hf]
  simp only [hc]
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `relu (λ z) = λ relu z` for `λ > 0`. -/
private theorem relu_mul_rgz {lam : ℝ} (hlam : 0 < lam) (z : ℝ) :
    relu (lam * z) = lam * relu z := by
  rw [relu_homogeneous lam z hlam, pow_one]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `relu' (λ z) = relu' z` for `λ > 0`. -/
private theorem reluDeriv_mul_rgz {lam : ℝ} (hlam : 0 < lam) (z : ℝ) :
    reluDeriv (lam * z) = reluDeriv z := by
  simp only [reluDeriv, mul_pos_iff_of_pos_left hlam]

omit [DecidableEq d] in
/-- Helper: `unitSum_rgz` is homogeneous of degree `2` in the row, for positive factors. -/
private theorem unitSum_smul_rgz {q : Type*} [Fintype q] (R R' : Matrix d (q ⊕ q) ℝ)
    (W W' : Matrix q d ℝ) {lam : ℝ} (hlam : 0 < lam) (u : d → ℝ) (k : d) :
    unitSum_rgz R R' W W' (lam • u) k = lam ^ 2 * unitSum_rgz R R' W W' u k := by
  simp only [unitSum_rgz, smul_dotProduct, smul_eq_mul, Finset.mul_sum, relu_mul_rgz hlam,
    reluDeriv_mul_rgz hlam]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Helper: `relu'` is continuous away from the kink (it is constant near `z ≠ 0`). -/
private theorem continuousAt_reluDeriv_rgz {z : ℝ} (hz : z ≠ 0) : ContinuousAt reluDeriv z := by
  rcases hz.lt_or_gt with hneg | hpos
  · refine ContinuousAt.congr (f := fun _ : ℝ => (0 : ℝ)) continuousAt_const ?_
    filter_upwards [eventually_lt_nhds hneg] with y hy
    simp only [reluDeriv, not_lt.2 hy.le, ite_false]
  · refine ContinuousAt.congr (f := fun _ : ℝ => (1 : ℝ)) continuousAt_const ?_
    filter_upwards [eventually_gt_nhds hpos] with y hy
    simp only [reluDeriv, hy, ite_true]

/-- Helper: at `z ≠ 0` with `relu z = 0` (an inactive gate), `relu' z = 0`. -/
private theorem reluDeriv_eq_zero_rgz {z : ℝ} (h0 : relu z = 0) : reluDeriv z = 0 := by
  have hz : ¬ 0 < z := fun hz => by
    rw [relu, max_eq_left hz.le] at h0
    exact hz.ne' h0
  simp only [reluDeriv, hz, ite_false]

omit [DecidableEq d] in
/-- Helper: the derivative `unitSum_rgz` of the block is continuous in the row at a row with no
gate at its kink. -/
private theorem continuousAt_unitSum_rgz {q : Type*} [Fintype q] (R R' : Matrix d (q ⊕ q) ℝ)
    (W W' : Matrix q d ℝ) (k : d) {u : d → ℝ} (hu : ∀ i, u ⬝ᵥ Rᵀ (Sum.inl i) ≠ 0) :
    ContinuousAt (fun v : d → ℝ => unitSum_rgz R R' W W' v k) u := by
  have hdot : ∀ c : d → ℝ, Continuous fun v : d → ℝ => v ⬝ᵥ c := fun c =>
    continuous_id.dotProduct continuous_const
  have hterm : ∀ i, ContinuousAt (fun v : d → ℝ =>
      relu (v ⬝ᵥ Rᵀ (Sum.inl i)) * (v ⬝ᵥ Rᵀ (Sum.inr i)) * W' i k
        + reluDeriv (v ⬝ᵥ Rᵀ (Sum.inl i)) * (v ⬝ᵥ R'ᵀ (Sum.inl i)) * (v ⬝ᵥ Rᵀ (Sum.inr i))
          * W i k
        + relu (v ⬝ᵥ Rᵀ (Sum.inl i)) * (v ⬝ᵥ R'ᵀ (Sum.inr i)) * W i k) u := by
    intro i
    have h1 : ContinuousAt (fun v : d → ℝ => relu (v ⬝ᵥ Rᵀ (Sum.inl i))) u :=
      ContinuousAt.comp (f := fun v : d → ℝ => v ⬝ᵥ Rᵀ (Sum.inl i)) (x := u)
        (hasDerivAt_relu (hu i)).continuousAt (hdot _).continuousAt
    have h2 : ContinuousAt (fun v : d → ℝ => reluDeriv (v ⬝ᵥ Rᵀ (Sum.inl i))) u :=
      ContinuousAt.comp (f := fun v : d → ℝ => v ⬝ᵥ Rᵀ (Sum.inl i)) (x := u)
        (continuousAt_reluDeriv_rgz (hu i)) (hdot _).continuousAt
    have h3 := (hdot (Rᵀ (Sum.inr i))).continuousAt (x := u)
    have h4 := (hdot (R'ᵀ (Sum.inl i))).continuousAt (x := u)
    have h5 := (hdot (R'ᵀ (Sum.inr i))).continuousAt (x := u)
    exact (((h1.mul h3).mul continuousAt_const).add
      (((h2.mul h4).mul h3).mul continuousAt_const)).add ((h1.mul h5).mul continuousAt_const)
  have h := tendsto_finsetSum (f := fun (i : q) (v : d → ℝ) =>
    relu (v ⬝ᵥ Rᵀ (Sum.inl i)) * (v ⬝ᵥ Rᵀ (Sum.inr i)) * W' i k
      + reluDeriv (v ⬝ᵥ Rᵀ (Sum.inl i)) * (v ⬝ᵥ R'ᵀ (Sum.inl i)) * (v ⬝ᵥ Rᵀ (Sum.inr i)) * W i k
      + relu (v ⬝ᵥ Rᵀ (Sum.inl i)) * (v ⬝ᵥ R'ᵀ (Sum.inr i)) * W i k) Finset.univ
    fun i _ => hterm i
  exact h

/-- Helper: a function continuous at a point `u` of the closure of `S` that vanishes at the
points of `S` with a property `P` holding near `u` vanishes at `u`. -/
private theorem eq_zero_of_mem_closure_rgz {X : Type*} [TopologicalSpace X] {F : X → ℝ} {u : X}
    {S : Set X} {P : X → Prop} (hF : ContinuousAt F u) (hu : u ∈ closure S)
    (hP : ∀ᶠ v in 𝓝 u, P v) (h0 : ∀ v ∈ S, P v → F v = 0) : F u = 0 := by
  by_contra hne
  obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ := mem_closure_iff_nhds.1 hu _ ((hF.eventually_ne hne).and hP)
  exact hv1 (h0 v hv3 hv2)

/-! ### The normalized rows and the block on one row -/

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `N_0` scales every row: `(N_0(h) W)_{t i} = (‖h_t‖²/d)^{-1/2} (h W)_{t i}`. -/
private theorem rmsNorm_mul_apply_rgz {n : Type*} [Fintype n] (h : Matrix T d ℝ)
    (W : Matrix d n ℝ) (t : T) (i : n) :
    (rmsNorm 0 h * W) t i
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + 0))⁻¹ * (h * W) t i := by
  simp only [Matrix.mul_apply, Finset.mul_sum, rmsNorm, rmsRow, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul, mul_assoc]

omit [DecidableEq d] in
/-- Helper: the factor of `N_0` at a row `v ≠ 0` is positive. -/
private theorem inv_sqrt_pos_rgz {v : d → ℝ} (hv : v ≠ 0) :
    0 < (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + 0))⁻¹ := by
  have h1 : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j))
      (fun h => hv (dotProduct_self_eq_zero.1 h.symm))
  obtain ⟨j, -⟩ := Function.ne_iff.1 hv
  have h2 : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩)
  rw [add_zero]
  exact inv_pos.2 (Real.sqrt_pos.2 (div_pos h1 h2))

omit [DecidableEq d] in
/-- Helper: the ReGLU block on one row is positively homogeneous of degree `2`:
`b(s u) = s² b(u)` for `s > 0`. -/
private theorem gatedBlock_smul_rgz {q : Type*} [Fintype q] (Wg Wv : Matrix d q ℝ)
    (W : Matrix q d ℝ) (u : d → ℝ) {s : ℝ} (hs : 0 < s) :
    gatedBlock relu Wg Wv W (s • u) = s ^ 2 • gatedBlock relu Wg Wv W u := by
  unfold gatedBlock
  have e : (fun i => relu (((s • u) ᵥ* Wg) i) * ((s • u) ᵥ* Wv) i)
      = s ^ 2 • fun i => relu ((u ᵥ* Wg) i) * (u ᵥ* Wv) i := by
    funext i
    simp only [Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul, relu_mul_rgz hs]
    ring
  rw [e, Matrix.smul_vecMul]

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: at a row `h_t ≠ 0`, the row `t` of the block `f(N_0(h) W_read) W_write` is
`s² b(h_t)`, with `s = (‖h_t‖²/d)^{-1/2} > 0`. -/
private theorem row_block_rgz (R : Matrix d (hid 0 ⊕ hid 0) ℝ) (W : Matrix (hid 0) d ℝ)
    (h : Matrix T d ℝ) (t : T) (ht : h t ≠ 0) :
    ((Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0 (rmsNorm 0 h * R) * W) t
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + 0))⁻¹ ^ 2
        • gatedBlock relu (R.submatrix id Sum.inl) (R.submatrix id Sum.inr) W (h t) := by
  have e1 : ((Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0 (rmsNorm 0 h * R) * W) t
      = gatedBlock relu (R.submatrix id Sum.inl) (R.submatrix id Sum.inr) W (rmsNorm 0 h t) :=
    rfl
  have e2 : rmsNorm 0 h t = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + 0))⁻¹ • h t := rfl
  rw [e1, e2]
  exact gatedBlock_smul_rgz _ _ W (h t) (inv_sqrt_pos_rgz ht)

/-- Helper: scaling the second vector of an independent pair by `r ≠ 0` keeps it independent. -/
private theorem linearIndependent_pair_smul_rgz {V : Type*} [AddCommGroup V] [Module ℝ V]
    {a b : V} (h : LinearIndependent ℝ ![a, b]) {r : ℝ} (hr : r ≠ 0) :
    LinearIndependent ℝ ![a, r • b] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  obtain ⟨h1, h2⟩ := h s (t * r) (by rw [mul_smul]; exact hst)
  exact ⟨h1, (mul_eq_zero.1 h2).resolve_right hr⟩

end HelpersRgz

/-- **Proof of Theorem B.1 (iv) of the skips paper, "The residual network", for a ReGLU block:**
let `ε = 0` and `d ≥ 2`; under the conditions `OneBlockGenericReGLURMS`, if the block turns a
dense set of the rows with an active gate and turns some row off the kinks of the gates, then a
direction that is flat at every input at which no normalized row vanishes and no gate sits at its
kink is the direction of a rotation and of a scaling shared by `h_0` and `h_1`, plus a rescaling
of the values and a rescaling of the gates of the hidden units. -/
theorem flatOn_noKinkGate_le_reglu_residual_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d) (hturn : TurnsActiveRowsGated θ)
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v])
    (η : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.gated relu (rmsNorm 0) hid) 1 θ
      (residualZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ ∩ noKinkGateRMS θ)) :
    ∃ (Y : Matrix d d ℝ) (c : ℝ) (α β : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
      η = cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c) + rescaleDir θ α
        + rescaleDirGate 1 θ β := by
  classical
  -- `x ↦ x E` is onto, through a left inverse `B` of `E`
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hθ.gated.rank_E)
  have hxE : ∀ u : d → ℝ, (Matrix.of fun _ : T => u) * B * θ.E = Matrix.of fun _ : T => u :=
    fun u => by rw [Matrix.mul_assoc, hB, Matrix.mul_one]
  -- the input with every row `u'`, `u' E = u`, for a row `u` with no gate at its kink and with
  -- `u`, `b(u)` independent: no gate of `x E W_read` is at its kink, and for every token the
  -- rows `u` of `x E` and `b(N_0(u)) = s² b(u)` (`s > 0`) of `g(x)` are independent
  have hgood : ∀ u : d → ℝ, (∀ i, (u ᵥ* θ.read 0) (Sum.inl i) ≠ 0) →
      LinearIndependent ℝ ![u, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) u] →
      (Matrix.of fun _ : T => u) * B * θ.E * θ.read 0
          ∈ {M : Matrix T (hid 0 ⊕ hid 0) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0} ∧
      ∀ t, LinearIndependent ℝ ![((Matrix.of fun _ : T => u) * B * θ.E) t,
        ((Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0
          (rmsNorm 0 ((Matrix.of fun _ : T => u) * B * θ.E) * θ.read 0) * θ.write 0) t] := by
    intro u hu hli
    rw [hxE]
    refine ⟨fun t i => hu i, fun t => ?_⟩
    have hu0 : u ≠ 0 := hli.ne_zero 0
    rw [row_block_rgz (θ.read 0) (θ.write 0) (Matrix.of fun _ : T => u) t hu0]
    exact linearIndependent_pair_smul_rgz hli (pow_ne_zero _ (inv_sqrt_pos_rgz hu0).ne')
  -- Steps 1 to 3 (the case `ε = 0` of part (iii)) on the cone of pre-activations with no gate at
  -- its kink, which is open and invariant under positive scalings of the rows, and on which the
  -- block map is `C¹`: `η_E = E (Y + c I)`, `η_D = -Y D`, and the derivative of the block along
  -- `ψ` vanishes at `N_0(x E)` for every input whose rows of `x E` and `g(x)` are independent
  obtain ⟨v₀, hv₀, hli₀⟩ := hw
  obtain ⟨Y, c, hYa, hEY, hDY, hF⟩ := exists_antisymm_scale_of_flatOn_residual_rmsNorm_zero_on
    (A := Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) rfl hd
    {M | ∀ t i, M t (Sum.inl i) ≠ 0} isOpen_gateSet_rgz
    (fun M hM c hc t i => mul_ne_zero (hc t).ne' (hM t i)) contDiffOn_f_rgz θ
    hθ.gated.rank_E hθ.gated.rank_D ⟨_, hgood v₀ hv₀ hli₀⟩ η hη
  generalize hR' : η.read 0 + Y * θ.read 0 = R' at hF
  generalize hW' : η.write 0 - θ.write 0 * (Y + c • 1) = W' at hF
  -- Step 4 (a), one row: at a row `v` with no gate at its kink and with `v`, `b(v)` independent,
  -- the block equation at the input with every row `v'`, `v' E = v`; the normalization scales
  -- `v` by `s > 0`, and the equation at `s v` is `s²` times the equation at `v`
  have hind : ∀ v : d → ℝ, (∀ i, v ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0) →
      LinearIndependent ℝ ![v, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v] → ∀ k : d,
      unitSum_rgz (θ.read 0) R' (θ.write 0) W' v k = 0 := by
    intro v hv hli k
    obtain ⟨hx, hxi⟩ := hgood v hv hli
    have e := hF _ hx hxi
    rw [hxE] at e
    have hv0 : v ≠ 0 := hli.ne_zero 0
    obtain ⟨s, hs, hrow⟩ : ∃ s : ℝ, 0 < s ∧
        ∀ t, rmsNorm 0 (Matrix.of fun _ : T => v) t = s • v :=
      ⟨_, inv_sqrt_pos_rgz hv0, fun t => rfl⟩
    have hn : ∀ t i,
        (rmsNorm 0 (Matrix.of fun _ : T => v) * θ.read 0) t (Sum.inl i) ≠ 0 := by
      intro t i
      show rmsNorm 0 (Matrix.of fun _ : T => v) t ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0
      rw [hrow, smul_dotProduct, smul_eq_mul]
      exact mul_ne_zero hs.ne' (hv i)
    have h2 := congrFun (congrFun e (Classical.arbitrary T)) k
    rw [fderiv_add_apply_rgz _ _ _ _ _ hn, hrow, unitSum_smul_rgz _ _ _ _ hs,
      Matrix.zero_apply] at h2
    exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero 2 hs.ne')
  -- Step 4 (a), every row with no gate at its kink: if some gate is active at `v`, then `v` is a
  -- limit of rows `u` with `u`, `b(u)` independent (`hturn`), and the derivative is continuous
  -- off the kinks; if no gate is active, `relu` and `relu'` vanish at every gate of `v`
  have hall : ∀ v : d → ℝ, (∀ i, v ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0) → ∀ k : d,
      unitSum_rgz (θ.read 0) R' (θ.write 0) W' v k = 0 := by
    intro v hv k
    by_cases hact : ∃ i, relu (v ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i)) ≠ 0
    · have hnear : ∀ᶠ u in nhds v, ∀ i, u ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0 :=
        Filter.eventually_all.2 fun i =>
          ContinuousAt.eventually_ne (g := fun u : d → ℝ => u ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i))
            (continuous_id.dotProduct continuous_const).continuousAt (hv i)
      have h := eq_zero_of_mem_closure_rgz
        (continuousAt_unitSum_rgz (θ.read 0) R' (θ.write 0) W' k hv) (hturn v hv hact) hnear
        fun u hu huk => hind u huk hu k
      exact h
    · push Not at hact
      rw [unitSum_rgz]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [reluDeriv_eq_zero_rgz (hact i), hact i]
      ring
  -- Step 4 (b): Lemma B.3 for ReGLU with `E` and `D` replaced by the identity and `M = 0`: the
  -- gate column `c_i` moves by `λ_i c_i`, the value column `e_i` by `-α_i e_i` and the write row
  -- `a_i` by `(α_i - λ_i) a_i`
  obtain ⟨-, -, lam, α, hlam⟩ := relu_gated_units_flat
    (fun i => (θ.read 0)ᵀ (Sum.inl i)) 0 (fun i => (θ.read 0)ᵀ (Sum.inr i)) 0
    (fun i => θ.write 0 i) 0 0 (fun i => R'ᵀ (Sum.inl i)) 0 (fun i => R'ᵀ (Sum.inr i)) 0
    (fun i => W' i) (fun i => hθ.gated.row_ne_zero i) (fun i => hθ.gated.gate_ne_zero i)
    (fun i j hij => hθ.gated.gate_not_collinear i j hij) (fun i => hθ.gated.value_ne_zero i)
    (fun i r h => hθ.value_not_gate i r (by have h1 := congrArg Prod.fst h; exact h1)) (by
      intro v hv
      have hv' : ∀ i, v ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0 := fun i => by
        have h := hv i
        simp only [Pi.zero_apply, add_zero] at h
        exact h
      funext k
      have h := hall v hv' k
      simp only [Matrix.vecMul_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, add_zero, zero_add]
      exact h)
  -- Step 4 (c): `η = cobDir θ (Y, Y) + scaleDir θ (c, c) + rescaleDir θ α + rescaleDirGate 1 θ λ`,
  -- component by component (one block)
  obtain ⟨α', hα'⟩ : ∃ α' : ∀ ℓ : Fin 1, hid ℓ → ℝ, α' 0 = α :=
    ⟨fun ℓ => Fin.cases α (fun l => l.elim0) ℓ, rfl⟩
  obtain ⟨β', hβ'⟩ : ∃ β' : ∀ ℓ : Fin 1, hid ℓ → ℝ, β' 0 = lam :=
    ⟨fun ℓ => Fin.cases lam (fun l => l.elim0) ℓ, rfl⟩
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at hW'
  refine ⟨Y, c, α', β', hYa, Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_⟩
  · show η.E = θ.E * Y + c • θ.E + 0 + 0
    rw [hEY, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, add_zero, add_zero]
  · obtain rfl := Subsingleton.elim ℓ 0
    ext k j
    rcases j with i | i
    · have h1 : R' k (Sum.inl i) = lam i * θ.read 0 k (Sum.inl i) := congrFun (hlam i).1 k
      have h2 : η.read 0 k (Sum.inl i) + (Y * θ.read 0) k (Sum.inl i) = R' k (Sum.inl i) :=
        congrFun (congrFun hR' k) (Sum.inl i)
      show η.read 0 k (Sum.inl i)
        = -((Y * θ.read 0) k (Sum.inl i)) + 0 + 0 + β' 0 i * θ.read 0 k (Sum.inl i)
      rw [hβ']
      linear_combination h2 + h1
    · have h1 : R' k (Sum.inr i) = -(α i) * θ.read 0 k (Sum.inr i) :=
        congrFun (hlam i).2.2.1 k
      have h2 : η.read 0 k (Sum.inr i) + (Y * θ.read 0) k (Sum.inr i) = R' k (Sum.inr i) :=
        congrFun (congrFun hR' k) (Sum.inr i)
      show η.read 0 k (Sum.inr i)
        = -((Y * θ.read 0) k (Sum.inr i)) + 0 + -(α' 0 i) * θ.read 0 k (Sum.inr i) + 0
      rw [hα']
      linear_combination h2 + h1
  · obtain rfl := Subsingleton.elim ℓ 0
    ext i k
    have h1 : W' i k = (α i - lam i) * θ.write 0 i k := congrFun (hlam i).2.2.2.2 k
    have h2 : η.write 0 i k - ((θ.write 0 * Y) i k + c * θ.write 0 i k) = W' i k :=
      congrFun (congrFun hW' i) k
    show η.write 0 i k = (θ.write 0 * Y) i k + c * θ.write 0 i k + α' 0 i * θ.write 0 i k
      + -(((1 : ℕ) : ℝ) * β' 0 i) * θ.write 0 i k
    rw [hα', hβ', Nat.cast_one]
    linear_combination h2 + h1
  · show η.D = -(Y * θ.D) + 0 + 0 + 0
    rw [hDY, add_zero, add_zero, add_zero]

/-! ### Helpers: the directions of the symmetries, and differentiability at the inputs -/

/-- Helper: `c ↦ scaleDir θ (fun _ => c)` (one scale shared by `h_0` and `h_1`) is linear. -/
private noncomputable def scaleLin_rgz
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    ℝ →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut where
  toFun c := scaleDir θ (fun _ => c)
  map_add' a b := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.add_E, Params.add_read, Params.add_write, Params.add_D,
        add_smul, add_zero]
  map_smul' a b := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        smul_eq_mul, mul_smul, smul_zero, RingHom.id_apply]

/-- Helper: `α ↦ rescaleDir θ α` is linear (a copy of the private `rescaleDirLin_rglu`). -/
private noncomputable def rescaleDirLin_rgz
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    (∀ ℓ : Fin 1, hid ℓ → ℝ) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut where
  toFun := rescaleDir θ
  map_add' α β := by
    apply Params.ext'
    · exact (add_zero 0).symm
    · intro ℓ
      ext k j
      rcases j with i | i
      · exact (add_zero 0).symm
      · show -((α + β) ℓ i) * θ.read ℓ k (Sum.inr i)
          = -(α ℓ i) * θ.read ℓ k (Sum.inr i) + -(β ℓ i) * θ.read ℓ k (Sum.inr i)
        rw [Pi.add_apply, Pi.add_apply]
        ring
    · intro ℓ
      ext i k
      show (α + β) ℓ i * θ.write ℓ i k = α ℓ i * θ.write ℓ i k + β ℓ i * θ.write ℓ i k
      rw [Pi.add_apply, Pi.add_apply]
      ring
    · exact (add_zero 0).symm
  map_smul' c α := by
    apply Params.ext'
    · exact (smul_zero c).symm
    · intro ℓ
      ext k j
      rcases j with i | i
      · exact (smul_zero c).symm
      · show -((c • α) ℓ i) * θ.read ℓ k (Sum.inr i) = c * (-(α ℓ i) * θ.read ℓ k (Sum.inr i))
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
        ring
    · intro ℓ
      ext i k
      show (c • α) ℓ i * θ.write ℓ i k = c * (α ℓ i * θ.write ℓ i k)
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · exact (smul_zero c).symm

/-- Helper: `β ↦ rescaleDirGate 1 θ β` is linear (a copy of the private
`rescaleDirGateLin_rglu`). -/
private noncomputable def rescaleDirGateLin_rgz
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    (∀ ℓ : Fin 1, hid ℓ → ℝ) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut where
  toFun := rescaleDirGate 1 θ
  map_add' α β := by
    apply Params.ext'
    · exact (add_zero 0).symm
    · intro ℓ
      ext a j
      rcases j with i | i
      · show (α + β) ℓ i * θ.read ℓ a (Sum.inl i)
          = α ℓ i * θ.read ℓ a (Sum.inl i) + β ℓ i * θ.read ℓ a (Sum.inl i)
        rw [Pi.add_apply, Pi.add_apply]
        ring
      · exact (add_zero 0).symm
    · intro ℓ
      ext i a
      show -(((1 : ℕ) : ℝ) * (α + β) ℓ i) * θ.write ℓ i a
        = -(((1 : ℕ) : ℝ) * α ℓ i) * θ.write ℓ i a + -(((1 : ℕ) : ℝ) * β ℓ i) * θ.write ℓ i a
      rw [Pi.add_apply, Pi.add_apply]
      ring
    · exact (add_zero 0).symm
  map_smul' c α := by
    apply Params.ext'
    · exact (smul_zero c).symm
    · intro ℓ
      ext a j
      rcases j with i | i
      · show (c • α) ℓ i * θ.read ℓ a (Sum.inl i) = c * (α ℓ i * θ.read ℓ a (Sum.inl i))
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · exact (smul_zero c).symm
    · intro ℓ
      ext i a
      show -(((1 : ℕ) : ℝ) * (c • α) ℓ i) * θ.write ℓ i a
        = c * (-(((1 : ℕ) : ℝ) * α ℓ i) * θ.write ℓ i a)
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · exact (smul_zero c).symm

/-- Helper: the directions of one rotation and one scaling of both hidden states and of the two
rescalings, `((Y, c), (α, β)) ↦ cobDir θ (Y, Y) + scaleDir θ (c, c) + rescaleDir θ α
+ rescaleDirGate 1 θ β` with `Y` antisymmetric, as a linear map. -/
private noncomputable def dirLin_rgz
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    ((antisymmetric d × ℝ) × ((∀ ℓ : Fin 1, hid ℓ → ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ))) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut :=
  (((cobDirLin θ).comp (LinearMap.pi fun _ => (antisymmetric d).subtype)).coprod
    (scaleLin_rgz θ)).coprod ((rescaleDirLin_rgz θ).coprod (rescaleDirGateLin_rgz θ))

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: these directions span a space of dimension at most `(d(d-1)/2 + 1) + 2 s`. -/
private theorem finrank_range_dirLin_le_rgz
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    Module.finrank ℝ (LinearMap.range (dirLin_rgz θ))
      ≤ (Fintype.card d * (Fintype.card d - 1) / 2 + 1) + 2 * Fintype.card (hid 0) := by
  refine (LinearMap.finrank_range_le _).trans (le_of_eq ?_)
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, finrank_antisymmetric,
    Module.finrank_self, Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]
  ring

/-- Helper: the directions that are flat at every input of
`residualZeroDomain ∩ noKinkGateRMS θ` are among them. -/
private theorem flatOn_le_range_rgz
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d) (hturn : TurnsActiveRowsGated θ)
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v]) :
    flatOn (Arch.gated relu (rmsNorm 0) hid) 1 θ
        (residualZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ ∩ noKinkGateRMS θ)
      ≤ LinearMap.range (dirLin_rgz θ) := by
  intro η hη
  obtain ⟨Y, c, α, β, hY, rfl⟩ :=
    flatOn_noKinkGate_le_reglu_residual_rmsNorm_zero θ hθ hd hturn hw η hη
  exact ⟨((⟨Y, hY⟩, c), (α, β)), (add_assoc _ _ _).symm⟩

/-- **Theorem B.1 (iv) of the skips paper, the residual network, for a ReGLU block, at one
parameter:** under the conditions of `flatOn_noKinkGate_le_reglu_residual_rmsNorm_zero`,
`funDim = P − (d(d−1)/2 + 1) − s`, with `s` twice the number of hidden units. -/
theorem funDim_reglu_oneBlock_residual_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d) (hturn : TurnsActiveRowsGated θ)
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v]) :
    funDim (Arch.gated relu (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- `≤`: the rotation and the scaling of both hidden states and the two rescalings of the hidden
  -- units are flat and independent
  have hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0 := by
    intro ℓ i
    obtain rfl := Subsingleton.elim ℓ 0
    exact hθ.gated.value_ne_zero i
  have hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0 := by
    intro ℓ i
    obtain rfl := Subsingleton.elim ℓ 0
    exact hθ.gated.gate_ne_zero i
  have hle := funDim_add_le_residual_gated_gate_rmsNorm_zero relu_homogeneous θ
    hθ.gated.rank_E hv hg
  rw [Fin.sum_univ_one] at hle
  -- `≥`: `K(θ)` lies in the directions flat on `residualZeroDomain ∩ noKinkGateRMS θ`, which are
  -- of this form
  have hflat : flat (Arch.gated relu (rmsNorm 0) hid) 1 θ ≤ LinearMap.range (dirLin_rgz θ) :=
    (flat_le_flatOn θ _).trans (flatOn_le_range_rgz θ hθ hd hturn hw)
  -- `fd(θ) + dim K(θ) = P`
  have h := funDim_add_finrank_flat' (S := 1) θ
  have hmono := Submodule.finrank_mono hflat
  have hdim := finrank_range_dirLin_le_rgz θ
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at hle hdim ⊢
  omega

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the function of one residual ReGLU block under pre-RMSNorm with `ε = 0`,
`F_θ(x) = N_0(x E + f(N_0(x E) W_read) W_write) D`. -/
private theorem eval_eq_rgz
    (θ' : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (x : Matrix T dIn ℝ) :
    eval (Arch.gated relu (rmsNorm 0) hid) 1 θ' x
      = rmsNorm 0 (x * θ'.E + (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0
          (rmsNorm 0 (x * θ'.E) * θ'.read 0) * θ'.write 0) * θ'.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero]
  simp only [Pi.one_apply, Matrix.mul_one]

/-- Helper: the product of two matrix-valued maps differentiable at `y` is differentiable at `y`
(a copy of the private `differentiableAt_matMul_rzr`). -/
private theorem differentiableAt_matMul_rgz {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] {f : E → Matrix m n ℝ}
    {g : E → Matrix n p ℝ} {y : E} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) : DifferentiableAt ℝ (fun y => f y * g y) y := by
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.differentiableAt.comp y hf).clm_apply hg

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: a linear map of the parameters is differentiable. -/
private theorem differentiable_lin_rgz {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut →ₗ[ℝ] F) :
    Differentiable ℝ l := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).differentiable

omit [Nonempty T] in
/-- Helper: at an input of `residualZeroDomain ∩ noKinkGateRMS θ` the output is differentiable in
the parameters: no row of `x E` and of `h_1` vanishes, so `N_0` is differentiable at both, and no
gate of the pre-activations `N_0(x E) W_read` is at its kink, as `N_0` scales the rows of `x E` by
positive numbers. -/
private theorem differentiableAt_eval_rgz
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (x : Matrix T dIn ℝ)
    (hx : x ∈ residualZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ ∩ noKinkGateRMS θ) :
    DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut =>
        eval (Arch.gated relu (rmsNorm 0) hid) 1 θ' x) θ := by
  obtain ⟨⟨hx0, hx1⟩, hxk⟩ := hx
  have e : (fun θ' : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut =>
      eval (Arch.gated relu (rmsNorm 0) hid) 1 θ' x) = fun θ' => rmsNorm 0 (x * θ'.E
        + (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0
          (rmsNorm 0 (x * θ'.E) * θ'.read 0) * θ'.write 0) * θ'.D :=
    funext fun θ' => eval_eq_rgz θ' x
  rw [e]
  -- the components of the parameters are linear, hence differentiable
  have hE : Differentiable ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut => θ'.E) := by
    have h := differentiable_lin_rgz (Params.linE
      (A := Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) (dIn := dIn) (dOut := dOut))
    exact h
  have hR : Differentiable ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut =>
        θ'.read 0) := by
    have h := differentiable_lin_rgz (Params.linRead
      (A := Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) (dIn := dIn) (dOut := dOut) 0)
    exact h
  have hW : Differentiable ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut =>
        θ'.write 0) := by
    have h := differentiable_lin_rgz (Params.linWrite
      (A := Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) (dIn := dIn) (dOut := dOut) 0)
    exact h
  have hD : Differentiable ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut => θ'.D) := by
    have h := differentiable_lin_rgz (Params.linD
      (A := Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) (dIn := dIn) (dOut := dOut))
    exact h
  -- `x E`, `N_0(x E)` and the pre-activations `N_0(x E) W_read`
  have hxE : DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut =>
        x * θ'.E) θ :=
    differentiableAt_matMul_rgz (differentiableAt_const x) (hE θ)
  have hN0 : DifferentiableAt ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) :=
    (analyticAt_rmsNorm_zero _ hx0).differentiableAt
  have hn : DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut =>
        rmsNorm 0 (x * θ'.E)) θ :=
    DifferentiableAt.comp (f := fun θ' : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0)
      hid) dIn dOut => x * θ'.E) θ hN0 hxE
  have hpre : DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut =>
        rmsNorm 0 (x * θ'.E) * θ'.read 0) θ :=
    differentiableAt_matMul_rgz hn (hR θ)
  -- at `θ` no gate of them is at its kink, so the block map is differentiable there
  have hP : ∀ t i, (rmsNorm 0 (x * θ.E) * θ.read 0) t (Sum.inl i) ≠ 0 := by
    intro t i
    rw [rmsNorm_mul_apply_rgz]
    exact mul_ne_zero (inv_sqrt_pos_rgz (hx0 t)).ne' (hxk t i)
  have hact : DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut =>
        (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0
          (rmsNorm 0 (x * θ'.E) * θ'.read 0)) θ := by
    have h := (contDiffAt_f_rgz (d := d) _ hP).differentiableAt_one.comp θ hpre
    exact h
  -- `h_1 = x E + f(N_0(x E) W_read) W_write`, no row of which vanishes, and the output `N_0(h_1) D`
  have hh : DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut =>
        x * θ'.E + (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0
          (rmsNorm 0 (x * θ'.E) * θ'.read 0) * θ'.write 0) θ :=
    hxE.add (differentiableAt_matMul_rgz hact (hW θ))
  have hN1 : DifferentiableAt ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ)
      (x * θ.E + (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0
        (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) :=
    (analyticAt_rmsNorm_zero _ hx1).differentiableAt
  have hout : DifferentiableAt ℝ
      (fun θ' : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut =>
        rmsNorm 0 (x * θ'.E + (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0
          (rmsNorm 0 (x * θ'.E) * θ'.read 0) * θ'.write 0)) θ :=
    DifferentiableAt.comp (f := fun θ' : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0)
      hid) dIn dOut => x * θ'.E + (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid).f 0
        (rmsNorm 0 (x * θ'.E) * θ'.read 0) * θ'.write 0) θ hN1 hh
  exact differentiableAt_matMul_rgz hout (hD θ)

/-- **Theorem B.1 (iv) of the skips paper, the residual network, in the paper's own sense, for a
ReGLU block, at one parameter:** under the same conditions, a finite batch of inputs at which no
normalized row vanishes and no gate sits at its kink, on which the Jacobian has the rank
`P − (d(d−1)/2 + 1) − s`. -/
theorem exists_jacobianRank_reglu_oneBlock_residual_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d) (hturn : TurnsActiveRowsGated θ)
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧
      LinearIndependent ℝ ![v, gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v]) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ residualZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ ∩ noKinkGateRMS θ) ∧
      jacobianRank (Arch.gated relu (rmsNorm 0) hid) 1 X θ
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  -- a batch of inputs of `U = residualZeroDomain ∩ noKinkGateRMS θ`, where the network is
  -- differentiable in `θ`, with the rank `P - dim K_U(θ)`
  obtain ⟨n, X, hX, h⟩ := exists_jacobianRank_add_finrank_flatOn (S := 1) θ
    (residualZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ ∩ noKinkGateRMS θ)
    (fun x hx => differentiableAt_eval_rgz θ x hx)
  -- the sandwich: `dim K(θ) ≤ dim K_U(θ) ≤ d(d-1)/2 + 1 + 2 s = dim K(θ)`
  have hfd := funDim_reglu_oneBlock_residual_rmsNorm_zero θ hθ hd hturn hw
  have h' := funDim_add_finrank_flat' (S := 1) θ
  have h1 := Submodule.finrank_mono (flat_le_flatOn (S := 1) θ
    (residualZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ ∩ noKinkGateRMS θ))
  have h2 := Submodule.finrank_mono (flatOn_le_range_rgz θ hθ hd hturn hw)
  have h3 := finrank_range_dirLin_le_rgz θ
  refine ⟨n, X, hX, ?_⟩
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at hfd h3 ⊢
  omega

end Skips
