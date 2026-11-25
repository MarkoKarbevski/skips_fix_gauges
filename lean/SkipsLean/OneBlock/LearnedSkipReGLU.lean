import SkipsLean.OneBlock.LearnedSkipGain
import SkipsLean.OneBlock.ResidualRMSReGLU
import SkipsLean.Symmetry.InsideBlocksKinds
import SkipsLean.Dimension.UpperBoundTransformerRescale
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-!
# One ReGLU block with a full learned skip under pre-RMSNorm

Paper (skips paper): Theorem 4.6 (ii): "A learned skip raises it by exactly
`d_model (d_model + 1)/2` more than an identity skip." Theorem B.1 (iii): "Let the network be
pre-RMSNorm without biases, with a learned skip `A`, full or upper triangular. For generic
parameters and `ε > 0`, its functional dimension exceeds that of the residual network of part (ii)
by exactly `d_model (d_model + 1)/2`, and it satisfies the equality condition." Its proof, Step 4,
after equation (17), `∂_ψ B(n) = q(n) 𝐃B(n) n`: "For ReLU, ReLU² and ReGLU, `B(λn) = λ^k B(n)` for
`λ > 0`, with `k = 1` or `2`, so the right side of (17) is `k q(n) B(n)`. Replacing `n` by `λn`
with `0 < λ ≤ 1` multiplies the left side by `λ^k` and the right side by `λ^{k+2}`, so both vanish,
and `q = 0` wherever `B ≠ 0`." For ReGLU `k = 2` and `s = 2 d_hidden`: one rescaling of the gate
and one of the value for each hidden unit.

Stated here, as in `OneBlock/ResidualRMSReGLU.lean` (the same block with the identity skip) and
`OneBlock/LearnedSkipRescale.lean` (ReLU and ReLU² blocks with a learned skip), for a block of any
width with at least one hidden unit:

* Step 4: `NoSymmetricPart` at the inputs `noKinkGateRMS θ` with no gate at its kink, under the
  conditions `OneBlockGenericReGLURMS`.
* At one parameter, with an invertible skip: the functional dimension is that of the residual
  network at the same weights plus `d (d + 1)/2`; it is `P + d² − d (d − 1) − 2 d_hidden` (the
  equality condition: `P + d²` parameters, symmetries of dimension `d (d − 1) + 2 d_hidden`); and a
  batch of inputs of `noKinkGateRMS θ` has a Jacobian of this rank.
* For `d_in, d_out ≥ d ≥ 2`: the same at almost every `(θ, A)`.

The route is that of `OneBlock/LearnedSkipRescale.lean`, with Lemma B.3 for ReGLU as in
`flatOn_noKinkGateRMS_le_reglu_residual_rmsNorm` and the residual value
`funDim_reglu_oneBlock_residual_rmsNorm`. Numeric check:
`learned_skip_relu_attention_check_2026-11-24.py`. The upper triangular skip:
`OneBlock/LearnedSkipTriangularRescale.lean`. `ε = 0`: `OneBlock/LearnedSkipRMSZeroReGLU.lean`,
`OneBlock/LearnedSkipRMSZeroReGLUGeneric.lean`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)] {ε : ℝ}

/-! ### Helpers: the block map near pre-activations with no gate at its kink (copies of the
private helpers of `OneBlock/ResidualRMSReGLU.lean`) -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `hasDerivAt_affine_rg` of `ResidualRMSGated.lean`): `τ ↦ a + τ b` has the
derivative `b` at `0`. -/
private theorem hasDerivAt_affine_lsu (a b : ℝ) : HasDerivAt (fun τ : ℝ => a + τ * b) b 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const b).const_add a
  rw [one_mul] at h
  exact h

/-- Helper: `relu` is `C¹` away from its kink (it is `0` or the identity near `z ≠ 0`). -/
private theorem contDiffAt_relu_lsu {z : ℝ} (hz : z ≠ 0) : ContDiffAt ℝ 1 relu z := by
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
private theorem isOpen_gateSet_lsu :
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
private theorem contDiffAt_f_lsu (M : Matrix T (hid 0 ⊕ hid 0) ℝ)
    (hM : ∀ t i, M t (Sum.inl i) ≠ 0) :
    ContDiffAt ℝ 1 ((Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0) M := by
  refine contDiffAt_pi.2 fun t => contDiffAt_pi.2 fun i => ?_
  have he : ∀ j, ContDiffAt ℝ 1 (fun N : Matrix T (hid 0 ⊕ hid 0) ℝ => N t j) M := fun j =>
    (contDiff_apply_apply ℝ t j).contDiffAt
  have h := ((contDiffAt_relu_lsu (hM t i)).comp M (he (Sum.inl i))).mul (he (Sum.inr i))
  exact h

omit [Nonempty T] [DecidableEq d] in
/-- Helper: the map of the ReGLU block is `C¹` on the pre-activations with no gate at its
kink. -/
private theorem contDiffOn_f_lsu :
    ContDiffOn ℝ 1 ((Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0)
      {M : Matrix T (hid 0 ⊕ hid 0) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0} := by
  intro M hM
  exact (contDiffAt_f_lsu M hM).contDiffWithinAt

omit [Nonempty T] [DecidableEq d] in
/-- Helper (as `fderiv_f_gated_apply_rg` of `ResidualRMSGated.lean`, at a pre-activation with no
gate at its kink): the derivative of the map of the ReGLU block at `M` along `N`, entry `(t, i)`:
`1[M_{t, g i} > 0] N_{t, g i} M_{t, v i} + relu(M_{t, g i}) N_{t, v i}`. -/
private theorem fderiv_f_apply_lsu (M N : Matrix T (hid 0 ⊕ hid 0) ℝ)
    (hM : ∀ t i, M t (Sum.inl i) ≠ 0) (t : T) (i : hid 0) :
    fderiv ℝ ((Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0) M N t i
      = reluDeriv (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + relu (M t (Sum.inl i)) * N t (Sum.inr i) := by
  have hd := (contDiffAt_f_lsu (d := d) (ε := ε) M hM).differentiableAt_one
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
    have hu := hasDerivAt_affine_lsu (M t (Sum.inl i)) (N t (Sum.inl i))
    have hw := hasDerivAt_affine_lsu (M t (Sum.inr i)) (N t (Sum.inr i))
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
private noncomputable def unitSum_lsu {q : Type*} [Fintype q] (R R' : Matrix d (q ⊕ q) ℝ)
    (W W' : Matrix q d ℝ) (u : d → ℝ) (k : d) : ℝ :=
  ∑ i, (relu (u ⬝ᵥ Rᵀ (Sum.inl i)) * (u ⬝ᵥ Rᵀ (Sum.inr i)) * W' i k
    + reluDeriv (u ⬝ᵥ Rᵀ (Sum.inl i)) * (u ⬝ᵥ R'ᵀ (Sum.inl i)) * (u ⬝ᵥ Rᵀ (Sum.inr i)) * W i k
    + relu (u ⬝ᵥ Rᵀ (Sum.inl i)) * (u ⬝ᵥ R'ᵀ (Sum.inr i)) * W i k)

omit [Nonempty T] [DecidableEq d] in
/-- Helper: the derivative of `n ↦ f(n R) W` along `R'`, `W'`, entry `(t, k)`, is `unitSum_lsu`
at the row `n_t`, when no gate of `n R` sits at its kink. -/
private theorem fderiv_add_apply_lsu (n : Matrix T d ℝ) (R R' : Matrix d (hid 0 ⊕ hid 0) ℝ)
    (W W' : Matrix (hid 0) d ℝ) (hn : ∀ t i, (n * R) t (Sum.inl i) ≠ 0) (t : T) (k : d) :
    (fderiv ℝ ((Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0) (n * R) (n * R') * W
        + (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0 (n * R) * W') t k
      = unitSum_lsu R R' W W' (n t) k := by
  rw [unitSum_lsu, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_apply_lsu _ _ hn]
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
private theorem relu_mul_lsu {lam : ℝ} (hlam : 0 < lam) (z : ℝ) :
    relu (lam * z) = lam * relu z := by
  rw [relu_homogeneous lam z hlam, pow_one]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `relu' (λ z) = relu' z` for `λ > 0`. -/
private theorem reluDeriv_mul_lsu {lam : ℝ} (hlam : 0 < lam) (z : ℝ) :
    reluDeriv (lam * z) = reluDeriv z := by
  simp only [reluDeriv, mul_pos_iff_of_pos_left hlam]

omit [DecidableEq d] in
/-- Helper: `unitSum_lsu` is homogeneous of degree `2` in the row, for positive factors. -/
private theorem unitSum_smul_lsu {q : Type*} [Fintype q] (R R' : Matrix d (q ⊕ q) ℝ)
    (W W' : Matrix q d ℝ) {lam : ℝ} (hlam : 0 < lam) (u : d → ℝ) (k : d) :
    unitSum_lsu R R' W W' (lam • u) k = lam ^ 2 * unitSum_lsu R R' W W' u k := by
  simp only [unitSum_lsu, smul_dotProduct, smul_eq_mul, Finset.mul_sum, relu_mul_lsu hlam,
    reluDeriv_mul_lsu hlam]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [DecidableEq d] in
/-- Helper: the factor of RMSNorm on one row is positive for `ε > 0`. -/
private theorem scale_pos_lsu (hε : 0 < ε) (v : d → ℝ) :
    0 < (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹ := by
  apply inv_pos.2
  apply Real.sqrt_pos.2
  have h1 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun k _ => mul_self_nonneg _
  have h2 : 0 ≤ (v ⬝ᵥ v) / (Fintype.card d : ℝ) := div_nonneg h1 (Nat.cast_nonneg _)
  linarith

/-- Helper: a finite family of nonzero vectors has a vector with no zero dot product with them (a
real vector space is not a finite union of proper subspaces). -/
private theorem exists_dotProduct_ne_zero_lsu {n q : Type*} [Fintype n] [Finite q]
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
private theorem exists_input_lsu
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericGatedRMS θ) :
    ∃ w : dIn → ℝ, (Matrix.of fun _ : T => w) * θ.E * θ.read 0
      ∈ {M : Matrix T (hid 0 ⊕ hid 0) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0} := by
  obtain ⟨v, hv⟩ := exists_dotProduct_ne_zero_lsu (fun i => (θ.read 0)ᵀ (Sum.inl i))
    hθ.gate_ne_zero
  obtain ⟨w, hw⟩ := (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hθ.rank_E) v
  refine ⟨w, fun t i => ?_⟩
  have h : ((Matrix.of fun _ : T => w) * θ.E * θ.read 0) t (Sum.inl i)
      = (w ᵥ* θ.E) ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) := rfl
  have hw' : w ᵥ* θ.E = v := hw
  rw [h, hw']
  exact hv i

/-! ### Helpers: Step 4, equation (17) at the rows with no gate at its kink -/

/-- Helper: the map of the block at one row `u`, entry `k`:
`B(u)_k = ∑_i relu(u c_i) (u e_i) W_{i k}`. -/
private noncomputable def blockRow_lsu {q : Type*} [Fintype q] (R : Matrix d (q ⊕ q) ℝ)
    (W : Matrix q d ℝ) (u : d → ℝ) (k : d) : ℝ :=
  ∑ i, relu (u ⬝ᵥ Rᵀ (Sum.inl i)) * (u ⬝ᵥ Rᵀ (Sum.inr i)) * W i k

/-- Helper: the quadratic form `q(u) = u X uᵀ / d` of `tangentRMS`. -/
private noncomputable def qv_lsu (X : Matrix d d ℝ) (u : d → ℝ) : ℝ :=
  ((u ᵥ* X) ⬝ᵥ u) / (Fintype.card d : ℝ)

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `relu_eq_reluDeriv_mul` of `OneBlock/UnitsReGLU.lean`):
`relu z = relu'(z) z`. -/
private theorem relu_eq_reluDeriv_mul_lsu (z : ℝ) : relu z = reluDeriv z * z := by
  unfold relu reluDeriv
  split_ifs with hz
  · rw [one_mul, max_eq_left hz.le]
  · rw [zero_mul, max_eq_right (not_lt.1 hz)]

omit [DecidableEq d] in
/-- Helper: `B` is homogeneous of degree `2` in the row, for positive factors. -/
private theorem blockRow_smul_lsu {q : Type*} [Fintype q] (R : Matrix d (q ⊕ q) ℝ)
    (W : Matrix q d ℝ) {lam : ℝ} (hlam : 0 < lam) (u : d → ℝ) (k : d) :
    blockRow_lsu R W (lam • u) k = lam ^ 2 * blockRow_lsu R W u k := by
  simp only [blockRow_lsu, smul_dotProduct, smul_eq_mul, Finset.mul_sum, relu_mul_lsu hlam]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [DecidableEq d] in
/-- Helper: `q` is homogeneous of degree `2`. -/
private theorem qv_smul_lsu (X : Matrix d d ℝ) (lam : ℝ) (u : d → ℝ) :
    qv_lsu X (lam • u) = lam ^ 2 * qv_lsu X u := by
  simp only [qv_lsu, Matrix.smul_vecMul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

omit [DecidableEq d] in
/-- Helper: `q = 0` for `X = 0`. -/
private theorem qv_zero_lsu (u : d → ℝ) : qv_lsu (0 : Matrix d d ℝ) u = 0 := by
  simp only [qv_lsu, Matrix.vecMul_zero, zero_dotProduct, zero_div]

omit [DecidableEq d] in
/-- Helper: moving the read along `s R` adds `2 s B(u)` to the derivative of the block (Euler's
identity for the block, homogeneous of degree `2`: `relu'(z) z = relu z`). -/
private theorem unitSum_add_smul_lsu {q : Type*} [Fintype q] (R R' : Matrix d (q ⊕ q) ℝ)
    (W W' : Matrix q d ℝ) (s : ℝ) (u : d → ℝ) (k : d) :
    unitSum_lsu R (R' + s • R) W W' u k
      = unitSum_lsu R R' W W' u k + 2 * s * blockRow_lsu R W u k := by
  simp only [unitSum_lsu, blockRow_lsu, Matrix.transpose_add, Matrix.transpose_smul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (R'ᵀ + s • Rᵀ) (Sum.inl i) = R'ᵀ (Sum.inl i) + s • Rᵀ (Sum.inl i) := rfl
  have h2 : (R'ᵀ + s • Rᵀ) (Sum.inr i) = R'ᵀ (Sum.inr i) + s • Rᵀ (Sum.inr i) := rfl
  rw [h1, h2, dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, relu_eq_reluDeriv_mul_lsu (u ⬝ᵥ Rᵀ (Sum.inl i))]
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: at a hidden state with all rows equal to `v`, the change of `n` along `tangentRMS X n`
and of the read along `ψ_r` is `n` times the read change `X R + ψ_r − q(v) R`. -/
private theorem tangent_rows_lsu {m : Type*} (X : Matrix d d ℝ) (n : Matrix T d ℝ) (v : d → ℝ)
    (hn : ∀ t, n t = v) (R ψr : Matrix d m ℝ) :
    tangentRMS X n * R + n * ψr = n * (X * R + ψr + (-(qv_lsu X v)) • R) := by
  obtain rfl : n = Matrix.of fun _ => v := by
    ext t j
    exact congrFun (hn t) j
  -- one row: `(v X − q(v) v) R + v ψ_r = v (X R + ψ_r − q(v) R)`
  have key : (v ᵥ* X - qv_lsu X v • v) ᵥ* R + v ᵥ* ψr
      = v ᵥ* (X * R + ψr + (-(qv_lsu X v)) • R) := by
    rw [Matrix.vecMul_add, Matrix.vecMul_add, Matrix.vecMul_smul, ← Matrix.vecMul_vecMul,
      Matrix.sub_vecMul, Matrix.smul_vecMul, neg_smul]
    abel
  ext t j
  exact congrFun key j

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `tangentRMS 0 n = 0`. -/
private theorem tangentRMS_zero_lsu (n : Matrix T d ℝ) : tangentRMS (0 : Matrix d d ℝ) n = 0 := by
  ext t j
  show ((n * (0 : Matrix d d ℝ)) t
    - (((n * (0 : Matrix d d ℝ)) t ⬝ᵥ n t) / (Fintype.card d : ℝ)) • n t) j = 0
  rw [Matrix.mul_zero]
  show ((0 : d → ℝ) - (((0 : d → ℝ) ⬝ᵥ n t) / (Fintype.card d : ℝ)) • n t) j = 0
  rw [zero_dotProduct, zero_div, zero_smul, sub_zero]
  rfl

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (equation (17) at one row): if equation (17) holds at the inputs of `noKinkGateRMS θ`,
then at every row `u` with no gate at its kink the derivative of the block along
`ψ' = (ψ_r + X W_read, ψ_w)` is `2 q(u) B(u)` times the factor `(‖u‖²/d + ε)⁻¹`: take the input `x`
with all rows `w`, `w E = u`; `N_ε(x E)` has all rows `c u`, `c > 0`; the direction is `n` times
`X W_read + ψ_r − q(c u) W_read`; and every term is homogeneous of degree `2` in the row. -/
private theorem key_lsu [Nonempty T] (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (X : Matrix d d ℝ)
    (ψr : Matrix d (hid 0 ⊕ hid 0) ℝ) (ψw : Matrix (hid 0) d ℝ)
    (h : ∀ x ∈ noKinkGateRMS θ,
      fderiv ℝ ((Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0)
          (rmsNorm ε (x * θ.E) * θ.read 0)
          (tangentRMS X (rmsNorm ε (x * θ.E)) * θ.read 0 + rmsNorm ε (x * θ.E) * ψr)
          * θ.write 0
        + (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0
          (rmsNorm ε (x * θ.E) * θ.read 0) * ψw = 0)
    (u : d → ℝ) (hu : ∀ i, u ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0) (k : d) :
    unitSum_lsu (θ.read 0) (X * θ.read 0 + ψr) (θ.write 0) ψw u k
      = 2 * ((u ⬝ᵥ u / (Fintype.card d : ℝ) + ε)⁻¹ * qv_lsu X u)
        * blockRow_lsu (θ.read 0) (θ.write 0) u k := by
  -- the input `x` with all rows `w`, `w E = u`
  obtain ⟨w, hw⟩ := (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hE) u
  have hw' : w ᵥ* θ.E = u := hw
  have hxE : (Matrix.of fun _ : T => w) * θ.E = Matrix.of fun _ : T => u := by
    ext t l
    rw [← hw']
    rfl
  have hx : (Matrix.of fun _ : T => w) ∈ noKinkGateRMS θ := by
    intro t i
    rw [hxE]
    exact hu i
  have h1 := h _ hx
  rw [hxE] at h1
  -- the rows of `N_ε(x E)` are `c u`, `c > 0`
  obtain ⟨c, hc, hrow, hc2⟩ : ∃ c : ℝ, 0 < c ∧
      (∀ t, rmsNorm ε (Matrix.of fun _ : T => u) t = c • u) ∧
      c ^ 2 = (u ⬝ᵥ u / (Fintype.card d : ℝ) + ε)⁻¹ := by
    refine ⟨(Real.sqrt ((u ⬝ᵥ u) / (Fintype.card d : ℝ) + ε))⁻¹, scale_pos_lsu hε u,
      fun t => rfl, ?_⟩
    have h0 : 0 ≤ u ⬝ᵥ u / (Fintype.card d : ℝ) + ε := by
      have h2 : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun k _ => mul_self_nonneg _
      have h3 : 0 ≤ (u ⬝ᵥ u) / (Fintype.card d : ℝ) := div_nonneg h2 (Nat.cast_nonneg _)
      linarith
    rw [inv_pow, Real.sq_sqrt h0]
  rw [tangent_rows_lsu X _ (c • u) hrow] at h1
  have hn : ∀ t i,
      (rmsNorm ε (Matrix.of fun _ : T => u) * θ.read 0) t (Sum.inl i) ≠ 0 := by
    intro t i
    show rmsNorm ε (Matrix.of fun _ : T => u) t ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0
    rw [hrow, smul_dotProduct, smul_eq_mul]
    exact mul_ne_zero hc.ne' (hu i)
  -- entry `(t, k)`: `c² ∂_{ψ'} B(u) − 2 c² q(u) c² B(u) = 0`
  have h2 := congrFun (congrFun h1 (Classical.arbitrary T)) k
  rw [fderiv_add_apply_lsu _ _ _ _ _ hn, hrow, unitSum_add_smul_lsu, unitSum_smul_lsu _ _ _ _ hc,
    blockRow_smul_lsu _ _ hc, qv_smul_lsu, Matrix.zero_apply] at h2
  rw [← hc2]
  have h3 : c ^ 2 * (unitSum_lsu (θ.read 0) (X * θ.read 0 + ψr) (θ.write 0) ψw u k
      - 2 * (c ^ 2 * qv_lsu X u) * blockRow_lsu (θ.read 0) (θ.write 0) u k) = 0 := by
    linear_combination h2
  have h4 := (mul_eq_zero.1 h3).resolve_left (pow_ne_zero 2 hc.ne')
  linear_combination h4

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (Step 4, the homogeneity argument): under equation (17) at the inputs of
`noKinkGateRMS θ`, `q(u) B(u) = 0` at every row `u` with no gate at its kink. The identity of
`key_lsu` at `u` and at `2 u` gives `2 q(u) B(u) ((‖u‖²/d + ε)⁻¹ − 4 (4‖u‖²/d + ε)⁻¹) = 0`, and the
factor is `−3 ε` times a positive number. -/
private theorem qB_zero_lsu [Nonempty T] (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (X : Matrix d d ℝ)
    (ψr : Matrix d (hid 0 ⊕ hid 0) ℝ) (ψw : Matrix (hid 0) d ℝ)
    (h : ∀ x ∈ noKinkGateRMS θ,
      fderiv ℝ ((Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0)
          (rmsNorm ε (x * θ.E) * θ.read 0)
          (tangentRMS X (rmsNorm ε (x * θ.E)) * θ.read 0 + rmsNorm ε (x * θ.E) * ψr)
          * θ.write 0
        + (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0
          (rmsNorm ε (x * θ.E) * θ.read 0) * ψw = 0)
    (u : d → ℝ) (hu : ∀ i, u ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0) (k : d) :
    qv_lsu X u * blockRow_lsu (θ.read 0) (θ.write 0) u k = 0 := by
  have hu2 : ∀ i, ((2 : ℝ) • u) ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0 := fun i => by
    rw [smul_dotProduct, smul_eq_mul]
    exact mul_ne_zero two_ne_zero (hu i)
  have k1 := key_lsu hε θ hE X ψr ψw h u hu k
  have k2 := key_lsu hε θ hE X ψr ψw h ((2 : ℝ) • u) hu2 k
  rw [unitSum_smul_lsu _ _ _ _ two_pos, qv_smul_lsu, blockRow_smul_lsu _ _ two_pos,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at k2
  -- `a = ‖u‖²/d ≥ 0`, `r₁ = (a + ε)⁻¹`, `r₂ = (4 a + ε)⁻¹`
  have ha : 0 ≤ u ⬝ᵥ u / (Fintype.card d : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun k _ => mul_self_nonneg _) (Nat.cast_nonneg _)
  have e2 : (2 : ℝ) * (2 * (u ⬝ᵥ u)) / (Fintype.card d : ℝ) + ε
      = 4 * (u ⬝ᵥ u / (Fintype.card d : ℝ)) + ε := by ring
  rw [e2] at k2
  generalize u ⬝ᵥ u / (Fintype.card d : ℝ) = a at k1 k2 ha
  have hb1 : 0 < a + ε := by linarith
  have hb2 : 0 < 4 * a + ε := by linarith
  have h1 : (a + ε)⁻¹ * (a + ε) = 1 := inv_mul_cancel₀ hb1.ne'
  have h2 : (4 * a + ε)⁻¹ * (4 * a + ε) = 1 := inv_mul_cancel₀ hb2.ne'
  have hr : (a + ε)⁻¹ - 4 * (4 * a + ε)⁻¹ = -(3 * ε * ((a + ε)⁻¹ * (4 * a + ε)⁻¹)) := by
    linear_combination 4 * (4 * a + ε)⁻¹ * h1 - (a + ε)⁻¹ * h2
  have hne : (a + ε)⁻¹ - 4 * (4 * a + ε)⁻¹ ≠ 0 := by
    rw [hr, neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero three_ne_zero hε.ne')
      (mul_ne_zero (inv_ne_zero hb1.ne') (inv_ne_zero hb2.ne'))
  have h3 : qv_lsu X u * blockRow_lsu (θ.read 0) (θ.write 0) u k
      * ((a + ε)⁻¹ - 4 * (4 * a + ε)⁻¹) = 0 := by
    linear_combination (k2 - 4 * k1) / 8
  exact (mul_eq_zero.1 h3).resolve_right hne

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] in
/-- Helper: `B` is not `0` at every row with no gate at its kink. Otherwise the direction that moves
every write row `a_i` along itself has derivative zero there, and Lemma B.3 for ReGLU makes it a
rescaling of the gate and the value of each unit; its read columns are `0`, so both rescalings are
trivial, and `a_i = 0`, against the nonzero write rows. -/
private theorem exists_blockRow_ne_zero_lsu [Nonempty (hid 0)]
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) :
    ∃ u : d → ℝ, (∀ i, u ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0) ∧
      ∃ k, blockRow_lsu (θ.read 0) (θ.write 0) u k ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, lam, α, hlam⟩ := relu_gated_units_flat
    (fun i => (θ.read 0)ᵀ (Sum.inl i)) 0 (fun i => (θ.read 0)ᵀ (Sum.inr i)) 0
    (fun i => θ.write 0 i) 0 0 0 0 0 0 (fun i => θ.write 0 i)
    (fun i => hθ.gated.row_ne_zero i) (fun i => hθ.gated.gate_ne_zero i)
    (fun i j hij => hθ.gated.gate_not_collinear i j hij) (fun i => hθ.gated.value_ne_zero i)
    (fun i r h => hθ.value_not_gate i r (by have h1 := congrArg Prod.fst h; exact h1)) (by
      intro v hv
      have hv' : ∀ i, v ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0 := fun i => by
        have h := hv i
        simp only [Pi.zero_apply, add_zero] at h
        exact h
      funext k
      have h := hcon v hv' k
      simp only [Matrix.vecMul_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, add_zero, zero_add, dotProduct_zero, mul_zero, zero_mul]
      exact h)
  obtain i := Classical.arbitrary (hid 0)
  have hl : lam i = 0 := by
    have h1 := (hlam i).1
    rw [Pi.zero_apply, eq_comm, smul_eq_zero] at h1
    exact h1.resolve_right (hθ.gated.gate_ne_zero i)
  have ha : α i = 0 := by
    have h1 := (hlam i).2.2.1
    rw [Pi.zero_apply, eq_comm, smul_eq_zero, neg_eq_zero] at h1
    exact h1.resolve_right (hθ.gated.value_ne_zero i)
  have h5 := (hlam i).2.2.2.2
  rw [hl, ha, sub_zero, zero_smul] at h5
  exact hθ.gated.row_ne_zero i h5

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: a symmetric `X` whose quadratic form `u X uᵀ` vanishes on a nonempty open set is `0`:
at `u₀ ± t y` in the set, `0 = q(u₀ + t y) + q(u₀ − t y) − 2 q(u₀) = 2 t² q(y)`, and then
`2 X_{i j} = q(e_i + e_j) − q(e_i) − q(e_j) = 0`. -/
private theorem eq_zero_of_quad_lsu (X : Matrix d d ℝ) (hX : Xᵀ = X) (U : Set (d → ℝ))
    (hU : IsOpen U) (u₀ : d → ℝ) (hu₀ : u₀ ∈ U) (h : ∀ u ∈ U, (u ᵥ* X) ⬝ᵥ u = 0) : X = 0 := by
  -- the quadratic form vanishes everywhere
  have hq : ∀ y : d → ℝ, (y ᵥ* X) ⬝ᵥ y = 0 := by
    intro y
    have hc1 : Continuous fun t : ℝ => u₀ + t • y :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hc2 : Continuous fun t : ℝ => u₀ - t • y :=
      continuous_const.sub (continuous_id.smul continuous_const)
    have e1 : ∀ᶠ t in nhds (0 : ℝ), u₀ + t • y ∈ U :=
      hc1.continuousAt.preimage_mem_nhds (by rw [zero_smul, add_zero]; exact hU.mem_nhds hu₀)
    have e2 : ∀ᶠ t in nhds (0 : ℝ), u₀ - t • y ∈ U :=
      hc2.continuousAt.preimage_mem_nhds (by rw [zero_smul, sub_zero]; exact hU.mem_nhds hu₀)
    obtain ⟨t, ⟨h1, h2⟩, ht⟩ := (((e1.and e2).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
    have k1 := h _ h1
    have k2 := h _ h2
    have k0 := h _ hu₀
    simp only [Matrix.add_vecMul, Matrix.sub_vecMul, Matrix.smul_vecMul, add_dotProduct,
      sub_dotProduct, dotProduct_add, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul] at k1 k2
    have k3 : t ^ 2 * ((y ᵥ* X) ⬝ᵥ y) = 0 := by linear_combination (k1 + k2 - 2 * k0) / 2
    exact (mul_eq_zero.1 k3).resolve_left (pow_ne_zero 2 (ne_of_gt ht))
  -- polarization
  ext i j
  have hij := hq (Pi.single i 1 + Pi.single j 1)
  have hi := hq (Pi.single i 1)
  have hj := hq (Pi.single j 1)
  simp only [Matrix.add_vecMul, dotProduct_add, Matrix.single_one_vecMul, dotProduct_single,
    Matrix.row_apply, Pi.add_apply, mul_one] at hij hi hj
  have hs : X j i = X i j := congrFun (congrFun hX i) j
  rw [Matrix.zero_apply]
  linarith

/-- **Proof of Theorem B.1 (iii), Step 4, for a ReGLU block:** for a block with at least one
hidden unit and `ε > 0`, under the conditions `OneBlockGenericReGLURMS`, equation (17) at the
inputs with no gate at its kink forces `X_s = 0`. -/
theorem noSymmetricPart_reglu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) :
    NoSymmetricPart (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) ε θ
      (noKinkGateRMS θ) := by
  intro X ψr ψw hXs h
  -- `B(u₀)_k ≠ 0` at some row `u₀` with no gate at its kink
  obtain ⟨u₀, hu₀, k, hk⟩ := exists_blockRow_ne_zero_lsu θ hθ
  have hd : Nonempty d := by
    by_contra hd
    rw [not_nonempty_iff] at hd
    exact hu₀ (Classical.arbitrary _) (Finset.sum_of_isEmpty _)
  -- the rows with no gate at its kink and `B(u)_k ≠ 0` form an open set
  have hcont : Continuous fun u : d → ℝ => blockRow_lsu (θ.read 0) (θ.write 0) u k := by
    unfold blockRow_lsu
    refine continuous_finsetSum _ fun i _ => ?_
    have hr : Continuous relu := continuous_id.max continuous_const
    exact ((hr.comp (continuous_id.dotProduct continuous_const)).mul
      (continuous_id.dotProduct continuous_const)).mul continuous_const
  have hU : IsOpen {u : d → ℝ | (∀ i, u ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0) ∧
      blockRow_lsu (θ.read 0) (θ.write 0) u k ≠ 0} := by
    have h1 : {u : d → ℝ | (∀ i, u ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0) ∧
        blockRow_lsu (θ.read 0) (θ.write 0) u k ≠ 0}
        = (⋂ i, {u : d → ℝ | u ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0})
          ∩ {u | blockRow_lsu (θ.read 0) (θ.write 0) u k ≠ 0} := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [h1]
    exact (isOpen_iInter_of_finite fun i =>
      isOpen_ne_fun (continuous_id.dotProduct continuous_const) continuous_const).inter
      (isOpen_ne_fun hcont continuous_const)
  -- there `q = 0` (Step 4), so the symmetric `X` is `0`
  refine eq_zero_of_quad_lsu X hXs _ hU u₀ ⟨hu₀, hk⟩ fun u hu => ?_
  have h1 := qB_zero_lsu hε θ hθ.gated.rank_E X ψr ψw h u hu.1 k
  have h2 := (mul_eq_zero.1 h1).resolve_right hu.2
  rw [qv_lsu, div_eq_zero_iff] at h2
  exact h2.resolve_right (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

omit [DecidableEq d] in
/-- Helper (the block part of Step 4 of part (ii), Lemma B.3 for ReGLU): a direction `ψ` of the
weights of the block (`ψ.E = 0`, `ψ.D = 0`) along which the block has derivative zero at the
inputs with no gate at its kink is a rescaling of the values plus a rescaling of the gates, so it
lies in the span of the directions of symmetries inside the block. -/
private theorem mem_span_lsu (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ)
    (ψ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hψE : ψ.E = 0) (hψD : ψ.D = 0)
    (h : ∀ x ∈ noKinkGateRMS θ,
      fderiv ℝ ((Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0)
          (rmsNorm ε (x * θ.E) * θ.read 0) (rmsNorm ε (x * θ.E) * ψ.read 0) * θ.write 0
        + (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0
          (rmsNorm ε (x * θ.E) * θ.read 0) * ψ.write 0 = 0) :
    ψ ∈ Submodule.span ℝ
      {η | InsideBlocks (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) θ η} := by
  -- the derivative of the block along `ψ` vanishes at every row with no gate at its kink
  -- (`key_lsu` with `X = 0`)
  have hzero : ∀ v : d → ℝ, (∀ i, v ⬝ᵥ (θ.read 0)ᵀ (Sum.inl i) ≠ 0) → ∀ k,
      unitSum_lsu (θ.read 0) (ψ.read 0) (θ.write 0) (ψ.write 0) v k = 0 := by
    intro v hv k
    have h1 := key_lsu hε θ hθ.gated.rank_E 0 (ψ.read 0) (ψ.write 0) (fun x hx => by
      rw [tangentRMS_zero_lsu, Matrix.zero_mul, zero_add]
      exact h x hx) v hv k
    rw [qv_zero_lsu, mul_zero, mul_zero, zero_mul, Matrix.zero_mul, zero_add] at h1
    exact h1
  -- Lemma B.3 for ReGLU with `E` and `D` replaced by the identity and `M = 0`: the gate column
  -- `c_i` moves by `λ_i c_i`, the value column `e_i` by `-α_i e_i` and the write row `a_i` by
  -- `(α_i - λ_i) a_i`
  obtain ⟨-, -, lam, α, hlam⟩ := relu_gated_units_flat
    (fun i => (θ.read 0)ᵀ (Sum.inl i)) 0 (fun i => (θ.read 0)ᵀ (Sum.inr i)) 0
    (fun i => θ.write 0 i) 0 0 (fun i => (ψ.read 0)ᵀ (Sum.inl i)) 0
    (fun i => (ψ.read 0)ᵀ (Sum.inr i)) 0 (fun i => ψ.write 0 i)
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
  -- `ψ = rescaleDir θ α + rescaleDirGate 1 θ λ`, component by component (one block)
  obtain ⟨α', hα'⟩ : ∃ α' : ∀ ℓ : Fin 1, hid ℓ → ℝ, α' 0 = α :=
    ⟨fun ℓ => Fin.cases α (fun l => l.elim0) ℓ, rfl⟩
  obtain ⟨β', hβ'⟩ : ∃ β' : ∀ ℓ : Fin 1, hid ℓ → ℝ, β' 0 = lam :=
    ⟨fun ℓ => Fin.cases lam (fun l => l.elim0) ℓ, rfl⟩
  have hψ : ψ = rescaleDir θ α' + rescaleDirGate 1 θ β' := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
    · show ψ.E = 0 + 0
      rw [add_zero]
      exact hψE
    · obtain rfl := Subsingleton.elim ℓ 0
      ext k j
      rcases j with i | i
      · have h1 : ψ.read 0 k (Sum.inl i) = lam i * θ.read 0 k (Sum.inl i) :=
          congrFun (hlam i).1 k
        show ψ.read 0 k (Sum.inl i) = 0 + β' 0 i * θ.read 0 k (Sum.inl i)
        rw [hβ', zero_add]
        exact h1
      · have h1 : ψ.read 0 k (Sum.inr i) = -(α i) * θ.read 0 k (Sum.inr i) :=
          congrFun (hlam i).2.2.1 k
        show ψ.read 0 k (Sum.inr i) = -(α' 0 i) * θ.read 0 k (Sum.inr i) + 0
        rw [hα', add_zero]
        exact h1
    · obtain rfl := Subsingleton.elim ℓ 0
      ext i k
      have h1 : ψ.write 0 i k = (α i - lam i) * θ.write 0 i k := congrFun (hlam i).2.2.2.2 k
      show ψ.write 0 i k = α' 0 i * θ.write 0 i k + -(((1 : ℕ) : ℝ) * β' 0 i) * θ.write 0 i k
      rw [hα', hβ', Nat.cast_one, h1]
      ring
    · show ψ.D = 0 + 0
      rw [add_zero]
      exact hψD
  -- each part is the direction of a symmetry inside the block
  rw [hψ]
  exact Submodule.add_mem _ (Submodule.subset_span (insideBlocks_rescaleDir θ α'))
    (Submodule.subset_span (insideBlocks_rescaleDirGate relu_homogeneous θ β'))

/-- Helper (Steps 3 and 5, `funDimLearned_eq_funDim_residual_add_of_noSymmetricPart_on` with the
open cone `V` of pre-activations with no gate at its kink): under the conditions
`OneBlockGenericReGLURMS`, for an invertible skip, the functional dimension with the full learned
skip is that of the residual network plus `d (d + 1)/2`, and a batch of inputs of
`noKinkGateRMS θ` has a Jacobian of this rank. -/
private theorem learned_on_lsu (hε : 0 < ε) [Nonempty (hid 0)]
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det) :
    funDimLearned (Arch.gated relu (rmsNorm ε) hid) (θ, R)
        = funDim (Arch.gated relu (rmsNorm ε) hid) 1 θ
          + Fintype.card d * (Fintype.card d + 1) / 2 ∧
      ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateRMS θ) ∧
        jacobianRankSkips (Arch.gated relu (rmsNorm ε) hid)
            (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X (θ, R)
          = funDimLearned (Arch.gated relu (rmsNorm ε) hid) (θ, R) :=
  funDimLearned_eq_funDim_residual_add_of_noSymmetricPart_on
    (A := Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) hε rfl
    {M | ∀ t i, M t (Sum.inl i) ≠ 0} isOpen_gateSet_lsu
    (fun _ hM _ hc t i => mul_ne_zero (hc t).ne' (hM t i)) contDiffOn_f_lsu θ R
    hθ.gated.rank_E hθ.gated.rank_D hR (exists_input_lsu θ hθ.gated)
    (noSymmetricPart_reglu_rmsNorm hε θ hθ)
    (mem_span_lsu hε θ hθ)

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `half_add_half_lsk` of `OneBlock/LearnedSkipKinds.lean`):
`d (d + 1)/2 + d (d − 1)/2 = d²` (both products are even). -/
private theorem half_add_half_lsu (n : ℕ) : n * (n + 1) / 2 + n * (n - 1) / 2 = n ^ 2 := by
  have h1 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  have h3 : n * (n + 1) + n * (n - 1) = 2 * n ^ 2 := by
    cases n with
    | zero => rfl
    | succ m => rw [Nat.add_sub_cancel]; ring
  generalize n * (n + 1) = y at h1 h3 ⊢
  generalize n * (n - 1) = x at h2 h3 ⊢
  generalize n ^ 2 = q at h3 ⊢
  omega

/-- **Theorem 4.6 (ii), "A learned skip raises it by exactly `d (d + 1)/2` more than an identity
skip", for a ReGLU block, at one parameter:** under the conditions `OneBlockGenericReGLURMS`, for
an invertible skip `A = R 0`, the network with the full learned skip has at `(θ, A)` the functional
dimension of the residual network at `θ` plus `d (d + 1)/2`. -/
theorem funDimLearned_reglu_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (hid 0)]
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det) :
    funDimLearned (Arch.gated relu (rmsNorm ε) hid) (θ, R)
      = funDim (Arch.gated relu (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  exact (learned_on_lsu hε θ hθ R hR).1

/-- **Theorem B.1 (iii) for a ReGLU block with a full learned skip, at one parameter:** under the
conditions `OneBlockGenericReGLURMS`, for an invertible skip,
`funDim = P + d² − d (d − 1) − 2 d_hidden`, with `P` the number of weights without the skip. -/
theorem funDimLearned_reglu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det) :
    funDimLearned (Arch.gated relu (rmsNorm ε) hid) (θ, R)
        + (Fintype.card d * (Fintype.card d - 1) + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  -- the value with the learned skip, `fd_res + d(d+1)/2`, and the residual value
  -- `fd_res + d(d-1)/2 + 2 d_hidden = P`; `d(d+1)/2 + d(d-1)/2 = d²`
  have h1 := (learned_on_lsu hε θ hθ R hR).1
  have h2 := funDim_reglu_oneBlock_residual_rmsNorm hε θ hθ
  have h3 := half_add_half_lsu (Fintype.card d)
  have h4 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  rw [h1]
  generalize Fintype.card d * (Fintype.card d + 1) = y at h3 ⊢
  generalize Fintype.card d * (Fintype.card d - 1) = x at h2 h3 h4 ⊢
  generalize Fintype.card d ^ 2 = q at h3 ⊢
  omega

/-- **Theorem B.1 (iii) in the paper's own sense, for a ReGLU block, at one parameter:** a finite
batch of inputs with no gate at its kink on which the Jacobian in the weights and the skip has the
rank `P + d² − d (d − 1) − 2 d_hidden`. -/
theorem exists_jacobianRankSkips_reglu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateRMS θ) ∧
      jacobianRankSkips (Arch.gated relu (rmsNorm ε) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X (θ, R)
          + (Fintype.card d * (Fintype.card d - 1) + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  -- the batch of `learned_on_lsu`, whose rank is the functional dimension
  obtain ⟨n, X, hX, hJ⟩ := (learned_on_lsu hε θ hθ R hR).2
  exact ⟨n, X, hX, by rw [hJ]; exact funDimLearned_reglu_rmsNorm hε θ hθ R hR⟩

/-! ### Helpers: almost every `(θ, A)` -/

omit [DecidableEq d] in
/-- Helper (the private `borelSpace_skips_lsk` of `OneBlock/LearnedSkipKinds.lean`): the skips
`Fin 1 → Matrix d d ℝ` carry the Borel σ-algebra of their norm topology. -/
private theorem borelSpace_skips_lsu : BorelSpace (Fin 1 → Matrix d d ℝ) :=
  inferInstanceAs (BorelSpace (Fin 1 → d → d → ℝ))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper (the private `ae_fst_lsk` of `OneBlock/LearnedSkipKinds.lean`): a condition on the
weights that holds at almost every `θ` holds at almost every `(θ, v)`. -/
private theorem ae_fst_lsu {A : Arch T d 1} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] (hB : BorelSpace V)
    (μ : Measure (Params A dIn dOut × V)) (hμ : μ.IsAddHaarMeasure) {Q : Params A dIn dOut → Prop}
    (h : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), Q θ) :
    ∀ᵐ p ∂μ, Q p.1 := by
  -- a measurable null set `N` outside which `Q` holds
  rw [ae_iff] at h
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null h
  have hc : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), θ ∈ Nᶜ :=
    measure_eq_zero_iff_ae_notMem.1 hN0
  have h1 := (ae_comp_linearMap_mem_iff (LinearMap.fst ℝ (Params A dIn dOut) V) μ
    Measure.addHaar (LinearMap.fst_surjective) hN.compl).2 hc
  refine h1.mono fun p hp => ?_
  by_contra hq
  exact hp (hsub hq)

/-- Helper (the private `ae_isUnit_det_lst` of `OneBlock/LearnedSkipTriangular.lean`): if a square
matrix that depends linearly on a point of `E` is the identity at one point, it is invertible at
almost every point (its determinant is analytic and not identically zero). -/
private theorem ae_isUnit_det_lsu {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] (hB : BorelSpace E) (μ : Measure E)
    (hμ : μ.IsAddHaarMeasure) (Φ : E →ₗ[ℝ] Matrix d d ℝ) (x₀ : E) (h₀ : Φ x₀ = 1) :
    ∀ᵐ x ∂μ, IsUnit (Φ x).det := by
  -- the entries are linear, so the determinant is analytic
  have hentry : ∀ i j, AnalyticOnNhd ℝ (fun x => Φ x i j) Set.univ := fun i j =>
    (LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℝ ℝ i j) ∘ₗ Φ)).analyticOnNhd _
  have hφ : AnalyticOnNhd ℝ (fun x => (Φ x).det) Set.univ := by
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (σ i) i)
  -- it is `1` at `x₀`, so its zero set is null
  have hnull := measure_zeroSet_of_analytic μ hφ ⟨x₀, by rw [h₀, Matrix.det_one]; exact one_ne_zero⟩
  rw [ae_iff]
  simpa only [isUnit_iff_ne_zero, not_not] using hnull

/-- Helper: at almost every `(θ, A)` the conditions `OneBlockGenericReGLURMS θ` hold
(`ae_oneBlockGenericReGLURMS` on the first factor) and the skip `A 0` is invertible. -/
private theorem ae_generic_lsu
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [hμ : μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, OneBlockGenericReGLURMS p.1 ∧ IsUnit (p.2 0).det := by
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := borelSpace_skips_lsu
  have hBp : BorelSpace (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)) := Prod.borelSpace
  have h1 := ae_fst_lsu hBs μ hμ
    (ae_oneBlockGenericReGLURMS (σ := relu) (ε := ε) Measure.addHaar hd hdIn hdOut)
  have h2 : ∀ᵐ p ∂μ, IsUnit (p.2 0).det := ae_isUnit_det_lsu hBp μ hμ
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix d d ℝ) 0)
      ∘ₗ (LinearMap.snd ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
        (Fin 1 → Matrix d d ℝ))) (0, fun _ => 1) rfl
  exact h1.and h2

omit [Fintype T] [Nonempty T] in
/-- Helper (the private `ae_eq_residual_add_lsk` of `OneBlock/LearnedSkipKinds.lean`): from the
value `fd + (d (d − 1) + s) = P + d²` with the learned skip and the value
`fd₁ + (d (d − 1)/2 + s) = P` of the residual network, the difference is `d (d + 1)/2`. -/
private theorem ae_eq_residual_add_lsu {A : Arch T d 1}
    (μ : Measure (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))) (ν : Measure (Params A dIn dOut))
    {k₁ k₂ s : ℕ}
    (hval : ∀ᵐ p ∂μ, funDimLearned A p + k₁
      = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2)
    (hres : ∀ᵐ θ' ∂ν, funDim A 1 θ' + k₂ = Module.finrank ℝ (Params A dIn dOut))
    (hk₁ : k₁ = Fintype.card d * (Fintype.card d - 1) + s)
    (hk₂ : k₂ = Fintype.card d * (Fintype.card d - 1) / 2 + s) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearned A p
      = funDim A 1 θ' + Fintype.card d * (Fintype.card d + 1) / 2 := by
  have h := half_add_half_lsu (Fintype.card d)
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  filter_upwards [hval] with p hp
  filter_upwards [hres] with θ' hθ'
  generalize Fintype.card d * (Fintype.card d + 1) = y at h ⊢
  generalize Fintype.card d * (Fintype.card d - 1) = x at h h2 hk₁ hk₂
  generalize Fintype.card d ^ 2 = q at h hp
  omega

/-- **Theorem B.1 (iii) of the skips paper for one ReGLU block with a full learned skip,
`ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and a block of any width with at least one hidden unit, at
almost every `(θ, A)` the functional dimension is `P + d² − d (d − 1) − 2 d_hidden`. -/
theorem ae_funDimLearned_reglu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.gated relu (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  -- the conditions and an invertible skip at almost every `(θ, A)`
  filter_upwards [ae_generic_lsu μ hd hdIn hdOut] with p hp
  exact funDimLearned_reglu_rmsNorm hε p.1 hp.1 p.2 hp.2

/-- **Theorem B.1 (iii) in the paper's own sense, for one ReGLU block with a full learned skip:**
at almost every `(θ, A)` there is a finite batch of inputs with no gate at its kink on which the
Jacobian in the weights and the skip has the rank `P + d² − d (d − 1) − 2 d_hidden`. -/
theorem ae_exists_jacobianRankSkips_reglu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateRMS p.1) ∧
      jacobianRankSkips (Arch.gated relu (rmsNorm ε) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X p
          + (Fintype.card d * (Fintype.card d - 1) + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  -- the conditions and an invertible skip at almost every `(θ, A)`
  filter_upwards [ae_generic_lsu μ hd hdIn hdOut] with p hp
  exact exists_jacobianRankSkips_reglu_rmsNorm hε p.1 hp.1 p.2 hp.2

/-- **Theorem 4.6 (ii) of the skips paper, "A learned skip raises it by exactly `d (d + 1)/2` more
than an identity skip", for one ReGLU block, `ε > 0`:** at almost every `(θ, A)` and almost every
`θ'`, the network with the full learned skip `A` has `d (d + 1)/2` more functional dimension than
the residual network at `θ'`. -/
theorem ae_funDimLearned_reglu_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearned (Arch.gated relu (rmsNorm ε) hid) p
      = funDim (Arch.gated relu (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the value with the learned skip and the residual value, at almost every point
  exact ae_eq_residual_add_lsu μ ν (ae_funDimLearned_reglu_rmsNorm hε μ hd hdIn hdOut)
    (ae_funDim_reglu_oneBlock_residual_rmsNorm hε ν hd hdIn hdOut) rfl rfl

end Skips
