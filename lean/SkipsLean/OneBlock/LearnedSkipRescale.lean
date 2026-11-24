import SkipsLean.OneBlock.LearnedSkipGain
import SkipsLean.OneBlock.ResidualRMSRescale
import SkipsLean.Dimension.UpperBoundTransformerRescale
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-!
# One ReLU or ReLU² block with a full learned skip under pre-RMSNorm

Paper (skips paper): Theorem 4.6 (ii): "A learned skip raises it by exactly
`d_model (d_model + 1)/2` more than an identity skip." Theorem B.1 (iii): "Let the network be
pre-RMSNorm without biases, with a learned skip `A`, full or upper triangular. For generic
parameters and `ε > 0`, its functional dimension exceeds that of the residual network of part (ii)
by exactly `d_model (d_model + 1)/2`, and it satisfies the equality condition." Its proof, Step 4,
after equation (17), `∂_ψ B(n) = q(n) 𝐃B(n) n`: "We show that `q = 0`, hence `X_s = 0`. For ReLU,
ReLU² and ReGLU, `B(λn) = λ^k B(n)` for `λ > 0`, with `k = 1` or `2`, so the right side of (17) is
`k q(n) B(n)`. Replacing `n` by `λn` with `0 < λ ≤ 1` multiplies the left side by `λ^k` and the
right side by `λ^{k+2}`, so both vanish, and `q = 0` wherever `B ≠ 0`."

Stated here, as in `OneBlock/ResidualRMSRescale.lean` (the same block with the identity skip), for
an activation that is differentiable away from `0`, positively homogeneous of degree `k ≥ 1`, and
satisfies Lemma B.3 in the form `UnitsRescale`, for a block of any width with at least one hidden
unit (a block with no hidden unit is the zero map, and then every change of basis at `h_0` is
undone by the skip):

* Step 4: `NoSymmetricPart` at the inputs `noKinkRMS θ` with no hidden unit at its kink, under the
  conditions `OneBlockGenericRMS` (they give `B ≠ 0` on an open set, by Lemma B.3).
* At one parameter, with an invertible skip: the functional dimension is that of the residual
  network at the same weights plus `d (d + 1)/2`; it is `P + d² − d (d − 1) − s` with `s` the
  number of hidden units (the equality condition: `P + d²` parameters, symmetries of dimension
  `d (d − 1) + s`); and a batch of inputs of `noKinkRMS θ` has a Jacobian of this rank (the paper's
  functional dimension for these blocks).
* For ReLU and ReLU² blocks, `d_in, d_out ≥ d ≥ 2`: the same at almost every `(θ, A)`.

The route: Steps 1 to 3 (`exists_of_flatSkipsOn_learned_rmsNorm`), Step 4 by homogeneity, Step 5 as
`funDimLearned_eq_funDim_residual_add_of_noSymmetricPart_on` (`OneBlock/LearnedSkipGain.lean`), with
the residual value `funDim_mlp_oneBlock_rescale_residual_rmsNorm`. Numeric check:
`learned_skip_relu_attention_check_2026-11-24.py`. Not stated here: the upper triangular skip;
`ε = 0`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-! ### Helpers: the activation away from its kink (copies of `OneBlock/ResidualRMSRescale.lean`) -/

/-- Helper: the matrices with no zero entry. -/
private def noZero_lsr (m n : Type*) : Set (Matrix m n ℝ) :=
  {M | ∀ t i, M t i ≠ 0}

/-- Helper: the matrices with no zero entry form an open set. -/
private theorem isOpen_noZero_lsr {m n : Type*} [Fintype m] [Fintype n] :
    IsOpen (noZero_lsr m n) := by
  refine isOpen_iff_mem_nhds.2 fun M hM => ?_
  exact Filter.eventually_all.2 fun t => Filter.eventually_all.2 fun i =>
    (continuous_id.matrix_elem t i).continuousAt.eventually_ne (hM t i)

/-- Helper: a positively homogeneous `σ` is `C¹` at every `z ≠ 0`. -/
private theorem contDiffAt_of_homogeneous_lsr {k : ℕ}
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {z : ℝ} (hz : z ≠ 0) :
    ContDiffAt ℝ 1 σ z := by
  rcases hz.lt_or_gt with hneg | hpos
  · have h : σ =ᶠ[nhds z] fun y : ℝ => (-y) ^ k * σ (-1) := by
      filter_upwards [eventually_lt_nhds hneg] with y hy
      have e := hhom (-y) (-1) (by linarith)
      rwa [show -y * -1 = y by ring] at e
    have hc : ContDiff ℝ 1 (fun y : ℝ => (-y) ^ k * σ (-1)) := by fun_prop
    exact hc.contDiffAt.congr_of_eventuallyEq h
  · have h : σ =ᶠ[nhds z] fun y : ℝ => y ^ k * σ 1 := by
      filter_upwards [eventually_gt_nhds hpos] with y hy
      have e := hhom y 1 hy
      rwa [mul_one] at e
    have hc : ContDiff ℝ 1 (fun y : ℝ => y ^ k * σ 1) := by fun_prop
    exact hc.contDiffAt.congr_of_eventuallyEq h

/-- Helper: `M ↦ σ(M)` (entrywise) is `C¹` on the matrices with no zero entry. -/
private theorem contDiffOn_map_lsr {k : ℕ}
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {m n : Type*} [Fintype m]
    [Fintype n] : ContDiffOn ℝ 1 (fun M : Matrix m n ℝ => M.map σ) (noZero_lsr m n) := by
  intro M hM
  refine ContDiffAt.contDiffWithinAt (contDiffAt_pi.2 fun t => contDiffAt_pi.2 fun i => ?_)
  have hent : ContDiff ℝ 1 (fun M : Matrix m n ℝ => M t i) :=
    contDiff_pi.1 (contDiff_pi.1 contDiff_id t) i
  have h := (contDiffAt_of_homogeneous_lsr hhom (hM t i)).comp M hent.contDiffAt
  exact h

/-- Helper: `M ↦ σ(M)` (entrywise) is differentiable at a matrix with no zero entry. -/
private theorem differentiableAt_map_lsr (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {m n : Type*} [Fintype m] [Fintype n] {P : Matrix m n ℝ} (hP : ∀ t i, P t i ≠ 0) :
    DifferentiableAt ℝ (fun M : Matrix m n ℝ => M.map σ) P := by
  refine differentiableAt_pi.2 fun t => differentiableAt_pi.2 fun i => ?_
  have hent : Differentiable ℝ (fun M : Matrix m n ℝ => M t i) :=
    differentiable_pi.1 (differentiable_pi.1 differentiable_id t) i
  have h := (hσ _ (hP t i)).differentiableAt.comp P (hent P)
  exact h

/-- Helper: at a matrix `P` with no zero entry, the derivative of `M ↦ σ(M)` along `Q` has the
entries `σ'(P_{t i}) Q_{t i}`. -/
private theorem fderiv_map_apply_lsr (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {m n : Type*} [Fintype m] [Fintype n] {P : Matrix m n ℝ} (hP : ∀ t i, P t i ≠ 0)
    (Q : Matrix m n ℝ) (t : m) (i : n) :
    fderiv ℝ (fun M : Matrix m n ℝ => M.map σ) P Q t i = σ' (P t i) * Q t i := by
  have hline : HasDerivAt (fun τ : ℝ => P + τ • Q) Q 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const Q).const_add P
    rw [one_smul] at h
    exact h
  have h0 : P = P + (0 : ℝ) • Q := by rw [zero_smul, add_zero]
  have h1 := (differentiableAt_map_lsr hσ hP).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) i
  have h3 : HasDerivAt (fun τ : ℝ => σ (P t i + τ * Q t i)) (σ' (P t i) * Q t i) 0 := by
    have hu : HasDerivAt (fun τ : ℝ => P t i + τ * Q t i) (Q t i) 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).mul_const (Q t i)).const_add (P t i)
      rw [one_mul] at h
      exact h
    exact (hσ (P t i) (hP t i)).comp_of_eq (0 : ℝ) hu (by rw [zero_mul, add_zero])
  exact h2.unique h3

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper: an entry of the map of the block. -/
private theorem f_apply_lsr {χ : Matrix T d ℝ → Matrix T d ℝ} (P : Matrix T (hid 0) ℝ) (t : T)
    (i : hid 0) : (Arch.mlp (T := T) (d := d) σ χ hid).f 0 P t i = σ (P t i) := rfl

omit [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper: the same derivative for the map of the block. -/
private theorem fderiv_f_lsr (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {χ : Matrix T d ℝ → Matrix T d ℝ} {P : Matrix T (hid 0) ℝ} (hP : ∀ t i, P t i ≠ 0)
    (Q : Matrix T (hid 0) ℝ) (t : T) (i : hid 0) :
    fderiv ℝ ((Arch.mlp (T := T) (d := d) σ χ hid).f 0) P Q t i = σ' (P t i) * Q t i :=
  fderiv_map_apply_lsr hσ hP Q t i

/-- Helper: differentiating `σ(λ z) = λ^k σ(z)` in `z ≠ 0` gives `λ σ'(λ z) = λ^k σ'(z)`. -/
private theorem mul_deriv_homogeneous_lsr {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {lam z : ℝ} (hlam : 0 < lam)
    (hz : z ≠ 0) : lam * σ' (lam * z) = lam ^ k * σ' z := by
  have hu : HasDerivAt (fun y : ℝ => lam * y) lam z := by
    simpa using (hasDerivAt_id z).const_mul lam
  have h1 : HasDerivAt (fun y => σ (lam * y)) (σ' (lam * z) * lam) z := by
    have h := (hσ (lam * z) (mul_ne_zero hlam.ne' hz)).comp z hu
    exact h
  have h2 : HasDerivAt (fun y => σ (lam * y)) (lam ^ k * σ' z) z := by
    have e : (fun y => σ (lam * y)) = fun y => lam ^ k * σ y := funext fun y => hhom lam y hlam
    rw [e]
    exact (hσ z hz).const_mul _
  have h := h1.unique h2
  linear_combination h

/-- Helper: Euler's identity `σ'(z) z = k σ(z)` for `z ≠ 0` (differentiate `σ(λ z) = λ^k σ(z)`
in `λ` at `λ = 1`). -/
private theorem euler_lsr {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {z : ℝ} (hz : z ≠ 0) :
    σ' z * z = k * σ z := by
  have hu : HasDerivAt (fun lam : ℝ => lam * z) z 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const z
  have h1 : HasDerivAt (fun lam : ℝ => σ (lam * z)) (σ' z * z) 1 :=
    (hσ z hz).comp_of_eq (1 : ℝ) hu (one_mul z).symm
  have h2 : HasDerivAt (fun lam : ℝ => σ (lam * z)) (k * σ z) 1 := by
    have h := (hasDerivAt_pow k (1 : ℝ)).mul_const (σ z)
    rw [one_pow, mul_one] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds one_pos] with lam hlam
    exact hhom lam z hlam
  exact h1.unique h2

omit [DecidableEq d] in
/-- Helper: the factor of `N_ε` is positive for `ε > 0`. -/
private theorem inv_sqrt_pos_lsr (hε : 0 < ε) (v : d → ℝ) :
    0 < (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹ := by
  have h0 : 0 ≤ (v ⬝ᵥ v) / (Fintype.card d : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)) (Nat.cast_nonneg _)
  exact inv_pos.2 (Real.sqrt_pos.2 (by linarith))

/-- Helper: for nonzero vectors `c_i`, some `v` has `v ⬝ c_i ≠ 0` for all `i`. -/
private theorem exists_dotProduct_ne_zero_lsr {n q : Type*} [Fintype n] [Fintype q]
    (c : q → n → ℝ) (hc : ∀ i, c i ≠ 0) : ∃ v : n → ℝ, ∀ i, v ⬝ᵥ c i ≠ 0 := by
  let K : q → Submodule ℝ (n → ℝ) := fun i =>
    { carrier := {ν | ν ⬝ᵥ c i = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢; rw [add_dotProduct, hx, hy, add_zero]
      zero_mem' := by simp
      smul_mem' := fun s x hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢; rw [smul_dotProduct, hx, smul_zero] }
  by_contra hcon
  push Not at hcon
  obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ (p := K) (by
    ext ν
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, h0⟩ := hcon ν
    exact ⟨i, h0⟩)
  have hmem : c i ∈ K i := hi ▸ Submodule.mem_top
  exact hc i (dotProduct_self_eq_zero.1 hmem)

/-! ### Helpers: equation (17) along a row -/

/-- Helper: the left side of equation (17) along a row `u` without the part `q(u) 𝐃B(u) u`:
`∑_i σ'(u c_i) (u X c_i + u ψ_{r,i}) a_i + σ(u c_i) ψ_{w,i}` at the coordinate `j`. -/
private noncomputable def lhs_lsr (σ σ' : ℝ → ℝ) {m : Type*} [Fintype m] (X : Matrix d d ℝ)
    (Wr ψr : Matrix d m ℝ) (Ww ψw : Matrix m d ℝ) (u : d → ℝ) (j : d) : ℝ :=
  ∑ i, (σ' (u ⬝ᵥ Wrᵀ i) * ((u ᵥ* X) ⬝ᵥ Wrᵀ i + u ⬝ᵥ ψrᵀ i) * Ww i j + σ (u ⬝ᵥ Wrᵀ i) * ψw i j)

/-- Helper: the block along a row `u`, `B(u) = ∑_i σ(u c_i) a_i`, at the coordinate `j`. -/
private noncomputable def out_lsr (σ : ℝ → ℝ) {m : Type*} [Fintype m] (Wr : Matrix d m ℝ)
    (Ww : Matrix m d ℝ) (u : d → ℝ) (j : d) : ℝ :=
  ∑ i, σ (u ⬝ᵥ Wrᵀ i) * Ww i j

omit [DecidableEq d] in
/-- Helper: the first part is positively homogeneous of degree `k` off the kinks. -/
private theorem lhs_smul_lsr {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {m : Type*} [Fintype m]
    (X : Matrix d d ℝ) (Wr ψr : Matrix d m ℝ) (Ww ψw : Matrix m d ℝ) (u : d → ℝ)
    (hu : ∀ i, u ⬝ᵥ Wrᵀ i ≠ 0) {c : ℝ} (hc : 0 < c) (j : d) :
    lhs_lsr σ σ' X Wr ψr Ww ψw (c • u) j = c ^ k * lhs_lsr σ σ' X Wr ψr Ww ψw u j := by
  unfold lhs_lsr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_vecMul, smul_dotProduct, smul_eq_mul]
  rw [hhom c _ hc]
  have hd := mul_deriv_homogeneous_lsr hσ hhom hc (hu i)
  linear_combination ((u ᵥ* X) ⬝ᵥ Wrᵀ i + u ⬝ᵥ ψrᵀ i) * Ww i j * hd

omit [DecidableEq d] in
/-- Helper: the block is positively homogeneous of degree `k`. -/
private theorem out_smul_lsr {k : ℕ}
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {m : Type*} [Fintype m]
    (Wr : Matrix d m ℝ) (Ww : Matrix m d ℝ) (u : d → ℝ) {c : ℝ} (hc : 0 < c) (j : d) :
    out_lsr σ Wr Ww (c • u) j = c ^ k * out_lsr σ Wr Ww u j := by
  unfold out_lsr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_dotProduct, smul_eq_mul, hhom c _ hc, mul_assoc]

omit [DecidableEq d] in
/-- Helper: the quadratic form `u X uᵀ` is homogeneous of degree `2`. -/
private theorem quad_smul_lsr (X : Matrix d d ℝ) (u : d → ℝ) (c : ℝ) :
    ((c • u) ᵥ* X) ⬝ᵥ (c • u) = c ^ 2 * ((u ᵥ* X) ⬝ᵥ u) := by
  simp only [smul_vecMul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

omit [Nonempty T] [DecidableEq d] in
/-- Helper: equation (17) at the input whose rows are all `u`, at the token `t` and the coordinate
`j`: by Euler's identity `σ'(z) z = k σ(z)` it is `lhs(u) − k q(u) B(u)`. -/
private theorem entry_lsr {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (Wr ψr : Matrix d (hid 0) ℝ) (Ww ψw : Matrix (hid 0) d ℝ) (X : Matrix d d ℝ)
    (u : d → ℝ) (hu : ∀ i, u ⬝ᵥ Wrᵀ i ≠ 0) (t : T) (j : d) :
    (fderiv ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f 0) ((of fun _ : T => u) * Wr)
          (tangentRMS X (of fun _ : T => u) * Wr + (of fun _ : T => u) * ψr) * Ww
        + (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f 0 ((of fun _ : T => u) * Wr) * ψw) t j
      = lhs_lsr σ σ' X Wr ψr Ww ψw u j
        - k * (((u ᵥ* X) ⬝ᵥ u) / Fintype.card d) * out_lsr σ Wr Ww u j := by
  have hP : ∀ t i, ((of fun _ : T => u) * Wr) t i ≠ 0 := fun _ i => hu i
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, lhs_lsr, out_lsr, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_lsr hσ hP, f_apply_lsr, Matrix.add_apply]
  have h1 : ((of fun _ : T => u) * Wr) t i = u ⬝ᵥ Wrᵀ i := rfl
  have h2 : (tangentRMS X (of fun _ : T => u) * Wr) t i
      = (u ᵥ* X) ⬝ᵥ Wrᵀ i - ((u ᵥ* X) ⬝ᵥ u) / Fintype.card d * (u ⬝ᵥ Wrᵀ i) := by
    show (u ᵥ* X - (((u ᵥ* X) ⬝ᵥ u) / Fintype.card d) • u) ⬝ᵥ Wrᵀ i = _
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
  have h3 : ((of fun _ : T => u) * ψr) t i = u ⬝ᵥ ψrᵀ i := rfl
  rw [h1, h2, h3]
  have he := euler_lsr hσ hhom (hu i)
  linear_combination (-(((u ᵥ* X) ⬝ᵥ u) / Fintype.card d) * Ww i j) * he

omit [Fintype dOut] in
/-- Helper (Step 4 at one row): if equation (17) holds at every input of `noKinkRMS θ`, then at
every row `w` off the kinks, `lhs(w) (‖w‖²/d + ε) = k q(w) B(w)`: the input with all rows `w` is
normalized to the rows `s w`, `s = (‖w‖²/d + ε)^{-1/2}`, and by homogeneity the equation at `s w`
is `s^k` times `lhs(w) − k s² q(w) B(w)`. -/
private theorem row_lsr {k : ℕ} (hε : 0 < ε) (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (X : Matrix d d ℝ) (ψr : Matrix d (hid 0) ℝ)
    (ψw : Matrix (hid 0) d ℝ)
    (h : ∀ x ∈ noKinkRMS θ,
      fderiv ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f 0)
          (rmsNorm ε (x * θ.E) * θ.read 0)
          (tangentRMS X (rmsNorm ε (x * θ.E)) * θ.read 0 + rmsNorm ε (x * θ.E) * ψr) * θ.write 0
        + (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f 0 (rmsNorm ε (x * θ.E) * θ.read 0)
          * ψw = 0)
    (w : d → ℝ) (hw : ∀ i, w ⬝ᵥ (θ.read 0)ᵀ i ≠ 0) (j : d) :
    lhs_lsr σ σ' X (θ.read 0) ψr (θ.write 0) ψw w j * (w ⬝ᵥ w / Fintype.card d + ε)
      = k * (((w ᵥ* X) ⬝ᵥ w) / Fintype.card d) * out_lsr σ (θ.read 0) (θ.write 0) w j := by
  -- `x ↦ x E` is onto, through a left inverse `B` of `E`: the input `x = (w, …, w) B`
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hE)
  have hxE : (Matrix.of fun _ : T => w) * B * θ.E = Matrix.of fun _ : T => w := by
    rw [Matrix.mul_assoc, hB, Matrix.mul_one]
  have hx : (Matrix.of fun _ : T => w) * B ∈ noKinkRMS θ := by
    intro t i
    rw [hxE]
    exact hw i
  -- the normalization scales every row by `s > 0`, with `s² (‖w‖²/d + ε) = 1`
  obtain ⟨s, hs⟩ : ∃ s, s = (Real.sqrt (w ⬝ᵥ w / Fintype.card d + ε))⁻¹ := ⟨_, rfl⟩
  have hspos : 0 < s := hs ▸ inv_sqrt_pos_lsr hε w
  have hDpos : 0 < w ⬝ᵥ w / Fintype.card d + ε := by
    have h0 : 0 ≤ (w ⬝ᵥ w) / (Fintype.card d : ℝ) :=
      div_nonneg (Finset.sum_nonneg fun j _ => mul_self_nonneg (w j)) (Nat.cast_nonneg _)
    linarith
  have hs2 : s ^ 2 * (w ⬝ᵥ w / Fintype.card d + ε) = 1 := by
    rw [hs, inv_pow, Real.sq_sqrt hDpos.le, inv_mul_cancel₀ hDpos.ne']
  have hn : rmsNorm ε (Matrix.of fun _ : T => w) = Matrix.of fun _ : T => s • w := by
    rw [hs]
    rfl
  have e := h _ hx
  rw [hxE, hn] at e
  -- the equation at the row `s w`, at one token
  have hsw : ∀ i, (s • w) ⬝ᵥ (θ.read 0)ᵀ i ≠ 0 := fun i => by
    rw [smul_dotProduct, smul_eq_mul]
    exact mul_ne_zero hspos.ne' (hw i)
  have e2 := (entry_lsr (ε := ε) hσ hhom (θ.read 0) ψr (θ.write 0) ψw X (s • w) hsw
    (Classical.arbitrary T) j).symm.trans (congrFun (congrFun e (Classical.arbitrary T)) j)
  rw [Matrix.zero_apply, lhs_smul_lsr hσ hhom _ _ _ _ _ w hw hspos, out_smul_lsr hhom _ _ w hspos,
    quad_smul_lsr] at e2
  -- divide by `s^k`
  have e3 : s ^ k * (lhs_lsr σ σ' X (θ.read 0) ψr (θ.write 0) ψw w j
        * (w ⬝ᵥ w / Fintype.card d + ε)
      - k * (((w ᵥ* X) ⬝ᵥ w) / Fintype.card d) * out_lsr σ (θ.read 0) (θ.write 0) w j) = 0 := by
    linear_combination (w ⬝ᵥ w / Fintype.card d + ε) * e2
      + (k * (((w ᵥ* X) ⬝ᵥ w) / Fintype.card d) * s ^ k
        * out_lsr σ (θ.read 0) (θ.write 0) w j) * hs2
  exact sub_eq_zero.1 ((mul_eq_zero.1 e3).resolve_left (pow_ne_zero _ hspos.ne'))

omit [Fintype dOut] in
/-- Helper (Step 4, "both sides vanish"): replacing `w` by `2 w` multiplies `lhs` and `B` by `2^k`
and `q` by `4`, but `‖w‖²/d + ε` by less than `4` (`ε > 0`); so `lhs(v) = 0` and `k q(v) B(v) = 0`
at every row `v` off the kinks. -/
private theorem stepA_lsr {k : ℕ} (hε : 0 < ε) (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (X : Matrix d d ℝ) (ψr : Matrix d (hid 0) ℝ)
    (ψw : Matrix (hid 0) d ℝ)
    (h : ∀ x ∈ noKinkRMS θ,
      fderiv ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f 0)
          (rmsNorm ε (x * θ.E) * θ.read 0)
          (tangentRMS X (rmsNorm ε (x * θ.E)) * θ.read 0 + rmsNorm ε (x * θ.E) * ψr) * θ.write 0
        + (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f 0 (rmsNorm ε (x * θ.E) * θ.read 0)
          * ψw = 0)
    (v : d → ℝ) (hv : ∀ i, v ⬝ᵥ (θ.read 0)ᵀ i ≠ 0) (j : d) :
    lhs_lsr σ σ' X (θ.read 0) ψr (θ.write 0) ψw v j = 0 ∧
      k * (((v ᵥ* X) ⬝ᵥ v) / Fintype.card d) * out_lsr σ (θ.read 0) (θ.write 0) v j = 0 := by
  have h2v : ∀ i, ((2 : ℝ) • v) ⬝ᵥ (θ.read 0)ᵀ i ≠ 0 := fun i => by
    rw [smul_dotProduct, smul_eq_mul]
    exact mul_ne_zero two_ne_zero (hv i)
  have h1 := row_lsr hε hσ hhom θ hE X ψr ψw h v hv j
  have h2 := row_lsr hε hσ hhom θ hE X ψr ψw h ((2 : ℝ) • v) h2v j
  rw [lhs_smul_lsr hσ hhom _ _ _ _ _ v hv two_pos, out_smul_lsr hhom _ _ v two_pos,
    quad_smul_lsr, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h2
  have h3 : (2 : ℝ) ^ k * (3 * ε) * lhs_lsr σ σ' X (θ.read 0) ψr (θ.write 0) ψw v j = 0 := by
    linear_combination 4 * (2 : ℝ) ^ k * h1 - h2
  have hL := (mul_eq_zero.1 h3).resolve_left
    (mul_ne_zero (pow_ne_zero _ two_ne_zero) (by positivity))
  refine ⟨hL, ?_⟩
  rw [hL, zero_mul] at h1
  exact h1.symm

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] in
/-- Helper (Step 4, "`B` is not `0` at some `v` off the kinks"): otherwise Lemma B.3 with
`ψ_a = a` gives `λ_i` with `0 = λ_i c_i` and `a_i = −k λ_i a_i`, so `a_i = 0` for a hidden unit. -/
private theorem stepB_lsr {k : ℕ} (hU : UnitsRescale σ σ' k d d (hid 0)) [Nonempty (hid 0)]
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) :
    ∃ v : d → ℝ, (∀ i, v ⬝ᵥ (θ.read 0)ᵀ i ≠ 0) ∧
      ∃ j, out_lsr σ (θ.read 0) (θ.write 0) v j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, lam, hlam⟩ := hU (fun i => (θ.read 0)ᵀ i) 0 (fun i => θ.write 0 i) 0 0 0 0
    (fun i => θ.write 0 i) hθ.row_ne_zero hθ.col_ne_zero hθ.col_not_collinear (by
      intro x hx
      have hx' : ∀ i, x ⬝ᵥ (θ.read 0)ᵀ i ≠ 0 := fun i => by
        have h := hx i
        simp only [Pi.zero_apply, add_zero] at h
        exact h
      funext j
      have h := hcon x hx' j
      unfold out_lsr at h
      simp only [Matrix.vecMul_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, add_zero, zero_add, dotProduct_zero, mul_zero, zero_mul]
      exact h)
  obtain ⟨i⟩ := ‹Nonempty (hid 0)›
  have h1 : lam i • (θ.read 0)ᵀ i = 0 := ((hlam i).1).symm
  have hl : lam i = 0 := (smul_eq_zero.1 h1).resolve_right (hθ.col_ne_zero i)
  have h3 : θ.write 0 i = -((k : ℝ) * lam i) • θ.write 0 i := (hlam i).2.2
  rw [hl, mul_zero, neg_zero, zero_smul] at h3
  exact hθ.row_ne_zero i h3

omit [DecidableEq d] in
/-- Helper: off the kinks and where `B_j ≠ 0`, along every line `v₀ + t w`, near `t = 0` the
row stays off the kinks and `B_j` stays nonzero (`σ` is continuous away from `0`). -/
private theorem eventually_line_lsr (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z) {m : Type*}
    [Fintype m] (Wr : Matrix d m ℝ) (Ww : Matrix m d ℝ) (v₀ w : d → ℝ)
    (hv₀ : ∀ i, v₀ ⬝ᵥ Wrᵀ i ≠ 0) (j : d) (hj : out_lsr σ Wr Ww v₀ j ≠ 0) :
    ∀ᶠ t in nhds (0 : ℝ), (∀ i, (v₀ + t • w) ⬝ᵥ Wrᵀ i ≠ 0) ∧
      out_lsr σ Wr Ww (v₀ + t • w) j ≠ 0 := by
  have hlin : ∀ i, Continuous fun t : ℝ => (v₀ + t • w) ⬝ᵥ Wrᵀ i := by
    intro i
    have e : (fun t : ℝ => (v₀ + t • w) ⬝ᵥ Wrᵀ i) = fun t => v₀ ⬝ᵥ Wrᵀ i + t * (w ⬝ᵥ Wrᵀ i) := by
      funext t
      rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [e]
    fun_prop
  have h0 : ∀ i, (v₀ + (0 : ℝ) • w) ⬝ᵥ Wrᵀ i = v₀ ⬝ᵥ Wrᵀ i := fun i => by rw [zero_smul, add_zero]
  have hσc : ∀ i, ContinuousAt (fun t : ℝ => σ ((v₀ + t • w) ⬝ᵥ Wrᵀ i)) 0 := fun i =>
    ContinuousAt.comp_of_eq (hσ _ (hv₀ i)).continuousAt (hlin i).continuousAt (h0 i)
  have hout : ContinuousAt (fun t : ℝ => out_lsr σ Wr Ww (v₀ + t • w) j) 0 := by
    unfold out_lsr
    exact tendsto_finsetSum _ fun i _ => (hσc i).mul continuousAt_const
  have hev1 : ∀ᶠ t in nhds (0 : ℝ), ∀ i, (v₀ + t • w) ⬝ᵥ Wrᵀ i ≠ 0 :=
    Filter.eventually_all.2 fun i => (hlin i).continuousAt.eventually_ne (by
      show (v₀ + (0 : ℝ) • w) ⬝ᵥ Wrᵀ i ≠ 0
      rw [h0]
      exact hv₀ i)
  have hev2 : ∀ᶠ t in nhds (0 : ℝ), out_lsr σ Wr Ww (v₀ + t • w) j ≠ 0 :=
    hout.eventually_ne (by
      show out_lsr σ Wr Ww (v₀ + (0 : ℝ) • w) j ≠ 0
      rw [zero_smul, add_zero]
      exact hj)
  exact hev1.and hev2

/-- Helper: a symmetric matrix whose quadratic form vanishes on a segment through `v₀` in every
direction is `0` (the form is then `0`, and by polarization so is `X`). -/
private theorem eq_zero_of_quad_lsr (X : Matrix d d ℝ) (hX : Xᵀ = X) (v₀ : d → ℝ)
    (h : ∀ w : d → ℝ, ∃ δ > 0, ∀ t : ℝ, |t| < δ → ((v₀ + t • w) ᵥ* X) ⬝ᵥ (v₀ + t • w) = 0) :
    X = 0 := by
  have hexp : ∀ (w : d → ℝ) (t : ℝ), ((v₀ + t • w) ᵥ* X) ⬝ᵥ (v₀ + t • w)
      = (v₀ ᵥ* X) ⬝ᵥ v₀ + t * ((v₀ ᵥ* X) ⬝ᵥ w + (w ᵥ* X) ⬝ᵥ v₀) + t ^ 2 * ((w ᵥ* X) ⬝ᵥ w) := by
    intro w t
    simp only [add_vecMul, smul_vecMul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    ring
  -- the quadratic form vanishes everywhere: compare `t = 0`, `δ/2`, `-δ/2`
  have hQ : ∀ w : d → ℝ, (w ᵥ* X) ⬝ᵥ w = 0 := by
    intro w
    obtain ⟨δ, hδ, hw⟩ := h w
    have h0 := hw 0 (by rw [abs_zero]; exact hδ)
    have h1 := hw (δ / 2) (by rw [abs_of_pos (by positivity)]; linarith)
    have h2 := hw (-(δ / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
    rw [hexp] at h0 h1 h2
    have h3 : (δ / 2) ^ 2 * ((w ᵥ* X) ⬝ᵥ w) = 0 := by linear_combination (h1 + h2) / 2 - h0
    exact (mul_eq_zero.1 h3).resolve_left (by positivity)
  -- polarization at two basis vectors
  have hpol : ∀ u w : d → ℝ, ((u + w) ᵥ* X) ⬝ᵥ (u + w)
      = (u ᵥ* X) ⬝ᵥ u + ((u ᵥ* X) ⬝ᵥ w + (w ᵥ* X) ⬝ᵥ u) + (w ᵥ* X) ⬝ᵥ w := by
    intro u w
    simp only [add_vecMul, add_dotProduct, dotProduct_add]
    ring
  have hB : ∀ a b : d, (Pi.single a (1 : ℝ) ᵥ* X) ⬝ᵥ Pi.single b 1 = X a b := by
    intro a b
    rw [single_one_vecMul, dotProduct_single, mul_one]
    rfl
  ext a b
  have e := hpol (Pi.single a 1) (Pi.single b 1)
  rw [hQ, hQ, hQ, hB, hB] at e
  have hs : X b a = X a b := by
    have h1 := congrFun (congrFun hX a) b
    rw [Matrix.transpose_apply] at h1
    exact h1
  rw [Matrix.zero_apply]
  linarith

/-- **Proof of Theorem B.1 (iii), Step 4, for ReLU-type MLP blocks:** for an activation that is
positively homogeneous of degree `k ≥ 1`, a block with at least one hidden unit and `ε > 0`, under
the conditions `OneBlockGenericRMS`, equation (17) at the inputs with no hidden unit at its kink
forces `X_s = 0`. -/
theorem noSymmetricPart_mlp_rescale_rmsNorm {k : ℕ} (hk : k ≠ 0) (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0)) [Nonempty (hid 0)]
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) :
    NoSymmetricPart (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) ε θ (noKinkRMS θ) := by
  intro X ψr ψw hXs h
  rcases isEmpty_or_nonempty d with hd | hd
  · ext a
    exact (IsEmpty.false a).elim
  have hc : (Fintype.card d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  -- `B ≠ 0` at some row `v₀` off the kinks (Lemma B.3)
  obtain ⟨v₀, hv₀, j, hj⟩ := stepB_lsr hU θ hθ
  -- near `v₀` the rows stay off the kinks with `B_j ≠ 0`, so there `q = 0`
  refine eq_zero_of_quad_lsr X hXs v₀ fun w => ?_
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    (eventually_line_lsr hσ (θ.read 0) (θ.write 0) v₀ w hv₀ j hj)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨hoff, hout⟩ := hball (show dist t 0 < δ by rw [Real.dist_eq, sub_zero]; exact ht)
  have h2 := (stepA_lsr hε hσ hhom θ hθ.rank_E X ψr ψw h _ hoff j).2
  rcases mul_eq_zero.1 h2 with h3 | h3
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 hk'
    · exact (div_eq_zero_iff.1 h4).resolve_right hc
  · exact absurd h3 hout


/-- **Theorem 4.6 (ii), "A learned skip raises it by exactly `d (d + 1)/2` more than an identity
skip", for ReLU-type MLP blocks, at one parameter:** under the conditions `OneBlockGenericRMS`,
for an invertible skip `A = R 0`, the network with the full learned skip has at `(θ, A)` the
functional dimension of the residual network at `θ` plus `d (d + 1)/2`. -/
theorem funDimLearned_mlp_rescale_rmsNorm_eq_residual_add {k : ℕ} (hk : k ≠ 0) (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0)) [Nonempty (hid 0)]
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det) :
    funDimLearned (Arch.mlp σ (rmsNorm ε) hid) (θ, R)
      = funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) for ReLU-type MLP blocks with a full learned skip, at one parameter:**
under the conditions `OneBlockGenericRMS`, for an invertible skip,
`funDim = P + d² − d (d − 1) − s`, with `s` the number of hidden units and `P` the number of
weights without the skip. -/
theorem funDimLearned_mlp_rescale_rmsNorm {k : ℕ} (hk : k ≠ 0) (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0)) [Nonempty (hid 0)]
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det) :
    funDimLearned (Arch.mlp σ (rmsNorm ε) hid) (θ, R)
        + (Fintype.card d * (Fintype.card d - 1) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem B.1 (iii) in the paper's own sense, for ReLU-type MLP blocks, at one parameter:** a
finite batch of inputs with no hidden unit at its kink on which the Jacobian in the weights and
the skip has the rank `P + d² − d (d − 1) − s`. -/
theorem exists_jacobianRankSkips_mlp_rescale_rmsNorm {k : ℕ} (hk : k ≠ 0) (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0)) [Nonempty (hid 0)]
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkRMS θ) ∧
      jacobianRankSkips (Arch.mlp σ (rmsNorm ε) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X (θ, R)
          + (Fintype.card d * (Fintype.card d - 1) + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one ReLU block with a full learned skip, `ε > 0`:**
for `d_in, d_out ≥ d ≥ 2` and a block of any width with at least one hidden unit, at almost every
`(θ, A)` the functional dimension is `P + d² − d (d − 1) − d_hidden`. -/
theorem ae_funDimLearned_relu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp relu (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem B.1 (iii) in the paper's own sense, for one ReLU block with a full learned skip:**
at almost every `(θ, A)` there is a finite batch of inputs with no hidden unit at its kink on which
the Jacobian in the weights and the skip has the rank `P + d² − d (d − 1) − d_hidden`. -/
theorem ae_exists_jacobianRankSkips_relu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkRMS p.1) ∧
      jacobianRankSkips (Arch.mlp relu (rmsNorm ε) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X p
          + (Fintype.card d * (Fintype.card d - 1) + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem 4.6 (ii) of the skips paper, "A learned skip raises it by exactly `d (d + 1)/2` more
than an identity skip", for one ReLU block, `ε > 0`:** at almost every `(θ, A)` and almost every
`θ'`, the network with the full learned skip `A` has `d (d + 1)/2` more functional dimension than
the residual network at `θ'`. -/
theorem ae_funDimLearned_relu_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearned (Arch.mlp relu (rmsNorm ε) hid) p
      = funDim (Arch.mlp relu (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one ReLU² block with a full learned skip,
`ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and a block of any width with at least one hidden unit, at
almost every `(θ, A)` the functional dimension is `P + d² − d (d − 1) − d_hidden`. -/
theorem ae_funDimLearned_reluSq_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp reluSq (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem B.1 (iii) in the paper's own sense, for one ReLU² block with a full learned skip:**
at almost every `(θ, A)` there is a finite batch of inputs with no hidden unit at its kink on which
the Jacobian in the weights and the skip has the rank `P + d² − d (d − 1) − d_hidden`. -/
theorem ae_exists_jacobianRankSkips_reluSq_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkRMS p.1) ∧
      jacobianRankSkips (Arch.mlp reluSq (rmsNorm ε) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X p
          + (Fintype.card d * (Fintype.card d - 1) + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem 4.6 (ii) of the skips paper, "A learned skip raises it by exactly `d (d + 1)/2` more
than an identity skip", for one ReLU² block, `ε > 0`:** at almost every `(θ, A)` and almost every
`θ'`, the network with the full learned skip `A` has `d (d + 1)/2` more functional dimension than
the residual network at `θ'`. -/
theorem ae_funDimLearned_reluSq_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearned (Arch.mlp reluSq (rmsNorm ε) hid) p
      = funDim (Arch.mlp reluSq (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

end Skips
