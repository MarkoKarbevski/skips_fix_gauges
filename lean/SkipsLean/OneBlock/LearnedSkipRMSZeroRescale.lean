import SkipsLean.OneBlock.LearnedSkipRMSZeroSteps
import SkipsLean.OneBlock.UnitsRescaleSphere
import SkipsLean.OneBlock.LearnedSkipRMSZeroRescaleBound

/-!
# One ReLU or ReLU² block with a full learned skip under pre-RMSNorm with `ε = 0`: the equality

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

Steps 1 to 3 (`OneBlock/LearnedSkipRMSZeroSteps.lean`) give `D_θ g η = g(x) (Y + c I)` only at
the inputs at which `x E A` and `g(x)` are linearly independent ("The constant terms then give
`μ = c` wherever `w E A` and `g(w)` are linearly independent"). To pass to all inputs off the
kinks the proof needs a condition on the parameters that the paper does not state, as for the
residual network (`TurnsActiveRows`, `OneBlock/ResidualRMSZeroRescale.lean`): the rows `u` at
which `u A` and the output of the block are linearly independent are dense among the rows with an
active unit (`TurnsActiveRowsSkip`). It holds at almost every weights and skip
(`OneBlock/LearnedSkipRMSZeroRescaleGeneric.lean`).

Here, for one MLP block with a positively homogeneous activation and a full learned skip (the twin
for `ε = 0` of `OneBlock/LearnedSkipRescale.lean`, and for a learned skip of
`OneBlock/ResidualRMSZeroRescale.lean`), at one parameter under the conditions of the proof:

* the directions of the weights and the skip that are flat at the paper's inputs (no normalized
  row vanishes, no hidden unit at its kink) are a rotation and a scaling of `h_0`, a rotation and
  a scaling of `h_1`, and a rescaling of the hidden units;
* the value of Lean's `funDimLearned`: `P + d² − (d(d−1) + 2) − s`, with `s` the number of hidden
  units and `P` the number of weights without the skip (the bound "at most" is
  `funDimLearned_add_le_rmsNorm_zero'`, `OneBlock/LearnedSkipRMSZeroRescaleBound.lean`);
* a finite batch of the paper's inputs on which the Jacobian in the weights and the skip has
  this rank.

The step "`X_0` is a multiple of `I`", with Lemma B.3, is the hypothesis `UnitsRescaleSphere`
(`OneBlock/UnitsRescaleSphere.lean`; ReLU and ReLU²). No width of the block is asked. Numeric
check of the values: `learned_skip_zero_relu_check_2026-11-24.py`. Not stated: ReGLU blocks; the
upper triangular skip.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **The block turns a dense set of the active rows, for the skip `S`:** every row `v` with no
hidden unit at its kink (no entry of `v W_read` is zero) and with some active unit (`σ` of an
entry of `v W_read` is not zero) is a limit of rows `u` such that `u S` and the output
`σ(u W_read) W_write` of the block at `u` are linearly independent. For `S = 1` this is
`TurnsActiveRows`. -/
def TurnsActiveRowsSkip (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (S : Matrix d d ℝ) : Prop :=
  ∀ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) → (∃ i, σ ((v ᵥ* θ.read 0) i) ≠ 0) →
    v ∈ closure {u : d → ℝ |
      LinearIndependent ℝ ![u ᵥ* S, vanillaBlock σ (θ.read 0) (θ.write 0) u]}

section HelpersLzf

open Filter
open scoped Topology

/-! ### The activation away from its kink (copies of the `_rzr` helpers of
`OneBlock/ResidualRMSZeroRescale.lean`) -/

/-- Helper: the matrices with no zero entry (for a ReLU-type block: the pre-activations with no
hidden unit at its kink). -/
private def noZero_lzf (m n : Type*) : Set (Matrix m n ℝ) :=
  {M | ∀ t i, M t i ≠ 0}

/-- Helper: the matrices with no zero entry form an open set. -/
private theorem isOpen_noZero_lzf {m n : Type*} [Fintype m] [Fintype n] :
    IsOpen (noZero_lzf m n) := by
  refine isOpen_iff_mem_nhds.2 fun M hM => ?_
  exact Filter.eventually_all.2 fun t => Filter.eventually_all.2 fun i =>
    (continuous_id.matrix_elem t i).continuousAt.eventually_ne (hM t i)

/-- Helper: a positively homogeneous `σ` is a monomial on each side of `0` (`σ y = y^k σ(1)` for
`y > 0`, `σ y = (-y)^k σ(-1)` for `y < 0`), hence `C¹` at every `z ≠ 0`. -/
private theorem contDiffAt_of_homogeneous_lzf {k : ℕ}
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
private theorem contDiffOn_map_lzf {k : ℕ}
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {m n : Type*} [Fintype m]
    [Fintype n] : ContDiffOn ℝ 1 (fun M : Matrix m n ℝ => M.map σ) (noZero_lzf m n) := by
  intro M hM
  refine ContDiffAt.contDiffWithinAt (contDiffAt_pi.2 fun t => contDiffAt_pi.2 fun i => ?_)
  have hent : ContDiff ℝ 1 (fun M : Matrix m n ℝ => M t i) :=
    contDiff_pi.1 (contDiff_pi.1 contDiff_id t) i
  have h := (contDiffAt_of_homogeneous_lzf hhom (hM t i)).comp M hent.contDiffAt
  exact h

/-- Helper: `M ↦ σ(M)` (entrywise) is differentiable at a matrix with no zero entry. -/
private theorem differentiableAt_map_lzf (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {m n : Type*} [Fintype m] [Fintype n] {P : Matrix m n ℝ} (hP : ∀ t i, P t i ≠ 0) :
    DifferentiableAt ℝ (fun M : Matrix m n ℝ => M.map σ) P := by
  refine differentiableAt_pi.2 fun t => differentiableAt_pi.2 fun i => ?_
  have hent : Differentiable ℝ (fun M : Matrix m n ℝ => M t i) :=
    differentiable_pi.1 (differentiable_pi.1 differentiable_id t) i
  have h := (hσ _ (hP t i)).differentiableAt.comp P (hent P)
  exact h

/-- Helper: at a matrix `P` with no zero entry, the derivative of `M ↦ σ(M)` along `Q` has the
entries `σ'(P_{t i}) Q_{t i}`. -/
private theorem fderiv_map_apply_lzf (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {m n : Type*} [Fintype m] [Fintype n] {P : Matrix m n ℝ} (hP : ∀ t i, P t i ≠ 0)
    (Q : Matrix m n ℝ) (t : m) (i : n) :
    fderiv ℝ (fun M : Matrix m n ℝ => M.map σ) P Q t i = σ' (P t i) * Q t i := by
  -- the chain rule along the line `τ ↦ P + τ Q`
  have hline : HasDerivAt (fun τ : ℝ => P + τ • Q) Q 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const Q).const_add P
    rw [one_smul] at h
    exact h
  have h0 : P = P + (0 : ℝ) • Q := by rw [zero_smul, add_zero]
  have h1 := (differentiableAt_map_lzf hσ hP).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) i
  -- the same derivative, entrywise: `τ ↦ σ(P_{t i} + τ Q_{t i})`
  have h3 : HasDerivAt (fun τ : ℝ => σ (P t i + τ * Q t i)) (σ' (P t i) * Q t i) 0 := by
    have hu : HasDerivAt (fun τ : ℝ => P t i + τ * Q t i) (Q t i) 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).mul_const (Q t i)).const_add (P t i)
      rw [one_mul] at h
      exact h
    exact (hσ (P t i) (hP t i)).comp_of_eq (0 : ℝ) hu (by rw [zero_mul, add_zero])
  exact h2.unique h3

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper: an entry of the map of the block. -/
private theorem f_apply_lzf {χ : Matrix T d ℝ → Matrix T d ℝ} (P : Matrix T (hid 0) ℝ) (t : T)
    (i : hid 0) : (Arch.mlp (T := T) (d := d) σ χ hid).f 0 P t i = σ (P t i) := rfl

omit [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper: the same derivative for the map of the block. -/
private theorem fderiv_f_lzf (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {χ : Matrix T d ℝ → Matrix T d ℝ} {P : Matrix T (hid 0) ℝ} (hP : ∀ t i, P t i ≠ 0)
    (Q : Matrix T (hid 0) ℝ) (t : T) (i : hid 0) :
    fderiv ℝ ((Arch.mlp (T := T) (d := d) σ χ hid).f 0) P Q t i = σ' (P t i) * Q t i :=
  fderiv_map_apply_lzf hσ hP Q t i

/-- Helper: differentiating `σ(λ z) = λ^k σ(z)` in `z ≠ 0` gives `λ σ'(λ z) = λ^k σ'(z)`. -/
private theorem mul_deriv_homogeneous_lzf {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
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

/-- Helper (a copy of the private `euler_lsr`): Euler's identity `σ'(z) z = k σ(z)` for `z ≠ 0`
(differentiate `σ(λ z) = λ^k σ(z)` in `λ` at `λ = 1`). -/
private theorem euler_lzf {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
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

/-! ### The activation near a point `z ≠ 0` -/

/-- Helper: near `z ≠ 0` the quotient `y / z` is positive. -/
private theorem eventually_div_pos_lzf {z : ℝ} (hz : z ≠ 0) : ∀ᶠ y in 𝓝 z, 0 < y / z := by
  rcases hz.lt_or_gt with hneg | hpos
  · filter_upwards [eventually_lt_nhds hneg] with y hy
    exact div_pos_of_neg_of_neg hy hneg
  · filter_upwards [eventually_gt_nhds hpos] with y hy
    exact div_pos hy hpos

/-- Helper: a positively homogeneous `σ` that vanishes at `z ≠ 0` vanishes on the half-line of
`z`, so `σ'(z) = 0` (an inactive unit has derivative zero). -/
private theorem deriv_eq_zero_of_eq_zero_lzf {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {z : ℝ} (hz : z ≠ 0)
    (h0 : σ z = 0) : σ' z = 0 := by
  -- `σ(y) = (y/z)^k σ(z) = 0` for `y` near `z`
  have h : σ =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_div_pos_lzf hz] with y hy
    have e := hhom (y / z) z hy
    rwa [div_mul_cancel₀ y hz, h0, mul_zero] at e
  exact (hσ z hz).unique ((hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq h)

/-- Helper: `σ'` is continuous at every `z ≠ 0`: near `z`, `σ'(y) = (y/z)^k σ'(z) / (y/z)`. -/
private theorem continuousAt_deriv_lzf {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {z : ℝ} (hz : z ≠ 0) :
    ContinuousAt σ' z := by
  have h1 : ContinuousAt (fun y : ℝ => y / z) z := continuousAt_id.div_const z
  have hc : ContinuousAt (fun y : ℝ => (y / z) ^ k * σ' z / (y / z)) z :=
    ((h1.pow k).mul continuousAt_const).div h1 (div_ne_zero hz hz)
  refine hc.congr ?_
  filter_upwards [eventually_div_pos_lzf hz] with y hy
  -- `(y/z) σ'(y) = (y/z)^k σ'(z)` by homogeneity
  have e := mul_deriv_homogeneous_lzf hσ hhom hy hz
  rw [div_mul_cancel₀ y hz] at e
  rw [← e]
  exact mul_div_cancel_left₀ _ hy.ne'

/-! ### The two sides of the equation of `UnitsRescaleSphere` on one row -/

/-- Helper: the derivative of the block along a direction, on the row `v`, at the coordinate `j`:
`∑_i (σ(v c_i) β_{i j} + σ'(v c_i) (v ψc_i) a_{i j})`, with `c_i`, `ψc_i` the columns of `Wr`,
`Ψr` and `a_i`, `β_i` the rows of `Ww`, `W'`. -/
private noncomputable def dBlock_lzf (σ σ' : ℝ → ℝ) {q : Type*} [Fintype q]
    (Wr Ψr : Matrix d q ℝ) (Ww W' : Matrix q d ℝ) (v : d → ℝ) (j : d) : ℝ :=
  ∑ i, (σ (v ⬝ᵥ Wrᵀ i) * W' i j + σ' (v ⬝ᵥ Wrᵀ i) * (v ⬝ᵥ Ψrᵀ i) * Ww i j)

/-- Helper: the block on the row `v`, `B(v) = ∑_i σ(v c_i) a_i`, at the coordinate `j`. -/
private noncomputable def block_lzf (σ : ℝ → ℝ) {q : Type*} [Fintype q] (Wr : Matrix d q ℝ)
    (Ww : Matrix q d ℝ) (v : d → ℝ) (j : d) : ℝ :=
  ∑ i, σ (v ⬝ᵥ Wrᵀ i) * Ww i j

omit [DecidableEq d] in
/-- Helper: `‖v‖² ∂_ψ B(v)_j − k (v X vᵀ) B(v)_j` is continuous in the row `v` at a row off the
kinks. -/
private theorem continuousAt_eq_lzf {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {q : Type*} [Fintype q]
    (Wr Ψr : Matrix d q ℝ) (Ww W' : Matrix q d ℝ) (X : Matrix d d ℝ) (j : d) {u : d → ℝ}
    (hu : ∀ i, u ⬝ᵥ Wrᵀ i ≠ 0) :
    ContinuousAt (fun v : d → ℝ => (v ⬝ᵥ v) * dBlock_lzf σ σ' Wr Ψr Ww W' v j
      - (k : ℝ) * ((v ᵥ* X) ⬝ᵥ v) * block_lzf σ Wr Ww v j) u := by
  have hdot : ∀ c : d → ℝ, Continuous fun v : d → ℝ => v ⬝ᵥ c := fun c =>
    continuous_id.dotProduct continuous_const
  -- `σ` and `σ'` of the pre-activations are continuous off the kinks
  have hs : ∀ i, ContinuousAt (fun v : d → ℝ => σ (v ⬝ᵥ Wrᵀ i)) u := fun i =>
    ContinuousAt.comp (f := fun v : d → ℝ => v ⬝ᵥ Wrᵀ i) (x := u) (hσ _ (hu i)).continuousAt
      (hdot _).continuousAt
  have hs' : ∀ i, ContinuousAt (fun v : d → ℝ => σ' (v ⬝ᵥ Wrᵀ i)) u := fun i =>
    ContinuousAt.comp (f := fun v : d → ℝ => v ⬝ᵥ Wrᵀ i) (x := u)
      (continuousAt_deriv_lzf hσ hhom (hu i)) (hdot _).continuousAt
  have hD : ContinuousAt (fun v : d → ℝ => dBlock_lzf σ σ' Wr Ψr Ww W' v j) u := by
    have h := tendsto_finsetSum (f := fun (i : q) (v : d → ℝ) => σ (v ⬝ᵥ Wrᵀ i) * W' i j
      + σ' (v ⬝ᵥ Wrᵀ i) * (v ⬝ᵥ Ψrᵀ i) * Ww i j) Finset.univ fun i _ =>
        ((hs i).mul continuousAt_const).add
          (((hs' i).mul (hdot _).continuousAt).mul continuousAt_const)
    exact h
  have hB : ContinuousAt (fun v : d → ℝ => block_lzf σ Wr Ww v j) u := by
    have h := tendsto_finsetSum (f := fun (i : q) (v : d → ℝ) => σ (v ⬝ᵥ Wrᵀ i) * Ww i j)
      Finset.univ fun i _ => (hs i).mul continuousAt_const
    exact h
  have hq : Continuous fun v : d → ℝ => (v ᵥ* X) ⬝ᵥ v :=
    (continuous_id.matrix_vecMul continuous_const).dotProduct continuous_id
  exact ((continuous_id.dotProduct continuous_id).continuousAt.mul hD).sub
    ((continuousAt_const.mul hq.continuousAt).mul hB)

/-- Helper: a function continuous at a point `u` of the closure of `S` that vanishes at the
points of `S` with a property `P` holding near `u` vanishes at `u`. -/
private theorem eq_zero_of_mem_closure_lzf {X : Type*} [TopologicalSpace X] {F : X → ℝ} {u : X}
    {S : Set X} {P : X → Prop} (hF : ContinuousAt F u) (hu : u ∈ closure S)
    (hP : ∀ᶠ v in 𝓝 u, P v) (h0 : ∀ v ∈ S, P v → F v = 0) : F u = 0 := by
  by_contra hne
  obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ := mem_closure_iff_nhds.1 hu _ ((hF.eventually_ne hne).and hP)
  exact hv1 (h0 v hv3 hv2)

/-! ### The normalized rows and the block on one row -/

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `N_0` scales every row: `(N_0(h) W)_{t i} = (‖h_t‖²/d)^{-1/2} (h W)_{t i}`. -/
private theorem rmsNorm_mul_apply_lzf {n : Type*} [Fintype n] (h : Matrix T d ℝ)
    (W : Matrix d n ℝ) (t : T) (i : n) :
    (rmsNorm 0 h * W) t i
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ * (h * W) t i := by
  simp only [Matrix.mul_apply, Finset.mul_sum, rmsNorm, rmsRow, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul, mul_assoc, add_zero]

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: the same at the input whose rows are all `v`. -/
private theorem rmsNorm_const_mul_lzf {n : Type*} [Fintype n] (v : d → ℝ) (W : Matrix d n ℝ)
    (t : T) (i : n) :
    (rmsNorm 0 (Matrix.of fun _ : T => v) * W) t i
      = (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ)))⁻¹ * (v ⬝ᵥ Wᵀ i) := by
  rw [rmsNorm_mul_apply_lzf]
  rfl

omit [DecidableEq d] in
/-- Helper: the factor of `N_0` at a row `v ≠ 0` is positive. -/
private theorem inv_sqrt_pos_lzf {v : d → ℝ} (hv : v ≠ 0) :
    0 < (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ)))⁻¹ := by
  have h1 : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j))
      (fun h => hv (dotProduct_self_eq_zero.1 h.symm))
  obtain ⟨j, -⟩ := Function.ne_iff.1 hv
  have h2 : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩)
  exact inv_pos.2 (Real.sqrt_pos.2 (div_pos h1 h2))

omit [DecidableEq d] in
/-- Helper: the block on one row is positively homogeneous: `b(s u) = s^k b(u)` for `s > 0`. -/
private theorem vanillaBlock_smul_lzf {k : ℕ}
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {q : Type*} [Fintype q]
    (Wr : Matrix d q ℝ) (Ww : Matrix q d ℝ) (u : d → ℝ) {s : ℝ} (hs : 0 < s) :
    vanillaBlock σ Wr Ww (s • u) = s ^ k • vanillaBlock σ Wr Ww u := by
  unfold vanillaBlock
  have e : (fun i => σ (((s • u) ᵥ* Wr) i)) = s ^ k • fun i => σ ((u ᵥ* Wr) i) := by
    funext i
    rw [Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul, hhom s _ hs]
    rfl
  rw [e, Matrix.smul_vecMul]

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: at a row `h_t ≠ 0`, the row `t` of the block `σ(N_0(h) W_read) W_write` is a nonzero
multiple of `b(h_t)` (the multiple `s^k`, with `s = (‖h_t‖²/d)^{-1/2} > 0`). -/
private theorem row_block_lzf {k : ℕ}
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {q : Type*} [Fintype q]
    (Wr : Matrix d q ℝ) (Ww : Matrix q d ℝ) (h : Matrix T d ℝ) (t : T) (ht : h t ≠ 0) :
    ∃ r : ℝ, r ≠ 0 ∧ ((rmsNorm 0 h * Wr).map σ * Ww) t = r • vanillaBlock σ Wr Ww (h t) := by
  have hpos : 0 < (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + 0))⁻¹ := by
    rw [add_zero]
    exact inv_sqrt_pos_lzf ht
  refine ⟨_, pow_ne_zero k hpos.ne', ?_⟩
  rw [map_mul_mul_row]
  exact vanillaBlock_smul_lzf hhom Wr Ww (h t) hpos

/-- Helper: scaling the second vector of an independent pair by `r ≠ 0` keeps it independent. -/
private theorem linearIndependent_pair_smul_lzf {V : Type*} [AddCommGroup V] [Module ℝ V]
    {a b : V} (h : LinearIndependent ℝ ![a, b]) {r : ℝ} (hr : r ≠ 0) :
    LinearIndependent ℝ ![a, r • b] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  obtain ⟨h1, h2⟩ := h s (t * r) (by rw [mul_smul]; exact hst)
  exact ⟨h1, (mul_eq_zero.1 h2).resolve_right hr⟩

omit [Nonempty T] [DecidableEq d] in
/-- Helper: at the input whose rows are all `v ≠ 0`, with `s = (‖v‖²/d)^{-1/2}`,
`(𝐃N_0(h)(h X) W)_{t i} = s (v X) c_i − (v·vX/d) s³ (v c_i)`, `c_i` the column `i` of `W`. -/
private theorem fderiv_rmsNorm_const_mul_lzf {n : Type*} [Fintype n] {v : d → ℝ} (hv : v ≠ 0)
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
`(X, η_read, β)` vanishes at the input whose rows are all `v` (a row off the kinks), then
`‖v‖² ∂_ψ B(v) = k (v X vᵀ) B(v)` with `ψc_i = X c_i + (η_read)_i`: the normalization scales `v`
by `s = (‖v‖²/d)^{-1/2}`, its derivative along `v X` is `s (v X) − (v·vX/d) s³ v`, and by
homogeneity and Euler's identity `σ'(z) z = k σ(z)` the equation is `s^k` times
`∂_ψ B(v) − k (v·vX/d) s² B(v)`, with `s² ‖v‖² = d`. -/
private theorem row_eq_lzf {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (Wr ηr : Matrix d (hid 0) ℝ) (Ww W' : Matrix (hid 0) d ℝ) (X : Matrix d d ℝ)
    {v : d → ℝ} (hv0 : v ≠ 0) (hv : ∀ i, v ⬝ᵥ Wrᵀ i ≠ 0) (j : d)
    (e : fderiv ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f 0)
          (rmsNorm 0 (Matrix.of fun _ : T => v) * Wr)
          (fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (Matrix.of fun _ : T => v)
              ((Matrix.of fun _ : T => v) * X) * Wr
            + rmsNorm 0 (Matrix.of fun _ : T => v) * ηr) * Ww
        + (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f 0
          (rmsNorm 0 (Matrix.of fun _ : T => v) * Wr) * W' = 0) :
    (v ⬝ᵥ v) * dBlock_lzf σ σ' Wr (X * Wr + ηr) Ww W' v j
      = (k : ℝ) * ((v ᵥ* X) ⬝ᵥ v) * block_lzf σ Wr Ww v j := by
  -- the normalization scales the row `v` by `s = (‖v‖²/d)^{-1/2} > 0`, and `s² ‖v‖² = d`
  obtain ⟨s, hs_def⟩ : ∃ s, s = (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ)))⁻¹ := ⟨_, rfl⟩
  have hs : 0 < s := hs_def ▸ inv_sqrt_pos_lzf hv0
  have hvv : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j))
      (fun h => hv0 (dotProduct_self_eq_zero.1 h.symm))
  obtain ⟨j₀, -⟩ := Function.ne_iff.1 hv0
  have hd0 : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j₀⟩)
  have hs2 : s ^ 2 * (v ⬝ᵥ v) = Fintype.card d := by
    rw [hs_def, inv_pow, Real.sq_sqrt (div_nonneg hvv.le hd0.le)]
    field_simp
  -- no pre-activation of the normalized row is zero
  have hP : ∀ t i, (rmsNorm 0 (Matrix.of fun _ : T => v) * Wr) t i ≠ 0 := fun t i => by
    rw [rmsNorm_const_mul_lzf, ← hs_def]
    exact mul_ne_zero hs.ne' (hv i)
  -- the entry `(t, j)` of the equation, unit by unit
  have e2 := congrFun (congrFun e (Classical.arbitrary T)) j
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib,
    Matrix.zero_apply] at e2
  have key : ∀ i : hid 0, fderiv ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f 0)
        (rmsNorm 0 (Matrix.of fun _ : T => v) * Wr)
        (fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (Matrix.of fun _ : T => v)
            ((Matrix.of fun _ : T => v) * X) * Wr
          + rmsNorm 0 (Matrix.of fun _ : T => v) * ηr) (Classical.arbitrary T) i * Ww i j
      + (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f 0
          (rmsNorm 0 (Matrix.of fun _ : T => v) * Wr) (Classical.arbitrary T) i * W' i j
      = s ^ k * (σ (v ⬝ᵥ Wrᵀ i) * W' i j
          + σ' (v ⬝ᵥ Wrᵀ i) * (v ⬝ᵥ (X * Wr + ηr)ᵀ i) * Ww i j)
        - s ^ k * ((k : ℝ) * ((v ⬝ᵥ (v ᵥ* X)) / Fintype.card d) * s ^ 2)
          * (σ (v ⬝ᵥ Wrᵀ i) * Ww i j) := by
    intro i
    rw [fderiv_f_lzf hσ hP, f_apply_lzf, Matrix.add_apply, fderiv_rmsNorm_const_mul_lzf hv0,
      rmsNorm_const_mul_lzf, rmsNorm_const_mul_lzf, ← hs_def, hhom s _ hs]
    have hψ : v ⬝ᵥ (X * Wr + ηr)ᵀ i = (v ᵥ* X) ⬝ᵥ Wrᵀ i + v ⬝ᵥ ηrᵀ i := by
      show v ⬝ᵥ (X *ᵥ Wrᵀ i + ηrᵀ i) = _
      rw [dotProduct_add, Matrix.dotProduct_mulVec]
    have hdv := mul_deriv_homogeneous_lzf hσ hhom hs (hv i)
    have he := euler_lzf hσ hhom (hv i)
    linear_combination (((v ᵥ* X) ⬝ᵥ Wrᵀ i + v ⬝ᵥ ηrᵀ i) * Ww i j
        - (v ⬝ᵥ (v ᵥ* X)) / Fintype.card d * s ^ 2 * (v ⬝ᵥ Wrᵀ i) * Ww i j) * hdv
      - s ^ k * σ' (v ⬝ᵥ Wrᵀ i) * Ww i j * hψ
      - (v ⬝ᵥ (v ᵥ* X)) / Fintype.card d * s ^ 2 * s ^ k * Ww i j * he
  -- the sum over the units: `s^k (∂_ψ B(v) − k (v·vX/d) s² B(v)) = 0`
  have e3 := (Finset.sum_congr rfl fun i _ => (key i).symm).trans e2
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at e3
  have hq : (v ⬝ᵥ (v ᵥ* X)) / Fintype.card d * (s ^ 2 * (v ⬝ᵥ v)) = (v ᵥ* X) ⬝ᵥ v := by
    rw [hs2, div_mul_cancel₀ _ hd0.ne', dotProduct_comm]
  unfold dBlock_lzf block_lzf
  refine sub_eq_zero.1 ((mul_eq_zero.1 ?_).resolve_left (pow_ne_zero k hs.ne'))
  linear_combination (v ⬝ᵥ v) * e3 + s ^ k * k * (∑ i, σ (v ⬝ᵥ Wrᵀ i) * Ww i j) * hq

end HelpersLzf

/-- **Proof of Theorem B.1 (iii) of the skips paper, "The case `ε = 0`", the flat directions for
one MLP block with a positively homogeneous activation and a full learned skip:** under the
conditions `OneBlockGenericRMS`, for `d ≥ 2`, an invertible skip `A = R 0`, a block that turns a
dense set of the active rows and one turned row off the kinks, a direction `(η, η_A)` of the
weights and the skip that is flat at every input at which no normalized row vanishes and no
hidden unit sits at its kink is the sum of the rotations of `h_0` and `h_1` (antisymmetric `X₀`,
`Y`), the scalings of `h_0` and `h_1` (numbers `c₀`, `c₁`) and a rescaling of the hidden units:
`η = (E (X₀ + c₀ I), −X₀ W_read + W_read diag(α), W_write (Y + c₁ I) − k diag(α) W_write, −Y D)`
and `η_A = A (Y + c₁ I) − (X₀ + c₀ I) A`. -/
theorem flatSkipsOn_noKink_le_mlp_rescale_learned_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescaleSphere σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det)
    (hturn : TurnsActiveRowsSkip θ (R 0))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* R 0, vanillaBlock σ (θ.read 0) (θ.write 0) v])
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (ρ : Fin 1 → Matrix d d ℝ)
    (hη : (η, ρ) ∈ flatSkipsOn (Arch.mlp σ (rmsNorm 0) hid)
      (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
      (learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ R ∩ noKinkRMS θ)) :
    ∃ (X₀ Y : Matrix d d ℝ) (c₀ c₁ : ℝ) (α : ∀ ℓ, hid ℓ → ℝ), X₀ᵀ = -X₀ ∧ Yᵀ = -Y ∧
      η = cobDir θ ![X₀, Y] + scaleDir θ ![c₀, c₁] + rescaleDirMlp k θ α ∧
      ρ 0 = R 0 * (Y + c₁ • 1) - (X₀ + c₀ • 1) * R 0 := by
  classical
  -- `x ↦ x E` is onto, through a left inverse `Ep` of `E`
  obtain ⟨Ep, hEp⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hθ.rank_E)
  have hxE : ∀ u : d → ℝ, (Matrix.of fun _ : T => u) * Ep * θ.E = Matrix.of fun _ : T => u :=
    fun u => by rw [Matrix.mul_assoc, hEp, Matrix.mul_one]
  -- the input with every row `u'`, `u' E = u`, for a row `u` off the kinks with `u A`, `b(u)`
  -- independent: no entry of `x E W_read` is zero, and for every token the rows `u A` of `x E A`
  -- and `b(N_0(u)) = s^k b(u)` (`s > 0`) of `g(x)` are independent
  have hgood : ∀ u : d → ℝ, (∀ i, (u ᵥ* θ.read 0) i ≠ 0) →
      LinearIndependent ℝ ![u ᵥ* R 0, vanillaBlock σ (θ.read 0) (θ.write 0) u] →
      (Matrix.of fun _ : T => u) * Ep * θ.E * θ.read 0 ∈ noZero_lzf T (hid 0) ∧
      ∀ t, LinearIndependent ℝ ![((Matrix.of fun _ : T => u) * Ep * θ.E * R 0) t,
        ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f 0
          (rmsNorm 0 ((Matrix.of fun _ : T => u) * Ep * θ.E) * θ.read 0) * θ.write 0) t] := by
    intro u hu hli
    rw [hxE]
    refine ⟨fun t i => hu i, fun t => ?_⟩
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact hli.ne_zero 0 (by simp)
    obtain ⟨r, hr, e⟩ : ∃ r : ℝ, r ≠ 0 ∧ ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f 0
          (rmsNorm 0 (Matrix.of fun _ : T => u) * θ.read 0) * θ.write 0) t
        = r • vanillaBlock σ (θ.read 0) (θ.write 0) u :=
      row_block_lzf hhom (θ.read 0) (θ.write 0) (Matrix.of fun _ : T => u) t hu0
    have e' : ((Matrix.of fun _ : T => u) * R 0) t = u ᵥ* R 0 := rfl
    rw [e, e']
    exact linearIndependent_pair_smul_lzf hli hr
  -- Steps 1 to 3 (the case `ε = 0` of part (iii), with the learned skip) on the cone of
  -- pre-activations with no zero entry, which is open and invariant under positive scalings of
  -- the rows, and on which the block map is `C¹`: `η_E = E X`, `η_A = A (Y + c I) − X A`,
  -- `η_D = −Y D`, and the derivative of the block along `η` is `g(x) (Y + c I)` at every input
  -- whose rows of `x E A` and `g(x)` are independent
  obtain ⟨v₀, hv₀, hli₀⟩ := hw
  obtain ⟨X, Y, c, hYa, hEX, hρ, hDY, hF⟩ := exists_of_flatSkipsOn_learned_rmsNorm_zero_on
    (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) rfl hd (noZero_lzf T (hid 0))
    isOpen_noZero_lzf (fun M hM c hc t i => mul_ne_zero (hc t).ne' (hM t i))
    (contDiffOn_map_lzf hhom) θ R hθ.rank_E hθ.rank_D hR ⟨_, hgood v₀ hv₀ hli₀⟩ η ρ hη
  obtain ⟨W', hW'⟩ : ∃ W', W' = η.write 0 - θ.write 0 * (Y + c • 1) := ⟨_, rfl⟩
  -- Step 4 (a), one row: at a row `v` off the kinks with `v A`, `b(v)` independent, the block
  -- equation at the input with every row `v'`, `v' E = v`, gives
  -- `‖v‖² ∂_ψ B(v) = k (v X vᵀ) B(v)`, with `ψc_i = X c_i + (η_read)_i`,
  -- `β_i = (η_write)_i − a_i (Y + c I)`
  have hind : ∀ v : d → ℝ, (∀ i, v ⬝ᵥ (θ.read 0)ᵀ i ≠ 0) →
      LinearIndependent ℝ ![v ᵥ* R 0, vanillaBlock σ (θ.read 0) (θ.write 0) v] → ∀ j : d,
      (v ⬝ᵥ v) * dBlock_lzf σ σ' (θ.read 0) (X * θ.read 0 + η.read 0) (θ.write 0) W' v j
        = (k : ℝ) * ((v ᵥ* X) ⬝ᵥ v) * block_lzf σ (θ.read 0) (θ.write 0) v j := by
    intro v hv hli j
    obtain ⟨hx, hxi⟩ := hgood v hv hli
    have e := hF _ hx hxi
    rw [hxE] at e
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hli.ne_zero 0 (by simp)
    refine row_eq_lzf (T := T) hσ hhom (θ.read 0) (η.read 0) (θ.write 0) W' X hv0 hv j ?_
    rw [hW', Matrix.mul_sub, ← Matrix.mul_assoc, ← e]
    abel
  -- Step 4 (a), every row off the kinks: if some unit is active at `v`, then `v` is a limit of
  -- rows `u` with `u A`, `b(u)` independent (`hturn`), and both sides are continuous off the
  -- kinks; if no unit is active, `σ` and `σ'` vanish at every pre-activation of `v`
  have hall : ∀ v : d → ℝ, (∀ i, v ⬝ᵥ (θ.read 0)ᵀ i ≠ 0) → ∀ j : d,
      (v ⬝ᵥ v) * dBlock_lzf σ σ' (θ.read 0) (X * θ.read 0 + η.read 0) (θ.write 0) W' v j
        - (k : ℝ) * ((v ᵥ* X) ⬝ᵥ v) * block_lzf σ (θ.read 0) (θ.write 0) v j = 0 := by
    intro v hv j
    by_cases hact : ∃ i, σ (v ⬝ᵥ (θ.read 0)ᵀ i) ≠ 0
    · have hnear : ∀ᶠ u in nhds v, ∀ i, u ⬝ᵥ (θ.read 0)ᵀ i ≠ 0 :=
        Filter.eventually_all.2 fun i =>
          ContinuousAt.eventually_ne (g := fun u : d → ℝ => u ⬝ᵥ (θ.read 0)ᵀ i)
            (continuous_id.dotProduct continuous_const).continuousAt (hv i)
      have hc := continuousAt_eq_lzf hσ hhom (θ.read 0) (X * θ.read 0 + η.read 0) (θ.write 0)
        W' X j hv
      have h := eq_zero_of_mem_closure_lzf hc (hturn v hv hact) hnear
        fun u hu huk => sub_eq_zero.2 (hind u huk hu j)
      exact h
    · push Not at hact
      have h1 : dBlock_lzf σ σ' (θ.read 0) (X * θ.read 0 + η.read 0) (θ.write 0) W' v j = 0 :=
        Finset.sum_eq_zero fun i _ => by
          simp only [hact i, deriv_eq_zero_of_eq_zero_lzf hσ hhom (hv i) (hact i), zero_mul,
            add_zero]
      have h2 : block_lzf σ (θ.read 0) (θ.write 0) v j = 0 :=
        Finset.sum_eq_zero fun i _ => by simp only [hact i, zero_mul]
      rw [h1, h2]
      ring
  -- Step 4 (b): `UnitsRescaleSphere` with the symmetric part `X_s = (X + Xᵀ)/2` of `X` (the same
  -- quadratic form): `X_s = c₀ I`, `ψc_i = λ_i c_i`, `β_i = k (c₀ − λ_i) a_i`
  have hsymm : ((1 / 2 : ℝ) • (X + Xᵀ))ᵀ = (1 / 2 : ℝ) • (X + Xᵀ) := by
    rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  obtain ⟨c₀, lam, hXs, hlam⟩ := hU (fun i => (θ.read 0)ᵀ i) (fun i => θ.write 0 i)
    ((1 / 2 : ℝ) • (X + Xᵀ)) (fun i => (X * θ.read 0 + η.read 0)ᵀ i) (fun i => W' i)
    hθ.row_ne_zero hθ.col_ne_zero hθ.col_not_collinear hsymm (by
      intro v hv
      have hq : (v ᵥ* ((1 / 2 : ℝ) • (X + Xᵀ))) ⬝ᵥ v = (v ᵥ* X) ⬝ᵥ v := by
        rw [Matrix.vecMul_smul, Matrix.vecMul_add, Matrix.vecMul_transpose, smul_dotProduct,
          add_dotProduct, dotProduct_comm (X *ᵥ v) v, Matrix.dotProduct_mulVec, smul_eq_mul]
        ring
      funext j
      have h := hall v hv j
      unfold dBlock_lzf block_lzf at h
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hq]
      linear_combination h)
  -- Step 4 (c): with `X₀ = X − c₀ I` (antisymmetric) and `α_i = λ_i − c₀`, the direction is
  -- `cobDir θ (X₀, Y) + scaleDir θ (c₀, c) + rescaleDirMlp k θ α`, component by component
  have hX₀ : (X - c₀ • 1)ᵀ = -(X - c₀ • 1) := by
    ext a b
    have h := congrFun (congrFun hXs a) b
    have h1 : (1 : Matrix d d ℝ) b a = (1 : Matrix d d ℝ) a b :=
      congrFun (congrFun (Matrix.transpose_one (n := d) (α := ℝ)) a) b
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul] at h
    simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
      smul_eq_mul, h1]
    linear_combination 2 * h
  obtain ⟨α, hα⟩ : ∃ α : ∀ ℓ : Fin 1, hid ℓ → ℝ, ∀ i, α 0 i = lam i - c₀ :=
    ⟨fun ℓ => Fin.cases (fun i => lam i - c₀) (fun l => l.elim0) ℓ, fun i => rfl⟩
  refine ⟨X - c₀ • 1, Y, c₀, c, α, hX₀, hYa, Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_, ?_⟩
  · show η.E = θ.E * (X - c₀ • 1) + c₀ • θ.E + 0
    rw [hEX, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, add_zero, sub_add_cancel]
  · obtain rfl := Subsingleton.elim ℓ 0
    ext a i
    have h1 : (X * θ.read 0) a i + η.read 0 a i = lam i * θ.read 0 a i :=
      congrFun (hlam i).1 a
    have h2 : ((X - c₀ • 1) * θ.read 0 : Matrix d (hid 0) ℝ) a i
        = (X * θ.read 0) a i - c₀ * θ.read 0 a i := by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul]
    show η.read 0 a i
      = -(((X - c₀ • 1) * θ.read 0 : Matrix d (hid 0) ℝ) a i) + 0 + α 0 i * θ.read 0 a i
    rw [h2, hα i]
    linear_combination h1
  · obtain rfl := Subsingleton.elim ℓ 0
    ext i a
    have h1 : η.write 0 i a - (θ.write 0 * (Y + c • 1) : Matrix (hid 0) d ℝ) i a
        = (k : ℝ) * (c₀ - lam i) * θ.write 0 i a := by
      rw [← Matrix.sub_apply, ← hW']
      exact congrFun (hlam i).2 a
    have h2 : (θ.write 0 * (Y + c • 1) : Matrix (hid 0) d ℝ) i a
        = (θ.write 0 * Y) i a + c * θ.write 0 i a := by
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul]
    show η.write 0 i a = (θ.write 0 * Y) i a + c * θ.write 0 i a
      + -((k : ℝ) * α 0 i) * θ.write 0 i a
    rw [hα i]
    linear_combination h1 + h2
  · show η.D = -(Y * θ.D) + 0 + 0
    rw [hDY, add_zero, add_zero]
  · rw [hρ, sub_add_cancel]


/-! ### Helpers: the directions of the symmetries, as a linear map, and their dimension -/

/-- Helper (copy of the private `skipDirLin_lzr`): the direction of the skips under the
rotations `X`: `S_ℓ ↦ −X_{ℓ-1} S_ℓ + S_ℓ X_ℓ`, linear in `X`. -/
private noncomputable def skipDirLin_lzf {L : ℕ} (S : Fin L → Matrix d d ℝ) :
    (Fin (L + 1) → Matrix d d ℝ) →ₗ[ℝ] (Fin L → Matrix d d ℝ) where
  toFun X ℓ := -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ
  map_add' X Y := by
    funext ℓ
    simp only [Pi.add_apply, Matrix.add_mul, Matrix.mul_add, neg_add]
    abel
  map_smul' c X := by
    funext ℓ
    simp only [Pi.smul_apply, Matrix.smul_mul, Matrix.mul_smul, smul_neg, smul_add,
      RingHom.id_apply]

/-- Helper (copy of the private `scaleDirLin_lzr`): `β ↦ scaleDir θ β` is linear. -/
private noncomputable def scaleDirLin_lzf {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut) :
    (Fin (L + 1) → ℝ) →ₗ[ℝ] Params A dIn dOut where
  toFun := scaleDir θ
  map_add' β β' := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.add_E, Params.add_read, Params.add_write, Params.add_D,
        Pi.add_apply, add_smul, add_zero]
  map_smul' c β := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        Pi.smul_apply, smul_eq_mul, mul_smul, smul_zero, RingHom.id_apply]

/-- Helper (copy of the private `scaleSkipLin_lzr`): the direction of the skips under the scales
`β`: `S_ℓ ↦ (β_ℓ − β_{ℓ-1}) S_ℓ`, linear in `β`. -/
private noncomputable def scaleSkipLin_lzf {L : ℕ} (S : Fin L → Matrix d d ℝ) :
    (Fin (L + 1) → ℝ) →ₗ[ℝ] (Fin L → Matrix d d ℝ) where
  toFun β ℓ := (β ℓ.succ - β ℓ.castSucc) • S ℓ
  map_add' β β' := by
    funext ℓ
    simp only [Pi.add_apply]
    rw [add_sub_add_comm, add_smul]
  map_smul' c β := by
    funext ℓ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← mul_sub, mul_smul]

/-- Helper: `α ↦ rescaleDirMlp k θ α` is linear (a copy of the private `rescaleLin_rzr`). -/
private noncomputable def rescaleLin_lzf (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    (∀ ℓ : Fin 1, hid ℓ → ℝ) →ₗ[ℝ]
      Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut where
  toFun := rescaleDirMlp k θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDirMlp]
    · intro ℓ
      ext a i
      simp only [rescaleDirMlp, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply]
      ring
    · intro ℓ
      ext i a
      simp only [rescaleDirMlp, Pi.add_apply, Params.add_write, Matrix.add_apply, Matrix.of_apply]
      ring
    · simp [rescaleDirMlp]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDirMlp]
    · intro ℓ
      ext a i
      simp only [rescaleDirMlp, Pi.smul_apply, Params.smul_read, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · intro ℓ
      ext i a
      simp only [rescaleDirMlp, Pi.smul_apply, Params.smul_write, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [rescaleDirMlp]

/-- Helper: the directions of the rotations and the scalings of `h_0` and `h_1` and of the
rescalings, with the matching directions of the skip,
`((X, β), α) ↦ (cobDir θ X + scaleDir θ β + rescaleDirMlp k θ α,
−X_0 A + A X_1 + (β_1 − β_0) A)` with `X_0`, `X_1` antisymmetric, as a linear map. -/
private noncomputable def dirLin_lzf (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (R : Fin 1 → Matrix d d ℝ) :
    ((Fin (1 + 1) → antisymmetric d) × (Fin (1 + 1) → ℝ)) × (∀ ℓ : Fin 1, hid ℓ → ℝ) →ₗ[ℝ]
      Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ) :=
  ((((cobDirLin θ).comp (LinearMap.compLeft (antisymmetric d).subtype (Fin (1 + 1)))).prod
      ((skipDirLin_lzf R).comp (LinearMap.compLeft (antisymmetric d).subtype (Fin (1 + 1))))).coprod
    ((scaleDirLin_lzf θ).prod (scaleSkipLin_lzf R))).coprod
    ((LinearMap.inl ℝ _ _).comp (rescaleLin_lzf k θ))

/-- Helper: the source of `dirLin_lzf` has dimension `(d(d−1) + 2) + s`. -/
private theorem finrank_dom_lzf :
    Module.finrank ℝ
        (((Fin (1 + 1) → antisymmetric d) × (Fin (1 + 1) → ℝ)) × (∀ ℓ : Fin 1, hid ℓ → ℝ))
      = (Fintype.card d * (Fintype.card d - 1) + 2) + Fintype.card (hid 0) := by
  rw [Module.finrank_prod, Module.finrank_prod,
    Module.finrank_pi_fintype (R := ℝ) (ι := Fin (1 + 1)) (M := fun _ => antisymmetric d),
    finrank_antisymmetric, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Module.finrank_fin_fun, Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  generalize Fintype.card d * (Fintype.card d - 1) = n at h2 ⊢
  omega

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: the weights and the skip have `P + d²` entries. -/
private theorem finrank_paramsSkip_lzf {A : Arch T d 1} :
    Module.finrank ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
      = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_matrix]
  simp [sq]

/-- Helper: the directions that are flat at every input of `learnedZeroDomain ∩ noKinkRMS θ` are
among the directions of `dirLin_lzf`. -/
private theorem flatSkipsOn_le_range_lzf {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescaleSphere σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det)
    (hturn : TurnsActiveRowsSkip θ (R 0))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* R 0, vanillaBlock σ (θ.read 0) (θ.write 0) v]) :
    flatSkipsOn (Arch.mlp σ (rmsNorm 0) hid)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
        (learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ R ∩ noKinkRMS θ)
      ≤ LinearMap.range (dirLin_lzf k θ R) := by
  rintro ⟨η, ρ⟩ hη
  obtain ⟨X₀, Y, c₀, c₁, α, hX₀, hY, rfl, hρ⟩ :=
    flatSkipsOn_noKink_le_mlp_rescale_learned_rmsNorm_zero hσ hhom hU θ hθ hd R hR hturn hw η ρ
      hη
  have hΨ : (LinearMap.compLeft (antisymmetric d).subtype (Fin (1 + 1)))
      ![⟨X₀, hX₀⟩, ⟨Y, hY⟩] = ![X₀, Y] := by
    funext i
    fin_cases i <;> rfl
  refine ⟨((![⟨X₀, hX₀⟩, ⟨Y, hY⟩], ![c₀, c₁]), α), Prod.ext ?_ (funext fun ℓ => ?_)⟩
  · show cobDirLin θ ((LinearMap.compLeft (antisymmetric d).subtype (Fin (1 + 1)))
        ![⟨X₀, hX₀⟩, ⟨Y, hY⟩]) + scaleDir θ ![c₀, c₁] + rescaleDirMlp k θ α = _
    rw [hΨ, cobDirLin_apply]
  · obtain rfl := Subsingleton.elim ℓ 0
    show skipDirLin_lzf R ((LinearMap.compLeft (antisymmetric d).subtype (Fin (1 + 1)))
        ![⟨X₀, hX₀⟩, ⟨Y, hY⟩]) 0 + scaleSkipLin_lzf R ![c₀, c₁] 0 + 0 = ρ 0
    rw [hΨ, hρ]
    show -(X₀ * R 0) + R 0 * Y + (c₁ - c₀) • R 0 + 0 = _
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, sub_smul, add_zero]
    abel

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", for one MLP block with a
positively homogeneous activation and a full learned skip, at one parameter:** under the
conditions of the proof, `funDimLearned = P + d² − (d(d−1) + 2) − s`, with `s` the number of
hidden units and `P` the number of weights without the skip. -/
theorem funDimLearned_mlp_oneBlock_rescale_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescaleSphere σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det)
    (hturn : TurnsActiveRowsSkip θ (R 0))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* R 0, vanillaBlock σ (θ.read 0) (θ.write 0) v]) :
    funDimLearned (Arch.mlp σ (rmsNorm 0) hid) (θ, R)
        + ((Fintype.card d * (Fintype.card d - 1) + 2) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- `≤`: the rotations and the scalings of `h_0` and `h_1` and the rescalings of the hidden
  -- units are flat and independent (no read column is zero)
  have hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0 := fun ℓ i => by
    obtain rfl := Subsingleton.elim ℓ 0
    exact hθ.col_ne_zero i
  obtain ⟨V, hVle, -, hVdim⟩ := mlp_part_ubr hhom θ hc
  have hle := funDimLearned_add_le_rmsNorm_zero'
    (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) rfl (θ, R) hθ.rank_E hR V hVle
  rw [hVdim, Fin.sum_univ_one] at hle
  -- `≥`: the flat directions lie in the directions flat on `learnedZeroDomain ∩ noKinkRMS θ`,
  -- which are in the range of `dirLin_lzf`
  have hflat := (flatSkips_le_flatSkipsOn (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid)
    (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
    (learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ R ∩ noKinkRMS θ)).trans
    (flatSkipsOn_le_range_lzf hσ hhom hU θ hθ hd R hR hturn hw)
  -- `fd + dim K = P + d²`
  have h : funDimLearned (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) (θ, R)
      + Module.finrank ℝ (flatSkips (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ)) :=
    funDimSkips_add_finrank_flatSkips' _ _ (θ, R)
  have hmono := Submodule.finrank_mono hflat
  have hdim := (LinearMap.finrank_range_le (dirLin_lzf k θ R)).trans_eq finrank_dom_lzf
  have hP := finrank_paramsSkip_lzf
    (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) (dIn := dIn) (dOut := dOut)
  generalize Fintype.card d * (Fintype.card d - 1) = N at hle hdim ⊢
  generalize Fintype.card d ^ 2 = Q at hle hP ⊢
  omega


/-! ### Helpers: differentiability at the inputs off the kinks (copies of the private `_lzt`
helpers of `OneBlock/LearnedSkipTriangularRMSZeroBound.lean`) -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `differentiableAt_matMul_lzt`): the product of two matrix-valued
maps that are differentiable at a point is differentiable there. -/
private theorem differentiableAt_matMul_lzf {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : P → Matrix m n ℝ} {g : P → Matrix n p ℝ} {y : P}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    DifferentiableAt ℝ (fun y => f y * g y) y := by
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

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (a copy of the private `eval_eq_lzt`): the function of one block under pre-RMSNorm
with the skip `S 0`, `F(x) = N_0(x E S + f(N_0(x E) W_read) W_write) D`. -/
private theorem eval_eq_lzf {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (S : Fin 1 → Matrix d d ℝ) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    eval A S θ x = rmsNorm 0 (x * θ.E * S 0
      + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) * θ.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]

omit [Nonempty T] [DecidableEq d] in
/-- Helper (a copy of the private `differentiableAt_evalSkips_lzt`): at an input `x` at which no
normalized row vanishes and `f` is differentiable at `N_0(x E) W_read`, the output with the full
learned skip is a differentiable function of `(θ, R)`. -/
private theorem differentiableAt_evalSkips_lzf {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ)
    (x : Matrix T dIn ℝ) (hx : x ∈ learnedZeroDomain A θ R)
    (hfx : DifferentiableAt ℝ (A.f 0) (rmsNorm 0 (x * θ.E) * θ.read 0)) :
    DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x) (θ, R) := by
  have e : (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x)
      = fun p => rmsNorm 0 (x * p.1.E * p.2 0
          + A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0) * p.1.write 0) * p.1.D :=
    funext fun p => eval_eq_lzf hA p.2 p.1 x
  rw [e]
  -- the weights and the skip are linear, hence differentiable, functions of `(θ, R)`
  have hE : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.E) (θ, R) :=
    ((LinearMap.toContinuousLinearMap (Params.linE (A := A) (dIn := dIn) (dOut := dOut))).comp
      (ContinuousLinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))).differentiableAt
  have hR : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.read 0) (θ, R) :=
    ((LinearMap.toContinuousLinearMap
      (Params.linRead (A := A) (dIn := dIn) (dOut := dOut) 0)).comp
      (ContinuousLinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))).differentiableAt
  have hW : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.write 0) (θ, R) :=
    ((LinearMap.toContinuousLinearMap
      (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) 0)).comp
      (ContinuousLinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))).differentiableAt
  have hD : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.D) (θ, R) :=
    ((LinearMap.toContinuousLinearMap (Params.linD (A := A) (dIn := dIn) (dOut := dOut))).comp
      (ContinuousLinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))).differentiableAt
  have hS : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.2 0) (θ, R) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix d d ℝ) 0).comp
      (ContinuousLinearMap.snd ℝ (Params A dIn dOut) _)).differentiableAt
  -- `x E`, `N_0(x E)` (no row of `x E` is zero), `N_0(x E) W_read`, `f(…)`
  have h1 : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => x * p.1.E) (θ, R) :=
    differentiableAt_matMul_lzf (differentiableAt_const x) hE
  have h2 : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => rmsNorm 0 (x * p.1.E)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E) (θ, R) (analyticAt_rmsNorm_zero (x * θ.E) hx.1).differentiableAt h1
  have h3 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm 0 (x * p.1.E) * p.1.read 0) (θ, R) :=
    differentiableAt_matMul_lzf h2 hR
  have h4 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm 0 (x * p.1.E) * p.1.read 0) (θ, R) hfx h3
  -- `h_1 = x E S + f(…) W_write`, `N_0(h_1)` (no row of `h_1` is zero) and `N_0(h_1) D`
  have h5 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E * p.2 0 + A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0) * p.1.write 0) (θ, R) :=
    (differentiableAt_matMul_lzf h1 hS).add (differentiableAt_matMul_lzf h4 hW)
  have h6 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm 0 (x * p.1.E * p.2 0
        + A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0) * p.1.write 0)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E * p.2 0 + A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0) * p.1.write 0) (θ, R)
      (analyticAt_rmsNorm_zero _ hx.2).differentiableAt h5
  exact differentiableAt_matMul_lzf h6 hD

omit [Nonempty T] [DecidableEq d] in
/-- Helper: at an input of `learnedZeroDomain ∩ noKinkRMS θ` the output is differentiable in the
weights and the skip: the pre-activations `N_0(x E) W_read` have no zero entry, as `N_0` scales
the rows of `x E` by positive numbers. -/
private theorem differentiableAt_noKink_lzf (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (R : Fin 1 → Matrix d d ℝ) (x : Matrix T dIn ℝ)
    (hx : x ∈ learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ R ∩ noKinkRMS θ) :
    DifferentiableAt ℝ (fun p : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ) =>
      evalSkips (Arch.mlp σ (rmsNorm 0) hid) (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ))
        p x) (θ, R) := by
  have hP : ∀ t i, (rmsNorm 0 (x * θ.E) * θ.read 0) t i ≠ 0 := fun t i => by
    rw [rmsNorm_mul_apply_lzf]
    exact mul_ne_zero (inv_sqrt_pos_lzf (hx.1.1 t)).ne' (hx.2 t i)
  exact differentiableAt_evalSkips_lzf rfl θ R x hx.1 (differentiableAt_map_lzf hσ hP)

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", in the paper's own
sense, for one MLP block with a positively homogeneous activation and a full learned skip, at
one parameter:** a finite batch of inputs at which no normalized row vanishes and no hidden unit
sits at its kink, on which the Jacobian in the weights and the skip has the rank
`P + d² − (d(d−1) + 2) − s`. -/
theorem exists_jacobianRankSkips_mlp_oneBlock_rescale_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescaleSphere σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → Matrix d d ℝ) (hR : IsUnit (R 0).det)
    (hturn : TurnsActiveRowsSkip θ (R 0))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v ᵥ* R 0, vanillaBlock σ (θ.read 0) (θ.write 0) v]) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ R ∩ noKinkRMS θ) ∧
      jacobianRankSkips (Arch.mlp σ (rmsNorm 0) hid)
          (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X (θ, R)
          + ((Fintype.card d * (Fintype.card d - 1) + 2) + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
          + Fintype.card d ^ 2 := by
  -- a batch of inputs of `U = learnedZeroDomain ∩ noKinkRMS θ`, where the output is
  -- differentiable in the weights and the skip, with the rank `P + d² − dim K_U(θ, A)`
  obtain ⟨n, X, hX, h⟩ := exists_jacobianRankSkips_add_finrank_flatSkipsOn
    (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid)
    (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
    (learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ R ∩ noKinkRMS θ)
    (fun x hx => differentiableAt_noKink_lzf hσ θ R x hx)
  -- the sandwich: `dim K ≤ dim K_U ≤ d(d−1) + 2 + s = dim K`
  have hfd := funDimLearned_mlp_oneBlock_rescale_rmsNorm_zero hσ hhom hU θ hθ hd R hR hturn hw
  have h' : funDimLearned (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) (θ, R)
      + Module.finrank ℝ (flatSkips (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
        × (Fin 1 → Matrix d d ℝ)) :=
    funDimSkips_add_finrank_flatSkips' _ _ (θ, R)
  have h1 := Submodule.finrank_mono (flatSkips_le_flatSkipsOn
    (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid)
    (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
    (learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ R ∩ noKinkRMS θ))
  have h2 := Submodule.finrank_mono (flatSkipsOn_le_range_lzf hσ hhom hU θ hθ hd R hR hturn hw)
  have h3 := (LinearMap.finrank_range_le (dirLin_lzf k θ R)).trans_eq finrank_dom_lzf
  have hP := finrank_paramsSkip_lzf
    (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) (dIn := dIn) (dOut := dOut)
  refine ⟨n, X, hX, ?_⟩
  generalize Fintype.card d * (Fintype.card d - 1) = N at hfd h3 ⊢
  omega

end Skips
