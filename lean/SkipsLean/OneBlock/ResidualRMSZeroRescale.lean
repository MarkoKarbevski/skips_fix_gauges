import SkipsLean.OneBlock.ResidualRMSZeroStepsOn
import SkipsLean.OneBlock.ResidualRMSRescale
import SkipsLean.Residual.UpperBoundRescaleRMSNormZero
import SkipsLean.Absorb.Block

/-!
# One residual ReLU or ReLU² block under pre-RMSNorm with `ε = 0`: the functional dimension

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`".

Its proof, "The residual network": "The case `ε = 0` of part (iii), with `A = I`, shows that a
flat direction is the sum of a direction of the rotation and scaling of all hidden states and a
direction `ψ` of the weights of the block along which `B` has derivative zero on the sphere of
radius `√d_model`. This derivative is positively homogeneous of degree `k` in `n`, so it vanishes
for all `n ≠ 0`, and Lemma B.3, with `E` and `D` replaced by the identity and `M = 0`, makes `ψ` a
rescaling of the units. So `dim K(θ) = d_model (d_model − 1)/2 + 1 + s`."

The case `ε = 0` of part (iii) gives the zero derivative only at the inputs `w` at which `w E` and
`g(w)` are linearly independent ("The constant terms then give `μ = c` wherever `w E A` and `g(w)`
are linearly independent"; `OneBlock/ResidualRMSZeroStepsOn.lean`). To pass to all inputs off the
kinks, the proof needs one more condition on the parameters, which the paper does not state: the
block turns a dense set of the rows at which some hidden unit is active (`TurnsActiveRows`). At a
row where no unit is active the derivative of the block along any direction is zero; elsewhere
the derivative is continuous off the kinks and vanishes on a dense set. The condition holds at
almost every parameter for ReLU and ReLU² blocks (`OneBlock/ResidualRMSZeroRescaleGeneric.lean`).

Here, for one MLP block with a positively homogeneous activation (twin of
`OneBlock/ResidualRMSRescale.lean` for `ε > 0`), at one parameter under the conditions of the
proof: the flat directions at the paper's inputs (no normalized row vanishes, no hidden unit at
its kink) are a rotation and a scaling of both hidden states plus a rescaling of the hidden units;
the value of Lean's `funDim`; a finite batch of the paper's inputs on which the Jacobian has this
rank. No width of the block is asked.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **The block turns a dense set of the rows at which some hidden unit is active:** every row
`v` with no hidden unit at its kink (no entry of `v W_read` is zero) and with some active unit
(`σ` of an entry of `v W_read` is not zero) is a limit of rows `u` such that `u` and the output
`σ(u W_read) W_write` of the block at `u` are linearly independent. -/
def TurnsActiveRows (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) : Prop :=
  ∀ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) → (∃ i, σ ((v ᵥ* θ.read 0) i) ≠ 0) →
    v ∈ closure {u : d → ℝ |
      LinearIndependent ℝ ![u, vanillaBlock σ (θ.read 0) (θ.write 0) u]}

section HelpersRzr

open Filter
open scoped Topology

/-! ### The activation away from its kink (copies of the `_rres` helpers of
`OneBlock/ResidualRMSRescale.lean`) -/

/-- Helper: the matrices with no zero entry (for a ReLU-type block: the pre-activations with no
hidden unit at its kink). -/
private def noZero_rzr (m n : Type*) : Set (Matrix m n ℝ) :=
  {M | ∀ t i, M t i ≠ 0}

/-- Helper: the matrices with no zero entry form an open set. -/
private theorem isOpen_noZero_rzr {m n : Type*} [Fintype m] [Fintype n] :
    IsOpen (noZero_rzr m n) := by
  refine isOpen_iff_mem_nhds.2 fun M hM => ?_
  exact Filter.eventually_all.2 fun t => Filter.eventually_all.2 fun i =>
    (continuous_id.matrix_elem t i).continuousAt.eventually_ne (hM t i)

/-- Helper: a positively homogeneous `σ` is a monomial on each side of `0` (`σ y = y^k σ(1)` for
`y > 0`, `σ y = (-y)^k σ(-1)` for `y < 0`), hence `C¹` at every `z ≠ 0`. -/
private theorem contDiffAt_of_homogeneous_rzr {k : ℕ}
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
private theorem contDiffOn_map_rzr {k : ℕ}
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {m n : Type*} [Fintype m]
    [Fintype n] : ContDiffOn ℝ 1 (fun M : Matrix m n ℝ => M.map σ) (noZero_rzr m n) := by
  intro M hM
  refine ContDiffAt.contDiffWithinAt (contDiffAt_pi.2 fun t => contDiffAt_pi.2 fun i => ?_)
  have hent : ContDiff ℝ 1 (fun M : Matrix m n ℝ => M t i) :=
    contDiff_pi.1 (contDiff_pi.1 contDiff_id t) i
  have h := (contDiffAt_of_homogeneous_rzr hhom (hM t i)).comp M hent.contDiffAt
  exact h

/-- Helper: `M ↦ σ(M)` (entrywise) is differentiable at a matrix with no zero entry. -/
private theorem differentiableAt_map_rzr (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {m n : Type*} [Fintype m] [Fintype n] {P : Matrix m n ℝ} (hP : ∀ t i, P t i ≠ 0) :
    DifferentiableAt ℝ (fun M : Matrix m n ℝ => M.map σ) P := by
  refine differentiableAt_pi.2 fun t => differentiableAt_pi.2 fun i => ?_
  have hent : Differentiable ℝ (fun M : Matrix m n ℝ => M t i) :=
    differentiable_pi.1 (differentiable_pi.1 differentiable_id t) i
  have h := (hσ _ (hP t i)).differentiableAt.comp P (hent P)
  exact h

/-- Helper: at a matrix `P` with no zero entry, the derivative of `M ↦ σ(M)` along `Q` has the
entries `σ'(P_{t i}) Q_{t i}`. -/
private theorem fderiv_map_apply_rzr (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {m n : Type*} [Fintype m] [Fintype n] {P : Matrix m n ℝ} (hP : ∀ t i, P t i ≠ 0)
    (Q : Matrix m n ℝ) (t : m) (i : n) :
    fderiv ℝ (fun M : Matrix m n ℝ => M.map σ) P Q t i = σ' (P t i) * Q t i := by
  -- the chain rule along the line `τ ↦ P + τ Q`
  have hline : HasDerivAt (fun τ : ℝ => P + τ • Q) Q 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const Q).const_add P
    rw [one_smul] at h
    exact h
  have h0 : P = P + (0 : ℝ) • Q := by rw [zero_smul, add_zero]
  have h1 := (differentiableAt_map_rzr hσ hP).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0
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
private theorem f_apply_rzr {χ : Matrix T d ℝ → Matrix T d ℝ} (P : Matrix T (hid 0) ℝ) (t : T)
    (i : hid 0) : (Arch.mlp (T := T) (d := d) σ χ hid).f 0 P t i = σ (P t i) := rfl

omit [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper: the same derivative for the map of the block. -/
private theorem fderiv_f_rzr (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {χ : Matrix T d ℝ → Matrix T d ℝ} {P : Matrix T (hid 0) ℝ} (hP : ∀ t i, P t i ≠ 0)
    (Q : Matrix T (hid 0) ℝ) (t : T) (i : hid 0) :
    fderiv ℝ ((Arch.mlp (T := T) (d := d) σ χ hid).f 0) P Q t i = σ' (P t i) * Q t i :=
  fderiv_map_apply_rzr hσ hP Q t i

/-- Helper: differentiating `σ(λ z) = λ^k σ(z)` in `z ≠ 0` gives `λ σ'(λ z) = λ^k σ'(z)`. -/
private theorem mul_deriv_homogeneous_rzr {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
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

/-! ### The activation near a point `z ≠ 0` -/

/-- Helper: near `z ≠ 0` the quotient `y / z` is positive. -/
private theorem eventually_div_pos_rzr {z : ℝ} (hz : z ≠ 0) : ∀ᶠ y in 𝓝 z, 0 < y / z := by
  rcases hz.lt_or_gt with hneg | hpos
  · filter_upwards [eventually_lt_nhds hneg] with y hy
    exact div_pos_of_neg_of_neg hy hneg
  · filter_upwards [eventually_gt_nhds hpos] with y hy
    exact div_pos hy hpos

/-- Helper: a positively homogeneous `σ` that vanishes at `z ≠ 0` vanishes on the half-line of
`z`, so `σ'(z) = 0` (an inactive unit has derivative zero). -/
private theorem deriv_eq_zero_of_eq_zero_rzr {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {z : ℝ} (hz : z ≠ 0)
    (h0 : σ z = 0) : σ' z = 0 := by
  -- `σ(y) = (y/z)^k σ(z) = 0` for `y` near `z`
  have h : σ =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_div_pos_rzr hz] with y hy
    have e := hhom (y / z) z hy
    rwa [div_mul_cancel₀ y hz, h0, mul_zero] at e
  exact (hσ z hz).unique ((hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq h)

/-- Helper: `σ'` is continuous at every `z ≠ 0`: near `z`, `σ'(y) = (y/z)^k σ'(z) / (y/z)`. -/
private theorem continuousAt_deriv_rzr {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {z : ℝ} (hz : z ≠ 0) :
    ContinuousAt σ' z := by
  have h1 : ContinuousAt (fun y : ℝ => y / z) z := continuousAt_id.div_const z
  have hc : ContinuousAt (fun y : ℝ => (y / z) ^ k * σ' z / (y / z)) z :=
    ((h1.pow k).mul continuousAt_const).div h1 (div_ne_zero hz hz)
  refine hc.congr ?_
  filter_upwards [eventually_div_pos_rzr hz] with y hy
  -- `(y/z) σ'(y) = (y/z)^k σ'(z)` by homogeneity
  have e := mul_deriv_homogeneous_rzr hσ hhom hy hz
  rw [div_mul_cancel₀ y hz] at e
  rw [← e]
  exact mul_div_cancel_left₀ _ hy.ne'

omit [DecidableEq d] in
/-- Helper: the derivative `D_ψ(v)_j = ∑_i (σ(v c_i) ψ_{a_i j} + σ'(v c_i) (v ψ_{c_i}) a_{i j})`
of the block along `ψ` is continuous in the row `v` at a row off the kinks. -/
private theorem continuousAt_D_rzr {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {q : Type*} [Fintype q]
    (Wr R : Matrix d q ℝ) (W' Ww : Matrix q d ℝ) (j : d) {u : d → ℝ}
    (hu : ∀ i, u ⬝ᵥ Wrᵀ i ≠ 0) :
    ContinuousAt (fun v : d → ℝ => ∑ i : q, (σ (v ⬝ᵥ Wrᵀ i) * W' i j
      + σ' (v ⬝ᵥ Wrᵀ i) * (v ⬝ᵥ Rᵀ i) * Ww i j)) u := by
  have hdot : ∀ c : d → ℝ, Continuous fun v : d → ℝ => v ⬝ᵥ c := fun c =>
    continuous_id.dotProduct continuous_const
  have hterm : ∀ i, ContinuousAt (fun v : d → ℝ => σ (v ⬝ᵥ Wrᵀ i) * W' i j
      + σ' (v ⬝ᵥ Wrᵀ i) * (v ⬝ᵥ Rᵀ i) * Ww i j) u := by
    intro i
    have h1 : ContinuousAt (fun v : d → ℝ => σ (v ⬝ᵥ Wrᵀ i)) u :=
      ContinuousAt.comp (f := fun v : d → ℝ => v ⬝ᵥ Wrᵀ i) (x := u) (hσ _ (hu i)).continuousAt
        (hdot _).continuousAt
    have h2 : ContinuousAt (fun v : d → ℝ => σ' (v ⬝ᵥ Wrᵀ i)) u :=
      ContinuousAt.comp (f := fun v : d → ℝ => v ⬝ᵥ Wrᵀ i) (x := u)
        (continuousAt_deriv_rzr hσ hhom (hu i)) (hdot _).continuousAt
    exact (h1.mul continuousAt_const).add ((h2.mul (hdot _).continuousAt).mul continuousAt_const)
  have h := tendsto_finsetSum (f := fun (i : q) (v : d → ℝ) => σ (v ⬝ᵥ Wrᵀ i) * W' i j
    + σ' (v ⬝ᵥ Wrᵀ i) * (v ⬝ᵥ Rᵀ i) * Ww i j) Finset.univ fun i _ => hterm i
  exact h

/-- Helper: a function continuous at a point `u` of the closure of `S` that vanishes at the
points of `S` with a property `P` holding near `u` vanishes at `u`. -/
private theorem eq_zero_of_mem_closure_rzr {X : Type*} [TopologicalSpace X] {F : X → ℝ} {u : X}
    {S : Set X} {P : X → Prop} (hF : ContinuousAt F u) (hu : u ∈ closure S)
    (hP : ∀ᶠ v in 𝓝 u, P v) (h0 : ∀ v ∈ S, P v → F v = 0) : F u = 0 := by
  by_contra hne
  obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ := mem_closure_iff_nhds.1 hu _ ((hF.eventually_ne hne).and hP)
  exact hv1 (h0 v hv3 hv2)

/-! ### The normalized rows and the block on one row -/

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `N_0` scales every row: `(N_0(h) W)_{t i} = (‖h_t‖²/d)^{-1/2} (h W)_{t i}`. -/
private theorem rmsNorm_mul_apply_rzr {n : Type*} [Fintype n] (h : Matrix T d ℝ)
    (W : Matrix d n ℝ) (t : T) (i : n) :
    (rmsNorm 0 h * W) t i
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + 0))⁻¹ * (h * W) t i := by
  simp only [Matrix.mul_apply, Finset.mul_sum, rmsNorm, rmsRow, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul, mul_assoc]

omit [DecidableEq d] in
/-- Helper: the factor of `N_0` at a row `v ≠ 0` is positive. -/
private theorem inv_sqrt_pos_rzr {v : d → ℝ} (hv : v ≠ 0) :
    0 < (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + 0))⁻¹ := by
  have h1 : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j))
      (fun h => hv (dotProduct_self_eq_zero.1 h.symm))
  obtain ⟨j, -⟩ := Function.ne_iff.1 hv
  have h2 : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩)
  rw [add_zero]
  exact inv_pos.2 (Real.sqrt_pos.2 (div_pos h1 h2))

omit [DecidableEq d] in
/-- Helper: the block on one row is positively homogeneous: `b(s u) = s^k b(u)` for `s > 0`. -/
private theorem vanillaBlock_smul_rzr {k : ℕ}
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
/-- Helper: at a row `h_t ≠ 0`, the row `t` of the block `σ(N_0(h) W_read) W_write` is
`s^k b(h_t)`, with `s = (‖h_t‖²/d)^{-1/2} > 0`. -/
private theorem row_block_rzr {k : ℕ}
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {q : Type*} [Fintype q]
    (Wr : Matrix d q ℝ) (Ww : Matrix q d ℝ) (h : Matrix T d ℝ) (t : T) (ht : h t ≠ 0) :
    ((rmsNorm 0 h * Wr).map σ * Ww) t
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + 0))⁻¹ ^ k
        • vanillaBlock σ Wr Ww (h t) := by
  rw [map_mul_mul_row]
  exact vanillaBlock_smul_rzr hhom Wr Ww (h t) (inv_sqrt_pos_rzr ht)

/-- Helper: scaling the second vector of an independent pair by `r ≠ 0` keeps it independent. -/
private theorem linearIndependent_pair_smul_rzr {V : Type*} [AddCommGroup V] [Module ℝ V]
    {a b : V} (h : LinearIndependent ℝ ![a, b]) {r : ℝ} (hr : r ≠ 0) :
    LinearIndependent ℝ ![a, r • b] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  obtain ⟨h1, h2⟩ := h s (t * r) (by rw [mul_smul]; exact hst)
  exact ⟨h1, (mul_eq_zero.1 h2).resolve_right hr⟩

end HelpersRzr

/-- **Proof of Theorem B.1 (iv) of the skips paper, "The residual network", for ReLU-type MLP
blocks:** let `ε = 0`, `d ≥ 2`, let `σ` be differentiable off `0` and positively homogeneous of
degree `k`, with Lemma B.3 in the form `UnitsRescale`; under the conditions `OneBlockGenericRMS`,
if the block turns a dense set of the active rows and turns some row off the kinks, then a
direction that is flat at every input at which no normalized row vanishes and no hidden unit sits
at its kink is the direction of a rotation and of a scaling shared by `h_0` and `h_1`, plus a
rescaling of the hidden units. -/
theorem flatOn_noKink_le_mlp_rescale_residual_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d) (hturn : TurnsActiveRows θ)
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v, vanillaBlock σ (θ.read 0) (θ.write 0) v])
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.mlp σ (rmsNorm 0) hid) 1 θ
      (residualZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ)) :
    ∃ (Y : Matrix d d ℝ) (c : ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
      η = cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c) + rescaleDirMlp k θ α := by
  classical
  -- `x ↦ x E` is onto, through a left inverse `B` of `E`
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hθ.rank_E)
  have hxE : ∀ u : d → ℝ, (Matrix.of fun _ : T => u) * B * θ.E = Matrix.of fun _ : T => u :=
    fun u => by rw [Matrix.mul_assoc, hB, Matrix.mul_one]
  -- the input with every row `u'`, `u' E = u`, for a row `u` off the kinks with `u`, `b(u)`
  -- independent: no entry of `x E W_read` is zero, and for every token the rows `u` of `x E` and
  -- `b(N_0(u)) = s^k b(u)` (`s > 0`) of `g(x)` are independent
  have hgood : ∀ u : d → ℝ, (∀ i, (u ᵥ* θ.read 0) i ≠ 0) →
      LinearIndependent ℝ ![u, vanillaBlock σ (θ.read 0) (θ.write 0) u] →
      (Matrix.of fun _ : T => u) * B * θ.E * θ.read 0 ∈ noZero_rzr T (hid 0) ∧
      ∀ t, LinearIndependent ℝ ![((Matrix.of fun _ : T => u) * B * θ.E) t,
        ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f 0
          (rmsNorm 0 ((Matrix.of fun _ : T => u) * B * θ.E) * θ.read 0) * θ.write 0) t] := by
    intro u hu hli
    rw [hxE]
    refine ⟨fun t i => hu i, fun t => ?_⟩
    have hu0 : u ≠ 0 := hli.ne_zero 0
    have e : ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f 0
          (rmsNorm 0 (Matrix.of fun _ : T => u) * θ.read 0) * θ.write 0) t
        = (Real.sqrt ((u ⬝ᵥ u) / (Fintype.card d : ℝ) + 0))⁻¹ ^ k
          • vanillaBlock σ (θ.read 0) (θ.write 0) u :=
      row_block_rzr hhom (θ.read 0) (θ.write 0) (Matrix.of fun _ : T => u) t hu0
    rw [e]
    exact linearIndependent_pair_smul_rzr hli (pow_ne_zero _ (inv_sqrt_pos_rzr hu0).ne')
  -- Steps 1 to 3 (the case `ε = 0` of part (iii)) on the cone of pre-activations with no zero
  -- entry, which is open and invariant under positive scalings of the rows, and on which the
  -- block map is `C¹`: `η_E = E (Y + c I)`, `η_D = -Y D`, and the derivative of the block along
  -- `ψ` vanishes at `N_0(x E)` for every input whose rows of `x E` and `g(x)` are independent
  obtain ⟨v₀, hv₀, hli₀⟩ := hw
  obtain ⟨Y, c, hYa, hEY, hDY, hF⟩ := exists_antisymm_scale_of_flatOn_residual_rmsNorm_zero_on
    (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) rfl hd (noZero_rzr T (hid 0))
    isOpen_noZero_rzr (fun M hM c hc t i => mul_ne_zero (hc t).ne' (hM t i))
    (contDiffOn_map_rzr hhom) θ hθ.rank_E hθ.rank_D ⟨_, hgood v₀ hv₀ hli₀⟩ η hη
  generalize hR' : η.read 0 + Y * θ.read 0 = R' at hF
  generalize hW' : η.write 0 - θ.write 0 * (Y + c • 1) = W' at hF
  -- Step 4 (a), one row: at a row `v` off the kinks with `v`, `b(v)` independent, the block
  -- equation at the input with every row `v'`, `v' E = v`; the normalization scales `v` by
  -- `s > 0`, and by homogeneity the equation at `s v` is `s^k` times the equation at `v`
  have hind : ∀ v : d → ℝ, (∀ i, v ⬝ᵥ (θ.read 0)ᵀ i ≠ 0) →
      LinearIndependent ℝ ![v, vanillaBlock σ (θ.read 0) (θ.write 0) v] → ∀ j : d,
      ∑ i : hid 0, (σ (v ⬝ᵥ (θ.read 0)ᵀ i) * W' i j
        + σ' (v ⬝ᵥ (θ.read 0)ᵀ i) * (v ⬝ᵥ R'ᵀ i) * θ.write 0 i j) = 0 := by
    intro v hv hli j
    obtain ⟨hx, hxi⟩ := hgood v hv hli
    have e := hF _ hx hxi
    rw [hxE] at e
    have hv0 : v ≠ 0 := hli.ne_zero 0
    obtain ⟨s, hs, hsP⟩ : ∃ s : ℝ, 0 < s ∧ ∀ (W : Matrix d (hid 0) ℝ) (i : hid 0),
        (rmsNorm 0 (Matrix.of fun _ : T => v) * W) (Classical.arbitrary T) i
          = s * (v ⬝ᵥ Wᵀ i) :=
      ⟨_, inv_sqrt_pos_rzr hv0, fun W i => by rw [rmsNorm_mul_apply_rzr]; rfl⟩
    have hP : ∀ t i, (rmsNorm 0 (Matrix.of fun _ : T => v) * θ.read 0) t i ≠ 0 := by
      intro t i
      rw [rmsNorm_mul_apply_rzr]
      exact mul_ne_zero (inv_sqrt_pos_rzr hv0).ne' (hv i)
    have e2 := congrFun (congrFun e (Classical.arbitrary T)) j
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib,
      Matrix.zero_apply] at e2
    have key : ∀ i : hid 0, fderiv ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f 0)
        (rmsNorm 0 (Matrix.of fun _ : T => v) * θ.read 0)
        (rmsNorm 0 (Matrix.of fun _ : T => v) * R') (Classical.arbitrary T) i * θ.write 0 i j
        + (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f 0
          (rmsNorm 0 (Matrix.of fun _ : T => v) * θ.read 0) (Classical.arbitrary T) i * W' i j
        = s ^ k * (σ (v ⬝ᵥ (θ.read 0)ᵀ i) * W' i j
          + σ' (v ⬝ᵥ (θ.read 0)ᵀ i) * (v ⬝ᵥ R'ᵀ i) * θ.write 0 i j) := by
      intro i
      rw [fderiv_f_rzr hσ hP, f_apply_rzr, hsP, hsP, hhom s _ hs]
      have hdv := mul_deriv_homogeneous_rzr hσ hhom hs (hv i)
      linear_combination ((v ⬝ᵥ R'ᵀ i) * θ.write 0 i j) * hdv
    have e3 : ∑ i : hid 0, s ^ k * (σ (v ⬝ᵥ (θ.read 0)ᵀ i) * W' i j
        + σ' (v ⬝ᵥ (θ.read 0)ᵀ i) * (v ⬝ᵥ R'ᵀ i) * θ.write 0 i j) = 0 :=
      (Finset.sum_congr rfl fun i _ => (key i).symm).trans e2
    rw [← Finset.mul_sum] at e3
    exact (mul_eq_zero.1 e3).resolve_left (pow_ne_zero _ hs.ne')
  -- Step 4 (a), every row off the kinks: if some unit is active at `v`, then `v` is a limit of
  -- rows `u` with `u`, `b(u)` independent (`hturn`), and the derivative is continuous off the
  -- kinks; if no unit is active, `σ` and `σ'` vanish at every pre-activation of `v`
  have hall : ∀ v : d → ℝ, (∀ i, v ⬝ᵥ (θ.read 0)ᵀ i ≠ 0) → ∀ j : d,
      ∑ i : hid 0, (σ (v ⬝ᵥ (θ.read 0)ᵀ i) * W' i j
        + σ' (v ⬝ᵥ (θ.read 0)ᵀ i) * (v ⬝ᵥ R'ᵀ i) * θ.write 0 i j) = 0 := by
    intro v hv j
    by_cases hact : ∃ i, σ (v ⬝ᵥ (θ.read 0)ᵀ i) ≠ 0
    · have hnear : ∀ᶠ u in nhds v, ∀ i, u ⬝ᵥ (θ.read 0)ᵀ i ≠ 0 :=
        Filter.eventually_all.2 fun i =>
          ContinuousAt.eventually_ne (g := fun u : d → ℝ => u ⬝ᵥ (θ.read 0)ᵀ i)
            (continuous_id.dotProduct continuous_const).continuousAt (hv i)
      have h := eq_zero_of_mem_closure_rzr
        (continuousAt_D_rzr hσ hhom (θ.read 0) R' W' (θ.write 0) j hv) (hturn v hv hact) hnear
        fun u hu huk => hind u huk hu j
      exact h
    · push Not at hact
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hact i, deriv_eq_zero_of_eq_zero_rzr hσ hhom (hv i) (hact i)]
      ring
  -- Step 4 (b): Lemma B.3 with `E`, `D` the identity and `M = 0`: every hidden unit is only
  -- rescaled, `ψ_{c_i} = λ_i c_i` and `ψ_{a_i} = -k λ_i a_i`
  obtain ⟨-, -, lam, hlam⟩ := hU (fun i => (θ.read 0)ᵀ i) 0 (fun i => θ.write 0 i) 0 0
    (fun i => R'ᵀ i) 0 (fun i => W' i) hθ.row_ne_zero hθ.col_ne_zero hθ.col_not_collinear (by
      intro v hv
      have hv' : ∀ i, v ⬝ᵥ (θ.read 0)ᵀ i ≠ 0 := fun i => by
        have h := hv i
        simp only [Pi.zero_apply, add_zero] at h
        exact h
      funext j
      have h := hall v hv' j
      simp only [Matrix.vecMul_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, add_zero, zero_add]
      exact h)
  -- Step 4 (c): `η = cobDir θ (Y, Y) + scaleDir θ (c, c) + rescaleDirMlp k θ α`, component by
  -- component
  obtain ⟨α, hα⟩ : ∃ α : ∀ ℓ : Fin 1, hid ℓ → ℝ, α 0 = lam :=
    ⟨fun ℓ => Fin.cases lam (fun l => l.elim0) ℓ, rfl⟩
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at hW'
  refine ⟨Y, c, α, hYa, Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_⟩
  · show η.E = θ.E * Y + c • θ.E + 0
    rw [hEY, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, add_zero]
  · obtain rfl := Subsingleton.elim ℓ 0
    ext a i
    have h1 : R' a i = lam i * θ.read 0 a i := congrFun (hlam i).1 a
    have h2 : η.read 0 a i + (Y * θ.read 0) a i = R' a i := congrFun (congrFun hR' a) i
    show η.read 0 a i = -((Y * θ.read 0) a i) + 0 + α 0 i * θ.read 0 a i
    rw [hα]
    linear_combination h2 + h1
  · obtain rfl := Subsingleton.elim ℓ 0
    ext i a
    have h1 : W' i a = -((k : ℝ) * lam i) * θ.write 0 i a := congrFun (hlam i).2.2 a
    have h2 : η.write 0 i a - ((θ.write 0 * Y) i a + c * θ.write 0 i a) = W' i a :=
      congrFun (congrFun hW' i) a
    show η.write 0 i a = (θ.write 0 * Y) i a + c * θ.write 0 i a
      + -((k : ℝ) * α 0 i) * θ.write 0 i a
    rw [hα]
    linear_combination h2 + h1
  · show η.D = -(Y * θ.D) + 0 + 0
    rw [hDY, add_zero, add_zero]

/-! ### Helpers: the directions of the symmetries, and differentiability at the inputs -/

/-- Helper: `c ↦ scaleDir θ (fun _ => c)` (one scale shared by `h_0` and `h_1`) is linear. -/
private noncomputable def scaleLin_rzr
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    ℝ →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut where
  toFun c := scaleDir θ (fun _ => c)
  map_add' a b := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.add_E, Params.add_read, Params.add_write, Params.add_D,
        add_smul, add_zero]
  map_smul' a b := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        smul_eq_mul, mul_smul, smul_zero, RingHom.id_apply]

/-- Helper: `α ↦ rescaleDirMlp k θ α` is linear (a copy of the private `rescaleLin_rres`). -/
private noncomputable def rescaleLin_rzr (k : ℕ)
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

/-- Helper: the directions of one rotation and one scaling of both hidden states and of the
rescalings, `((Y, c), α) ↦ cobDir θ (Y, Y) + scaleDir θ (c, c) + rescaleDirMlp k θ α` with `Y`
antisymmetric, as a linear map. -/
private noncomputable def dirLin_rzr (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    ((antisymmetric d × ℝ) × (∀ ℓ : Fin 1, hid ℓ → ℝ)) →ₗ[ℝ]
      Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut :=
  (((cobDirLin θ).comp (LinearMap.pi fun _ => (antisymmetric d).subtype)).coprod
    (scaleLin_rzr θ)).coprod (rescaleLin_rzr k θ)

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: these directions span a space of dimension at most `(d(d-1)/2 + 1) + s`. -/
private theorem finrank_range_dirLin_le_rzr (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    Module.finrank ℝ (LinearMap.range (dirLin_rzr k θ))
      ≤ (Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Fintype.card (hid 0) := by
  refine (LinearMap.finrank_range_le _).trans (le_of_eq ?_)
  rw [Module.finrank_prod, Module.finrank_prod, finrank_antisymmetric, Module.finrank_self,
    Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]

/-- Helper: the directions that are flat at every input of
`residualZeroDomain ∩ noKinkRMS θ` are among them. -/
private theorem flatOn_le_range_rzr {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d) (hturn : TurnsActiveRows θ)
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v, vanillaBlock σ (θ.read 0) (θ.write 0) v]) :
    flatOn (Arch.mlp σ (rmsNorm 0) hid) 1 θ
        (residualZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ)
      ≤ LinearMap.range (dirLin_rzr k θ) := by
  intro η hη
  obtain ⟨Y, c, α, hY, rfl⟩ :=
    flatOn_noKink_le_mlp_rescale_residual_rmsNorm_zero hσ hhom hU θ hθ hd hturn hw η hη
  exact ⟨((⟨Y, hY⟩, c), α), rfl⟩

/-- **Theorem B.1 (iv) of the skips paper, the residual network, for ReLU-type MLP blocks, at one
parameter:** under the conditions of
`flatOn_noKink_le_mlp_rescale_residual_rmsNorm_zero`, `funDim = P − (d(d−1)/2 + 1) − s`, with `s`
the number of hidden units. -/
theorem funDim_mlp_oneBlock_rescale_residual_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d) (hturn : TurnsActiveRows θ)
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v, vanillaBlock σ (θ.read 0) (θ.write 0) v]) :
    funDim (Arch.mlp σ (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- `≤`: the rotation and the scaling of both hidden states and the rescalings of the hidden
  -- units are flat and independent
  have hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0 := fun ℓ i => by
    obtain rfl := Subsingleton.elim ℓ 0
    exact hθ.col_ne_zero i
  have hle := funDim_add_le_residual_mlp_rescale_rmsNorm_zero hhom θ hθ.rank_E hc
  rw [Fin.sum_univ_one] at hle
  -- `≥`: `K(θ)` lies in the directions flat on `residualZeroDomain ∩ noKinkRMS θ`, which are of
  -- this form
  have hflat : flat (Arch.mlp σ (rmsNorm 0) hid) 1 θ ≤ LinearMap.range (dirLin_rzr k θ) :=
    (flat_le_flatOn θ _).trans (flatOn_le_range_rzr hσ hhom hU θ hθ hd hturn hw)
  -- `fd(θ) + dim K(θ) = P`
  have h := funDim_add_finrank_flat' (S := 1) θ
  have hmono := Submodule.finrank_mono hflat
  have hdim := finrank_range_dirLin_le_rzr k θ
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at hle hdim ⊢
  omega

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the function of one residual block under pre-RMSNorm with `ε = 0`,
`F_θ(x) = N_0(x E + σ(N_0(x E) W_read) W_write) D`. -/
private theorem eval_eq_rzr
    (θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ) :
    eval (Arch.mlp σ (rmsNorm 0) hid) 1 θ' x
      = rmsNorm 0 (x * θ'.E + (rmsNorm 0 (x * θ'.E) * θ'.read 0).map σ * θ'.write 0) * θ'.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero]
  simp only [Pi.one_apply, Matrix.mul_one]

/-- Helper: the product of two matrix-valued maps differentiable at `y` is differentiable at `y`
(a copy of the private `differentiableAt_matMul_rres`). -/
private theorem differentiableAt_matMul_rzr {E : Type*} [NormedAddCommGroup E]
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
private theorem differentiable_lin_rzr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut →ₗ[ℝ] F) :
    Differentiable ℝ l := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).differentiable

omit [Nonempty T] in
/-- Helper: at an input of `residualZeroDomain ∩ noKinkRMS θ` the output is differentiable in the
parameters: no row of `x E` and of `h_1` vanishes, so `N_0` is differentiable at both, and the
pre-activations `N_0(x E) W_read` have no zero entry, as `N_0` scales the rows of `x E` by positive
numbers. -/
private theorem differentiableAt_eval_rzr (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ residualZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ) :
    DifferentiableAt ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        eval (Arch.mlp σ (rmsNorm 0) hid) 1 θ' x) θ := by
  obtain ⟨⟨hx0, hx1⟩, hxk⟩ := hx
  have e : (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
      eval (Arch.mlp σ (rmsNorm 0) hid) 1 θ' x) = fun θ' => rmsNorm 0 (x * θ'.E
        + (rmsNorm 0 (x * θ'.E) * θ'.read 0).map σ * θ'.write 0) * θ'.D :=
    funext fun θ' => eval_eq_rzr θ' x
  rw [e]
  -- the components of the parameters are linear, hence differentiable
  have hE : Differentiable ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut => θ'.E) := by
    have h := differentiable_lin_rzr (Params.linE
      (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) (dIn := dIn) (dOut := dOut))
    exact h
  have hR : Differentiable ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut => θ'.read 0) := by
    have h := differentiable_lin_rzr (Params.linRead
      (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) (dIn := dIn) (dOut := dOut) 0)
    exact h
  have hW : Differentiable ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        θ'.write 0) := by
    have h := differentiable_lin_rzr (Params.linWrite
      (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) (dIn := dIn) (dOut := dOut) 0)
    exact h
  have hD : Differentiable ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut => θ'.D) := by
    have h := differentiable_lin_rzr (Params.linD
      (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) (dIn := dIn) (dOut := dOut))
    exact h
  -- `x E`, `N_0(x E)` and the pre-activations `N_0(x E) W_read`
  have hxE : DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut => x * θ'.E) θ :=
    differentiableAt_matMul_rzr (differentiableAt_const x) (hE θ)
  have hN0 : DifferentiableAt ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) :=
    (analyticAt_rmsNorm_zero _ hx0).differentiableAt
  have hn : DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        rmsNorm 0 (x * θ'.E)) θ :=
    DifferentiableAt.comp (f := fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid)
      dIn dOut => x * θ'.E) θ hN0 hxE
  have hpre : DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        rmsNorm 0 (x * θ'.E) * θ'.read 0) θ :=
    differentiableAt_matMul_rzr hn (hR θ)
  -- at `θ` they have no zero entry, so `σ` is differentiable there
  have hP : ∀ t i, (rmsNorm 0 (x * θ.E) * θ.read 0) t i ≠ 0 := by
    intro t i
    rw [rmsNorm_mul_apply_rzr]
    exact mul_ne_zero (inv_sqrt_pos_rzr (hx0 t)).ne' (hxk t i)
  have hact : DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        (rmsNorm 0 (x * θ'.E) * θ'.read 0).map σ) θ := by
    have h := (differentiableAt_map_rzr hσ hP).comp θ hpre
    exact h
  -- `h_1 = x E + σ(N_0(x E) W_read) W_write`, no row of which vanishes, and the output `N_0(h_1) D`
  have hh : DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        x * θ'.E + (rmsNorm 0 (x * θ'.E) * θ'.read 0).map σ * θ'.write 0) θ :=
    hxE.add (differentiableAt_matMul_rzr hact (hW θ))
  have hN1 : DifferentiableAt ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ)
      (x * θ.E + (rmsNorm 0 (x * θ.E) * θ.read 0).map σ * θ.write 0) :=
    (analyticAt_rmsNorm_zero _ hx1).differentiableAt
  have hout : DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        rmsNorm 0 (x * θ'.E + (rmsNorm 0 (x * θ'.E) * θ'.read 0).map σ * θ'.write 0)) θ :=
    DifferentiableAt.comp (f := fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid)
      dIn dOut => x * θ'.E + (rmsNorm 0 (x * θ'.E) * θ'.read 0).map σ * θ'.write 0) θ hN1 hh
  exact differentiableAt_matMul_rzr hout (hD θ)

/-- **Theorem B.1 (iv) of the skips paper, the residual network, in the paper's own sense, for
ReLU-type MLP blocks, at one parameter:** under the same conditions, a finite batch of inputs at
which no normalized row vanishes and no hidden unit sits at its kink, on which the Jacobian has
the rank `P − (d(d−1)/2 + 1) − s`. -/
theorem exists_jacobianRank_mlp_oneBlock_rescale_residual_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d) (hturn : TurnsActiveRows θ)
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧
      LinearIndependent ℝ ![v, vanillaBlock σ (θ.read 0) (θ.write 0) v]) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ residualZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp σ (rmsNorm 0) hid) 1 X θ
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  -- a batch of inputs of `U = residualZeroDomain ∩ noKinkRMS θ`, where the network is
  -- differentiable in `θ`, with the rank `P - dim K_U(θ)`
  obtain ⟨n, X, hX, h⟩ := exists_jacobianRank_add_finrank_flatOn (S := 1) θ
    (residualZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ)
    (fun x hx => differentiableAt_eval_rzr hσ θ x hx)
  -- the sandwich: `dim K(θ) ≤ dim K_U(θ) ≤ d(d-1)/2 + 1 + s = dim K(θ)`
  have hfd := funDim_mlp_oneBlock_rescale_residual_rmsNorm_zero hσ hhom hU θ hθ hd hturn hw
  have h' := funDim_add_finrank_flat' (S := 1) θ
  have h1 := Submodule.finrank_mono (flat_le_flatOn (S := 1) θ
    (residualZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ))
  have h2 := Submodule.finrank_mono (flatOn_le_range_rzr hσ hhom hU θ hθ hd hturn hw)
  have h3 := finrank_range_dirLin_le_rzr k θ
  refine ⟨n, X, hX, ?_⟩
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at hfd h3 ⊢
  omega

end Skips
