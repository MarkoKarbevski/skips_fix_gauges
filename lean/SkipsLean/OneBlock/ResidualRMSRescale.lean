import SkipsLean.OneBlock.ResidualRMSStepsOn
import SkipsLean.OneBlock.ResidualRMSMlp
import SkipsLean.OneBlock.ResidualRescale

/-!
# One residual ReLU or ReLU² block under pre-RMSNorm

Paper (skips paper): Theorem 4.6 (ii), first sentence (Theorem B.1 (ii) in the appendix), for
`ε > 0` and no biases, for ReLU and ReLU² blocks: "For generic parameters the residual network has
functional dimension `P − d_model (d_model − 1)/2 − s`, which is the equality condition. If the
block has width at least `d_model`, the skip raises the functional dimension by at least
`d_model (d_model − 1)/2`." Here `s` is the number of hidden units.

Its proof, Step 4: "For the ReLU-type activations without biases the kinks lie on hyperplanes
through the center of the ball, and the arguments of Lemma B.3 are local. So Lemma B.3, with `E`
and `D` replaced by the identity and `M = 0`, makes the entries of `η'` at each hidden unit a
rescaling." Step 5: "The flat directions are thus those of the orthogonal change of basis and of
the symmetries inside the block. […] so `dim K(θ) = d_model (d_model − 1)/2 + s`."

Stated here, as in `OneBlock/ResidualRescale.lean` (the same block without normalization) and
`OneBlock/ResidualRMSMlp.lean` (tanh and GELU blocks under pre-RMSNorm), for an activation that is
differentiable away from `0`, positively homogeneous of degree `k`, and satisfies Lemma B.3 in the
form `UnitsRescale`:

* `noKinkRMS θ`: the inputs at which no hidden unit sits at its kink (every entry of
  `x E W_read` is nonzero; under pre-RMSNorm with `ε > 0` the block reads a positive multiple of
  each row of `x E`).
* A direction that is flat at these inputs is `cobDir θ (fun _ => Y) + rescaleDirMlp k θ α` with
  `Y` antisymmetric.
* The value: `funDim + d(d−1)/2 + s = P`, and a batch of inputs of `noKinkRMS θ` with this rank
  (the paper's functional dimension for these blocks), under the conditions `OneBlockGenericRMS`
  and at almost every parameter, for ReLU and ReLU² blocks of any width.
* The gain: for a block of at least `d` hidden units the skip raises `funDim` by at least
  `d(d−1)/2`.

Steps 1 to 3 at the inputs of `noKinkRMS θ` are `exists_antisymm_of_flatOn_residual_rmsNorm`
(`OneBlock/ResidualRMSStepsOn.lean`). ReGLU blocks are not stated here.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- The inputs at which no hidden unit of the block sits at its kink, under pre-RMSNorm: every
entry of `x E W_read` (one per token and hidden unit) is nonzero. -/
def noKinkRMS (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) :
    Set (Matrix T dIn ℝ) :=
  {x | ∀ (t : T) (i : hid 0), (x * θ.E * θ.read 0) t i ≠ 0}

/-! ### Helpers: the activation away from its kink, and the map of the block -/

/-- Helper: the matrices with no zero entry (for a ReLU-type block: the pre-activations with no
hidden unit at its kink). -/
private def noZero_rres (m n : Type*) : Set (Matrix m n ℝ) :=
  {M | ∀ t i, M t i ≠ 0}

/-- Helper: the matrices with no zero entry form an open set. -/
private theorem isOpen_noZero_rres {m n : Type*} [Fintype m] [Fintype n] :
    IsOpen (noZero_rres m n) := by
  refine isOpen_iff_mem_nhds.2 fun M hM => ?_
  exact Filter.eventually_all.2 fun t => Filter.eventually_all.2 fun i =>
    (continuous_id.matrix_elem t i).continuousAt.eventually_ne (hM t i)

/-- Helper: a positively homogeneous `σ` is a monomial on each side of `0` (`σ y = y^k σ(1)` for
`y > 0`, `σ y = (-y)^k σ(-1)` for `y < 0`), hence `C¹` at every `z ≠ 0`. -/
private theorem contDiffAt_of_homogeneous_rres {k : ℕ}
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
private theorem contDiffOn_map_rres {k : ℕ}
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {m n : Type*} [Fintype m]
    [Fintype n] : ContDiffOn ℝ 1 (fun M : Matrix m n ℝ => M.map σ) (noZero_rres m n) := by
  intro M hM
  refine ContDiffAt.contDiffWithinAt (contDiffAt_pi.2 fun t => contDiffAt_pi.2 fun i => ?_)
  have hent : ContDiff ℝ 1 (fun M : Matrix m n ℝ => M t i) :=
    contDiff_pi.1 (contDiff_pi.1 contDiff_id t) i
  have h := (contDiffAt_of_homogeneous_rres hhom (hM t i)).comp M hent.contDiffAt
  exact h

/-- Helper: `M ↦ σ(M)` (entrywise) is differentiable at a matrix with no zero entry. -/
private theorem differentiableAt_map_rres (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {m n : Type*} [Fintype m] [Fintype n] {P : Matrix m n ℝ} (hP : ∀ t i, P t i ≠ 0) :
    DifferentiableAt ℝ (fun M : Matrix m n ℝ => M.map σ) P := by
  refine differentiableAt_pi.2 fun t => differentiableAt_pi.2 fun i => ?_
  have hent : Differentiable ℝ (fun M : Matrix m n ℝ => M t i) :=
    differentiable_pi.1 (differentiable_pi.1 differentiable_id t) i
  have h := (hσ _ (hP t i)).differentiableAt.comp P (hent P)
  exact h

/-- Helper: at a matrix `P` with no zero entry, the derivative of `M ↦ σ(M)` along `Q` has the
entries `σ'(P_{t i}) Q_{t i}`. -/
private theorem fderiv_map_apply_rres (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {m n : Type*} [Fintype m] [Fintype n] {P : Matrix m n ℝ} (hP : ∀ t i, P t i ≠ 0)
    (Q : Matrix m n ℝ) (t : m) (i : n) :
    fderiv ℝ (fun M : Matrix m n ℝ => M.map σ) P Q t i = σ' (P t i) * Q t i := by
  -- the chain rule along the line `τ ↦ P + τ Q`
  have hline : HasDerivAt (fun τ : ℝ => P + τ • Q) Q 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const Q).const_add P
    rw [one_smul] at h
    exact h
  have h0 : P = P + (0 : ℝ) • Q := by rw [zero_smul, add_zero]
  have h1 := (differentiableAt_map_rres hσ hP).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0
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
private theorem f_apply_rres {χ : Matrix T d ℝ → Matrix T d ℝ} (P : Matrix T (hid 0) ℝ) (t : T)
    (i : hid 0) : (Arch.mlp (T := T) (d := d) σ χ hid).f 0 P t i = σ (P t i) := rfl

omit [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper: the same derivative for the map of the block. -/
private theorem fderiv_f_rres (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {χ : Matrix T d ℝ → Matrix T d ℝ} {P : Matrix T (hid 0) ℝ} (hP : ∀ t i, P t i ≠ 0)
    (Q : Matrix T (hid 0) ℝ) (t : T) (i : hid 0) :
    fderiv ℝ ((Arch.mlp (T := T) (d := d) σ χ hid).f 0) P Q t i = σ' (P t i) * Q t i :=
  fderiv_map_apply_rres hσ hP Q t i

/-- Helper: differentiating `σ(λ z) = λ^k σ(z)` in `z ≠ 0` gives `λ σ'(λ z) = λ^k σ'(z)`. -/
private theorem mul_deriv_homogeneous_rres {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
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

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `N_ε` scales every row: `(N_ε(h) W)_{t i} = (‖h_t‖²/d + ε)^{-1/2} (h W)_{t i}`. -/
private theorem rmsNorm_mul_apply_rres {n : Type*} [Fintype n] (h : Matrix T d ℝ)
    (W : Matrix d n ℝ) (t : T) (i : n) :
    (rmsNorm ε h * W) t i
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ * (h * W) t i := by
  simp only [Matrix.mul_apply, Finset.mul_sum, rmsNorm, rmsRow, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul, mul_assoc]

omit [DecidableEq d] in
/-- Helper: the factor of `N_ε` is positive for `ε > 0`. -/
private theorem inv_sqrt_pos_rres (hε : 0 < ε) (v : d → ℝ) :
    0 < (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹ := by
  have h0 : 0 ≤ (v ⬝ᵥ v) / (Fintype.card d : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)) (Nat.cast_nonneg _)
  exact inv_pos.2 (Real.sqrt_pos.2 (by linarith))

/-- Helper: for nonzero vectors `c_i`, some `v` has `v ⬝ c_i ≠ 0` for all `i` (a finite union of
hyperplanes is not the whole space). -/
private theorem exists_dotProduct_ne_zero_rres {n q : Type*} [Fintype n] [Fintype q]
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

/-- **Proof of Theorem B.1 (ii), Steps 1 to 4, for ReLU-type MLP blocks:** under the conditions
`OneBlockGenericRMS`, a direction that is flat at every input with no hidden unit at its kink is
the direction of an orthogonal change of basis shared by `h_0` and `h_1` plus a rescaling of the
hidden units. -/
theorem flatOn_noKinkRMS_le_mlp_rescale_residual_rmsNorm {k : ℕ} (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.mlp σ (rmsNorm ε) hid) 1 θ (noKinkRMS θ)) :
    ∃ (Y : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
      η = cobDir θ (fun _ => Y) + rescaleDirMlp k θ α := by
  -- `x ↦ x E` is onto, through a left inverse `B` of `E`
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hθ.rank_E)
  -- an input with equal rows and no hidden unit at its kink: `x = v B` with `v c_i ≠ 0`
  have hw : ∃ w : dIn → ℝ,
      (Matrix.of fun _ : T => w) * θ.E * θ.read 0 ∈ noZero_rres T (hid 0) := by
    obtain ⟨v, hv⟩ := exists_dotProduct_ne_zero_rres (fun i => (θ.read 0)ᵀ i) hθ.col_ne_zero
    refine ⟨v ᵥ* B, fun t i => ?_⟩
    have e : (Matrix.of fun _ : T => v ᵥ* B) = (Matrix.of fun _ : T => v) * B := by
      ext; rfl
    rw [e, Matrix.mul_assoc _ B, hB, Matrix.mul_one]
    exact hv i
  -- Steps 1 to 3 on the inputs of `noKinkRMS θ`: the pre-activations with no zero entry form an
  -- open set, invariant under positive scalings of the rows, on which the block map is `C¹`
  obtain ⟨Y, hYa, hEY, hDY, hF⟩ := exists_antisymm_of_flatOn_residual_rmsNorm
    (A := Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) hε rfl (noZero_rres T (hid 0))
    isOpen_noZero_rres (fun M hM c hc t i => mul_ne_zero (hc t).ne' (hM t i))
    (contDiffOn_map_rres hhom) θ hθ.rank_E hθ.rank_D hw η hη
  generalize hR' : η.read 0 + Y * θ.read 0 = R' at hF
  generalize hW' : η.write 0 - θ.write 0 * Y = W' at hF
  -- Step 4 (a): the block equation at the row `v` of an input with equal rows, `v c_i ≠ 0`; the
  -- normalization scales `v` by `s > 0`, and by homogeneity the equation at `s v` is `s^k` times
  -- the equation at `v`
  have hall : ∀ v : d → ℝ, (∀ i, v ⬝ᵥ (θ.read 0)ᵀ i ≠ 0) → ∀ j : d,
      ∑ i : hid 0, (σ (v ⬝ᵥ (θ.read 0)ᵀ i) * W' i j
        + σ' (v ⬝ᵥ (θ.read 0)ᵀ i) * (v ⬝ᵥ R'ᵀ i) * θ.write 0 i j) = 0 := by
    intro v hv j
    have hxE : (Matrix.of fun _ : T => v) * B * θ.E = Matrix.of fun _ : T => v := by
      rw [Matrix.mul_assoc, hB, Matrix.mul_one]
    have hx : (Matrix.of fun _ : T => v) * B * θ.E * θ.read 0 ∈ noZero_rres T (hid 0) := by
      rw [hxE]
      intro t i
      exact hv i
    have e := hF _ hx
    rw [hxE] at e
    obtain ⟨s, hs, hsP⟩ : ∃ s : ℝ, 0 < s ∧ ∀ (W : Matrix d (hid 0) ℝ) (i : hid 0),
        (rmsNorm ε (Matrix.of fun _ : T => v) * W) (Classical.arbitrary T) i
          = s * (v ⬝ᵥ Wᵀ i) :=
      ⟨_, inv_sqrt_pos_rres hε v, fun W i => by rw [rmsNorm_mul_apply_rres]; rfl⟩
    have hP : ∀ t i, (rmsNorm ε (Matrix.of fun _ : T => v) * θ.read 0) t i ≠ 0 := by
      intro t i
      rw [rmsNorm_mul_apply_rres]
      exact mul_ne_zero (inv_sqrt_pos_rres hε _).ne' (hv i)
    have e2 := congrFun (congrFun e (Classical.arbitrary T)) j
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib,
      Matrix.zero_apply] at e2
    have key : ∀ i : hid 0, fderiv ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f 0)
        (rmsNorm ε (Matrix.of fun _ : T => v) * θ.read 0)
        (rmsNorm ε (Matrix.of fun _ : T => v) * R') (Classical.arbitrary T) i * θ.write 0 i j
        + (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f 0
          (rmsNorm ε (Matrix.of fun _ : T => v) * θ.read 0) (Classical.arbitrary T) i * W' i j
        = s ^ k * (σ (v ⬝ᵥ (θ.read 0)ᵀ i) * W' i j
          + σ' (v ⬝ᵥ (θ.read 0)ᵀ i) * (v ⬝ᵥ R'ᵀ i) * θ.write 0 i j) := by
      intro i
      rw [fderiv_f_rres hσ hP, f_apply_rres, hsP, hsP, hhom s _ hs]
      have hd := mul_deriv_homogeneous_rres hσ hhom hs (hv i)
      linear_combination ((v ⬝ᵥ R'ᵀ i) * θ.write 0 i j) * hd
    have e3 : ∑ i : hid 0, s ^ k * (σ (v ⬝ᵥ (θ.read 0)ᵀ i) * W' i j
        + σ' (v ⬝ᵥ (θ.read 0)ᵀ i) * (v ⬝ᵥ R'ᵀ i) * θ.write 0 i j) = 0 :=
      (Finset.sum_congr rfl fun i _ => (key i).symm).trans e2
    rw [← Finset.mul_sum] at e3
    exact (mul_eq_zero.1 e3).resolve_left (pow_ne_zero _ hs.ne')
  -- Step 4 (b): Lemma B.3 with `E`, `D` the identity and `M = 0`: every hidden unit is only
  -- rescaled, `η'_{c_i} = λ_i c_i` and `η'_{a_i} = -k λ_i a_i`
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
  -- Step 4 (c): `η = cobDir θ (Y, Y) + rescaleDirMlp k θ α`, component by component
  obtain ⟨α, hα⟩ : ∃ α : ∀ ℓ : Fin 1, hid ℓ → ℝ, α 0 = lam :=
    ⟨fun ℓ => Fin.cases lam (fun l => l.elim0) ℓ, rfl⟩
  refine ⟨Y, α, hYa, Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_⟩
  · rw [Params.add_E, hEY]
    exact (add_zero _).symm
  · obtain rfl := Subsingleton.elim ℓ 0
    ext a i
    have h1 : R' a i = lam i * θ.read 0 a i := congrFun (hlam i).1 a
    have h2 : η.read 0 a i + (Y * θ.read 0) a i = R' a i := congrFun (congrFun hR' a) i
    show η.read 0 a i = -((Y * θ.read 0) a i) + α 0 i * θ.read 0 a i
    rw [hα]
    linear_combination h2 + h1
  · obtain rfl := Subsingleton.elim ℓ 0
    ext i a
    have h1 : W' i a = -((k : ℝ) * lam i) * θ.write 0 i a := congrFun (hlam i).2.2 a
    have h2 : η.write 0 i a - (θ.write 0 * Y) i a = W' i a := congrFun (congrFun hW' i) a
    show η.write 0 i a = (θ.write 0 * Y) i a + -((k : ℝ) * α 0 i) * θ.write 0 i a
    rw [hα]
    linear_combination h2 + h1
  · rw [Params.add_D, hDY]
    exact (add_zero _).symm

/-- **Theorem B.1 (ii), first sentence, for ReLU-type MLP blocks, at one parameter:** under the
conditions `OneBlockGenericRMS`, `funDim = P − d(d−1)/2 − s`, with `s` the number of hidden
units. -/
theorem funDim_mlp_oneBlock_rescale_residual_rmsNorm {k : ℕ} (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) :
    funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii) in the paper's own sense, for ReLU-type MLP blocks, at one parameter:** a
finite batch of inputs with no hidden unit at its kink on which the Jacobian has the rank
`P − d(d−1)/2 − s`. -/
theorem exists_jacobianRank_mlp_oneBlock_rescale_residual_rmsNorm {k : ℕ} (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp σ (rmsNorm ε) hid) 1 X θ
          + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii), first sentence, for one ReLU block:** for `ε > 0` and
`d_in, d_out ≥ d ≥ 2`, at almost every parameter the residual network of one ReLU block of any
width has `funDim = P − d(d−1)/2 − s`. -/
theorem ae_funDim_relu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii) in the paper's own sense, for one ReLU block:** at almost every
parameter there is a finite batch of inputs with no hidden unit at its kink on which the Jacobian
has the rank `P − d(d−1)/2 − s`. -/
theorem ae_exists_jacobianRank_relu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp relu (rmsNorm ε) hid) 1 X θ
          + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii), second sentence, for one ReLU block:** if the block has at least
`d` hidden units, at almost every parameter the skip raises `funDim` by at least `d(d−1)/2`. -/
theorem ae_funDim_skipless_add_le_relu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm ε) hid) 0 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ funDim (Arch.mlp relu (rmsNorm ε) hid) 1 θ := by
  sorry

/-- **Theorem B.1 (ii), first sentence, for one ReLU² block:** for `ε > 0` and
`d_in, d_out ≥ d ≥ 2`, at almost every parameter the residual network of one ReLU² block of
any width has `funDim = P − d(d−1)/2 − s`. -/
theorem ae_funDim_reluSq_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii) in the paper's own sense, for one ReLU² block:** at almost every
parameter there is a finite batch of inputs with no hidden unit at its kink on which the Jacobian
has the rank `P − d(d−1)/2 − s`. -/
theorem ae_exists_jacobianRank_reluSq_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp reluSq (rmsNorm ε) hid) 1 X θ
          + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (ii), second sentence, for one ReLU² block:** if the block has at least
`d` hidden units, at almost every parameter the skip raises `funDim` by at least `d(d−1)/2`. -/
theorem ae_funDim_skipless_add_le_reluSq_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm ε) hid) 0 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ funDim (Arch.mlp reluSq (rmsNorm ε) hid) 1 θ := by
  sorry

end Skips
