import SkipsLean.Residual.DepthMlp
import SkipsLean.Residual.SmallWritesOn
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.OneBlock.Rescale

/-!
# Residual networks of ReLU and ReLU² blocks with small writes

Paper (skips paper): Lemma A.30 (ReLU-type blocks with small writes), for ReLU and ReLU² blocks:
"Let the blocks be ReLU, ReLU² or ReGLU blocks, without normalization or biases, let `E` and `D`
have rank `d_model`, and let inputs range over all of `ℝ^{1×d_in}`, or over an open set that
contains `0`. For generic parameters `θ`, let `θ_τ` be the parameters `θ` with every `W_write^ℓ`
replaced by `τ W_write^ℓ`, as in Lemma A.27. For all small `τ ≠ 0`, the Jacobian of the residual
network at `θ_τ` has rank `P − d_model² − s` on some finite batch on which no pre-activation
vanishes. So the residual network has functional dimension `P − d_model² − s` on an open set of
weights that contains these, and at almost every point of this set the skips add at least
`L d_model²` when every block has width at least `d_model`."

Its proof: "The limit `J_0` is again the derivative of the one-block function `G` of Lemma B.3,
whose units are those of all blocks, with the pre-activations `x E W_read^ℓ`. […] a direction
that is flat on a neighborhood of `0` is flat at every input at which no pre-activation vanishes,
and by Lemma B.3, which covers these units, the flat directions form a space of dimension
`d_model² + s`, as in Lemma A.27. Fix a finite batch of such inputs, inside the set of inputs, on
which the kernel of `J_0` is this space".

Stated here for an activation `σ` that is differentiable away from `0`, positively homogeneous
of degree `k`, and satisfies Lemma B.3 in the form `UnitsRescale` for the hidden units of all
blocks together (ReLU with `k = 1`, ReLU² with `k = 2`), under the conditions `SmallWritesGeneric`
of `Residual/DepthMlp.lean` (the conditions of Lemma A.27; they hold at generic parameters), with
all inputs (`T × d_in` matrices), `s = ∑_ℓ d_hidden^ℓ`:

* `noKinkAll θ`: the inputs at which no limit pre-activation `x E W_read^ℓ` vanishes.
* A direction `η` in the kernel of `J_0` at these inputs has `η_E = E X`, `η_D = −X D`, and its
  reads and writes are those of a rescaling of the hidden units: it lies in a space of dimension
  at most `d² + s`.
* The first sentence: a finite batch in `noKinkAll θ` such that for all small `τ ≠ 0` no
  pre-activation on the batch vanishes at `θ_τ` and the Jacobian on the batch at `θ_τ` has rank
  `P − d² − s`; hence `funDim (θ_τ) = P − d² − s`.
* The second sentence: `funDim = P − d² − s` at every parameter near `θ_τ`; an open set `U` on
  which `funDim = P − d² − s` and which contains `θ_τ` for generic `θ` and all small `τ ≠ 0`; and
  the gain `≥ L d²` at almost every point of `U` when every block has at least `d` hidden units.

ReGLU blocks: `Residual/DepthReGLU.lean`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- The inputs at which no limit pre-activation vanishes: every entry of `x E W_read^ℓ`, for
every block `ℓ`, token and hidden unit, is nonzero. -/
def noKinkAll (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Set (Matrix T dIn ℝ) :=
  {x | ∀ (ℓ : Fin L) (t : T) (i : hid ℓ), (x * θ.E * θ.read ℓ) t i ≠ 0}

/-! ### Helpers: linear algebra (copies of the private helpers of `Residual/DepthMlp.lean`) -/

/-- Helper (as `cancel_left_of_rank_dm` of `Residual/DepthMlp.lean`): a matrix whose rank is its
number of columns cancels on the left, via a left inverse. -/
private theorem cancel_left_of_rank_drs {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

/-- Helper: a matrix whose rank is its number of rows cancels on the right, via a right
inverse. -/
private theorem cancel_right_of_rank_drs {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

/-- Helper: an entry of `M N + M' N'`. -/
private theorem mul_add_mul_apply_drs {m n k : Type*} [Fintype n] (M M' : Matrix m n ℝ)
    (N N' : Matrix n k ℝ) (t : m) (o : k) :
    (M * N + M' * N') t o = ∑ i, (M t i * N i o + M' t i * N' i o) := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

/-! ### Helpers: the activation away from its kink (as in `OneBlock/ResidualRMSRescale.lean`) -/

/-- Helper: the matrices with no zero entry (for ReLU-type blocks: the pre-activations with no
hidden unit at its kink). -/
private def noZero_drs (m n : Type*) : Set (Matrix m n ℝ) :=
  {M | ∀ t i, M t i ≠ 0}

/-- Helper: the matrices with no zero entry form an open set. -/
private theorem isOpen_noZero_drs {m n : Type*} [Fintype m] [Fintype n] :
    IsOpen (noZero_drs m n) := by
  refine isOpen_iff_mem_nhds.2 fun M hM => ?_
  exact Filter.eventually_all.2 fun t => Filter.eventually_all.2 fun i =>
    (continuous_id.matrix_elem t i).continuousAt.eventually_ne (hM t i)

/-- Helper: a positively homogeneous `σ` is a monomial on each side of `0` (`σ y = y^k σ(1)` for
`y > 0`, `σ y = (-y)^k σ(-1)` for `y < 0`), hence `C²` at every `z ≠ 0`. -/
private theorem contDiffAt_of_homogeneous_drs {k : ℕ}
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {z : ℝ} (hz : z ≠ 0) :
    ContDiffAt ℝ 2 σ z := by
  rcases hz.lt_or_gt with hneg | hpos
  · have h : σ =ᶠ[nhds z] fun y : ℝ => (-y) ^ k * σ (-1) := by
      filter_upwards [eventually_lt_nhds hneg] with y hy
      have e := hhom (-y) (-1) (by linarith)
      rwa [show -y * -1 = y by ring] at e
    have hc : ContDiff ℝ 2 (fun y : ℝ => (-y) ^ k * σ (-1)) := by fun_prop
    exact hc.contDiffAt.congr_of_eventuallyEq h
  · have h : σ =ᶠ[nhds z] fun y : ℝ => y ^ k * σ 1 := by
      filter_upwards [eventually_gt_nhds hpos] with y hy
      have e := hhom y 1 hy
      rwa [mul_one] at e
    have hc : ContDiff ℝ 2 (fun y : ℝ => y ^ k * σ 1) := by fun_prop
    exact hc.contDiffAt.congr_of_eventuallyEq h

/-- Helper: `M ↦ σ(M)` (entrywise) is `C²` on the matrices with no zero entry. -/
private theorem contDiffOn_map_drs {k : ℕ}
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {m n : Type*} [Fintype m]
    [Fintype n] : ContDiffOn ℝ 2 (fun M : Matrix m n ℝ => M.map σ) (noZero_drs m n) := by
  intro M hM
  refine ContDiffAt.contDiffWithinAt (contDiffAt_pi.2 fun t => contDiffAt_pi.2 fun i => ?_)
  have hent : ContDiff ℝ 2 (fun M : Matrix m n ℝ => M t i) :=
    contDiff_pi.1 (contDiff_pi.1 contDiff_id t) i
  have h := (contDiffAt_of_homogeneous_drs hhom (hM t i)).comp M hent.contDiffAt
  exact h

/-- Helper: `M ↦ σ(M)` (entrywise) is differentiable at a matrix with no zero entry. -/
private theorem differentiableAt_map_drs (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {m n : Type*} [Fintype m] [Fintype n] {P : Matrix m n ℝ} (hP : ∀ t i, P t i ≠ 0) :
    DifferentiableAt ℝ (fun M : Matrix m n ℝ => M.map σ) P := by
  refine differentiableAt_pi.2 fun t => differentiableAt_pi.2 fun i => ?_
  have hent : Differentiable ℝ (fun M : Matrix m n ℝ => M t i) :=
    differentiable_pi.1 (differentiable_pi.1 differentiable_id t) i
  have h := (hσ _ (hP t i)).differentiableAt.comp P (hent P)
  exact h

/-- Helper: at a matrix `P` with no zero entry, the derivative of `M ↦ σ(M)` along `Q` has the
entries `σ'(P_{t i}) Q_{t i}`. -/
private theorem fderiv_map_apply_drs (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {m n : Type*} [Fintype m] [Fintype n] {P : Matrix m n ℝ} (hP : ∀ t i, P t i ≠ 0)
    (Q : Matrix m n ℝ) (t : m) (i : n) :
    fderiv ℝ (fun M : Matrix m n ℝ => M.map σ) P Q t i = σ' (P t i) * Q t i := by
  -- the chain rule along the line `τ ↦ P + τ Q`
  have hline : HasDerivAt (fun τ : ℝ => P + τ • Q) Q 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const Q).const_add P
    rw [one_smul] at h
    exact h
  have h0 : P = P + (0 : ℝ) • Q := by rw [zero_smul, add_zero]
  have h1 := (differentiableAt_map_drs hσ hP).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) i
  -- the same derivative, entrywise: `τ ↦ σ(P_{t i} + τ Q_{t i})`
  have h3 : HasDerivAt (fun τ : ℝ => σ (P t i + τ * Q t i)) (σ' (P t i) * Q t i) 0 := by
    have hu : HasDerivAt (fun τ : ℝ => P t i + τ * Q t i) (Q t i) 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).mul_const (Q t i)).const_add (P t i)
      rw [one_mul] at h
      exact h
    exact (hσ (P t i) (hP t i)).comp_of_eq (0 : ℝ) hu (by rw [zero_mul, add_zero])
  exact h2.unique h3

omit [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper: the same derivative for the map of block `ℓ` of an MLP network. -/
private theorem fderiv_f_mlp_apply_drs (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z) (ℓ : Fin L)
    {P : Matrix T (hid ℓ) ℝ} (hP : ∀ t i, P t i ≠ 0) (Q : Matrix T (hid ℓ) ℝ) (t : T)
    (i : hid ℓ) :
    fderiv ℝ ((Arch.mlp (T := T) (d := d) σ id hid).f ℓ) P Q t i = σ' (P t i) * Q t i :=
  fderiv_map_apply_drs hσ hP Q t i

/-! ### Helpers: the limit `J_0` for MLP blocks at the inputs off the kinks -/

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (as `smallWritesLimit_mlp_apply` of `Residual/DepthMlp.lean`, at an input of
`noKinkAll θ`): the entries of `(J_0 η)(x)`,
`(x ψ_M)_{t o} + ∑_ℓ ∑_i [σ(z_{ℓ i}) (ψ_A^ℓ)_{i o} + σ'(z_{ℓ i}) (x ψ_C^ℓ)_{t i} (A^ℓ)_{i o}]` with
`z_{ℓ i} = (x C^ℓ)_{t i}`, `C^ℓ = E W_read^ℓ`, `A^ℓ = W_write^ℓ D`, `ψ_C^ℓ = E η_read^ℓ`,
`ψ_A^ℓ = η_write^ℓ D`. -/
private theorem smallWritesLimit_mlp_apply_drs (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ noKinkAll θ) (t : T) (o : dOut) :
    smallWritesLimit (Arch.mlp σ id hid) θ η x t o
      = (x * (η.E * θ.D + θ.E * η.D)) t o + ∑ ℓ, ∑ i : hid ℓ,
        (σ ((x * (θ.E * θ.read ℓ)) t i) * (η.write ℓ * θ.D) i o
          + σ' ((x * (θ.E * θ.read ℓ)) t i) * (x * (θ.E * η.read ℓ)) t i
            * (θ.write ℓ * θ.D) i o) := by
  rw [smallWritesLimit, Matrix.add_apply, Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have e : ∀ F' F : Matrix T (hid ℓ) ℝ, ((F' * θ.write ℓ + F * η.write ℓ) * θ.D) t o
      = ∑ i, (F' t i * (θ.write ℓ * θ.D) i o + F t i * (η.write ℓ * θ.D) i o) := by
    intro F' F
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    exact mul_add_mul_apply_drs _ _ _ _ t o
  rw [e]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- no pre-activation `x E W_read^ℓ` vanishes, so the derivative of `σ` is `σ'` there
  have hP : ∀ t i, (x * θ.E * θ.read ℓ) t i ≠ 0 := hx ℓ
  rw [fderiv_f_mlp_apply_drs hσ ℓ hP, Matrix.mul_assoc x θ.E (θ.read ℓ),
    Matrix.mul_assoc x θ.E (η.read ℓ)]
  show σ' _ * _ * _ + σ _ * _ = _
  ring

/-- **Proof of Lemma A.30, the kernel of `J_0`:** under the conditions `SmallWritesGeneric`, a
direction `η` with `(J_0 η)(x) = 0` at every input at which no limit pre-activation vanishes has
`η_E = E X` and `η_D = −X D` for one matrix `X`, and its reads and writes are those of a
rescaling of the hidden units (Lemma B.3 for the units of all blocks together). -/
theorem smallWritesLimit_eq_zero_mlp_rescale {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hU : UnitsRescale σ σ' k dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : SmallWritesGeneric θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : ∀ x ∈ noKinkAll θ, smallWritesLimit (Arch.mlp σ id hid) θ η x = 0) :
    ∃ (X : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), η.E = θ.E * X ∧ η.D = -(X * θ.D)
      ∧ (∀ ℓ, η.read ℓ = (rescaleDirMlp k θ α).read ℓ)
      ∧ (∀ ℓ, η.write ℓ = (rescaleDirMlp k θ α).write ℓ) := by
  -- row `t₀` of `(J_0 η)(x) = 0` at the inputs `x` whose rows all equal a `v` with `v c_p ≠ 0`
  -- for every hidden unit `p` (these inputs are in `noKinkAll θ`), as a sum over the hidden
  -- units `p = (ℓ, i)` of all blocks
  have key : ∀ v : dIn → ℝ, (∀ p : (Σ ℓ, hid ℓ), v ⬝ᵥ (θ.E * θ.read p.1)ᵀ p.2 ≠ 0) →
      ∀ o : dOut, (v ᵥ* (η.E * θ.D + θ.E * η.D)) o + ∑ p : (Σ ℓ, hid ℓ),
        (σ (v ⬝ᵥ (θ.E * θ.read p.1)ᵀ p.2) * (η.write p.1 * θ.D) p.2 o
          + σ' (v ⬝ᵥ (θ.E * θ.read p.1)ᵀ p.2) * (v ⬝ᵥ (θ.E * η.read p.1)ᵀ p.2)
            * (θ.write p.1 * θ.D) p.2 o) = 0 := by
    intro v hv o
    have hx : (Matrix.of fun _ : T => v) ∈ noKinkAll θ := by
      intro ℓ t i
      rw [Matrix.mul_assoc]
      exact hv ⟨ℓ, i⟩
    have h := congrFun (congrFun (hη _ hx) (Classical.arbitrary T)) o
    rw [smallWritesLimit_mlp_apply_drs hσ θ η _ hx, Matrix.zero_apply] at h
    rw [Fintype.sum_sigma]
    exact h
  -- Lemma B.3 for the units of all blocks together, with the linear term `x ψ_M`: `ψ_M = 0`,
  -- `ψ_c = λ c` and `ψ_a = -k λ a` unit by unit
  obtain ⟨hM, -, lam, hlam⟩ := hU (fun p => (θ.E * θ.read p.1)ᵀ p.2) 0
    (fun p => (θ.write p.1 * θ.D) p.2) (η.E * θ.D + θ.E * η.D) 0
    (fun p => (θ.E * η.read p.1)ᵀ p.2) 0 (fun p => (η.write p.1 * θ.D) p.2)
    (fun p => hθ.row_ne_zero p.1 p.2) (fun p => hθ.col_ne_zero p.1 p.2)
    (fun p q hpq => hθ.col_not_collinear p q hpq) (by
      intro v hv
      have hv' : ∀ p : (Σ ℓ, hid ℓ), v ⬝ᵥ (θ.E * θ.read p.1)ᵀ p.2 ≠ 0 := by
        intro p
        have h := hv p
        simp only [Pi.zero_apply, add_zero] at h
        exact h
      funext o
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        add_zero]
      exact key v hv' o)
  -- `E η_read^ℓ = E (λ W_read^ℓ)` column by column; `E` cancels on the left
  have hr : ∀ ℓ, η.read ℓ = (rescaleDirMlp k θ (fun ℓ i => lam ⟨ℓ, i⟩)).read ℓ := fun ℓ => by
    refine cancel_left_of_rank_drs θ.E hθ.rank_E ?_
    ext a i
    have h : (θ.E * η.read ℓ) a i = lam ⟨ℓ, i⟩ * (θ.E * θ.read ℓ) a i :=
      congrFun (hlam ⟨ℓ, i⟩).1 a
    rw [h, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show lam ⟨ℓ, i⟩ * (θ.E a j * θ.read ℓ j i) = θ.E a j * (lam ⟨ℓ, i⟩ * θ.read ℓ j i)
    ring
  -- `η_write^ℓ D = (-k λ W_write^ℓ) D` row by row; `D` cancels on the right
  have hw : ∀ ℓ, η.write ℓ = (rescaleDirMlp k θ (fun ℓ i => lam ⟨ℓ, i⟩)).write ℓ := fun ℓ => by
    refine cancel_right_of_rank_drs θ.D hθ.rank_D ?_
    ext i o
    have h : (η.write ℓ * θ.D) i o = -((k : ℝ) * lam ⟨ℓ, i⟩) * (θ.write ℓ * θ.D) i o :=
      congrFun (hlam ⟨ℓ, i⟩).2.2 o
    rw [h, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show -((k : ℝ) * lam ⟨ℓ, i⟩) * (θ.write ℓ i j * θ.D j o)
      = -((k : ℝ) * lam ⟨ℓ, i⟩) * θ.write ℓ i j * θ.D j o
    ring
  -- `η_E D + E η_D = 0`: with a right inverse `R` of `D`, `X = -(η_D R)`
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hθ.rank_D)
  have h1 : η.E + θ.E * (η.D * R) = 0 := by
    have h := congrArg (· * R) hM
    simpa only [Matrix.add_mul, Matrix.mul_assoc, hR, Matrix.mul_one, Matrix.zero_mul] using h
  have hE : η.E = θ.E * -(η.D * R) := by
    rw [Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left h1
  -- then `E η_D = -η_E D = E (-(X D))`
  have hD : θ.E * η.D = θ.E * -(-(η.D * R) * θ.D) := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← hE]
    exact eq_neg_of_add_eq_zero_right hM
  exact ⟨-(η.D * R), fun ℓ i => lam ⟨ℓ, i⟩, hE, cancel_left_of_rank_drs θ.E hθ.rank_E hD, hr, hw⟩

/-! ### Helpers: the batch and the space of the flat directions of `J_0` -/

/-- Helper (copy of `limitLin_SW` of `Residual/SmallWrites.lean`): `η ↦ (J_0 η)(x)` is linear in
`η`. -/
private noncomputable def limitLin_drs (A : Arch T d L) (θ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : Params A dIn dOut →ₗ[ℝ] Matrix T dOut ℝ where
  toFun η := smallWritesLimit A θ η x
  map_add' η η' := by
    simp only [smallWritesLimit, Params.add_E, Params.add_D, Params.add_read, Params.add_write,
      Matrix.add_mul, Matrix.mul_add, map_add, Finset.sum_add_distrib]
    abel
  map_smul' c η := by
    simp only [smallWritesLimit, Params.smul_E, Params.smul_D, Params.smul_read,
      Params.smul_write, Matrix.smul_mul, Matrix.mul_smul, map_smul, ← Finset.smul_sum,
      ← smul_add, RingHom.id_apply]

/-- Helper (copy of `exists_batch_ker_SW` of `Residual/SmallWrites.lean`, kernel stabilisation):
for a family of linear maps on a finite-dimensional space, finitely many of them have the common
kernel of all of them. -/
private theorem exists_batch_ker_drs {ι P F : Type*} [AddCommGroup P] [Module ℝ P]
    [FiniteDimensional ℝ P] [AddCommGroup F] [Module ℝ F] (Λ : ι → P →ₗ[ℝ] F) :
    ∃ (n : ℕ) (X : Fin n → ι), ∀ η, (∀ i, Λ (X i) η = 0) → ∀ x, Λ x η = 0 := by
  -- the common kernel of a batch
  let K : ∀ n : ℕ, (Fin n → ι) → Submodule ℝ P := fun n X => ⨅ i, LinearMap.ker (Λ (X i))
  have hmem : ∀ n (X : Fin n → ι) η, η ∈ K n X ↔ ∀ i, Λ (X i) η = 0 := by
    intro n X η
    simp only [K, Submodule.mem_iInf, LinearMap.mem_ker]
  -- a batch whose common kernel has least dimension
  obtain ⟨n, X, hX⟩ := Nat.sInf_mem (s := {k : ℕ | ∃ (n : ℕ) (X : Fin n → ι),
      k = Module.finrank ℝ (K n X)}) ⟨_, 0, Fin.elim0, rfl⟩
  refine ⟨n, X, fun η hη x => ?_⟩
  -- adding the input `x` can only shrink the kernel, and not its dimension: it stays the same
  have hle : K (n + 1) (Fin.cons x X) ≤ K n X := by
    intro ξ hξ
    rw [hmem] at hξ ⊢
    intro i
    simpa only [Fin.cons_succ] using hξ i.succ
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    rw [← hX]
    exact Nat.sInf_le ⟨n + 1, Fin.cons x X, rfl⟩)
  have hηK : η ∈ K (n + 1) (Fin.cons x X) := by
    rw [heq, hmem]
    exact hη
  rw [hmem] at hηK
  simpa only [Fin.cons_zero] using hηK 0

/-- Helper (copy of `smallWritesFlatLin` of `Residual/DepthMlp.lean`): the directions
`X ↦ (E X, 0, 0, -X D)` of one change of basis at all hidden states, as a linear map. -/
private def flatConstLin_drs (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix d d ℝ →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut where
  toFun X := ⟨θ.E * X, 0, 0, -(X * θ.D)⟩
  map_add' X Y := by
    apply Params.ext'
    · exact Matrix.mul_add _ _ _
    · intro ℓ
      exact (add_zero 0).symm
    · intro ℓ
      exact (add_zero 0).symm
    · show -((X + Y) * θ.D) = -(X * θ.D) + -(Y * θ.D)
      rw [Matrix.add_mul, neg_add]
  map_smul' c X := by
    apply Params.ext'
    · exact Matrix.mul_smul _ _ _
    · intro ℓ
      exact (smul_zero c).symm
    · intro ℓ
      exact (smul_zero c).symm
    · show -((c • X) * θ.D) = c • -(X * θ.D)
      rw [Matrix.smul_mul, smul_neg]

/-- Helper (copy of `mlpRescaleLin` of `Residual/UpperBoundSymmetries.lean`):
`α ↦ rescaleDirMlp k θ α` is linear. -/
private noncomputable def rescaleLin_drs (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut where
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

/-- Helper: the numbers of the rescalings of the hidden units form a space of dimension `s`, the
number of hidden units. -/
private theorem finrank_hidFun_drs :
    Module.finrank ℝ (∀ ℓ, hid ℓ → ℝ) = ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]

omit [Nonempty T] [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the directions `(E X, (λ W_read^ℓ)_ℓ, (-k λ W_write^ℓ)_ℓ, -X D)` form a space of
dimension at most `d² + s`. -/
private theorem finrank_range_flatLin_le_drs (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Module.finrank ℝ (LinearMap.range ((flatConstLin_drs θ).coprod (rescaleLin_drs k θ)))
      ≤ Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) := by
  have h := LinearMap.finrank_range_le ((flatConstLin_drs θ).coprod (rescaleLin_drs k θ))
  rwa [Module.finrank_prod, Module.finrank_matrix, Module.finrank_self, mul_one, ← sq,
    finrank_hidFun_drs] at h

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] in
/-- Helper: no column of a read vanishes when no column of `E W_read` vanishes. -/
private theorem read_col_ne_zero_drs
    {θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut} (hθ : SmallWritesGeneric θ) :
    ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0 := by
  intro ℓ i h0
  apply hθ.col_ne_zero ℓ i
  funext a
  show ∑ j, θ.E a j * θ.read ℓ j i = 0
  exact Finset.sum_eq_zero fun j _ => by
    rw [show θ.read ℓ j i = 0 from congrFun h0 j, mul_zero]

/-- **Lemma A.30, first sentence, at one parameter:** under the conditions `SmallWritesGeneric`
there is a finite batch of inputs at which no limit pre-activation vanishes such that, for all
small `τ ≠ 0`, no pre-activation on the batch vanishes at `θ_τ` and the Jacobian of the residual
network on the batch at `θ_τ` has rank `P − d² − s`. -/
theorem exists_eventually_jacobianRank_smallWrites_mlp_rescale {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : SmallWritesGeneric θ) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkAll θ) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.mlp σ id hid) 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) ∧
        jacobianRank (Arch.mlp σ id hid) 1 X (θ.smallWrites τ)
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the maps `η ↦ (J_0 η)(x)`, `x ∈ noKinkAll θ`, are linear: a finite batch `X` in
  -- `noKinkAll θ` decides their common kernel
  obtain ⟨n, X', hX'⟩ := exists_batch_ker_drs
    (fun x : noKinkAll θ => limitLin_drs (Arch.mlp σ id hid) θ (dOut := dOut) x.1)
  refine ⟨n, fun i => (X' i).1, fun i => (X' i).2, ?_⟩
  -- a direction that is flat for `J_0` on the batch is flat at every input of `noKinkAll θ`, so
  -- (the kernel of `J_0`) it lies in the space `W` of the directions
  -- `(E X, (λ W_read^ℓ)_ℓ, (-k λ W_write^ℓ)_ℓ, -X D)`, of dimension at most `d² + s`
  have hW : ∀ η, (∀ i, smallWritesLimit (Arch.mlp σ id hid) θ η (X' i).1 = 0) →
      η ∈ LinearMap.range ((flatConstLin_drs θ).coprod (rescaleLin_drs k θ)) := by
    intro η hη
    have hall : ∀ x ∈ noKinkAll θ, smallWritesLimit (Arch.mlp σ id hid) θ η x = 0 :=
      fun x hx => hX' η hη ⟨x, hx⟩
    obtain ⟨Y, α, hE, hD, hr, hw⟩ := smallWritesLimit_eq_zero_mlp_rescale hσ hU θ hθ η hall
    refine ⟨(Y, α), ?_⟩
    rw [LinearMap.coprod_apply]
    apply Params.ext'
    · show θ.E * Y + 0 = η.E
      rw [add_zero, hE]
    · intro ℓ
      show 0 + (rescaleDirMlp k θ α).read ℓ = η.read ℓ
      rw [zero_add, hr]
    · intro ℓ
      show 0 + (rescaleDirMlp k θ α).write ℓ = η.write ℓ
      rw [zero_add, hw]
    · show -(Y * θ.D) + 0 = η.D
      rw [add_zero, hD]
  have hdim := finrank_range_flatLin_le_drs k θ
  -- `≥`: for small `τ ≠ 0` the pre-activations on the batch stay off the kinks, where the
  -- blocks are `C²`, and the rank is at least `P - dim W` (Residual/SmallWritesOn.lean)
  filter_upwards [eventually_jacobianRank_smallWrites_ge_of_contDiffOn (Arch.mlp σ id hid) θ rfl
    (fun ℓ => noZero_drs T (hid ℓ)) (fun ℓ => isOpen_noZero_drs)
    (fun ℓ => contDiffOn_map_drs hhom) (fun i => (X' i).1) (fun i ℓ => (X' i).2 ℓ) _ hW]
    with τ hτ
  obtain ⟨hpre, hge⟩ := hτ
  refine ⟨fun i ℓ t j => hpre i ℓ t j, ?_⟩
  -- `≤`: the rank is at most `fd(θ_τ) ≤ P - d² - s` (the embedding and the reads of `θ_τ` are
  -- those of `θ`)
  have h1 := jacobianRank_le_funDim (A := Arch.mlp σ id hid) (S := 1) (θ.smallWrites τ)
    (fun i => (X' i).1)
  have hc := read_col_ne_zero_drs hθ
  have h2 := funDim_add_le_residual_mlp_rescale hhom (θ.smallWrites τ) hθ.rank_E hc
  omega

/-- **Lemma A.30, the functional dimension at `θ_τ`:** under the conditions
`SmallWritesGeneric`, for all small `τ ≠ 0` the residual network has `fd(θ_τ) = P − d² − s`. -/
theorem eventually_funDim_smallWrites_mlp_rescale {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : SmallWritesGeneric θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp σ id hid) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  obtain ⟨n, X, -, h⟩ := exists_eventually_jacobianRank_smallWrites_mlp_rescale hσ hhom hU θ hθ
  filter_upwards [h] with τ hτ
  -- the rank on the batch is at most `fd(θ_τ)`, which is at most `P - d² - s`
  have h1 := jacobianRank_le_funDim (A := Arch.mlp σ id hid) (S := 1) (θ.smallWrites τ) X
  have hc := read_col_ne_zero_drs hθ
  have h2 := funDim_add_le_residual_mlp_rescale hhom (θ.smallWrites τ) hθ.rank_E hc
  omega

/-! ### Helpers: the conditions of the upper bound are open -/

omit [Fintype T] [Nonempty T] in
/-- Helper (lower semicontinuity of the rank): if the embedding of `θ₀` has rank `d`, so has the
embedding of every parameter near `θ₀`. With a left inverse `B` of `E₀`, `det (B E')` is
continuous in `θ'` and equals `1` at `θ₀`. -/
private theorem eventually_rank_E_drs
    (θ₀ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (h : θ₀.E.rank = Fintype.card d) :
    ∀ᶠ θ' in 𝓝 θ₀, θ'.E.rank = Fintype.card d := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr h)
  have hE : Continuous fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => θ'.E :=
    (Params.linE (A := Arch.mlp (T := T) (d := d) σ id hid) (dIn := dIn)
      (dOut := dOut)).continuous_of_finiteDimensional
  have hc : Continuous fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
      (B * θ'.E).det :=
    (continuous_const.matrix_mul hE).matrix_det
  have h0 : (B * θ₀.E).det ≠ 0 := by
    rw [hB, Matrix.det_one]
    exact one_ne_zero
  filter_upwards [hc.continuousAt.eventually_ne h0] with θ' h'
  -- `B E'` is invertible, so `d = rank (B E') ≤ rank E' ≤ d`
  refine le_antisymm (Matrix.rank_le_card_width _) ?_
  have hu : IsUnit (B * θ'.E) := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit h')
  rw [← Matrix.rank_of_isUnit _ hu]
  exact Matrix.rank_mul_le_right _ _

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: if no column of a read of `θ₀` vanishes, the same holds near `θ₀` (each column has
an entry that is not `0`, and the entries are continuous in the parameters). -/
private theorem eventually_read_col_ne_zero_drs
    (θ₀ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (h : ∀ ℓ i, (fun a => θ₀.read ℓ a i) ≠ 0) :
    ∀ᶠ θ' in 𝓝 θ₀, ∀ ℓ i, (fun a => θ'.read ℓ a i) ≠ 0 := by
  refine Filter.eventually_all.2 fun ℓ => Filter.eventually_all.2 fun i => ?_
  obtain ⟨a, ha⟩ := Function.ne_iff.mp (h ℓ i)
  have hr : Continuous fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
      θ'.read ℓ :=
    (Params.linRead (A := Arch.mlp (T := T) (d := d) σ id hid) (dIn := dIn) (dOut := dOut)
      ℓ).continuous_of_finiteDimensional
  have hc : Continuous fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
      θ'.read ℓ a i :=
    hr.matrix_elem a i
  filter_upwards [hc.continuousAt.eventually_ne ha] with θ' h' h0
  exact h' (congrFun h0 a)

/-- **Lemma A.30, second sentence, near `θ_τ`:** under the conditions `SmallWritesGeneric`, for
all small `τ ≠ 0` the residual network has `fd = P − d² − s` at every parameter near `θ_τ`. -/
theorem eventually_eventually_funDim_smallWrites_mlp_rescale {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : SmallWritesGeneric θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ), ∀ᶠ θ' in 𝓝 (θ.smallWrites τ),
      funDim (Arch.mlp σ id hid) 1 θ' + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the batch of the first sentence: for small `τ ≠ 0` no pre-activation on it vanishes at
  -- `θ_τ`, and the rank on it is `P - d² - s`
  obtain ⟨n, X, -, h⟩ := exists_eventually_jacobianRank_smallWrites_mlp_rescale hσ hhom hU θ hθ
  have hc := read_col_ne_zero_drs hθ
  filter_upwards [h] with τ hτ
  obtain ⟨hpre, hrank⟩ := hτ
  -- near `θ_τ` the pre-activations on the batch stay off the kinks, where the blocks are `C¹`,
  -- and the rank on the batch does not drop (Residual/SmallWritesOn.lean)
  have hnear := eventually_jacobianRank_ge_of_contDiffOn (Arch.mlp σ id hid) (θ.smallWrites τ)
    rfl 1 (fun ℓ => noZero_drs T (hid ℓ)) (fun ℓ => isOpen_noZero_drs)
    (fun ℓ => (contDiffOn_map_drs hhom).of_le one_le_two) X (fun i ℓ => hpre i ℓ)
  -- near `θ_τ` the embedding has rank `d` and no column of a read vanishes, so `fd ≤ P - d² - s`
  have hE := eventually_rank_E_drs (θ.smallWrites τ) hθ.rank_E
  have hcol := eventually_read_col_ne_zero_drs (θ.smallWrites τ) hc
  filter_upwards [hnear, hE, hcol] with θ' h1 h2 h3
  have h4 := jacobianRank_le_funDim (A := Arch.mlp σ id hid) (S := 1) θ' X
  have h5 := funDim_add_le_residual_mlp_rescale hhom θ' h2 h3
  have h6 := h1.2
  omega

/-- **Lemma A.30 for ReLU blocks, first sentence:** with `d_in, d_out ≥ d ≥ 2` and blocks of any
widths, for generic parameters `θ` there is a finite batch of inputs at which no limit
pre-activation vanishes such that, for all small `τ ≠ 0`, no pre-activation on the batch vanishes
at `θ_τ` and the Jacobian of the residual network on the batch at `θ_τ` has rank
`P − d² − s`. -/
theorem ae_exists_eventually_jacobianRank_smallWrites_relu
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkAll θ) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.mlp relu id hid) 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ) t j
            ≠ 0) ∧
        jacobianRank (Arch.mlp relu id hid) 1 X (θ.smallWrites τ)
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  -- the conditions of Lemma A.27 hold at generic parameters (`Residual/DepthMlp.lean`)
  filter_upwards [ae_smallWritesGeneric μ hd hdIn hdOut] with θ hθ
  exact exists_eventually_jacobianRank_smallWrites_mlp_rescale (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous (relu_unitsRescale _ _ _) θ hθ

/-- **Lemma A.30 for ReLU blocks, second sentence:** with `d_in, d_out ≥ d ≥ 2` and blocks of
any widths, there is an open set `U` of weights on which the residual network has
`fd = P − d² − s`, which contains `θ_τ` for generic `θ` and all small `τ ≠ 0`, and at almost
every point of which the skips add at least `L d²` when every block has at least `d` hidden
units. -/
theorem exists_isOpen_funDim_smallWrites_relu
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut), IsOpen U ∧
      (∀ θ ∈ U, funDim (Arch.mlp relu id hid) 1 θ
          + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) ∧
      (∀ (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
        [μ.IsAddHaarMeasure], ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), θ.smallWrites τ ∈ U) ∧
      (∀ (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
        [μ.IsAddHaarMeasure], (∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) →
        ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp relu id hid) 0 θ + L * Fintype.card d ^ 2
          ≤ funDim (Arch.mlp relu id hid) 1 θ) := by
  -- `U` is the interior of the set where `fd = P - d² - s`
  refine ⟨interior {θ | funDim (Arch.mlp relu id hid) 1 θ
      + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)},
    isOpen_interior, fun θ hθ => interior_subset hθ, ?_, ?_⟩
  · -- for generic `θ` and small `τ ≠ 0`, `fd = P - d² - s` on a neighborhood of `θ_τ`
    intro μ _
    filter_upwards [ae_smallWritesGeneric μ hd hdIn hdOut] with θ hθ
    filter_upwards [eventually_eventually_funDim_smallWrites_mlp_rescale
      (fun _ hz => hasDerivAt_relu hz) relu_homogeneous (relu_unitsRescale _ _ _) θ hθ]
      with τ hτ
    exact mem_interior_iff_mem_nhds.2 hτ
  · -- the gain: `fd_0 + (L + 1) d² + s ≤ P = fd_1 + d² + s` (Theorem 4.3 without skips)
    intro μ _ hhid
    have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
    filter_upwards [ae_funDim_add_le_skipless_relu μ hdIn hhid] with θ h hθU
    have h1 : funDim (Arch.mlp relu id hid) 1 θ + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) :=
      interior_subset hθU
    rw [add_mul, one_mul] at h
    omega

/-- **Lemma A.30 for ReLU² blocks, first sentence.** -/
theorem ae_exists_eventually_jacobianRank_smallWrites_reluSq
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkAll θ) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.mlp reluSq id hid) 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ) t j
            ≠ 0) ∧
        jacobianRank (Arch.mlp reluSq id hid) 1 X (θ.smallWrites τ)
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ
              (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  -- the conditions of Lemma A.27 hold at generic parameters (`Residual/DepthMlp.lean`)
  filter_upwards [ae_smallWritesGeneric μ hd hdIn hdOut] with θ hθ
  exact exists_eventually_jacobianRank_smallWrites_mlp_rescale (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous (reluSq_unitsRescale _ _ _) θ hθ

/-- **Lemma A.30 for ReLU² blocks, second sentence.** -/
theorem exists_isOpen_funDim_smallWrites_reluSq
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut), IsOpen U ∧
      (∀ θ ∈ U, funDim (Arch.mlp reluSq id hid) 1 θ
          + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut)) ∧
      (∀ (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
        [μ.IsAddHaarMeasure], ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), θ.smallWrites τ ∈ U) ∧
      (∀ (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
        [μ.IsAddHaarMeasure], (∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) →
        ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp reluSq id hid) 0 θ + L * Fintype.card d ^ 2
          ≤ funDim (Arch.mlp reluSq id hid) 1 θ) := by
  -- `U` is the interior of the set where `fd = P - d² - s`
  refine ⟨interior {θ | funDim (Arch.mlp reluSq id hid) 1 θ
      + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut)},
    isOpen_interior, fun θ hθ => interior_subset hθ, ?_, ?_⟩
  · -- for generic `θ` and small `τ ≠ 0`, `fd = P - d² - s` on a neighborhood of `θ_τ`
    intro μ _
    filter_upwards [ae_smallWritesGeneric μ hd hdIn hdOut] with θ hθ
    filter_upwards [eventually_eventually_funDim_smallWrites_mlp_rescale
      (fun z _ => hasDerivAt_reluSq z) reluSq_homogeneous (reluSq_unitsRescale _ _ _) θ hθ]
      with τ hτ
    exact mem_interior_iff_mem_nhds.2 hτ
  · -- the gain: `fd_0 + (L + 1) d² + s ≤ P = fd_1 + d² + s` (Theorem 4.3 without skips)
    intro μ _ hhid
    have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
    filter_upwards [ae_funDim_add_le_skipless_reluSq μ hdIn hhid] with θ h hθU
    have h1 : funDim (Arch.mlp reluSq id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) :=
      interior_subset hθU
    rw [add_mul, one_mul] at h
    omega

end Skips
