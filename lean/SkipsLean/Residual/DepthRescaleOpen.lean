import SkipsLean.Residual.DepthRescale

/-!
# Lemma A.30 with inputs in an open set that contains `0`

Paper (skips paper), Lemma A.30 (ReLU-type blocks with small writes): "Let the blocks be ReLU,
ReLU² or ReGLU blocks, without normalization or biases, let `E` and `D` have rank `d_model`, and
let inputs range over all of `ℝ^{1×d_in}`, or over an open set that contains `0`. […] For all small
`τ ≠ 0`, the Jacobian of the residual network at `θ_τ` has rank `P − d_model² − s` on some finite
batch on which no pre-activation vanishes. So the residual network has functional dimension
`P − d_model² − s` on an open set of weights that contains these, and at almost every point of
this set the skips add at least `L d_model²` when every block has width at least `d_model`."

Its proof: "On each region of inputs on which these pre-activations keep their signs, `J_0 η` is a
polynomial in `x`, and the regions are cones with apex `0`. So a direction that is flat on a
neighborhood of `0` is flat at every input at which no pre-activation vanishes […]. Fix a finite
batch of such inputs, inside the set of inputs, on which the kernel of `J_0` is this space".

`Residual/DepthRescale.lean` has the lemma for inputs in all of `ℝ^{T×d_in}`, for MLP blocks with
a positively homogeneous activation (ReLU, ReLU²). Here the second case, for an open set `Ω` of
inputs with `0 ∈ Ω`:

* `smallWritesLimit_eq_zero_of_forall_mem_isOpen_mlp_rescale`: a direction that is flat for `J_0`
  at the inputs of `Ω` at which no limit pre-activation vanishes is flat at every such input. For
  `c > 0`, `(J_0 η)(c x) = c · x (η_E D + E η_D) + c^k · (the terms of the units)`, the inputs at
  which no pre-activation vanishes form a cone, and `c x ∈ Ω` for all small `c > 0`.
* `exists_eventually_jacobianRank_smallWrites_mlp_rescale_of_isOpen`: the first sentence of the
  lemma with the batch inside `Ω`.
* `exists_eventually_eventually_jacobianRank_smallWrites_mlp_rescale_of_isOpen`: near `θ_τ` the
  rank on this batch stays `P − d² − s` and no pre-activation on it vanishes. With
  `eventually_eventually_funDim_smallWrites_mlp_rescale` (the rank on every batch is at most this
  number near `θ_τ`), the functional dimension with inputs in `Ω` is `P − d² − s` near `θ_τ`.
* The statements for ReLU and ReLU² blocks at generic parameters, and the open set of weights.

ReGLU blocks: `Residual/DepthReGLUOpen.lean`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-! ### Helpers: the activation away from its kink (copies of the private helpers of
`Residual/DepthRescale.lean`) -/

/-- Helper (copy of `noZero_drs`): the matrices with no zero entry (for ReLU-type blocks: the
pre-activations with no hidden unit at its kink). -/
private def noZero_dro (m n : Type*) : Set (Matrix m n ℝ) :=
  {M | ∀ t i, M t i ≠ 0}

/-- Helper (copy of `isOpen_noZero_drs`): the matrices with no zero entry form an open set. -/
private theorem isOpen_noZero_dro {m n : Type*} [Fintype m] [Fintype n] :
    IsOpen (noZero_dro m n) := by
  refine isOpen_iff_mem_nhds.2 fun M hM => ?_
  exact Filter.eventually_all.2 fun t => Filter.eventually_all.2 fun i =>
    (continuous_id.matrix_elem t i).continuousAt.eventually_ne (hM t i)

/-- Helper (copy of `contDiffAt_of_homogeneous_drs`): a positively homogeneous `σ` is a monomial
on each side of `0`, hence `C²` at every `z ≠ 0`. -/
private theorem contDiffAt_of_homogeneous_dro {k : ℕ}
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

/-- Helper (copy of `contDiffOn_map_drs`): `M ↦ σ(M)` (entrywise) is `C²` on the matrices with no
zero entry. -/
private theorem contDiffOn_map_dro {k : ℕ}
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {m n : Type*} [Fintype m]
    [Fintype n] : ContDiffOn ℝ 2 (fun M : Matrix m n ℝ => M.map σ) (noZero_dro m n) := by
  intro M hM
  refine ContDiffAt.contDiffWithinAt (contDiffAt_pi.2 fun t => contDiffAt_pi.2 fun i => ?_)
  have hent : ContDiff ℝ 2 (fun M : Matrix m n ℝ => M t i) :=
    contDiff_pi.1 (contDiff_pi.1 contDiff_id t) i
  have h := (contDiffAt_of_homogeneous_dro hhom (hM t i)).comp M hent.contDiffAt
  exact h

/-- Helper (copy of `differentiableAt_map_drs`): `M ↦ σ(M)` (entrywise) is differentiable at a
matrix with no zero entry. -/
private theorem differentiableAt_map_dro (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {m n : Type*} [Fintype m] [Fintype n] {P : Matrix m n ℝ} (hP : ∀ t i, P t i ≠ 0) :
    DifferentiableAt ℝ (fun M : Matrix m n ℝ => M.map σ) P := by
  refine differentiableAt_pi.2 fun t => differentiableAt_pi.2 fun i => ?_
  have hent : Differentiable ℝ (fun M : Matrix m n ℝ => M t i) :=
    differentiable_pi.1 (differentiable_pi.1 differentiable_id t) i
  have h := (hσ _ (hP t i)).differentiableAt.comp P (hent P)
  exact h

/-- Helper (copy of `fderiv_map_apply_drs`): at a matrix `P` with no zero entry, the derivative
of `M ↦ σ(M)` along `Q` has the entries `σ'(P_{t i}) Q_{t i}`. -/
private theorem fderiv_map_apply_dro (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {m n : Type*} [Fintype m] [Fintype n] {P : Matrix m n ℝ} (hP : ∀ t i, P t i ≠ 0)
    (Q : Matrix m n ℝ) (t : m) (i : n) :
    fderiv ℝ (fun M : Matrix m n ℝ => M.map σ) P Q t i = σ' (P t i) * Q t i := by
  -- the chain rule along the line `τ ↦ P + τ Q`
  have hline : HasDerivAt (fun τ : ℝ => P + τ • Q) Q 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const Q).const_add P
    rw [one_smul] at h
    exact h
  have h0 : P = P + (0 : ℝ) • Q := by rw [zero_smul, add_zero]
  have h1 := (differentiableAt_map_dro hσ hP).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0
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
/-- Helper (copy of `fderiv_f_mlp_apply_drs`): the same derivative for the map of block `ℓ` of an
MLP network. -/
private theorem fderiv_f_mlp_apply_dro (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z) (ℓ : Fin L)
    {P : Matrix T (hid ℓ) ℝ} (hP : ∀ t i, P t i ≠ 0) (Q : Matrix T (hid ℓ) ℝ) (t : T)
    (i : hid ℓ) :
    fderiv ℝ ((Arch.mlp (T := T) (d := d) σ id hid).f ℓ) P Q t i = σ' (P t i) * Q t i :=
  fderiv_map_apply_dro hσ hP Q t i

/-- Helper: the derivative of a positively homogeneous `σ` of degree `k` scales as
`σ'(c z) c = c^k σ'(z)` at `z ≠ 0`, `c > 0`: both are the derivative at `z` of
`y ↦ σ(c y) = c^k σ(y)`. -/
private theorem deriv_mul_homogeneous_dro {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) {c z : ℝ} (hc : 0 < c)
    (hz : z ≠ 0) : σ' (c * z) * c = c ^ k * σ' z := by
  have h1 := (hσ (c * z) (mul_ne_zero hc.ne' hz)).comp z ((hasDerivAt_id' z).const_mul c)
  have hfun : (σ ∘ fun y => c * y) = fun y => c ^ k * σ y := funext fun y => hhom c y hc
  rw [hfun, mul_one] at h1
  exact h1.unique ((hσ z hz).const_mul (c ^ k))

/-- Helper: if `c a + c^k b = 0` for `c = 2 e` and for `c = e`, with `e > 0`, then `a + b = 0`
(for `k = 1` from one value of `c`; for `k ≠ 1`, `2^k ≠ 2` gives `b = 0` and then `a = 0`). -/
private theorem add_eq_zero_of_two_scales_dro {k : ℕ} {a b e : ℝ} (he : 0 < e)
    (h1 : (2 * e) * a + (2 * e) ^ k * b = 0) (h2 : e * a + e ^ k * b = 0) : a + b = 0 := by
  by_cases hk : k = 1
  · subst hk
    rw [pow_one] at h2
    have h : e * (a + b) = 0 := by linear_combination h2
    exact (mul_eq_zero.1 h).resolve_left he.ne'
  · -- `(2^k - 2) e^k b = 0` and `2^k ≠ 2`, so `b = 0`, and then `e a = 0`
    have h3 : ((2 : ℝ) ^ k - 2) * e ^ k * b = 0 := by
      rw [mul_pow] at h1
      linear_combination h1 - 2 * h2
    have h4 : (2 : ℝ) ^ k - 2 ≠ 0 := by
      intro h
      apply hk
      have h5 : (2 : ℝ) ^ k = 2 ^ 1 := by
        rw [pow_one]
        linarith
      exact (pow_right_inj₀ (by norm_num) (by norm_num)).1 h5
    have hb : b = 0 := by
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h (mul_ne_zero h4 (pow_ne_zero _ he.ne'))
      · exact h
    rw [hb, mul_zero, add_zero] at h2
    rw [hb, add_zero]
    exact (mul_eq_zero.1 h2).resolve_left he.ne'

/-! ### Helpers: the limit `J_0` for MLP blocks at the inputs off the kinks -/

/-- Helper (copy of `mul_add_mul_apply_drs`): an entry of `M N + M' N'`. -/
private theorem mul_add_mul_apply_dro {m n k : Type*} [Fintype n] (M M' : Matrix m n ℝ)
    (N N' : Matrix n k ℝ) (t : m) (o : k) :
    (M * N + M' * N') t o = ∑ i, (M t i * N i o + M' t i * N' i o) := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (copy of `smallWritesLimit_mlp_apply_drs`): the entries of `(J_0 η)(x)` at an input
of `noKinkAll θ`,
`(x ψ_M)_{t o} + ∑_ℓ ∑_i [σ(z_{ℓ i}) (ψ_A^ℓ)_{i o} + σ'(z_{ℓ i}) (x ψ_C^ℓ)_{t i} (A^ℓ)_{i o}]` with
`z_{ℓ i} = (x C^ℓ)_{t i}`. -/
private theorem smallWritesLimit_mlp_apply_dro (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
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
    exact mul_add_mul_apply_dro _ _ _ _ t o
  rw [e]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- no pre-activation `x E W_read^ℓ` vanishes, so the derivative of `σ` is `σ'` there
  have hP : ∀ t i, (x * θ.E * θ.read ℓ) t i ≠ 0 := hx ℓ
  rw [fderiv_f_mlp_apply_dro hσ ℓ hP, Matrix.mul_assoc x θ.E (θ.read ℓ),
    Matrix.mul_assoc x θ.E (η.read ℓ)]
  show σ' _ * _ * _ + σ _ * _ = _
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the inputs at which no limit pre-activation vanishes form a cone: with `x`, every
`c x` with `c ≠ 0` (every pre-activation is multiplied by `c`). -/
private theorem smul_mem_noKinkAll_dro
    {θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut} {x : Matrix T dIn ℝ}
    (hx : x ∈ noKinkAll θ) {c : ℝ} (hc : c ≠ 0) : c • x ∈ noKinkAll θ := by
  intro ℓ t i
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  exact mul_ne_zero hc (hx ℓ t i)

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: at an input `x` of `noKinkAll θ` and `c > 0`, `(J_0 η)(c x) = c A(x) + c^k B(x)`
entrywise, with `A(x) = x (η_E D + E η_D)` and `B(x)` the terms of the units: `σ(c z) = c^k σ(z)`
and `σ'(c z) (c n) = c^k σ'(z) n`. -/
private theorem smallWritesLimit_smul_apply_dro {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ noKinkAll θ) {c : ℝ} (hc : 0 < c) (t : T) (o : dOut) :
    smallWritesLimit (Arch.mlp σ id hid) θ η (c • x) t o
      = c * (x * (η.E * θ.D + θ.E * η.D)) t o + c ^ k * ∑ ℓ, ∑ i : hid ℓ,
        (σ ((x * (θ.E * θ.read ℓ)) t i) * (η.write ℓ * θ.D) i o
          + σ' ((x * (θ.E * θ.read ℓ)) t i) * (x * (θ.E * η.read ℓ)) t i
            * (θ.write ℓ * θ.D) i o) := by
  rw [smallWritesLimit_mlp_apply_dro hσ θ η _ (smul_mem_noKinkAll_dro hx hc.ne'),
    Finset.mul_sum]
  simp only [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- `σ(c z) = c^k σ(z)` and `σ'(c z) c = c^k σ'(z)` at `z ≠ 0`
  have hz : (x * (θ.E * θ.read ℓ)) t i ≠ 0 := by
    rw [← Matrix.mul_assoc]
    exact hx ℓ t i
  rw [hhom c _ hc]
  have hd := deriv_mul_homogeneous_dro hσ hhom hc hz
  linear_combination ((x * (θ.E * η.read ℓ)) t i * (θ.write ℓ * θ.D) i o) * hd

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- **Proof of Lemma A.30, "a direction that is flat on a neighborhood of `0` is flat at every
input at which no pre-activation vanishes", for MLP blocks with an activation that is positively
homogeneous of degree `k`:** let `Ω` be an open set of inputs that contains `0`. If
`(J_0 η)(x) = 0` at every input of `Ω` at which no limit pre-activation vanishes, then
`(J_0 η)(x) = 0` at every input at which no limit pre-activation vanishes. -/
theorem smallWritesLimit_eq_zero_of_forall_mem_isOpen_mlp_rescale {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω)
    (hη : ∀ x ∈ Ω, x ∈ noKinkAll θ → smallWritesLimit (Arch.mlp σ id hid) θ η x = 0) :
    ∀ x ∈ noKinkAll θ, smallWritesLimit (Arch.mlp σ id hid) θ η x = 0 := by
  intro x hx
  -- `c x ∈ Ω` for all small `c` (`c x → 0` as `c → 0`, and `Ω` is a neighborhood of `0`)
  have hlim : Tendsto (fun c : ℝ => c • x) (𝓝 0) (𝓝 0) := by
    have h : Continuous fun c : ℝ => c • x := continuous_id.smul continuous_const
    simpa only [zero_smul] using h.tendsto 0
  obtain ⟨ε, hε, hεΩ⟩ := Metric.eventually_nhds_iff.1 (hlim.eventually (hΩ.mem_nhds h0))
  -- for `0 < c < ε`, `c x` is an input of `Ω` off the kinks, so `c A(x) + c^k B(x) = 0`
  have key : ∀ c : ℝ, 0 < c → c < ε → ∀ t o,
      c * (x * (η.E * θ.D + θ.E * η.D)) t o + c ^ k * ∑ ℓ, ∑ i : hid ℓ,
        (σ ((x * (θ.E * θ.read ℓ)) t i) * (η.write ℓ * θ.D) i o
          + σ' ((x * (θ.E * θ.read ℓ)) t i) * (x * (θ.E * η.read ℓ)) t i
            * (θ.write ℓ * θ.D) i o) = 0 := by
    intro c hc hcε t o
    have hcΩ : c • x ∈ Ω := hεΩ (by rwa [Real.dist_0_eq_abs, abs_of_pos hc])
    have h := congrFun (congrFun (hη _ hcΩ (smul_mem_noKinkAll_dro hx hc.ne')) t) o
    rw [smallWritesLimit_smul_apply_dro hσ hhom θ η x hx hc] at h
    exact h
  -- two values of `c` give `A(x) + B(x) = 0`, entry by entry
  ext t o
  rw [smallWritesLimit_mlp_apply_dro hσ θ η x hx, Matrix.zero_apply]
  have he : (0 : ℝ) < ε / 4 := by positivity
  have h1 := key (2 * (ε / 4)) (by positivity) (by linarith) t o
  have h2 := key (ε / 4) he (by linarith) t o
  exact add_eq_zero_of_two_scales_dro he h1 h2

/-! ### Helpers: the batch and the space of the flat directions of `J_0` (copies of the private
helpers of `Residual/DepthRescale.lean`) -/

/-- Helper (copy of `limitLin_drs`): `η ↦ (J_0 η)(x)` is linear in `η`. -/
private noncomputable def limitLin_dro (A : Arch T d L) (θ : Params A dIn dOut)
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

/-- Helper (copy of `exists_batch_ker_drs`, kernel stabilisation): for a family of linear maps on
a finite-dimensional space, finitely many of them have the common kernel of all of them. -/
private theorem exists_batch_ker_dro {ι P F : Type*} [AddCommGroup P] [Module ℝ P]
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

/-- Helper (copy of `flatConstLin_drs`): the directions `X ↦ (E X, 0, 0, -X D)` of one change of
basis at all hidden states, as a linear map. -/
private def flatConstLin_dro (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
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

/-- Helper (copy of `rescaleLin_drs`): `α ↦ rescaleDirMlp k θ α` is linear. -/
private noncomputable def rescaleLin_dro (k : ℕ)
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

/-- Helper (copy of `finrank_hidFun_drs`): the numbers of the rescalings of the hidden units form
a space of dimension `s`, the number of hidden units. -/
private theorem finrank_hidFun_dro :
    Module.finrank ℝ (∀ ℓ, hid ℓ → ℝ) = ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]

omit [Nonempty T] [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `finrank_range_flatLin_le_drs`): the directions
`(E X, (λ W_read^ℓ)_ℓ, (-k λ W_write^ℓ)_ℓ, -X D)` form a space of dimension at most `d² + s`. -/
private theorem finrank_range_flatLin_le_dro (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Module.finrank ℝ (LinearMap.range ((flatConstLin_dro θ).coprod (rescaleLin_dro k θ)))
      ≤ Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) := by
  have h := LinearMap.finrank_range_le ((flatConstLin_dro θ).coprod (rescaleLin_dro k θ))
  rwa [Module.finrank_prod, Module.finrank_matrix, Module.finrank_self, mul_one, ← sq,
    finrank_hidFun_dro] at h

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] in
/-- Helper (copy of `read_col_ne_zero_drs`): no column of a read vanishes when no column of
`E W_read` vanishes. -/
private theorem read_col_ne_zero_dro
    {θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut} (hθ : SmallWritesGeneric θ) :
    ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0 := by
  intro ℓ i h0
  apply hθ.col_ne_zero ℓ i
  funext a
  show ∑ j, θ.E a j * θ.read ℓ j i = 0
  exact Finset.sum_eq_zero fun j _ => by
    rw [show θ.read ℓ j i = 0 from congrFun h0 j, mul_zero]

/-- **Lemma A.30, first sentence, with inputs in an open set that contains `0`, at one
parameter:** under the conditions `SmallWritesGeneric`, for an open set `Ω` of inputs with
`0 ∈ Ω` there is a finite batch of inputs of `Ω` at which no limit pre-activation vanishes such
that, for all small `τ ≠ 0`, no pre-activation on the batch vanishes at `θ_τ` and the Jacobian of
the residual network on the batch at `θ_τ` has rank `P − d² − s`. -/
theorem exists_eventually_jacobianRank_smallWrites_mlp_rescale_of_isOpen {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : SmallWritesGeneric θ)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧ (∀ i, X i ∈ noKinkAll θ) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.mlp σ id hid) 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) ∧
        jacobianRank (Arch.mlp σ id hid) 1 X (θ.smallWrites τ)
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the maps `η ↦ (J_0 η)(x)`, `x ∈ Ω ∩ noKinkAll θ`, are linear: a finite batch `X` in
  -- `Ω ∩ noKinkAll θ` decides their common kernel
  obtain ⟨n, X', hX'⟩ := exists_batch_ker_dro
    (fun x : {x // x ∈ Ω ∧ x ∈ noKinkAll θ} =>
      limitLin_dro (Arch.mlp σ id hid) θ (dOut := dOut) x.1)
  refine ⟨n, fun i => (X' i).1, fun i => (X' i).2.1, fun i => (X' i).2.2, ?_⟩
  -- a direction that is flat for `J_0` on the batch is flat at every input of `Ω ∩ noKinkAll θ`,
  -- hence (the cone argument) at every input of `noKinkAll θ`, so (the kernel of `J_0`) it lies
  -- in the space `W` of the directions `(E X, (λ W_read^ℓ)_ℓ, (-k λ W_write^ℓ)_ℓ, -X D)`, of
  -- dimension at most `d² + s`
  have hW : ∀ η, (∀ i, smallWritesLimit (Arch.mlp σ id hid) θ η (X' i).1 = 0) →
      η ∈ LinearMap.range ((flatConstLin_dro θ).coprod (rescaleLin_dro k θ)) := by
    intro η hη
    have hΩη : ∀ x ∈ Ω, x ∈ noKinkAll θ → smallWritesLimit (Arch.mlp σ id hid) θ η x = 0 :=
      fun x hxΩ hx => hX' η hη ⟨x, hxΩ, hx⟩
    have hall := smallWritesLimit_eq_zero_of_forall_mem_isOpen_mlp_rescale hσ hhom θ η hΩ h0 hΩη
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
  have hdim := finrank_range_flatLin_le_dro k θ
  -- `≥`: for small `τ ≠ 0` the pre-activations on the batch stay off the kinks, where the
  -- blocks are `C²`, and the rank is at least `P - dim W` (Residual/SmallWritesOn.lean)
  filter_upwards [eventually_jacobianRank_smallWrites_ge_of_contDiffOn (Arch.mlp σ id hid) θ rfl
    (fun ℓ => noZero_dro T (hid ℓ)) (fun ℓ => isOpen_noZero_dro)
    (fun ℓ => contDiffOn_map_dro hhom) (fun i => (X' i).1) (fun i ℓ => (X' i).2.2 ℓ) _ hW]
    with τ hτ
  obtain ⟨hpre, hge⟩ := hτ
  refine ⟨fun i ℓ t j => hpre i ℓ t j, ?_⟩
  -- `≤`: the rank is at most `fd(θ_τ) ≤ P - d² - s` (the embedding and the reads of `θ_τ` are
  -- those of `θ`)
  have h1 := jacobianRank_le_funDim (A := Arch.mlp σ id hid) (S := 1) (θ.smallWrites τ)
    (fun i => (X' i).1)
  have hc := read_col_ne_zero_dro hθ
  have h2 := funDim_add_le_residual_mlp_rescale hhom (θ.smallWrites τ) hθ.rank_E hc
  omega

/-! ### Helpers: the conditions of the upper bound are open (copies of the private helpers of
`Residual/DepthRescale.lean`) -/

omit [Fintype T] [Nonempty T] in
/-- Helper (copy of `eventually_rank_E_drs`, lower semicontinuity of the rank): if the embedding
of `θ₀` has rank `d`, so has the embedding of every parameter near `θ₀`. -/
private theorem eventually_rank_E_dro
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
/-- Helper (copy of `eventually_read_col_ne_zero_drs`): if no column of a read of `θ₀` vanishes,
the same holds near `θ₀`. -/
private theorem eventually_read_col_ne_zero_dro
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

/-- **Lemma A.30, second sentence, with inputs in an open set that contains `0`, near `θ_τ`:**
under the conditions `SmallWritesGeneric`, for an open set `Ω` of inputs with `0 ∈ Ω` there is a
finite batch of inputs of `Ω` such that, for all small `τ ≠ 0` and every parameter `θ'` near
`θ_τ`, no pre-activation on the batch vanishes at `θ'` and the Jacobian of the residual network on
the batch at `θ'` has rank `P − d² − s`. (Near `θ_τ` the rank on every batch is at most this
number: `eventually_eventually_funDim_smallWrites_mlp_rescale`.) -/
theorem exists_eventually_eventually_jacobianRank_smallWrites_mlp_rescale_of_isOpen {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : SmallWritesGeneric θ)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ), ∀ᶠ θ' in 𝓝 (θ.smallWrites τ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.mlp σ id hid) 1 θ' (X i) ℓ.castSucc * θ'.read ℓ) t j ≠ 0) ∧
        jacobianRank (Arch.mlp σ id hid) 1 X θ'
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the batch of the first sentence, inside `Ω`: for small `τ ≠ 0` no pre-activation on it
  -- vanishes at `θ_τ`, and the rank on it is `P - d² - s`
  obtain ⟨n, X, hXΩ, -, h⟩ :=
    exists_eventually_jacobianRank_smallWrites_mlp_rescale_of_isOpen hσ hhom hU θ hθ hΩ h0
  refine ⟨n, X, hXΩ, ?_⟩
  have hc := read_col_ne_zero_dro hθ
  filter_upwards [h] with τ hτ
  obtain ⟨hpre, hrank⟩ := hτ
  -- near `θ_τ` the pre-activations on the batch stay off the kinks, where the blocks are `C¹`,
  -- and the rank on the batch does not drop (Residual/SmallWritesOn.lean)
  have hnear := eventually_jacobianRank_ge_of_contDiffOn (Arch.mlp σ id hid) (θ.smallWrites τ)
    rfl 1 (fun ℓ => noZero_dro T (hid ℓ)) (fun ℓ => isOpen_noZero_dro)
    (fun ℓ => (contDiffOn_map_dro hhom).of_le one_le_two) X (fun i ℓ => hpre i ℓ)
  -- near `θ_τ` the embedding has rank `d` and no column of a read vanishes, so the rank on the
  -- batch is at most `fd ≤ P - d² - s`
  have hE := eventually_rank_E_dro (θ.smallWrites τ) hθ.rank_E
  have hcol := eventually_read_col_ne_zero_dro (θ.smallWrites τ) hc
  filter_upwards [hnear, hE, hcol] with θ' h1 h2 h3
  refine ⟨fun i ℓ t j => h1.1 i ℓ t j, ?_⟩
  have h4 := jacobianRank_le_funDim (A := Arch.mlp σ id hid) (S := 1) θ' X
  have h5 := funDim_add_le_residual_mlp_rescale hhom θ' h2 h3
  have h6 := h1.2
  omega

/-- **Lemma A.30 for ReLU blocks with inputs in an open set that contains `0`:** with
`d_in, d_out ≥ d ≥ 2` and blocks of any widths, for an open set `Ω` of inputs with `0 ∈ Ω`, there
is an open set `U` of weights such that: at every `θ ∈ U` the residual network has
`fd = P − d² − s`, attained by the rank of the Jacobian on a finite batch of inputs of `Ω` on
which no pre-activation vanishes; `U` contains `θ_τ` for generic `θ` and all small `τ ≠ 0`; and at
almost every point of `U` the skips add at least `L d²` when every block has at least `d` hidden
units. -/
theorem exists_isOpen_jacobianRank_smallWrites_relu_of_isOpen
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut), IsOpen U ∧
      (∀ θ ∈ U, funDim (Arch.mlp relu id hid) 1 θ
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) ∧
        ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧
          (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
            (hidden (Arch.mlp relu id hid) 1 θ (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) ∧
          jacobianRank (Arch.mlp relu id hid) 1 X θ
              + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
            = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) ∧
      (∀ (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
        [μ.IsAddHaarMeasure], ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), θ.smallWrites τ ∈ U) ∧
      (∀ (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
        [μ.IsAddHaarMeasure], (∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) →
        ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp relu id hid) 0 θ + L * Fintype.card d ^ 2
          ≤ funDim (Arch.mlp relu id hid) 1 θ) := by
  -- `U` is the interior of the set where `fd = P - d² - s` and some batch inside `Ω`, off the
  -- kinks, has rank `P - d² - s`
  refine ⟨interior {θ | funDim (Arch.mlp relu id hid) 1 θ
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) ∧
        ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧
          (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
            (hidden (Arch.mlp relu id hid) 1 θ (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) ∧
          jacobianRank (Arch.mlp relu id hid) 1 X θ
              + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
            = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)},
    isOpen_interior, fun θ hθ => interior_subset hθ, ?_, ?_⟩
  · -- for generic `θ` and small `τ ≠ 0`, both hold on a neighborhood of `θ_τ`, with one batch
    intro μ _
    filter_upwards [ae_smallWritesGeneric μ hd hdIn hdOut] with θ hθ
    obtain ⟨n, X, hXΩ, h⟩ :=
      exists_eventually_eventually_jacobianRank_smallWrites_mlp_rescale_of_isOpen
        (fun _ hz => hasDerivAt_relu hz) relu_homogeneous (relu_unitsRescale _ _ _) θ hθ hΩ h0
    filter_upwards [h, eventually_eventually_funDim_smallWrites_mlp_rescale
      (fun _ hz => hasDerivAt_relu hz) relu_homogeneous (relu_unitsRescale _ _ _) θ hθ]
      with τ hτ hτ'
    refine mem_interior_iff_mem_nhds.2 ?_
    filter_upwards [hτ, hτ'] with θ' h1 h2
    exact ⟨h2, n, X, hXΩ, h1.1, h1.2⟩
  · -- the gain: `fd_0 + (L + 1) d² + s ≤ P = fd_1 + d² + s` (Theorem 4.3 without skips)
    intro μ _ hhid
    have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
    filter_upwards [ae_funDim_add_le_skipless_relu μ hdIn hhid] with θ h hθU
    obtain ⟨h1, -⟩ := interior_subset hθU
    rw [add_mul, one_mul] at h
    omega

/-- **Lemma A.30 for ReLU² blocks with inputs in an open set that contains `0`:** as
`exists_isOpen_jacobianRank_smallWrites_relu_of_isOpen`. -/
theorem exists_isOpen_jacobianRank_smallWrites_reluSq_of_isOpen
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut), IsOpen U ∧
      (∀ θ ∈ U, funDim (Arch.mlp reluSq id hid) 1 θ
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) ∧
        ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧
          (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
            (hidden (Arch.mlp reluSq id hid) 1 θ (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) ∧
          jacobianRank (Arch.mlp reluSq id hid) 1 X θ
              + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
            = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut)) ∧
      (∀ (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
        [μ.IsAddHaarMeasure], ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), θ.smallWrites τ ∈ U) ∧
      (∀ (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
        [μ.IsAddHaarMeasure], (∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) →
        ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp reluSq id hid) 0 θ + L * Fintype.card d ^ 2
          ≤ funDim (Arch.mlp reluSq id hid) 1 θ) := by
  -- `U` is the interior of the set where `fd = P - d² - s` and some batch inside `Ω`, off the
  -- kinks, has rank `P - d² - s`
  refine ⟨interior {θ | funDim (Arch.mlp reluSq id hid) 1 θ
            + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) ∧
        ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧
          (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
            (hidden (Arch.mlp reluSq id hid) 1 θ (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) ∧
          jacobianRank (Arch.mlp reluSq id hid) 1 X θ
              + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
            = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut)},
    isOpen_interior, fun θ hθ => interior_subset hθ, ?_, ?_⟩
  · -- for generic `θ` and small `τ ≠ 0`, both hold on a neighborhood of `θ_τ`, with one batch
    intro μ _
    filter_upwards [ae_smallWritesGeneric μ hd hdIn hdOut] with θ hθ
    obtain ⟨n, X, hXΩ, h⟩ :=
      exists_eventually_eventually_jacobianRank_smallWrites_mlp_rescale_of_isOpen
        (fun z _ => hasDerivAt_reluSq z) reluSq_homogeneous (reluSq_unitsRescale _ _ _) θ hθ hΩ
          h0
    filter_upwards [h, eventually_eventually_funDim_smallWrites_mlp_rescale
      (fun z _ => hasDerivAt_reluSq z) reluSq_homogeneous (reluSq_unitsRescale _ _ _) θ hθ]
      with τ hτ hτ'
    refine mem_interior_iff_mem_nhds.2 ?_
    filter_upwards [hτ, hτ'] with θ' h1 h2
    exact ⟨h2, n, X, hXΩ, h1.1, h1.2⟩
  · -- the gain: `fd_0 + (L + 1) d² + s ≤ P = fd_1 + d² + s` (Theorem 4.3 without skips)
    intro μ _ hhid
    have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
    filter_upwards [ae_funDim_add_le_skipless_reluSq μ hdIn hhid] with θ h hθU
    obtain ⟨h1, -⟩ := interior_subset hθU
    rw [add_mul, one_mul] at h
    omega

end Skips
