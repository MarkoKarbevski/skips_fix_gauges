import SkipsLean.Residual.DepthReGLU

/-!
# Lemma A.30 for ReGLU blocks with inputs in an open set that contains `0`

Paper (skips paper), Lemma A.30: "Let the blocks be ReLU, ReLU² or ReGLU blocks, without
normalization or biases, let `E` and `D` have rank `d_model`, and let inputs range over all of
`ℝ^{1×d_in}`, or over an open set that contains `0`." Its proof: "On each region of inputs on which
these pre-activations keep their signs, `J_0 η` is a polynomial in `x`, and the regions are cones
with apex `0`. So a direction that is flat on a neighborhood of `0` is flat at every input at
which no pre-activation vanishes".

`Residual/DepthReGLU.lean` has the lemma for inputs in all of `ℝ^{T×d_in}`. Here the second case,
for an open set `Ω` of inputs with `0 ∈ Ω`, as in `Residual/DepthRescaleOpen.lean` for ReLU and
ReLU² blocks. A ReGLU unit `relu(g) v` is positively homogeneous of degree `2` in its gate and
value together, so for `c > 0`, `(J_0 η)(c x) = c · x (η_E D + E η_D) + c² · (the terms of the
units)`. The inputs are those at which no gate pre-activation vanishes (`noKinkGateAll`); `s` is
twice the number of hidden units (the rescalings of the values and of the gates).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-! ### Helpers: the block map near pre-activations with no gate at its kink (copies of the
private helpers of `Residual/DepthReGLU.lean`) -/

/-- Helper (copy of `contDiffAt_relu_drg`): `relu` is `C²` away from its kink. -/
private theorem contDiffAt_relu_dgo {z : ℝ} (hz : z ≠ 0) : ContDiffAt ℝ 2 relu z := by
  rcases hz.lt_or_gt with hneg | hpos
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [eventually_lt_nhds hneg] with y hy
    exact max_eq_right hy.le
  · refine contDiffAt_id.congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds hpos] with y hy
    exact max_eq_left hy.le

omit [Nonempty T] in
/-- Helper (copy of `isOpen_gateSet_drg`): the pre-activations of block `ℓ` with no gate at its
kink form an open set. -/
private theorem isOpen_gateSet_dgo (ℓ : Fin L) :
    IsOpen {M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0} := by
  have h : {M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0}
      = ⋂ t, ⋂ i, {M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ | M t (Sum.inl i) ≠ 0} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun t => isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun (continuous_id.matrix_elem t (Sum.inl i)) continuous_const

omit [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper (copy of `contDiffAt_f_drg`): at a pre-activation with no gate at its kink, the map of
a ReGLU block is `C²`. -/
private theorem contDiffAt_f_dgo (ℓ : Fin L) (M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ)
    (hM : ∀ t i, M t (Sum.inl i) ≠ 0) :
    ContDiffAt ℝ 2 ((Arch.gated (T := T) (d := d) relu id hid).f ℓ) M := by
  refine contDiffAt_pi.2 fun t => contDiffAt_pi.2 fun i => ?_
  have he : ∀ j, ContDiffAt ℝ 2 (fun N : Matrix T (hid ℓ ⊕ hid ℓ) ℝ => N t j) M := fun j =>
    (contDiff_apply_apply ℝ t j).contDiffAt
  have h := ((contDiffAt_relu_dgo (hM t i)).comp M (he (Sum.inl i))).mul (he (Sum.inr i))
  exact h

omit [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper (copy of `contDiffOn_f_drg`): the map of a ReGLU block is `C²` on the pre-activations
with no gate at its kink. -/
private theorem contDiffOn_f_dgo (ℓ : Fin L) :
    ContDiffOn ℝ 2 ((Arch.gated (T := T) (d := d) relu id hid).f ℓ)
      {M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0} := by
  intro M hM
  exact (contDiffAt_f_dgo ℓ M hM).contDiffWithinAt

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `hasDerivAt_affine_drg`): `τ ↦ a + τ b` has the derivative `b` at `0`. -/
private theorem hasDerivAt_affine_dgo (a b : ℝ) : HasDerivAt (fun τ : ℝ => a + τ * b) b 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const b).const_add a
  rw [one_mul] at h
  exact h

omit [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper (copy of `fderiv_f_apply_drg`): the derivative of the map of a ReGLU block at `M` with
no gate at its kink, along `N`, entry `(t, i)`: `1[M_{t, g i} > 0] N_{t, g i} M_{t, v i}
+ relu(M_{t, g i}) N_{t, v i}`. -/
private theorem fderiv_f_apply_dgo (ℓ : Fin L) (M N : Matrix T (hid ℓ ⊕ hid ℓ) ℝ)
    (hM : ∀ t i, M t (Sum.inl i) ≠ 0) (t : T) (i : hid ℓ) :
    fderiv ℝ ((Arch.gated (T := T) (d := d) relu id hid).f ℓ) M N t i
      = reluDeriv (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + relu (M t (Sum.inl i)) * N t (Sum.inr i) := by
  have hd := (contDiffAt_f_dgo (d := d) ℓ M hM).differentiableAt two_ne_zero
  -- the chain rule along the line `τ ↦ M + τ N`
  have hline : HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
    rw [one_smul] at h
    exact h
  have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by rw [zero_smul, add_zero])
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) i
  -- the same derivative computed on the entry `(t, i)`
  have h3 : HasDerivAt (fun τ : ℝ => relu (M t (Sum.inl i) + τ * N t (Sum.inl i))
      * (M t (Sum.inr i) + τ * N t (Sum.inr i)))
      (reluDeriv (M t (Sum.inl i)) * N t (Sum.inl i) * M t (Sum.inr i)
        + relu (M t (Sum.inl i)) * N t (Sum.inr i)) 0 := by
    have hu := hasDerivAt_affine_dgo (M t (Sum.inl i)) (N t (Sum.inl i))
    have hw := hasDerivAt_affine_dgo (M t (Sum.inr i)) (N t (Sum.inr i))
    have h := ((hasDerivAt_relu (hM t i)).comp_of_eq (0 : ℝ) hu
      (by simp only [zero_mul, add_zero])).mul hw
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, add_zero]
  exact h2.unique h3

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (copy of `smallWritesLimit_apply_drg`): the entries of `(J_0 η)(x)` at an input with no
gate at its kink: `(x ψ_M)_{t o} + ∑_ℓ ∑_i [relu(z) w (ψ_A)_{i o} + 1[z > 0] (x ψ_C)_{t, g i} w
A_{i o} + relu(z) (x ψ_C)_{t, v i} A_{i o}]`, with `z = (x C)_{t, g i}`, `w = (x C)_{t, v i}`. -/
private theorem smallWritesLimit_apply_dgo
    (θ η : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ noKinkGateAll θ) (t : T) (o : dOut) :
    smallWritesLimit (Arch.gated relu id hid) θ η x t o
      = (x * (η.E * θ.D + θ.E * η.D)) t o + ∑ ℓ, ∑ i : hid ℓ,
        (relu ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * θ.read ℓ)) t (Sum.inr i)
            * (η.write ℓ * θ.D) i o
          + reluDeriv ((x * (θ.E * θ.read ℓ)) t (Sum.inl i))
            * (x * (θ.E * η.read ℓ)) t (Sum.inl i)
            * (x * (θ.E * θ.read ℓ)) t (Sum.inr i) * (θ.write ℓ * θ.D) i o
          + relu ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * η.read ℓ)) t (Sum.inr i)
            * (θ.write ℓ * θ.D) i o) := by
  unfold smallWritesLimit
  rw [Matrix.add_apply, Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc _ (η.write ℓ), Matrix.add_apply,
    Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_f_apply_dgo ℓ _ _ (hx ℓ), Matrix.mul_assoc x θ.E (θ.read ℓ),
    Matrix.mul_assoc x θ.E (η.read ℓ)]
  have hf : (Arch.gated (T := T) (d := d) relu id hid).f ℓ (x * (θ.E * θ.read ℓ)) t i
      = relu ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * θ.read ℓ)) t (Sum.inr i) := rfl
  rw [hf]
  ring

/-! ### Helpers: the cone argument -/

/-- Helper: the derivative of `relu` off its kink does not change under `z ↦ c z`, `c > 0`. -/
private theorem reluDeriv_mul_dgo {c : ℝ} (hc : 0 < c) (z : ℝ) :
    reluDeriv (c * z) = reluDeriv z := by
  simp only [reluDeriv, mul_pos_iff_of_pos_left hc]

/-- Helper: if `c a + c² b = 0` for `c = 2 e` and for `c = e`, with `e > 0`, then `a + b = 0`
(the two equations give `2 e² b = 0`, so `b = 0`, and then `e a = 0`). -/
private theorem add_eq_zero_of_two_scales_dgo {a b e : ℝ} (he : 0 < e)
    (h1 : (2 * e) * a + (2 * e) ^ 2 * b = 0) (h2 : e * a + e ^ 2 * b = 0) : a + b = 0 := by
  have h3 : 2 * e ^ 2 * b = 0 := by linear_combination h1 - 2 * h2
  have hb : b = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h (mul_ne_zero two_ne_zero (pow_ne_zero 2 he.ne'))
    · exact h
  rw [hb, mul_zero, add_zero] at h2
  rw [hb, add_zero]
  exact (mul_eq_zero.1 h2).resolve_left he.ne'

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the inputs at which no limit pre-activation of a gate vanishes form a cone: with `x`,
every `c x` with `c ≠ 0`. -/
private theorem smul_mem_noKinkGateAll_dgo
    {θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut} {x : Matrix T dIn ℝ}
    (hx : x ∈ noKinkGateAll θ) {c : ℝ} (hc : c ≠ 0) : c • x ∈ noKinkGateAll θ := by
  intro ℓ t i
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  exact mul_ne_zero hc (hx ℓ t i)

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: at an input `x` of `noKinkGateAll θ` and `c > 0`, `(J_0 η)(c x) = c A(x) + c² B(x)`
entrywise, with `A(x) = x (η_E D + E η_D)` and `B(x)` the terms of the units: each is a product of
two entries of `x E W_read` or `x E η_read`, with `relu(c z) = c relu(z)` and
`1[c z > 0] = 1[z > 0]`. -/
private theorem smallWritesLimit_smul_apply_dgo
    (θ η : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ noKinkGateAll θ) {c : ℝ} (hc : 0 < c) (t : T) (o : dOut) :
    smallWritesLimit (Arch.gated relu id hid) θ η (c • x) t o
      = c * (x * (η.E * θ.D + θ.E * η.D)) t o + c ^ 2 * ∑ ℓ, ∑ i : hid ℓ,
        (relu ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * θ.read ℓ)) t (Sum.inr i)
            * (η.write ℓ * θ.D) i o
          + reluDeriv ((x * (θ.E * θ.read ℓ)) t (Sum.inl i))
            * (x * (θ.E * η.read ℓ)) t (Sum.inl i)
            * (x * (θ.E * θ.read ℓ)) t (Sum.inr i) * (θ.write ℓ * θ.D) i o
          + relu ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * η.read ℓ)) t (Sum.inr i)
            * (θ.write ℓ * θ.D) i o) := by
  rw [smallWritesLimit_apply_dgo θ η _ (smul_mem_noKinkGateAll_dgo hx hc.ne'), Finset.mul_sum]
  simp only [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [relu_homogeneous c _ hc, reluDeriv_mul_dgo hc, pow_one]
  ring

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- **Proof of Lemma A.30, "a direction that is flat on a neighborhood of `0` is flat at every
input at which no pre-activation vanishes", for ReGLU blocks:** let `Ω` be an open set of inputs
that contains `0`. If `(J_0 η)(x) = 0` at every input of `Ω` at which no limit pre-activation of
a gate vanishes, then `(J_0 η)(x) = 0` at every input at which no limit pre-activation of a gate
vanishes. -/
theorem smallWritesLimit_eq_zero_of_forall_mem_isOpen_reglu
    (θ η : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω)
    (hη : ∀ x ∈ Ω, x ∈ noKinkGateAll θ →
      smallWritesLimit (Arch.gated relu id hid) θ η x = 0) :
    ∀ x ∈ noKinkGateAll θ, smallWritesLimit (Arch.gated relu id hid) θ η x = 0 := by
  intro x hx
  -- `c x ∈ Ω` for all small `c` (`c x → 0` as `c → 0`, and `Ω` is a neighborhood of `0`)
  have hlim : Tendsto (fun c : ℝ => c • x) (𝓝 0) (𝓝 0) := by
    have h : Continuous fun c : ℝ => c • x := continuous_id.smul continuous_const
    simpa only [zero_smul] using h.tendsto 0
  obtain ⟨ε, hε, hεΩ⟩ := Metric.eventually_nhds_iff.1 (hlim.eventually (hΩ.mem_nhds h0))
  -- for `0 < c < ε`, `c x` is an input of `Ω` with no gate at its kink, so
  -- `c A(x) + c² B(x) = 0`
  have key : ∀ c : ℝ, 0 < c → c < ε → ∀ t o,
      c * (x * (η.E * θ.D + θ.E * η.D)) t o + c ^ 2 * ∑ ℓ, ∑ i : hid ℓ,
        (relu ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * θ.read ℓ)) t (Sum.inr i)
            * (η.write ℓ * θ.D) i o
          + reluDeriv ((x * (θ.E * θ.read ℓ)) t (Sum.inl i))
            * (x * (θ.E * η.read ℓ)) t (Sum.inl i)
            * (x * (θ.E * θ.read ℓ)) t (Sum.inr i) * (θ.write ℓ * θ.D) i o
          + relu ((x * (θ.E * θ.read ℓ)) t (Sum.inl i)) * (x * (θ.E * η.read ℓ)) t (Sum.inr i)
            * (θ.write ℓ * θ.D) i o) = 0 := by
    intro c hc hcε t o
    have hcΩ : c • x ∈ Ω := hεΩ (by rwa [Real.dist_0_eq_abs, abs_of_pos hc])
    have h := congrFun (congrFun (hη _ hcΩ (smul_mem_noKinkGateAll_dgo hx hc.ne')) t) o
    rw [smallWritesLimit_smul_apply_dgo θ η x hx hc] at h
    exact h
  -- two values of `c` give `A(x) + B(x) = 0`, entry by entry
  ext t o
  rw [smallWritesLimit_apply_dgo θ η x hx, Matrix.zero_apply]
  have he : (0 : ℝ) < ε / 4 := by positivity
  have h1 := key (2 * (ε / 4)) (by positivity) (by linarith) t o
  have h2 := key (ε / 4) he (by linarith) t o
  exact add_eq_zero_of_two_scales_dgo he h1 h2

/-! ### Helpers: the batch and the flat directions (copies of the private helpers of
`Residual/DepthReGLU.lean`) -/

omit [Nonempty T] in
/-- Helper (copy of `limitLin_drg`): `η ↦ J_0 η` at one input `x` is linear in `η`. -/
private noncomputable def limitLin_dgo (A : Arch T d L) (θ : Params A dIn dOut)
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

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `exists_batch_ker_drg`, kernel stabilisation): for a family of linear maps on
a finite-dimensional space, finitely many of them have the common kernel of all of them. -/
private theorem exists_batch_ker_dgo {ι P F : Type*} [AddCommGroup P] [Module ℝ P]
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

omit [Nonempty T] in
/-- Helper (copy of `flatLin_drg`): the flat directions of `J_0` found in
`smallWritesLimit_eq_zero_reglu`, `(X, α, β) ↦ (E X, the reads and writes of
rescaleDir θ α + rescaleDirGate 1 θ β, -X D)`, as a linear map. -/
private noncomputable def flatLin_dgo
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) :
    (Matrix d d ℝ × (∀ ℓ, hid ℓ → ℝ) × (∀ ℓ, hid ℓ → ℝ)) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut where
  toFun p := ⟨θ.E * p.1, (rescaleDir θ p.2.1 + rescaleDirGate 1 θ p.2.2).read,
    (rescaleDir θ p.2.1 + rescaleDirGate 1 θ p.2.2).write, -(p.1 * θ.D)⟩
  map_add' p q := by
    apply Params.ext'
    · exact Matrix.mul_add _ _ _
    · intro ℓ
      ext k j
      rcases j with i | i
      · show 0 + (p.2.2 + q.2.2) ℓ i * θ.read ℓ k (Sum.inl i)
          = (0 + p.2.2 ℓ i * θ.read ℓ k (Sum.inl i)) + (0 + q.2.2 ℓ i * θ.read ℓ k (Sum.inl i))
        simp only [Pi.add_apply]
        ring
      · show -((p.2.1 + q.2.1) ℓ i) * θ.read ℓ k (Sum.inr i) + 0
          = (-(p.2.1 ℓ i) * θ.read ℓ k (Sum.inr i) + 0)
            + (-(q.2.1 ℓ i) * θ.read ℓ k (Sum.inr i) + 0)
        simp only [Pi.add_apply]
        ring
    · intro ℓ
      ext i k
      show (p.2.1 + q.2.1) ℓ i * θ.write ℓ i k
          + -(((1 : ℕ) : ℝ) * (p.2.2 + q.2.2) ℓ i) * θ.write ℓ i k
        = (p.2.1 ℓ i * θ.write ℓ i k + -(((1 : ℕ) : ℝ) * p.2.2 ℓ i) * θ.write ℓ i k)
          + (q.2.1 ℓ i * θ.write ℓ i k + -(((1 : ℕ) : ℝ) * q.2.2 ℓ i) * θ.write ℓ i k)
      simp only [Pi.add_apply]
      ring
    · show -((p.1 + q.1) * θ.D) = -(p.1 * θ.D) + -(q.1 * θ.D)
      rw [Matrix.add_mul, neg_add]
  map_smul' c p := by
    apply Params.ext'
    · exact Matrix.mul_smul _ _ _
    · intro ℓ
      ext k j
      rcases j with i | i
      · show 0 + (c • p.2.2) ℓ i * θ.read ℓ k (Sum.inl i)
          = c * (0 + p.2.2 ℓ i * θ.read ℓ k (Sum.inl i))
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      · show -((c • p.2.1) ℓ i) * θ.read ℓ k (Sum.inr i) + 0
          = c * (-(p.2.1 ℓ i) * θ.read ℓ k (Sum.inr i) + 0)
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
    · intro ℓ
      ext i k
      show (c • p.2.1) ℓ i * θ.write ℓ i k + -(((1 : ℕ) : ℝ) * (c • p.2.2) ℓ i) * θ.write ℓ i k
        = c * (p.2.1 ℓ i * θ.write ℓ i k + -(((1 : ℕ) : ℝ) * p.2.2 ℓ i) * θ.write ℓ i k)
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · show -((c • p.1) * θ.D) = c • -(p.1 * θ.D)
      rw [Matrix.smul_mul, smul_neg]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `finrank_flatDomain_drg`): the triples `(X, α, β)` form a space of dimension
`d² + 2 s`. -/
private theorem finrank_flatDomain_dgo :
    Module.finrank ℝ (Matrix d d ℝ × (∀ ℓ, hid ℓ → ℝ) × (∀ ℓ, hid ℓ → ℝ))
      = Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_matrix, Module.finrank_self,
    mul_one, ← sq, Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] in
/-- Helper (copy of `read_cols_ne_zero_drg`): the gate and value columns of the reads are nonzero
when those of `E W_read^ℓ` are. -/
private theorem read_cols_ne_zero_dgo
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : SmallWritesGenericGated θ) :
    (∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
      ∧ ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0 := by
  have h : ∀ ℓ (j : hid ℓ ⊕ hid ℓ), (fun a => θ.read ℓ a j) = 0 → (θ.E * θ.read ℓ)ᵀ j = 0 := by
    intro ℓ j h0
    funext a
    show ∑ k, θ.E a k * θ.read ℓ k j = 0
    exact Finset.sum_eq_zero fun k _ => by rw [show θ.read ℓ k j = 0 from congrFun h0 k, mul_zero]
  exact ⟨fun ℓ i h0 => hθ.value_ne_zero ℓ i (h ℓ _ h0),
    fun ℓ i h0 => hθ.gate_ne_zero ℓ i (h ℓ _ h0)⟩

/-- **Lemma A.30 for ReGLU blocks, first sentence, with inputs in an open set that contains `0`,
at one parameter:** under the conditions `SmallWritesGenericReGLU`, for an open set `Ω` of inputs
with `0 ∈ Ω` there is a finite batch of inputs of `Ω` at which no limit pre-activation of a gate
vanishes such that, for all small `τ ≠ 0`, no pre-activation of a gate on the batch vanishes at
`θ_τ` and the Jacobian of the residual network on the batch at `θ_τ` has rank `P − d² − s`. -/
theorem exists_eventually_jacobianRank_smallWrites_reglu_of_isOpen
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : SmallWritesGenericReGLU θ)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧ (∀ i, X i ∈ noKinkGateAll θ) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.gated relu id hid) 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ) t
            (Sum.inl j) ≠ 0) ∧
        jacobianRank (Arch.gated relu id hid) 1 X (θ.smallWrites τ)
            + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- a finite batch of inputs of `Ω` with no gate at its kink on which a direction flat for `J_0`
  -- is flat at every such input of `Ω`
  obtain ⟨n, Y, hY⟩ := exists_batch_ker_dgo
    (fun x : {x // x ∈ Ω ∧ x ∈ noKinkGateAll θ} =>
      limitLin_dgo (Arch.gated relu id hid) θ (dOut := dOut) x.1)
  refine ⟨n, fun i => (Y i).1, fun i => (Y i).2.1, fun i => (Y i).2.2, ?_⟩
  -- the kernel of `J_0`: a direction flat for `J_0` on the batch is flat at every input of
  -- `Ω ∩ noKinkGateAll θ`, hence (the cone argument) at every input of `noKinkGateAll θ`, so it
  -- lies in the range of `flatLin_dgo θ`, of dimension at most `d² + 2 s`
  have hW : ∀ η : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut,
      (∀ i, smallWritesLimit (Arch.gated relu id hid) θ η (Y i).1 = 0) →
      η ∈ LinearMap.range (flatLin_dgo θ) := by
    intro η hη
    have hall := smallWritesLimit_eq_zero_of_forall_mem_isOpen_reglu θ η hΩ h0
      fun x hxΩ hx => hY η hη ⟨x, hxΩ, hx⟩
    obtain ⟨X, α, β, hE, hD, hr, hw⟩ := smallWritesLimit_eq_zero_reglu θ hθ η hall
    exact ⟨(X, α, β), Params.ext' hE.symm (fun ℓ => (hr ℓ).symm) (fun ℓ => (hw ℓ).symm) hD.symm⟩
  have hdim : Module.finrank ℝ (LinearMap.range (flatLin_dgo θ))
      ≤ Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ) := by
    have h := LinearMap.finrank_range_le (flatLin_dgo θ)
    rw [finrank_flatDomain_dgo] at h
    exact h
  -- `≥`: for small `τ ≠ 0` the pre-activations on the batch stay off the kinks, where the block
  -- maps are `C²`, and the rank on the batch is at least `P − d² − 2 s`
  have hge := eventually_jacobianRank_smallWrites_ge_of_contDiffOn (Arch.gated relu id hid) θ rfl
    (fun ℓ => {M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0})
    (fun ℓ => isOpen_gateSet_dgo ℓ) (fun ℓ => contDiffOn_f_dgo ℓ) (fun i => (Y i).1)
    (fun i ℓ => (Y i).2.2 ℓ) _ hW
  -- `≤`: the symmetries at `θ_τ`, whose embedding and reads are those of `θ`
  obtain ⟨hv, hg⟩ := read_cols_ne_zero_dgo θ hθ.gated
  filter_upwards [hge] with τ hτ
  refine ⟨fun i ℓ t j => hτ.1 i ℓ t j, ?_⟩
  have h1 := jacobianRank_le_funDim (A := Arch.gated relu id hid) (S := 1) (θ.smallWrites τ)
    (fun i => (Y i).1)
  have h2 := funDim_add_le_residual_gated_gate relu_homogeneous (θ.smallWrites τ)
    hθ.gated.rank_E hv hg
  have h3 := hτ.2
  omega

/-! ### Helpers: open conditions near `θ_τ` (copies of the private helpers of
`Residual/DepthReGLU.lean`) -/

omit [Fintype T] [Nonempty T] in
/-- Helper (copy of `eventually_rank_E_drg`): near parameters whose embedding has rank `d`, the
embedding still has rank `d`. -/
private theorem eventually_rank_E_dgo
    (θ₀ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (h : θ₀.E.rank = Fintype.card d) :
    ∀ᶠ θ' in 𝓝 θ₀, θ'.E.rank = Fintype.card d := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr h)
  have hE : Continuous fun θ' : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
      θ'.E :=
    (Params.linE (A := Arch.gated (T := T) (d := d) relu id hid) (dIn := dIn)
      (dOut := dOut)).continuous_of_finiteDimensional
  have hc : Continuous fun θ' : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
      (B * θ'.E).det := (continuous_const.matrix_mul hE).matrix_det
  have h0 : (B * θ₀.E).det ≠ 0 := by
    rw [hB, Matrix.det_one]
    exact one_ne_zero
  filter_upwards [hc.continuousAt.eventually_ne h0] with θ' hθ'
  have h1 := Matrix.rank_of_isUnit (B * θ'.E) ((Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hθ'))
  have h2 := Matrix.rank_mul_le_right B θ'.E
  have h3 := Matrix.rank_le_card_width θ'.E
  omega

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper (copy of `eventually_col_ne_zero_drg`): near parameters no column of whose reads is
zero, no column of a read is zero. -/
private theorem eventually_col_ne_zero_dgo
    (θ₀ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (h : ∀ ℓ (j : hid ℓ ⊕ hid ℓ), (fun a => θ₀.read ℓ a j) ≠ 0) :
    ∀ᶠ θ' in 𝓝 θ₀, ∀ ℓ (j : hid ℓ ⊕ hid ℓ), (fun a => θ'.read ℓ a j) ≠ 0 := by
  refine Filter.eventually_all.2 fun ℓ => Filter.eventually_all.2 fun j => ?_
  obtain ⟨a, ha⟩ := Function.ne_iff.1 (h ℓ j)
  have hc : Continuous fun θ' : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
      θ'.read ℓ a j :=
    ((Matrix.entryLinearMap ℝ ℝ a j).comp
      (Params.linRead (A := Arch.gated (T := T) (d := d) relu id hid) (dIn := dIn) (dOut := dOut)
        ℓ)).continuous_of_finiteDimensional
  filter_upwards [hc.continuousAt.eventually_ne ha] with θ' hθ' h0
  exact hθ' (congrFun h0 a)

/-- **Lemma A.30 for ReGLU blocks, second sentence, with inputs in an open set that contains `0`,
near `θ_τ`:** under the conditions `SmallWritesGenericReGLU`, for an open set `Ω` of inputs with
`0 ∈ Ω` there is a finite batch of inputs of `Ω` such that, for all small `τ ≠ 0` and every
parameter `θ'` near `θ_τ`, no pre-activation of a gate on the batch vanishes at `θ'` and the
Jacobian of the residual network on the batch at `θ'` has rank `P − d² − s`. (Near `θ_τ` the rank
on every batch is at most this number: `eventually_eventually_funDim_smallWrites_reglu`.) -/
theorem exists_eventually_eventually_jacobianRank_smallWrites_reglu_of_isOpen
    (θ : Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hθ : SmallWritesGenericReGLU θ)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ), ∀ᶠ θ' in 𝓝 (θ.smallWrites τ),
        (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
          (hidden (Arch.gated relu id hid) 1 θ' (X i) ℓ.castSucc * θ'.read ℓ) t (Sum.inl j)
            ≠ 0) ∧
        jacobianRank (Arch.gated relu id hid) 1 X θ'
            + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- the batch of the first sentence, inside `Ω`
  obtain ⟨n, X, hXΩ, -, h⟩ := exists_eventually_jacobianRank_smallWrites_reglu_of_isOpen θ hθ hΩ h0
  refine ⟨n, X, hXΩ, ?_⟩
  obtain ⟨hv, hg⟩ := read_cols_ne_zero_dgo θ hθ.gated
  have hcol : ∀ ℓ (j : hid ℓ ⊕ hid ℓ), (fun a => θ.read ℓ a j) ≠ 0 := by
    intro ℓ j
    rcases j with i | i
    · exact hg ℓ i
    · exact hv ℓ i
  filter_upwards [h] with τ hτ
  -- near `θ_τ` the pre-activations on the batch stay off the kinks, and the rank on the batch
  -- does not drop below `P − d² − 2 s`
  have hnear := eventually_jacobianRank_ge_of_contDiffOn (Arch.gated relu id hid)
    (θ.smallWrites τ) rfl 1
    (fun ℓ => {M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0})
    (fun ℓ => isOpen_gateSet_dgo ℓ) (fun ℓ => (contDiffOn_f_dgo ℓ).of_le (by norm_num)) X
    (fun i ℓ t j => hτ.1 i ℓ t j)
  -- near `θ_τ` the embedding has rank `d` and no column of a read is zero, so the symmetries
  -- give `rank ≤ fd ≤ P − d² − 2 s`
  filter_upwards [hnear, eventually_rank_E_dgo (θ.smallWrites τ) hθ.gated.rank_E,
    eventually_col_ne_zero_dgo (θ.smallWrites τ) hcol] with θ' h1 h2 h3
  refine ⟨fun i ℓ t j => h1.1 i ℓ t j, ?_⟩
  have h4 := jacobianRank_le_funDim (A := Arch.gated relu id hid) (S := 1) θ' X
  have h5 := funDim_add_le_residual_gated_gate relu_homogeneous θ' h2
    (fun ℓ i => h3 ℓ (Sum.inr i)) (fun ℓ i => h3 ℓ (Sum.inl i))
  have h6 := hτ.2
  have h7 := h1.2
  omega

/-- **Lemma A.30 for ReGLU blocks with inputs in an open set that contains `0`:** with
`d_in, d_out ≥ d ≥ 2` and blocks of any widths, for an open set `Ω` of inputs with `0 ∈ Ω`, there
is an open set `U` of weights such that: at every `θ ∈ U` the residual network has
`fd = P − d² − s`, attained by the rank of the Jacobian on a finite batch of inputs of `Ω` on
which no pre-activation of a gate vanishes; `U` contains `θ_τ` for generic `θ` and all small
`τ ≠ 0`; and at almost every point of `U` the skips add at least `L d²` when every block has at
least `d` hidden units. -/
theorem exists_isOpen_jacobianRank_smallWrites_reglu_of_isOpen
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    {Ω : Set (Matrix T dIn ℝ)} (hΩ : IsOpen Ω) (h0 : (0 : Matrix T dIn ℝ) ∈ Ω) :
    ∃ U : Set (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut), IsOpen U ∧
      (∀ θ ∈ U, funDim (Arch.gated relu id hid) 1 θ
            + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) ∧
        ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧
          (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
            (hidden (Arch.gated relu id hid) 1 θ (X i) ℓ.castSucc * θ.read ℓ) t (Sum.inl j)
              ≠ 0) ∧
          jacobianRank (Arch.gated relu id hid) 1 X θ
              + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
            = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)) ∧
      (∀ (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
        [μ.IsAddHaarMeasure], ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), θ.smallWrites τ ∈ U) ∧
      (∀ (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
        [μ.IsAddHaarMeasure], (∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) →
        ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.gated relu id hid) 0 θ + L * Fintype.card d ^ 2
          ≤ funDim (Arch.gated relu id hid) 1 θ) := by
  -- `U`: the interior of the set where `fd = P − d² − 2 s` and some batch inside `Ω`, with no
  -- gate at its kink, has rank `P − d² − 2 s`
  refine ⟨interior {θ | funDim (Arch.gated relu id hid) 1 θ
            + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
          = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) ∧
        ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ Ω) ∧
          (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
            (hidden (Arch.gated relu id hid) 1 θ (X i) ℓ.castSucc * θ.read ℓ) t (Sum.inl j)
              ≠ 0) ∧
          jacobianRank (Arch.gated relu id hid) 1 X θ
              + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
            = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)},
    isOpen_interior, fun θ hθ => interior_subset hθ, fun μ _ => ?_, fun μ _ hhid => ?_⟩
  · -- at generic `θ` and small `τ ≠ 0`, both hold on a neighborhood of `θ_τ`, with one batch
    filter_upwards [ae_smallWritesGenericReGLU μ hd hdIn hdOut] with θ hθ
    obtain ⟨n, X, hXΩ, h⟩ :=
      exists_eventually_eventually_jacobianRank_smallWrites_reglu_of_isOpen θ hθ hΩ h0
    filter_upwards [h, eventually_eventually_funDim_smallWrites_reglu θ hθ] with τ hτ hτ'
    refine mem_interior_iff_mem_nhds.2 ?_
    filter_upwards [hτ, hτ'] with θ' h1 h2
    exact ⟨h2, n, X, hXΩ, h1.1, h1.2⟩
  · -- the gain: `fd_0 + (L + 1) d² + 2 s ≤ P` at generic `θ`, and `fd_1 + d² + 2 s = P` on `U`
    have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
    filter_upwards [ae_funDim_add_le_skipless_reglu μ hdIn hhid] with θ h hU
    obtain ⟨h1, -⟩ := interior_subset hU
    have h2 : (L + 1) * Fintype.card d ^ 2 = L * Fintype.card d ^ 2 + Fintype.card d ^ 2 :=
      add_one_mul _ _
    omega

end Skips
