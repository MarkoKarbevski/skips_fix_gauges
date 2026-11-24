import SkipsLean.Dimension.RescalingMlp

/-!
# The rescaling of the gate of a ReGLU hidden unit, and the upper bound for ReGLU blocks

Paper (dimension): Appendix B, "The symmetries inside the blocks". A hidden unit of a gated block
has the gate column `c_i`, the value column `e_i` and the write row `a_i`. Every gated block has
the rescaling of the value, `(e_i, a_i) ↦ (e_i / λ, λ a_i)` (`Dimension/Rescaling.lean`). A ReGLU
block has in addition the rescaling of the gate,

  `(c_i, a_i) ↦ (λ c_i, a_i / λ)`,   `λ > 0`,

so that `s = 2 d_hidden` for a ReGLU block. Stated here: this rescaling preserves the function and
its directions are flat; Lemma B.1 for ReGLU blocks in the form for directions; Theorem 4.3 for
ReGLU blocks.

The statements are for a gate activation `σ` that is positively homogeneous of degree `k`,
`σ(λ z) = λ^k σ(z)` for `λ > 0`; `k = 1` for ReLU. ReLU is not differentiable at `0`, so the
statements on flat directions and on the functional dimension use the forms without a hypothesis
of differentiability (`mem_flat_of_hasDerivAt'`, `funDim_add_finrank_le_of_le_flat'`,
`cobDir_mem_flat_skipless'`, `cobDir_mem_flat_skipless_rmsNorm'`, `rescaleDir_mem_flat'`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- The direction in which the rescalings `(c_i, a_i) ↦ (λ_i c_i, a_i / λ_i^k)` of the gates move
`θ`, for `λ_i = e^{τ β_i}`: the gate column of the hidden unit `i` of block `ℓ` times `β_i`, its
write row times `-k β_i`, and `0` at the value columns, at `E` and at `D`. -/
def rescaleDirGate (k : ℕ) (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (β : ∀ ℓ, hid ℓ → ℝ) : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  E := 0
  read ℓ := Matrix.of fun a j =>
    Sum.elim (fun i => β ℓ i * θ.read ℓ a (Sum.inl i)) (fun _ => 0) j
  write ℓ := Matrix.of fun i a => -((k : ℝ) * β ℓ i) * θ.write ℓ i a
  D := 0

/-- **The rescaling of the gates preserves the function** (Appendix B, "ReGLU, in addition").
Let `σ(λ z) = λ^k σ(z)` for `λ > 0`. If `θ'` has the gate column of every hidden unit `i`
multiplied by `c_i > 0` and its write row divided by `c_i^k`, and the same value columns, `E` and
`D`, then `θ'` and `θ` give the same function, for every map `χ` before the reads and all stream
matrices. -/
theorem eval_rescale_gate {k : ℕ} (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ θ' : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (c : ∀ ℓ, hid ℓ → ℝ) (hc : ∀ ℓ i, 0 < c ℓ i)
    (hE : θ'.E = θ.E) (hD : θ'.D = θ.D)
    (hg : ∀ ℓ a i, θ'.read ℓ a (Sum.inl i) = c ℓ i * θ.read ℓ a (Sum.inl i))
    (hv : ∀ ℓ a i, θ'.read ℓ a (Sum.inr i) = θ.read ℓ a (Sum.inr i))
    (hw : ∀ ℓ i a, θ'.write ℓ i a = (c ℓ i ^ k)⁻¹ * θ.write ℓ i a)
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (Arch.gated σ χ hid) S θ' x = eval (Arch.gated σ χ hid) S θ x := by
  -- the hidden states of `θ'` and `θ` agree, by induction along the network
  have hh : ∀ ℓ : Fin (L + 1),
      hidden (Arch.gated σ χ hid) S θ' x ℓ = hidden (Arch.gated σ χ hid) S θ x ℓ := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => rw [hidden_zero, hidden_zero, hE]
    | succ ℓ ih =>
      -- the stream term `h S_ℓ` is the same; compare the outputs of block `ℓ`
      rw [hidden_succ, hidden_succ, ih]
      congr 1
      set h := χ (hidden (Arch.gated σ χ hid) S θ x ℓ.castSucc)
      -- the gate of hidden unit `i` is multiplied by `c_i`, and the values are the same
      have hz : ∀ t i,
          (h * θ'.read ℓ) t (Sum.inl i) = c ℓ i * (h * θ.read ℓ) t (Sum.inl i) := by
        intro t i
        rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hg]
        ring
      have hu : ∀ t i, (h * θ'.read ℓ) t (Sum.inr i) = (h * θ.read ℓ) t (Sum.inr i) := by
        intro t i
        simp only [Matrix.mul_apply, hv]
      -- so hidden unit `i` contributes `σ(c_i z_i) w_i a_i / c_i^k = σ(z_i) w_i a_i`
      ext t a
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show σ ((h * θ'.read ℓ) t (Sum.inl i)) * (h * θ'.read ℓ) t (Sum.inr i) * θ'.write ℓ i a =
        σ ((h * θ.read ℓ) t (Sum.inl i)) * (h * θ.read ℓ) t (Sum.inr i) * θ.write ℓ i a
      have hk : c ℓ i ^ k ≠ 0 := pow_ne_zero k (hc ℓ i).ne'
      rw [hz, hu, hw, hσ _ _ (hc ℓ i)]
      field_simp
  -- hence the outputs agree
  rw [eval, eval, hh, hD]

/-- Helper: `τ ↦ e^{τ a} b` has derivative `a b` at `τ = 0`. -/
private theorem hasDerivAt_exp_mul_const_gate (a b : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.exp (τ * a) * b) (a * b) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const a).exp.mul_const b
  simpa using h

/-- Helper: the curve of the rescalings `λ_i = e^{τ β ℓ i}` of the gates: the gate column of
hidden unit `i` of block `ℓ` is multiplied by `e^{τ β ℓ i}`, its write row by `e^{-τ k β ℓ i}`,
and the value columns do not move. -/
private noncomputable def rescaleCurveGate (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (β : ∀ ℓ, hid ℓ → ℝ) (τ : ℝ) :
    Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a j =>
    Sum.elim (fun i => Real.exp (τ * β ℓ i) * θ.read ℓ a (Sum.inl i))
      (fun i => θ.read ℓ a (Sum.inr i)) j
  write ℓ := Matrix.of fun i a => Real.exp (τ * -((k : ℝ) * β ℓ i)) * θ.write ℓ i a
  D := θ.D

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the curve passes through `θ` at `τ = 0`. -/
private theorem rescaleCurveGate_zero (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (β : ∀ ℓ, hid ℓ → ℝ) :
    rescaleCurveGate k θ β 0 = θ := by
  apply Params.ext'
  · rfl
  · intro ℓ
    ext a j
    cases j <;> simp [rescaleCurveGate]
  · intro ℓ
    ext i a
    simp [rescaleCurveGate]
  · rfl

omit [Fintype T] [DecidableEq d] in
/-- Helper: the curve has velocity `rescaleDirGate k θ β` at `τ = 0`. The derivative is taken
entry by entry, through the linear equivalence of the parameters with the tuples of their
components. -/
private theorem hasDerivAt_rescaleCurveGate (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (β : ∀ ℓ, hid ℓ → ℝ) :
    HasDerivAt (rescaleCurveGate k θ β) (rescaleDirGate k θ β) 0 := by
  have hprod : HasDerivAt (fun τ : ℝ => Params.linearEquivProd (rescaleCurveGate k θ β τ))
      (Params.linearEquivProd (rescaleDirGate k θ β)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · -- the embedding does not move
      exact hasDerivAt_const (0 : ℝ) θ.E
    · -- the gate entries are `e^{τ β} g`; the value entries do not move
      refine hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun j => ?_
      cases j with
      | inl i => exact hasDerivAt_exp_mul_const_gate (β ℓ i) (θ.read ℓ a (Sum.inl i))
      | inr i => exact hasDerivAt_const (0 : ℝ) (θ.read ℓ a (Sum.inr i))
    · -- the write entries are `e^{-τ k β} a`
      exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun a =>
        hasDerivAt_exp_mul_const_gate (-((k : ℝ) * β ℓ i)) (θ.write ℓ i a)
    · -- the readout does not move
      exact hasDerivAt_const (0 : ℝ) θ.D
  -- back from the tuples of components to the parameters
  exact (LinearMap.toContinuousLinearMap
    (Params.linearEquivProd (A := Arch.gated (T := T) (d := d) σ χ hid) (dIn := dIn)
      (dOut := dOut)).symm.toLinearMap).hasFDerivAt.comp_hasDerivAt 0 hprod

/-- The directions of the rescalings of the gates are flat, for every map `χ` before the reads and
all stream matrices. No differentiability of `σ` is assumed. -/
theorem rescaleDirGate_mem_flat {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (S : Fin L → Matrix d d ℝ)
    (β : ∀ ℓ, hid ℓ → ℝ) :
    rescaleDirGate k θ β ∈ flat (Arch.gated σ χ hid) S θ := by
  -- the curve passes through `θ` with velocity `rescaleDirGate k θ β`, and at every `τ` it is the
  -- rescaling `c_i = e^{τ β ℓ i}` of the gates, which preserves the function
  refine mem_flat_of_hasDerivAt' θ (rescaleCurveGate k θ β) (rescaleDirGate k θ β)
    (hasDerivAt_rescaleCurveGate k θ β) (rescaleCurveGate_zero k θ β)
    (Filter.Eventually.of_forall fun τ x => ?_)
  refine eval_rescale_gate hσ θ (rescaleCurveGate k θ β τ) (fun ℓ i => Real.exp (τ * β ℓ i))
    (fun _ _ => Real.exp_pos _) rfl rfl (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun ℓ i a => ?_) S x
  -- the write rows: `e^{-τ k β} = (e^{τ β}^k)⁻¹`
  show Real.exp (τ * -((k : ℝ) * β ℓ i)) * θ.write ℓ i a =
    (Real.exp (τ * β ℓ i) ^ k)⁻¹ * θ.write ℓ i a
  rw [show τ * -((k : ℝ) * β ℓ i) = -((k : ℝ) * (τ * β ℓ i)) by ring, Real.exp_neg,
    Real.exp_nat_mul]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `mul_left_cancel_of_rank` of `UpperBound.lean`): a matrix `M` of rank equal
to its number of columns cancels on the left, `M X = M Y → X = Y` (its kernel is `0` by
rank–nullity). -/
private theorem cancel_left_of_rank_gate {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
    (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ} (h : M * X = M * Y) : X = Y := by
  -- `v ↦ M v` is injective: `rank M + dim ker M = card n`
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [Matrix.rank] at hM
    omega
  -- compare `X` and `Y` column by column
  ext i j
  have hcol : M.mulVecLin (fun l => X l j) = M.mulVecLin (fun l => Y l j) := by
    funext p
    have := congrFun (congrFun h p) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  exact congrFun (hinj hcol) i

/-- **Lemma B.1 for ReGLU blocks, in the form for directions.** If `E` and every write have rank
`d` and no gate column and no value column of a read vanishes, the matrices `X_0, …, X_L` of the
changes of basis, the numbers `α` of the rescalings of the values and the numbers `β` of the
rescalings of the gates are determined by the direction
`cobDir θ X + rescaleDir θ α + rescaleDirGate k θ β`. -/
theorem cobDir_add_rescaleDir_add_rescaleDirGate_injective (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    Function.Injective
      fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
        cobDir θ p.1 + rescaleDir θ p.2.1 + rescaleDirGate k θ p.2.2 := by
  rintro ⟨X, α, β⟩ ⟨X', α', β'⟩ h
  -- the embedding component: `E X_0 = E X'_0` (the rescalings leave `E` alone), and `E` has
  -- rank `d`
  have h0 : θ.E * X 0 = θ.E * X' 0 := by
    have hE0 := congrArg Params.E h
    change θ.E * X 0 + 0 + 0 = θ.E * X' 0 + 0 + 0 at hE0
    simpa only [add_zero] using hE0
  have hX0 : X 0 = X' 0 := cancel_left_of_rank_gate θ.E hE h0
  -- block `ℓ`: if `X_{ℓ-1} = X'_{ℓ-1}`, then `α_ℓ = α'_ℓ`, `β_ℓ = β'_ℓ` and `X_ℓ = X'_ℓ`
  have key : ∀ ℓ : Fin L, X ℓ.castSucc = X' ℓ.castSucc →
      α ℓ = α' ℓ ∧ β ℓ = β' ℓ ∧ X ℓ.succ = X' ℓ.succ := by
    intro ℓ hℓ
    -- the gate column `g_i` of hidden unit `i` moves by `-X_{ℓ-1} g_i + β_i g_i` (the rescaling
    -- of the value leaves it alone), and the first terms agree; an entry `a` with `g_i a ≠ 0`
    -- gives `β_i = β'_i`
    have hβ : β ℓ = β' ℓ := by
      funext i
      obtain ⟨a, ha⟩ := Function.ne_iff.mp (hg ℓ i)
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inl i)
      change -(X ℓ.castSucc * θ.read ℓ) a (Sum.inl i) + 0 + β ℓ i * θ.read ℓ a (Sum.inl i) =
        -(X' ℓ.castSucc * θ.read ℓ) a (Sum.inl i) + 0 + β' ℓ i * θ.read ℓ a (Sum.inl i) at hr
      rw [hℓ, add_right_inj] at hr
      exact mul_right_cancel₀ ha hr
    -- the value column `e_i` moves by `-X_{ℓ-1} e_i - α_i e_i` (the rescaling of the gate leaves
    -- it alone); an entry `a` with `e_i a ≠ 0` gives `α_i = α'_i`
    have hα : α ℓ = α' ℓ := by
      funext i
      obtain ⟨a, ha⟩ := Function.ne_iff.mp (hv ℓ i)
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inr i)
      change -(X ℓ.castSucc * θ.read ℓ) a (Sum.inr i) + -(α ℓ i) * θ.read ℓ a (Sum.inr i) + 0 =
        -(X' ℓ.castSucc * θ.read ℓ) a (Sum.inr i) + -(α' ℓ i) * θ.read ℓ a (Sum.inr i) + 0
        at hr
      rw [hℓ, add_left_inj, add_right_inj] at hr
      exact neg_inj.mp (mul_right_cancel₀ ha hr)
    refine ⟨hα, hβ, ?_⟩
    -- the write moves by `W X_ℓ + diag(α_ℓ) W - k diag(β_ℓ) W`; the diagonal terms agree, and
    -- `W` has rank `d`
    have hw' := congrArg (fun η => η.write ℓ) h
    change θ.write ℓ * X ℓ.succ + Matrix.of (fun i a => α ℓ i * θ.write ℓ i a)
        + Matrix.of (fun i a => -((k : ℝ) * β ℓ i) * θ.write ℓ i a) =
      θ.write ℓ * X' ℓ.succ + Matrix.of (fun i a => α' ℓ i * θ.write ℓ i a)
        + Matrix.of (fun i a => -((k : ℝ) * β' ℓ i) * θ.write ℓ i a) at hw'
    rw [hα, hβ, add_left_inj, add_left_inj] at hw'
    exact cancel_left_of_rank_gate (θ.write ℓ) (hw ℓ) hw'
  -- by induction along the network, `X = X'`; then `α = α'` and `β = β'`
  have hX : ∀ ℓ : Fin (L + 1), X ℓ = X' ℓ := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => exact hX0
    | succ ℓ ih => exact (key ℓ ih).2.2
  exact Prod.ext (funext hX) (Prod.ext (funext fun ℓ => (key ℓ (hX ℓ.castSucc)).1)
    (funext fun ℓ => (key ℓ (hX ℓ.castSucc)).2.1))

/-- Helper: `α ↦ rescaleDir θ α` is linear (the private `rescaleDirLin` of `Rescaling.lean`). -/
private noncomputable def rescaleDirLinValue
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  toFun := rescaleDir θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext a j
      cases j with
      | inl i => simp [rescaleDir]
      | inr i =>
        simp only [rescaleDir, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply,
          Sum.elim_inr]
        ring
    · intro ℓ
      ext i a
      simp [rescaleDir, add_mul]
    · simp [rescaleDir]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext a j
      cases j <;> simp [rescaleDir, mul_assoc]
    · intro ℓ
      ext i a
      simp [rescaleDir, mul_assoc]
    · simp [rescaleDir]

/-- Helper: `β ↦ rescaleDirGate k θ β` is linear. -/
private noncomputable def rescaleDirGateLin (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  toFun := rescaleDirGate k θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDirGate]
    · intro ℓ
      ext a j
      cases j with
      | inl i =>
        simp only [rescaleDirGate, Pi.add_apply, Params.add_read, Matrix.add_apply,
          Matrix.of_apply, Sum.elim_inl]
        ring
      | inr i => simp [rescaleDirGate]
    · intro ℓ
      ext i a
      simp only [rescaleDirGate, Pi.add_apply, Params.add_write, Matrix.add_apply,
        Matrix.of_apply]
      ring
    · simp [rescaleDirGate]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDirGate]
    · intro ℓ
      ext a j
      cases j with
      | inl i =>
        simp only [rescaleDirGate, Pi.smul_apply, Params.smul_read, Matrix.smul_apply,
          Matrix.of_apply, Sum.elim_inl, smul_eq_mul, RingHom.id_apply]
        ring
      | inr i => simp [rescaleDirGate]
    · intro ℓ
      ext i a
      simp only [rescaleDirGate, Pi.smul_apply, Params.smul_write, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [rescaleDirGate]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the triples `(X, α, β)` form a space of dimension `(L + 1) d² + 2 s`. -/
private theorem finrank_dirDomainGate :
    Module.finrank ℝ ((Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) × (∀ ℓ, hid ℓ → ℝ)) =
      (L + 1) * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_prod, Module.finrank_prod, finrank_cobDomain, Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]
  ring

/-- **Theorem 4.3 without normalization, for gated blocks with a positively homogeneous gate**
(ReGLU), under the conditions of the proof: `fd ≤ P - (L + 1) d² - s`, where `s` is twice the
number of hidden units. -/
theorem funDim_add_le_skipless_gated_gate {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.gated σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the linear map `(X, α, β) ↦ cobDir θ X + rescaleDir θ α + rescaleDirGate k θ β`
  let Φ := (cobDirLin θ).coprod ((rescaleDirLinValue θ).coprod (rescaleDirGateLin k θ))
  -- its directions are flat, since the three summands are
  have hV : LinearMap.range Φ ≤ flat (Arch.gated σ id hid) 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply]
    exact Submodule.add_mem _ (cobDir_mem_flat_skipless' θ rfl p.1)
      (Submodule.add_mem _ (rescaleDir_mem_flat' θ 0 p.2.1)
        (rescaleDirGate_mem_flat hσ θ 0 p.2.2))
  -- it is injective (Lemma B.1), so its range has dimension `(L + 1) d² + 2 s`
  have hinj : Function.Injective Φ := by
    intro p q hpq
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply, LinearMap.coprod_apply,
      LinearMap.coprod_apply, ← add_assoc, ← add_assoc] at hpq
    exact cobDir_add_rescaleDir_add_rescaleDirGate_injective k θ hE hw hv hg hpq
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, finrank_dirDomainGate] at h

/-- **Theorem 4.3 under pre-RMSNorm, for gated blocks with a positively homogeneous gate**
(ReGLU), under the conditions of the proof: `fd ≤ P - (L + 1) d (d - 1) / 2 - s`. It holds for
every real `ε`. -/
theorem funDim_add_le_skipless_gated_gate_rmsNorm {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (ε : ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  -- the linear map `(X, α, β) ↦ cobDir θ X + rescaleDir θ α + rescaleDirGate k θ β`, with
  -- antisymmetric `X_ℓ`
  let Φ : ((Fin (L + 1) → antisymmetric d) × (∀ ℓ, hid ℓ → ℝ) × (∀ ℓ, hid ℓ → ℝ)) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut :=
    ((cobDirLin θ).comp (LinearMap.compLeft (antisymmetric d).subtype (Fin (L + 1)))).coprod
      ((rescaleDirLinValue θ).coprod (rescaleDirGateLin k θ))
  -- its directions are flat, since the three summands are
  have hV : LinearMap.range Φ ≤ flat (Arch.gated σ (rmsNorm ε) hid) 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply]
    exact Submodule.add_mem _
      (cobDir_mem_flat_skipless_rmsNorm' θ ε rfl (fun ℓ => (p.1 ℓ : Matrix d d ℝ))
        fun ℓ => (p.1 ℓ).2)
      (Submodule.add_mem _ (rescaleDir_mem_flat' θ 0 p.2.1)
        (rescaleDirGate_mem_flat hσ θ 0 p.2.2))
  -- it is injective (Lemma B.1)
  have hinj : Function.Injective Φ := by
    intro p q hpq
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply, LinearMap.coprod_apply,
      LinearMap.coprod_apply, ← add_assoc, ← add_assoc] at hpq
    have h' : cobDir θ (fun ℓ => (p.1 ℓ : Matrix d d ℝ)) + rescaleDir θ p.2.1
          + rescaleDirGate k θ p.2.2
        = cobDir θ (fun ℓ => (q.1 ℓ : Matrix d d ℝ)) + rescaleDir θ q.2.1
          + rescaleDirGate k θ q.2.2 := hpq
    have h2 : ((fun ℓ => (p.1 ℓ : Matrix d d ℝ)), p.2.1, p.2.2) =
        ((fun ℓ => (q.1 ℓ : Matrix d d ℝ)), q.2.1, q.2.2) :=
      cobDir_add_rescaleDir_add_rescaleDirGate_injective k θ hE hw hv hg h'
    have h3 := Prod.mk.inj h2
    exact Prod.ext (funext fun ℓ => Subtype.ext (congrFun h3.1 ℓ)) h3.2
  -- the domain has dimension `(L + 1) d (d - 1) / 2 + 2 s`
  have hdim : Module.finrank ℝ
      ((Fin (L + 1) → antisymmetric d) × (∀ ℓ, hid ℓ → ℝ) × (∀ ℓ, hid ℓ → ℝ)) =
      (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
        + 2 * ∑ ℓ, Fintype.card (hid ℓ) := by
    rw [Module.finrank_prod, Module.finrank_prod,
      Module.finrank_pi_fintype (R := ℝ) (ι := Fin (L + 1)) (M := fun _ => antisymmetric d),
      finrank_antisymmetric, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Module.finrank_pi_fintype]
    simp only [Module.finrank_fintype_fun_eq_card]
    ring
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, hdim] at h

/-- At generic parameters no gate column of a read of a gated network vanishes. -/
theorem ae_gate_ne_zero [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0 := by
  -- finitely many conditions, one for each hidden unit `i` of each block `ℓ`
  refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_
  -- an entry `a₀` of the gate column
  obtain a₀ : d := Classical.arbitrary d
  -- the entry `θ ↦ θ.read ℓ a₀ (inl i)` is a linear functional of the parameters
  let l : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut →ₗ[ℝ] ℝ :=
    (Matrix.entryLinearMap ℝ ℝ a₀ (Sum.inl i)).comp
      (Params.linRead (A := Arch.gated (T := T) (d := d) σ χ hid) (dIn := dIn) (dOut := dOut) ℓ)
  have hl : ∀ θ, l θ = θ.read ℓ a₀ (Sum.inl i) := fun θ => rfl
  -- it is not zero at the parameters whose reads have all entries `1`
  have h₁ : l ⟨0, fun _ => Matrix.of fun _ _ => 1, 0, 0⟩ ≠ 0 := by
    rw [hl]
    exact one_ne_zero
  -- an analytic function that is not identically zero is nonzero almost everywhere
  have hne : ∀ᵐ θ ∂μ, l θ ≠ 0 :=
    ae_ne_zero_of_analytic μ (analyticOnNhd_linear l) ⟨_, h₁⟩
  -- and a function with a nonzero entry is not zero
  filter_upwards [hne] with θ h hz
  exact h (by rw [hl]; exact congrFun hz a₀)

/-- **Theorem 4.3 for ReGLU blocks at generic parameters, without normalization** (`d_in ≥ d`, at
least `d` hidden units per block): `fd ≤ P - (L + 1) d² - 2 ∑ d_hidden`. -/
theorem ae_funDim_add_le_skipless_reglu [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- the pointwise bound holds wherever `E` and the writes have rank `d` and no value column and
  -- no gate column of a read vanishes
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_value_ne_zero μ, ae_gate_ne_zero μ]
    with θ h1 h2 h3
  exact funDim_add_le_skipless_gated_gate relu_homogeneous θ h1.1 h1.2 h2 h3

/-- **Theorem 4.3 for ReGLU blocks at generic parameters, under pre-RMSNorm:**
`fd ≤ P - (L + 1) d (d - 1) / 2 - 2 ∑ d_hidden`. -/
theorem ae_funDim_add_le_skipless_reglu_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_value_ne_zero μ, ae_gate_ne_zero μ]
    with θ h1 h2 h3
  exact funDim_add_le_skipless_gated_gate_rmsNorm relu_homogeneous ε θ h1.1 h1.2 h2 h3

end Skips
