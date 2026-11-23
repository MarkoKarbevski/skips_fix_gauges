import SkipsLean.Dimension.UpperBound

/-!
# The upper bound from the changes of basis, under pre-RMSNorm

Papers: dimension paper, Theorem 4.3 under pre-RMSNorm with `ε > 0`, for the changes of basis at
the hidden states; skips paper, the bound for residual networks under pre-RMSNorm.

Under pre-RMSNorm the changes of basis are orthogonal, and their directions `cobDir θ X` have
antisymmetric `X_ℓ`. The antisymmetric matrices form a space of dimension `d (d - 1) / 2`, so the
functional dimension is at most `P - (L + 1) d (d - 1) / 2` without skip connections, and at most
`P - d (d - 1) / 2` in a residual network.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {A : Arch T d L}
variable (θ : Params A dIn dOut)

/-- RMSNorm with `ε > 0` is differentiable. -/
theorem differentiable_rmsNorm {ε : ℝ} (hε : 0 < ε) :
    Differentiable ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) := by
  -- With the elementwise norm, a matrix-valued map is differentiable if every entry is.
  refine differentiable_pi.2 fun t => differentiable_pi.2 fun i => ?_
  intro h
  -- The quantity under the root, `‖h t‖² / d + ε`, is differentiable and at least `ε > 0`.
  have hq : Differentiable ℝ
      fun h : Matrix T d ℝ => (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε := by
    simp only [dotProduct]
    fun_prop
  have hpos : 0 < (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε := by
    have : 0 ≤ (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) :=
      div_nonneg (Finset.sum_nonneg fun j _ => mul_self_nonneg (h t j)) (Nat.cast_nonneg _)
    linarith
  have hent : Differentiable ℝ fun h : Matrix T d ℝ => h t i :=
    differentiable_pi.1 (differentiable_pi.1 differentiable_id t) i
  -- The entry `(t, i)` is `(sqrt (‖h t‖² / d + ε))⁻¹ * h t i`.
  show DifferentiableAt ℝ (fun h : Matrix T d ℝ =>
    (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ * h t i) h
  exact (((hq h).sqrt hpos.ne').inv (Real.sqrt_pos.2 hpos).ne').mul (hent h)

-- As in Mathlib's `MatrixExponential.lean`: without this option the instances of the operator
-- norm (e.g. `CompleteSpace`) are not found.
set_option backward.isDefEq.respectTransparency false in
/-- The derivative at `τ = 0` of an entry of `exp (τ Y)` is the entry of `Y`. The derivative of the
matrix exponential needs a normed-ring structure on the matrices, which the elementwise norm does
not give; the operator norm gives one, and an entry is a real function of `τ`, whatever the norm. -/
private theorem hasDerivAt_exp_smul_apply (Y : Matrix d d ℝ) (i j : d) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) i j) (Y i j) 0 := by
  let _ : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℝ ℝ i j)).hasFDerivAt.comp_hasDerivAt 0 h

/-- With the elementwise norm, the derivative of a matrix-valued function is taken entry by
entry. -/
private theorem hasDerivAt_matrix {m n : Type*} [Fintype m] [Fintype n] {f : ℝ → Matrix m n ℝ}
    {f' : Matrix m n ℝ} {x : ℝ} (h : ∀ i j, HasDerivAt (fun τ => f τ i j) (f' i j) x) :
    HasDerivAt f f' x :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 (h i)

/-- The derivative of `τ ↦ M exp (τ Y)` at `0` is `M Y`. -/
private theorem hasDerivAt_mul_exp {m : Type*} [Fintype m] (M : Matrix m d ℝ)
    (Y : Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => M * NormedSpace.exp (τ • Y)) (M * Y) 0 :=
  hasDerivAt_matrix fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_apply Y k j).const_mul (M i k)

/-- The derivative of `τ ↦ exp (τ Y) M` at `0` is `Y M`. -/
private theorem hasDerivAt_exp_mul {n : Type*} [Fintype n] (Y : Matrix d d ℝ)
    (M : Matrix d n ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) * M) (Y * M) 0 :=
  hasDerivAt_matrix fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_apply Y i k).mul_const (M k j)

/-- `exp (τ Y) exp (-τ Y) = 1`. -/
private theorem exp_smul_mul_exp_smul_neg (Y : Matrix d d ℝ) (τ : ℝ) :
    NormedSpace.exp (τ • Y) * NormedSpace.exp (τ • -Y) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).neg_right.smul_left τ).smul_right τ),
    smul_neg, add_neg_cancel, NormedSpace.exp_zero]

/-- The invertible matrix `exp (τ Y)`, with inverse `exp (-τ Y)`. -/
private noncomputable def expGL (Y : Matrix d d ℝ) (τ : ℝ) : GL d ℝ :=
  ⟨NormedSpace.exp (τ • Y), NormedSpace.exp (τ • -Y), exp_smul_mul_exp_smul_neg Y τ,
    by simpa only [neg_neg] using exp_smul_mul_exp_smul_neg (-Y) τ⟩

/-- `exp (0 Y) = 1`. -/
private theorem expGL_zero (Y : Matrix d d ℝ) : expGL Y 0 = 1 := by
  apply Units.ext
  change NormedSpace.exp ((0 : ℝ) • Y) = 1
  rw [zero_smul, NormedSpace.exp_zero]

/-- For antisymmetric `Y`, `exp (τ Y)` is orthogonal: `exp (τ Y)ᵀ = exp (τ Yᵀ) = exp (-τ Y)`. -/
private theorem expGL_mem_orthogonalGroup {Y : Matrix d d ℝ} (hY : Yᵀ = -Y) (τ : ℝ) :
    (expGL Y τ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  change (NormedSpace.exp (τ • Y))ᵀ * NormedSpace.exp (τ • Y) = 1
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, hY]
  simpa only [neg_neg] using exp_smul_mul_exp_smul_neg (-Y) τ

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The change of basis `1` at every hidden state does not move the parameters. -/
private theorem cob_one : θ.cob (fun _ => 1) (fun _ => 1) = θ := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [Params.cob, inv_one, Units.val_one, Matrix.mul_one, Matrix.one_mul]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The curve `τ ↦ θ.cob (exp (τ X_ℓ)) (exp (τ X_ℓ))` passes through `θ` at `τ = 0`. -/
private theorem cob_expGL_zero (X : Fin (L + 1) → Matrix d d ℝ) :
    θ.cob (fun ℓ => expGL (X ℓ) 0) (fun ℓ => expGL (X ℓ) 0) = θ := by
  simp only [expGL_zero]
  exact cob_one θ

omit [Fintype T] in
/-- The curve `τ ↦ θ.cob (exp (τ X_ℓ)) (exp (τ X_ℓ))` has velocity `cobDir θ X` at `τ = 0`. -/
private theorem hasDerivAt_cob_expGL (X : Fin (L + 1) → Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => θ.cob (fun ℓ => expGL (X ℓ) τ) (fun ℓ => expGL (X ℓ) τ))
      (cobDir θ X) 0 := by
  -- The norm of the parameters is that of the tuple of their components.
  let e : Params A dIn dOut ≃L[ℝ] Params.Prod A dIn dOut :=
    Params.linearEquivProd.toContinuousLinearEquiv
  -- Componentwise: `E exp (τ X_0)`, `exp (-τ X_{ℓ-1}) W_read^ℓ`, `W_write^ℓ exp (τ X_ℓ)`,
  -- `exp (-τ X_L) D`.
  have key : HasDerivAt
      (fun τ : ℝ => e (θ.cob (fun ℓ => expGL (X ℓ) τ) (fun ℓ => expGL (X ℓ) τ)))
      (e (cobDir θ X)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · exact hasDerivAt_mul_exp θ.E (X 0)
    · exact hasDerivAt_pi.2 fun ℓ =>
        (hasDerivAt_exp_mul (-X ℓ.castSucc) (θ.read ℓ)).congr_deriv (Matrix.neg_mul _ _)
    · exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_mul_exp (θ.write ℓ) (X ℓ.succ)
    · exact (hasDerivAt_exp_mul (-X (Fin.last L)) θ.D).congr_deriv (Matrix.neg_mul _ _)
  -- Back to the parameters through `e⁻¹`.
  exact e.symm.hasFDerivAt.comp_hasDerivAt (0 : ℝ) key

/-- Under pre-RMSNorm with `ε > 0` and without skip connections, the directions `cobDir θ X` with
antisymmetric `X_ℓ` are flat. -/
theorem cobDir_mem_flat_skipless_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (X : Fin (L + 1) → Matrix d d ℝ)
    (hX : ∀ ℓ, (X ℓ)ᵀ = -X ℓ) :
    cobDir θ X ∈ flat A 0 θ := by
  -- `θ ↦ F_θ(x)` is differentiable, since the blocks and RMSNorm are.
  have hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 0 θ' x) θ := fun x =>
    (differentiable_eval hf (by rw [hA]; exact differentiable_rmsNorm hε) x).differentiableAt
  -- The orthogonal changes of basis `exp (τ X_ℓ)` move `θ` with velocity `cobDir θ X`, and keep
  -- the function (Proposition 3.2 under pre-RMSNorm).
  refine mem_flat_of_hasDerivAt θ hdiff
    (fun τ => θ.cob (fun ℓ => expGL (X ℓ) τ) (fun ℓ => expGL (X ℓ) τ)) (cobDir θ X)
    (hasDerivAt_cob_expGL θ X) (cob_expGL_zero θ X) ?_
  exact Filter.Eventually.of_forall fun τ x =>
    eval_cob_rmsNorm θ x ε hA _ fun ℓ => expGL_mem_orthogonalGroup (hX ℓ) τ

/-- The antisymmetric `d × d` matrices, as a subspace of all matrices. -/
def antisymmetric (d : Type*) [Fintype d] : Submodule ℝ (Matrix d d ℝ) where
  carrier := {X | Xᵀ = -X}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_ofPred_eq] at hX hY ⊢
    rw [Matrix.transpose_add, hX, hY, neg_add]
  zero_mem' := by simp
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_ofPred_eq] at hX ⊢
    rw [Matrix.transpose_smul, hX, smul_neg]

/-- The antisymmetric `d × d` matrices form a space of dimension `d (d - 1) / 2`. -/
theorem finrank_antisymmetric :
    Module.finrank ℝ (antisymmetric d) = Fintype.card d * (Fintype.card d - 1) / 2 := by
  sorry

/-- **Theorem 4.3, under pre-RMSNorm, for the changes of basis.** If `E` and every write have
rank `d`, the functional dimension of a network without skip connections is at most
`P - (L + 1) d (d - 1) / 2`. -/
theorem funDim_add_le_skipless_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **Skips paper, the upper bound for residual networks under pre-RMSNorm, for the one change of
basis.** If `E` has rank `d`, the functional dimension of a residual network is at most
`P - d (d - 1) / 2`. -/
theorem funDim_add_le_residual_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end Skips
