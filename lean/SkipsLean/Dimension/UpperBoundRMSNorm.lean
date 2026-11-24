import SkipsLean.Dimension.UpperBound
import SkipsLean.Residual.LearnedSkips

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

omit [DecidableEq d] in
/-- An antisymmetric matrix is determined by its entries above the diagonal (for a linear order
on `d`), and these can be chosen freely. -/
private def antisymmetricEquiv [LinearOrder d] :
    antisymmetric d ≃ₗ[ℝ] ({p : d × d // p.1 < p.2} → ℝ) where
  toFun X p := (X : Matrix d d ℝ) p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨Matrix.of fun i j =>
      if h : i < j then f ⟨(i, j), h⟩ else if h' : j < i then -f ⟨(j, i), h'⟩ else 0, by
    -- the matrix built from `f` is antisymmetric
    change Matrix.transpose _ = -_
    ext i j
    simp only [transpose_apply, of_apply, Matrix.neg_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [dite_eq_right (not_lt.2 h.le), dite_eq_left h, dite_eq_left h]
    · rw [dite_eq_right (lt_irrefl i), dite_eq_right (lt_irrefl i), neg_zero]
    · rw [dite_eq_left h, dite_eq_right (not_lt.2 h.le), dite_eq_left h, neg_neg]⟩
  left_inv X := by
    obtain ⟨X, hX⟩ := X
    -- the entries of an antisymmetric matrix: `X j i = -X i j`, so `X i i = 0`
    have hX' : ∀ i j, X j i = -X i j := fun i j => by
      have h := congrFun (congrFun (show Xᵀ = -X from hX) i) j
      rwa [transpose_apply, Matrix.neg_apply] at h
    apply Subtype.ext
    ext i j
    simp only [of_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [dite_eq_left h]
    · rw [dite_eq_right (lt_irrefl i), dite_eq_right (lt_irrefl i)]
      have := hX' i i
      linarith
    · rw [dite_eq_right (not_lt.2 h.le), dite_eq_left h, hX' j i]
  right_inv f := by
    funext p
    simp only [of_apply]
    rw [dite_eq_left p.2]

/-- The antisymmetric `d × d` matrices form a space of dimension `d (d - 1) / 2`. -/
theorem finrank_antisymmetric :
    Module.finrank ℝ (antisymmetric d) = Fintype.card d * (Fintype.card d - 1) / 2 := by
  -- Order `d` through a numbering `e : d ≃ Fin n`.
  let e := Fintype.equivFin d
  let _ : LinearOrder d := LinearOrder.lift' e e.injective
  -- An antisymmetric matrix is a free choice of its entries above the diagonal.
  rw [antisymmetricEquiv.finrank_eq, Module.finrank_pi, ← card_below_diagonal,
    ← Fintype.card_subtype]
  -- The pairs `i < j` of `d` are, through `e` and a swap, the pairs below the diagonal of `Fin n`.
  exact Fintype.card_congr
    (((Equiv.prodCongr e e).trans (Equiv.prodComm _ _)).subtypeEquiv fun p => Iff.rfl)

/-- The direction `cobDir θ X` is linear in `X`. -/
private noncomputable def cobDirLin : (Fin (L + 1) → Matrix d d ℝ) →ₗ[ℝ] Params A dIn dOut where
  toFun := cobDir θ
  map_add' X Y := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [cobDir, Params.add_E, Params.add_read, Params.add_write, Params.add_D,
        Pi.add_apply, Matrix.mul_add, Matrix.add_mul, neg_add]
  map_smul' c X := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [cobDir, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_neg, RingHom.id_apply]

/-- **Theorem 4.3, under pre-RMSNorm, for the changes of basis.** If `E` and every write have
rank `d`, the functional dimension of a network without skip connections is at most
`P - (L + 1) d (d - 1) / 2`. -/
theorem funDim_add_le_skipless_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  have hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 0 θ' x) θ := fun x =>
    (differentiable_eval hf (by rw [hA]; exact differentiable_rmsNorm hε) x).differentiableAt
  -- The directions `cobDir θ X`, `X_ℓ` antisymmetric, are the range of a linear map `Φ`.
  let Φ : (Fin (L + 1) → antisymmetric d) →ₗ[ℝ] Params A dIn dOut :=
    (cobDirLin θ).comp (LinearMap.compLeft (antisymmetric d).subtype (Fin (L + 1)))
  -- `Φ` is injective (Lemma B.1).
  have hΦ : Function.Injective Φ := by
    intro X Y h
    have h' : cobDir θ (fun ℓ => (X ℓ : Matrix d d ℝ))
        = cobDir θ (fun ℓ => (Y ℓ : Matrix d d ℝ)) := h
    exact funext fun ℓ => Subtype.ext (congrFun (cobDir_injective θ hE hw h') ℓ)
  -- These directions are flat.
  have hV : LinearMap.range Φ ≤ flat A 0 θ := by
    intro v hv
    obtain ⟨X, rfl⟩ := LinearMap.mem_range.1 hv
    exact cobDir_mem_flat_skipless_rmsNorm θ hε hA hf (fun ℓ => (X ℓ : Matrix d d ℝ))
      fun ℓ => (X ℓ).2
  -- They span a space of dimension `(L + 1) d (d - 1) / 2`.
  have hdim : Module.finrank ℝ (LinearMap.range Φ)
      = (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) := by
    rw [LinearMap.finrank_range_of_inj hΦ, Module.finrank_pi_fintype, finrank_antisymmetric,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← hdim]
  exact funDim_add_finrank_le_of_le_flat θ hdiff _ hV

/-- A matrix `M` of full column rank can be cancelled on the left: `M X = M Y` gives `X = Y`. -/
private theorem mul_left_cancel_of_rank {m : Type*} [Fintype m] {M : Matrix m d ℝ}
    (hM : M.rank = Fintype.card d) {X Y : Matrix d d ℝ} (h : M * X = M * Y) : X = Y := by
  -- `v ↦ v M` is onto, so some `B` has `B M = 1`.
  obtain ⟨B, hB⟩ : ∃ B : Matrix d m ℝ, B * M = 1 := by
    have hs := (Matrix.vecMul_surjective_iff_rank_eq_card (M := M)).2 hM
    choose v hv using fun i : d => hs (Pi.single i 1)
    have hv' : ∀ i, v i ᵥ* M = Pi.single i 1 := hv
    refine ⟨Matrix.of v, ?_⟩
    ext i j
    rw [Matrix.mul_apply_eq_vecMul, show (Matrix.of v) i = v i from rfl, hv',
      Matrix.one_eq_pi_single]
  calc X = B * M * X := by rw [hB, Matrix.one_mul]
    _ = B * M * Y := by rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc]
    _ = Y := by rw [hB, Matrix.one_mul]

/-- Under pre-RMSNorm with `ε > 0`, in a residual network, the direction of one antisymmetric `X`
at all hidden states is flat. -/
private theorem cobDir_const_mem_flat_residual_rmsNorm {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (X : Matrix d d ℝ)
    (hX : Xᵀ = -X) :
    cobDir θ (fun _ => X) ∈ flat A 1 θ := by
  have hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' x) θ := fun x =>
    (differentiable_eval hf (by rw [hA]; exact differentiable_rmsNorm hε) x).differentiableAt
  -- The same orthogonal change of basis `exp (τ X)` at all hidden states keeps the function of a
  -- residual network (Theorem 3.3 (i) under pre-RMSNorm).
  refine mem_flat_of_hasDerivAt θ hdiff
    (fun τ => θ.cob (fun _ => expGL X τ) (fun _ => expGL X τ)) (cobDir θ fun _ => X)
    (hasDerivAt_cob_expGL θ fun _ => X) (cob_expGL_zero θ fun _ => X) ?_
  exact Filter.Eventually.of_forall fun τ x =>
    eval_cob_residual_rmsNorm θ x ε hA (expGL X τ) (expGL_mem_orthogonalGroup hX τ)

/-- **Skips paper, the upper bound for residual networks under pre-RMSNorm, for the one change of
basis.** If `E` has rank `d`, the functional dimension of a residual network is at most
`P - d (d - 1) / 2`. -/
theorem funDim_add_le_residual_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  have hdiff : ∀ x : Matrix T dIn ℝ,
      DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' x) θ := fun x =>
    (differentiable_eval hf (by rw [hA]; exact differentiable_rmsNorm hε) x).differentiableAt
  -- The directions `cobDir θ (fun _ => X)`, `X` antisymmetric, are the range of a linear map `Φ`.
  let Φ : antisymmetric d →ₗ[ℝ] Params A dIn dOut :=
    (cobDirLin θ).comp (LinearMap.pi fun _ => (antisymmetric d).subtype)
  -- `Φ` is injective: its `E` component is `E X`, and `E` has rank `d`.
  have hΦ : Function.Injective Φ := by
    intro X Y h
    have h' : cobDir θ (fun _ => (X : Matrix d d ℝ))
        = cobDir θ (fun _ => (Y : Matrix d d ℝ)) := h
    exact Subtype.ext (mul_left_cancel_of_rank hE (congrArg Params.E h'))
  -- These directions are flat.
  have hV : LinearMap.range Φ ≤ flat A 1 θ := by
    intro v hv
    obtain ⟨X, rfl⟩ := LinearMap.mem_range.1 hv
    exact cobDir_const_mem_flat_residual_rmsNorm θ hε hA hf X X.2
  -- They span a space of dimension `d (d - 1) / 2`.
  have hdim : Module.finrank ℝ (LinearMap.range Φ)
      = Fintype.card d * (Fintype.card d - 1) / 2 := by
    rw [LinearMap.finrank_range_of_inj hΦ, finrank_antisymmetric]
  rw [← hdim]
  exact funDim_add_finrank_le_of_le_flat θ hdiff _ hV

/-! ### Without a hypothesis of differentiability on the blocks

The same statements for arbitrary maps `f_ℓ` and every real `ε`, from `mem_flat_of_hasDerivAt'`
and `funDim_add_finrank_le_of_le_flat'`. -/

/-- Under pre-RMSNorm and without skip connections, the direction `cobDir θ X` of antisymmetric
`X_0, …, X_L` is flat, for arbitrary maps `f_ℓ`. -/
theorem cobDir_mem_flat_skipless_rmsNorm' (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (X : Fin (L + 1) → Matrix d d ℝ) (hX : ∀ ℓ, (X ℓ)ᵀ = -X ℓ) :
    cobDir θ X ∈ flat A 0 θ := by
  -- The orthogonal changes of basis `exp (τ X_ℓ)` move `θ` with velocity `cobDir θ X`, and keep
  -- the function (Proposition 3.2 under pre-RMSNorm).
  refine mem_flat_of_hasDerivAt' θ
    (fun τ => θ.cob (fun ℓ => expGL (X ℓ) τ) (fun ℓ => expGL (X ℓ) τ)) (cobDir θ X)
    (hasDerivAt_cob_expGL θ X) (cob_expGL_zero θ X) ?_
  exact Filter.Eventually.of_forall fun τ x =>
    eval_cob_rmsNorm θ x ε hA _ fun ℓ => expGL_mem_orthogonalGroup (hX ℓ) τ

/-- **Theorem 4.3 under pre-RMSNorm, for the changes of basis, for arbitrary maps `f_ℓ`.** If `E`
and every write have rank `d`, the functional dimension of a network without skip connections is
at most `P - (L + 1) d (d - 1) / 2`. -/
theorem funDim_add_le_skipless_rmsNorm' (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- The directions `cobDir θ X`, `X_ℓ` antisymmetric, are the range of a linear map `Φ`.
  let Φ : (Fin (L + 1) → antisymmetric d) →ₗ[ℝ] Params A dIn dOut :=
    (cobDirLin θ).comp (LinearMap.compLeft (antisymmetric d).subtype (Fin (L + 1)))
  -- `Φ` is injective (Lemma B.1).
  have hΦ : Function.Injective Φ := by
    intro X Y h
    have h' : cobDir θ (fun ℓ => (X ℓ : Matrix d d ℝ))
        = cobDir θ (fun ℓ => (Y ℓ : Matrix d d ℝ)) := h
    exact funext fun ℓ => Subtype.ext (congrFun (cobDir_injective θ hE hw h') ℓ)
  -- These directions are flat.
  have hV : LinearMap.range Φ ≤ flat A 0 θ := by
    intro v hv
    obtain ⟨X, rfl⟩ := LinearMap.mem_range.1 hv
    exact cobDir_mem_flat_skipless_rmsNorm' θ ε hA (fun ℓ => (X ℓ : Matrix d d ℝ))
      fun ℓ => (X ℓ).2
  -- They span a space of dimension `(L + 1) d (d - 1) / 2`.
  have hdim : Module.finrank ℝ (LinearMap.range Φ)
      = (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) := by
    rw [LinearMap.finrank_range_of_inj hΦ, Module.finrank_pi_fintype, finrank_antisymmetric,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← hdim]
  exact funDim_add_finrank_le_of_le_flat' θ _ hV

end Skips
