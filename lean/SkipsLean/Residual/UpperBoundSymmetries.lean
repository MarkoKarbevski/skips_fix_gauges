import SkipsLean.Dimension.RescalingGate

/-!
# The upper bound with identity skips, with the symmetries inside the blocks

Paper (skips): Theorem 4.2. "Let `𝒢` be the group of changes of basis of one hidden state, and `s`
the dimension of the symmetries inside the blocks, the same with and without skips. With or
without pre-RMSNorm, at generic parameters, the functional dimension is at most
`P - (L+1) dim 𝒢 - s` without skips and at most `P - dim 𝒢 - s` with identity skips."

The bound without skips is Theorem 4.3 of the dimension paper (`Dimension/`, `Generic/`). This
file has the bound with identity skips (the stream matrices `1`), with the term `s`:

* for arbitrary maps `f_ℓ`, the bound from the one change of basis, `fd ≤ P - dim 𝒢`, with no
  hypothesis of differentiability;
* gated blocks with any gate (SwiGLU, GeGLU): `s` is the number of hidden units (the rescalings of
  the values);
* MLP blocks with a positively homogeneous activation (ReLU, ReLU²): `s` is the number of hidden
  units (the rescalings of the units);
* gated blocks with a positively homogeneous gate (ReGLU): `s` is twice the number of hidden
  units.

`dim 𝒢` is `d²` without normalization and `d (d - 1) / 2` under pre-RMSNorm, where the statements
hold for every real `ε`. With identity skips only `E` needs rank `d` (`d_in ≥ d`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

section General

variable {A : Arch T d L} (θ : Params A dIn dOut)

/-! ### Helpers: the curve of one change of basis `exp (τ X)` at all hidden states

Copies of the private helpers of `Dimension/UpperBoundRMSNorm.lean`, under other names. -/

-- As in Mathlib's `MatrixExponential.lean`: without this option the instances of the operator
-- norm (e.g. `CompleteSpace`) are not found.
set_option backward.isDefEq.respectTransparency false in
/-- Helper: the derivative at `τ = 0` of an entry of `exp (τ Y)` is the entry of `Y` (computed
with the operator norm, under which the matrices form a Banach algebra; an entry is a real
function of `τ`, whatever the norm). -/
private theorem hasDerivAt_exp_smul_entry (Y : Matrix d d ℝ) (i j : d) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) i j) (Y i j) 0 := by
  let _ : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℝ ℝ i j)).hasFDerivAt.comp_hasDerivAt 0 h

/-- Helper: with the elementwise norm, the derivative of a matrix-valued function is taken entry
by entry. -/
private theorem hasDerivAt_matrix_entries {m n : Type*} [Fintype m] [Fintype n]
    {f : ℝ → Matrix m n ℝ} {f' : Matrix m n ℝ} {x : ℝ}
    (h : ∀ i j, HasDerivAt (fun τ => f τ i j) (f' i j) x) :
    HasDerivAt f f' x :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 (h i)

/-- Helper: the derivative of `τ ↦ M exp (τ Y)` at `0` is `M Y`. -/
private theorem hasDerivAt_mul_expSmul {m : Type*} [Fintype m] (M : Matrix m d ℝ)
    (Y : Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => M * NormedSpace.exp (τ • Y)) (M * Y) 0 :=
  hasDerivAt_matrix_entries fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_entry Y k j).const_mul (M i k)

/-- Helper: the derivative of `τ ↦ exp (τ Y) M` at `0` is `Y M`. -/
private theorem hasDerivAt_expSmul_mul {n : Type*} [Fintype n] (Y : Matrix d d ℝ)
    (M : Matrix d n ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) * M) (Y * M) 0 :=
  hasDerivAt_matrix_entries fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_entry Y i k).mul_const (M k j)

/-- Helper: `exp (τ Y) exp (-τ Y) = 1`. -/
private theorem expSmul_mul_expSmul_neg (Y : Matrix d d ℝ) (τ : ℝ) :
    NormedSpace.exp (τ • Y) * NormedSpace.exp (τ • -Y) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).neg_right.smul_left τ).smul_right τ),
    smul_neg, add_neg_cancel, NormedSpace.exp_zero]

/-- Helper: the invertible matrix `exp (τ Y)`, with inverse `exp (-τ Y)`. -/
private noncomputable def expGLConst (Y : Matrix d d ℝ) (τ : ℝ) : GL d ℝ :=
  ⟨NormedSpace.exp (τ • Y), NormedSpace.exp (τ • -Y), expSmul_mul_expSmul_neg Y τ,
    by simpa only [neg_neg] using expSmul_mul_expSmul_neg (-Y) τ⟩

/-- Helper: `exp (0 Y) = 1`. -/
private theorem expGLConst_zero (Y : Matrix d d ℝ) : expGLConst Y 0 = 1 := by
  apply Units.ext
  change NormedSpace.exp ((0 : ℝ) • Y) = 1
  rw [zero_smul, NormedSpace.exp_zero]

/-- Helper: for antisymmetric `Y`, `exp (τ Y)` is orthogonal: `exp (τ Y)ᵀ = exp (-τ Y)`. -/
private theorem expGLConst_mem_orthogonalGroup {Y : Matrix d d ℝ} (hY : Yᵀ = -Y) (τ : ℝ) :
    (expGLConst Y τ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  change (NormedSpace.exp (τ • Y))ᵀ * NormedSpace.exp (τ • Y) = 1
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, hY]
  simpa only [neg_neg] using expSmul_mul_expSmul_neg (-Y) τ

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the change of basis `1` at every hidden state does not move the parameters. -/
private theorem cob_one_ubs : θ.cob (fun _ => 1) (fun _ => 1) = θ := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [Params.cob, inv_one, Units.val_one, Matrix.mul_one, Matrix.one_mul]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the curve `τ ↦ θ.cob (exp (τ X_ℓ)) (exp (τ X_ℓ))` passes through `θ` at `τ = 0`. -/
private theorem cob_expGLConst_zero (X : Fin (L + 1) → Matrix d d ℝ) :
    θ.cob (fun ℓ => expGLConst (X ℓ) 0) (fun ℓ => expGLConst (X ℓ) 0) = θ := by
  simp only [expGLConst_zero]
  exact cob_one_ubs θ

omit [Fintype T] in
/-- Helper: the curve `τ ↦ θ.cob (exp (τ X_ℓ)) (exp (τ X_ℓ))` has velocity `cobDir θ X` at
`τ = 0`. -/
private theorem hasDerivAt_cob_expGLConst (X : Fin (L + 1) → Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => θ.cob (fun ℓ => expGLConst (X ℓ) τ) (fun ℓ => expGLConst (X ℓ) τ))
      (cobDir θ X) 0 := by
  -- the norm of the parameters is that of the tuple of their components
  let e : Params A dIn dOut ≃L[ℝ] Params.Prod A dIn dOut :=
    Params.linearEquivProd.toContinuousLinearEquiv
  -- componentwise: `E exp (τ X_0)`, `exp (-τ X_{ℓ-1}) W_read^ℓ`, `W_write^ℓ exp (τ X_ℓ)`,
  -- `exp (-τ X_L) D`
  have key : HasDerivAt
      (fun τ : ℝ => e (θ.cob (fun ℓ => expGLConst (X ℓ) τ) (fun ℓ => expGLConst (X ℓ) τ)))
      (e (cobDir θ X)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · exact hasDerivAt_mul_expSmul θ.E (X 0)
    · exact hasDerivAt_pi.2 fun ℓ =>
        (hasDerivAt_expSmul_mul (-X ℓ.castSucc) (θ.read ℓ)).congr_deriv (Matrix.neg_mul _ _)
    · exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_mul_expSmul (θ.write ℓ) (X ℓ.succ)
    · exact (hasDerivAt_expSmul_mul (-X (Fin.last L)) θ.D).congr_deriv (Matrix.neg_mul _ _)
  -- back to the parameters through `e⁻¹`
  exact e.symm.hasFDerivAt.comp_hasDerivAt (0 : ℝ) key

/-- With identity skips and without normalization, the direction of one change of basis `X` at
all hidden states is flat, for arbitrary maps `f_ℓ`. -/
theorem cobDir_const_mem_flat_residual' (hA : A.χ = id) (X : Matrix d d ℝ) :
    cobDir θ (fun _ => X) ∈ flat A 1 θ := by
  -- the curve `τ ↦ θ.cob (exp (τ X))`, with the same `exp (τ X)` at every hidden state, moves
  -- `θ` with velocity `cobDir θ (fun _ => X)`; with identity skips it keeps the function at every
  -- `τ` (Theorem 3.3 (i))
  exact mem_flat_of_hasDerivAt' θ
    (fun τ => θ.cob (fun _ => expGLConst X τ) (fun _ => expGLConst X τ)) (cobDir θ (fun _ => X))
    (hasDerivAt_cob_expGLConst θ (fun _ => X)) (cob_expGLConst_zero θ (fun _ => X))
    (Filter.Eventually.of_forall fun τ x => eval_cob_residual θ x hA (expGLConst X τ))

/-- With identity skips and under pre-RMSNorm, the direction of one antisymmetric `X` at all
hidden states is flat, for arbitrary maps `f_ℓ` and every real `ε`. -/
theorem cobDir_const_mem_flat_residual_rmsNorm' (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (X : Matrix d d ℝ) (hX : Xᵀ = -X) :
    cobDir θ (fun _ => X) ∈ flat A 1 θ := by
  -- the same curve; for antisymmetric `X` the change of basis `exp (τ X)` is orthogonal, and
  -- it keeps the function of a residual network under pre-RMSNorm (Theorem 3.3 (i))
  exact mem_flat_of_hasDerivAt' θ
    (fun τ => θ.cob (fun _ => expGLConst X τ) (fun _ => expGLConst X τ)) (cobDir θ (fun _ => X))
    (hasDerivAt_cob_expGLConst θ (fun _ => X)) (cob_expGLConst_zero θ (fun _ => X))
    (Filter.Eventually.of_forall fun τ x =>
      eval_cob_residual_rmsNorm θ x ε hA (expGLConst X τ) (expGLConst_mem_orthogonalGroup hX τ))

/-! ### Helpers: the count of the flat directions -/

/-- Helper (the private `mul_left_cancel_of_rank` of `UpperBound.lean`): a matrix `M` of rank equal
to its number of columns cancels on the left, `M X = M Y → X = Y` (its kernel is `0` by
rank–nullity). -/
private theorem cancel_left_of_rank_ubs {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

omit [DecidableEq d] in
/-- Helper: the `d × d` matrices form a space of dimension `d²`. -/
private theorem finrank_matrix_sq : Module.finrank ℝ (Matrix d d ℝ) = Fintype.card d ^ 2 := by
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, sq]

/-- Helper: the bound from one change of basis. Let `ι : W → Matrix d d ℝ` be linear and injective
(all matrices, or the antisymmetric ones). If the directions `cobDir θ (fun _ => ι w)` are flat
and `E` has rank `d`, then `fd ≤ P - dim W`. -/
private theorem funDim_add_le_of_cobConst {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (ι : W →ₗ[ℝ] Matrix d d ℝ) (hι : Function.Injective ι)
    (hE : θ.E.rank = Fintype.card d) (hcob : ∀ w, cobDir θ (fun _ => ι w) ∈ flat A 1 θ) :
    funDim A 1 θ + Module.finrank ℝ W ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the linear map `w ↦ cobDir θ (fun _ => ι w)`
  let Φ : W →ₗ[ℝ] Params A dIn dOut :=
    (cobDirLin θ).comp (LinearMap.pi fun _ : Fin (L + 1) => ι)
  have hΦ : ∀ w, Φ w = cobDir θ (fun _ => ι w) := fun _ => rfl
  -- its directions are flat
  have hV : LinearMap.range Φ ≤ flat A 1 θ := by
    rintro _ ⟨w, rfl⟩
    rw [hΦ]
    exact hcob w
  -- it is injective: its `E` component is `E ι(w)`, and `E` has rank `d`
  have hinj : Function.Injective Φ := by
    intro w w' h
    rw [hΦ, hΦ] at h
    have h0 : θ.E * ι w = θ.E * ι w' := congrArg Params.E h
    exact hι (cancel_left_of_rank_ubs θ.E hE h0)
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj] at h

/-- Helper: the bound from one change of basis and the symmetries inside the blocks. Let
`ι : W → Matrix d d ℝ` be linear and injective, and `ρ : V → Params` linear and injective with
`E` component `0` (the directions of the symmetries inside the blocks). If the directions
`cobDir θ (fun _ => ι w)` and `ρ v` are flat and `E` has rank `d`, then
`fd ≤ P - dim W - dim V`. -/
private theorem funDim_add_le_of_cobConst_add {W V : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ι : W →ₗ[ℝ] Matrix d d ℝ) (hι : Function.Injective ι)
    (ρ : V →ₗ[ℝ] Params A dIn dOut) (hρ : Function.Injective ρ) (hρE : ∀ v, (ρ v).E = 0)
    (hE : θ.E.rank = Fintype.card d)
    (hcob : ∀ w, cobDir θ (fun _ => ι w) ∈ flat A 1 θ) (hflat : ∀ v, ρ v ∈ flat A 1 θ) :
    funDim A 1 θ + (Module.finrank ℝ W + Module.finrank ℝ V)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the linear map `(w, v) ↦ cobDir θ (fun _ => ι w) + ρ v`
  let Φ : W × V →ₗ[ℝ] Params A dIn dOut :=
    ((cobDirLin θ).comp (LinearMap.pi fun _ : Fin (L + 1) => ι)).coprod ρ
  have hΦ : ∀ w v, Φ (w, v) = cobDir θ (fun _ => ι w) + ρ v := fun _ _ => rfl
  -- its directions are flat, since both summands are
  have hV : LinearMap.range Φ ≤ flat A 1 θ := by
    rintro _ ⟨⟨w, v⟩, rfl⟩
    rw [hΦ]
    exact Submodule.add_mem _ (hcob w) (hflat v)
  -- it is injective: the `E` component `E ι(w)` (the symmetries inside the blocks leave `E`
  -- alone) gives `w`, since `E` has rank `d`; then `ρ v` gives `v`
  have hinj : Function.Injective Φ := by
    rintro ⟨w, v⟩ ⟨w', v'⟩ h
    rw [hΦ, hΦ] at h
    have h0 : θ.E * ι w = θ.E * ι w' := by
      have hE0 := congrArg Params.E h
      rw [Params.add_E, Params.add_E, hρE, hρE, add_zero, add_zero] at hE0
      exact hE0
    obtain rfl : w = w' := hι (cancel_left_of_rank_ubs θ.E hE h0)
    exact Prod.ext rfl (hρ (add_left_cancel h))
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rwa [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod] at h

/-- **Theorem 4.2 with identity skips, without normalization, for the change of basis, for
arbitrary maps `f_ℓ`:** if `E` has rank `d`, then `fd ≤ P - d²`. -/
theorem funDim_add_le_residual' (hA : A.χ = id) (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + Fintype.card d ^ 2 ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the directions `cobDir θ (fun _ => X)`, `X` any `d × d` matrix
  have h := funDim_add_le_of_cobConst θ LinearMap.id Function.injective_id hE
    (fun X => cobDir_const_mem_flat_residual' θ hA X)
  rwa [finrank_matrix_sq] at h

/-- **Theorem 4.2 with identity skips, under pre-RMSNorm, for the change of basis, for arbitrary
maps `f_ℓ`:** if `E` has rank `d`, then `fd ≤ P - d (d - 1) / 2`. -/
theorem funDim_add_le_residual_rmsNorm' (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the directions `cobDir θ (fun _ => X)`, `X` antisymmetric
  have h := funDim_add_le_of_cobConst θ (antisymmetric d).subtype
    (antisymmetric d).injective_subtype hE
    (fun X => cobDir_const_mem_flat_residual_rmsNorm' θ ε hA (X : Matrix d d ℝ) X.2)
  rwa [finrank_antisymmetric] at h

omit [Fintype T] in
/-- Helper (the private `rank_eq_of_isUnit_det_submatrix` of `Generic/Params.lean`): a matrix
with `d` columns has rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_submatrix_ubs {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- Helper (the private `ae_rank_E` of `Generic/Params.lean`): at generic parameters `E` has rank
`d`, when `d_in ≥ d`. -/
private theorem ae_rank_E_ubs (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d := by
  -- `d` rows of `E`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  exact rank_eq_of_isUnit_det_submatrix_ubs θ.E ρ (hθ.2.2.1 ρ)

end General

variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- Helper: the numbers of the rescalings of the hidden units form a space of dimension `s`, the
number of hidden units. -/
private theorem finrank_hidFun :
    Module.finrank ℝ (∀ ℓ, hid ℓ → ℝ) = ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]

/-! ### Gated blocks with any gate: the rescalings of the values -/

/-- Helper: `α ↦ rescaleDir θ α` is linear (the private `rescaleDirLinValue` of
`RescalingGate.lean`). -/
private noncomputable def valueRescaleLin {χ : Matrix T d ℝ → Matrix T d ℝ}
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

/-- Helper: if no value column of a read vanishes, `α ↦ rescaleDir θ α` is injective: the value
column `e_i` moves by `-α_i e_i`. -/
private theorem valueRescaleLin_injective {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0) :
    Function.Injective (valueRescaleLin θ) := by
  intro α α' h
  have h' : rescaleDir θ α = rescaleDir θ α' := h
  funext ℓ i
  -- an entry `a` with `e_i a ≠ 0`
  obtain ⟨a, ha⟩ := Function.ne_iff.mp (hv ℓ i)
  have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h') a) (Sum.inr i)
  change -(α ℓ i) * θ.read ℓ a (Sum.inr i) = -(α' ℓ i) * θ.read ℓ a (Sum.inr i) at hr
  exact neg_inj.mp (mul_right_cancel₀ ha hr)

/-- **Theorem 4.2 with identity skips for gated blocks, without normalization,** under the
conditions of the proof (`E` of rank `d`, no value column of a read zero):
`fd ≤ P - d² - s`, where `s` is the number of hidden units. -/
theorem funDim_add_le_residual_gated
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0) :
    funDim (Arch.gated σ id hid) 1 θ + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the flat directions `cobDir θ (fun _ => X) + rescaleDir θ α`, of dimension `d² + s`
  have h := funDim_add_le_of_cobConst_add θ LinearMap.id Function.injective_id
    (valueRescaleLin θ) (valueRescaleLin_injective θ hv) (fun _ => rfl) hE
    (fun X => cobDir_const_mem_flat_residual' θ rfl X) (fun α => rescaleDir_mem_flat' θ 1 α)
  rwa [finrank_matrix_sq, finrank_hidFun] at h

/-- **Theorem 4.2 with identity skips for gated blocks, under pre-RMSNorm:**
`fd ≤ P - d (d - 1) / 2 - s`. -/
theorem funDim_add_le_residual_gated_rmsNorm (ε : ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  -- the flat directions `cobDir θ (fun _ => X) + rescaleDir θ α`, `X` antisymmetric
  have h := funDim_add_le_of_cobConst_add θ (antisymmetric d).subtype
    (antisymmetric d).injective_subtype
    (valueRescaleLin θ) (valueRescaleLin_injective θ hv) (fun _ => rfl) hE
    (fun X => cobDir_const_mem_flat_residual_rmsNorm' θ ε rfl (X : Matrix d d ℝ) X.2)
    (fun α => rescaleDir_mem_flat' θ 1 α)
  rwa [finrank_antisymmetric, finrank_hidFun] at h

/-- Theorem 4.2 with identity skips for gated blocks at generic parameters (`d_in ≥ d`), without
normalization. -/
theorem ae_funDim_add_le_residual_gated [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the pointwise bound holds wherever `E` has rank `d` and no value column of a read vanishes
  filter_upwards [ae_rank_E_ubs μ hdIn, ae_value_ne_zero μ] with θ h1 h2
  exact funDim_add_le_residual_gated θ h1 h2

/-- Theorem 4.2 with identity skips for gated blocks at generic parameters (`d_in ≥ d`), under
pre-RMSNorm. -/
theorem ae_funDim_add_le_residual_gated_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_ubs μ hdIn, ae_value_ne_zero μ] with θ h1 h2
  exact funDim_add_le_residual_gated_rmsNorm ε θ h1 h2

/-! ### MLP blocks with a positively homogeneous activation (ReLU, ReLU²) -/

/-- Helper: `α ↦ rescaleDirMlp k θ α` is linear (the private `rescaleDirMlpLin` of
`RescalingMlp.lean`). -/
private noncomputable def mlpRescaleLin {χ : Matrix T d ℝ → Matrix T d ℝ} (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut where
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

/-- Helper: if no column of a read vanishes, `α ↦ rescaleDirMlp k θ α` is injective: the read
column `c_i` moves by `α_i c_i`. -/
private theorem mlpRescaleLin_injective {χ : Matrix T d ℝ → Matrix T d ℝ} (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    Function.Injective (mlpRescaleLin k θ) := by
  intro α α' h
  have h' : rescaleDirMlp k θ α = rescaleDirMlp k θ α' := h
  funext ℓ i
  -- an entry `a` with `c_i a ≠ 0`
  obtain ⟨a, ha⟩ := Function.ne_iff.mp (hc ℓ i)
  have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h') a) i
  change α ℓ i * θ.read ℓ a i = α' ℓ i * θ.read ℓ a i at hr
  exact mul_right_cancel₀ ha hr

/-- **Theorem 4.2 with identity skips for blocks with a positively homogeneous activation,
without normalization,** under the conditions of the proof (`E` of rank `d`, no column of a read
zero): `fd ≤ P - d² - s`, where `s` is the number of hidden units. -/
theorem funDim_add_le_residual_mlp_rescale {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ id hid) 1 θ + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the flat directions `cobDir θ (fun _ => X) + rescaleDirMlp k θ α`, of dimension `d² + s`
  have h := funDim_add_le_of_cobConst_add θ LinearMap.id Function.injective_id
    (mlpRescaleLin k θ) (mlpRescaleLin_injective k θ hc) (fun _ => rfl) hE
    (fun X => cobDir_const_mem_flat_residual' θ rfl X) (fun α => rescaleDirMlp_mem_flat hσ θ 1 α)
  rwa [finrank_matrix_sq, finrank_hidFun] at h

/-- **Theorem 4.2 with identity skips for blocks with a positively homogeneous activation, under
pre-RMSNorm:** `fd ≤ P - d (d - 1) / 2 - s`. -/
theorem funDim_add_le_residual_mlp_rescale_rmsNorm {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (ε : ℝ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  -- the flat directions `cobDir θ (fun _ => X) + rescaleDirMlp k θ α`, `X` antisymmetric
  have h := funDim_add_le_of_cobConst_add θ (antisymmetric d).subtype
    (antisymmetric d).injective_subtype
    (mlpRescaleLin k θ) (mlpRescaleLin_injective k θ hc) (fun _ => rfl) hE
    (fun X => cobDir_const_mem_flat_residual_rmsNorm' θ ε rfl (X : Matrix d d ℝ) X.2)
    (fun α => rescaleDirMlp_mem_flat hσ θ 1 α)
  rwa [finrank_antisymmetric, finrank_hidFun] at h

/-- Theorem 4.2 with identity skips for blocks with a positively homogeneous activation at generic
parameters (`d_in ≥ d`), without normalization. -/
theorem ae_funDim_add_le_residual_mlp_rescale [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the pointwise bound holds wherever `E` has rank `d` and no column of a read vanishes
  filter_upwards [ae_rank_E_ubs μ hdIn, ae_read_col_ne_zero μ] with θ h1 h2
  exact funDim_add_le_residual_mlp_rescale hσ θ h1 h2

/-- Theorem 4.2 with identity skips for blocks with a positively homogeneous activation at generic
parameters (`d_in ≥ d`), under pre-RMSNorm. -/
theorem ae_funDim_add_le_residual_mlp_rescale_rmsNorm [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (ε : ℝ)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_ubs μ hdIn, ae_read_col_ne_zero μ] with θ h1 h2
  exact funDim_add_le_residual_mlp_rescale_rmsNorm hσ ε θ h1 h2

/-! ### Gated blocks with a positively homogeneous gate (ReGLU) -/

/-- Helper: `β ↦ rescaleDirGate k θ β` is linear (the private `rescaleDirGateLin` of
`RescalingGate.lean`). -/
private noncomputable def gateRescaleLin {χ : Matrix T d ℝ → Matrix T d ℝ} (k : ℕ)
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

/-- Helper: if no value column and no gate column of a read vanishes,
`(α, β) ↦ rescaleDir θ α + rescaleDirGate k θ β` is injective: the gate column `g_i` moves by
`β_i g_i` and the value column `e_i` by `-α_i e_i`. -/
private theorem valueGateRescaleLin_injective {χ : Matrix T d ℝ → Matrix T d ℝ} (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    Function.Injective ((valueRescaleLin θ).coprod (gateRescaleLin k θ)) := by
  rintro ⟨α, β⟩ ⟨α', β'⟩ h
  have h' : rescaleDir θ α + rescaleDirGate k θ β = rescaleDir θ α' + rescaleDirGate k θ β' := h
  -- the gate columns: an entry `a` with `g_i a ≠ 0` gives `β_i = β'_i`
  have hβ : β = β' := by
    funext ℓ i
    obtain ⟨a, ha⟩ := Function.ne_iff.mp (hg ℓ i)
    have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h') a) (Sum.inl i)
    change 0 + β ℓ i * θ.read ℓ a (Sum.inl i) = 0 + β' ℓ i * θ.read ℓ a (Sum.inl i) at hr
    rw [zero_add, zero_add] at hr
    exact mul_right_cancel₀ ha hr
  -- the value columns: an entry `a` with `e_i a ≠ 0` gives `α_i = α'_i`
  have hα : α = α' := by
    funext ℓ i
    obtain ⟨a, ha⟩ := Function.ne_iff.mp (hv ℓ i)
    have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h') a) (Sum.inr i)
    change -(α ℓ i) * θ.read ℓ a (Sum.inr i) + 0 = -(α' ℓ i) * θ.read ℓ a (Sum.inr i) + 0 at hr
    rw [add_zero, add_zero] at hr
    exact neg_inj.mp (mul_right_cancel₀ ha hr)
  exact Prod.ext hα hβ

/-- **Theorem 4.2 with identity skips for gated blocks with a positively homogeneous gate, without
normalization,** under the conditions of the proof (`E` of rank `d`, no gate column and no value
column of a read zero): `fd ≤ P - d² - s`, where `s` is twice the number of hidden units. -/
theorem funDim_add_le_residual_gated_gate {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.gated σ id hid) 1 θ + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the flat directions `cobDir θ (fun _ => X) + rescaleDir θ α + rescaleDirGate k θ β`, of
  -- dimension `d² + 2 s`
  have h := funDim_add_le_of_cobConst_add θ LinearMap.id Function.injective_id
    ((valueRescaleLin θ).coprod (gateRescaleLin k θ)) (valueGateRescaleLin_injective k θ hv hg)
    (fun _ => show (0 : Matrix dIn d ℝ) + 0 = 0 from add_zero 0) hE
    (fun X => cobDir_const_mem_flat_residual' θ rfl X)
    (fun p => Submodule.add_mem _ (rescaleDir_mem_flat' θ 1 p.1)
      (rescaleDirGate_mem_flat hσ θ 1 p.2))
  rwa [finrank_matrix_sq, Module.finrank_prod, finrank_hidFun, ← two_mul] at h

/-- **Theorem 4.2 with identity skips for gated blocks with a positively homogeneous gate, under
pre-RMSNorm:** `fd ≤ P - d (d - 1) / 2 - s`. -/
theorem funDim_add_le_residual_gated_gate_rmsNorm {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (ε : ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  -- the same directions, with `X` antisymmetric
  have h := funDim_add_le_of_cobConst_add θ (antisymmetric d).subtype
    (antisymmetric d).injective_subtype
    ((valueRescaleLin θ).coprod (gateRescaleLin k θ)) (valueGateRescaleLin_injective k θ hv hg)
    (fun _ => show (0 : Matrix dIn d ℝ) + 0 = 0 from add_zero 0) hE
    (fun X => cobDir_const_mem_flat_residual_rmsNorm' θ ε rfl (X : Matrix d d ℝ) X.2)
    (fun p => Submodule.add_mem _ (rescaleDir_mem_flat' θ 1 p.1)
      (rescaleDirGate_mem_flat hσ θ 1 p.2))
  rwa [finrank_antisymmetric, Module.finrank_prod, finrank_hidFun, ← two_mul] at h

/-- Theorem 4.2 with identity skips for gated blocks with a positively homogeneous gate at generic
parameters (`d_in ≥ d`), without normalization. -/
theorem ae_funDim_add_le_residual_gated_gate [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 1 θ
        + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the pointwise bound holds wherever `E` has rank `d` and no value column and no gate column
  -- of a read vanishes
  filter_upwards [ae_rank_E_ubs μ hdIn, ae_value_ne_zero μ, ae_gate_ne_zero μ] with θ h1 h2 h3
  exact funDim_add_le_residual_gated_gate hσ θ h1 h2 h3

/-- Theorem 4.2 with identity skips for gated blocks with a positively homogeneous gate at generic
parameters (`d_in ≥ d`), under pre-RMSNorm. -/
theorem ae_funDim_add_le_residual_gated_gate_rmsNorm [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (ε : ℝ)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_ubs μ hdIn, ae_value_ne_zero μ, ae_gate_ne_zero μ] with θ h1 h2 h3
  exact funDim_add_le_residual_gated_gate_rmsNorm hσ ε θ h1 h2 h3

end Skips
