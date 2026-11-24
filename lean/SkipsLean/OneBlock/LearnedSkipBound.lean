import SkipsLean.OneBlock.LearnedSkip

/-!
# One block with a full learned skip under pre-RMSNorm: the upper bound

Paper (skips paper): Theorem B.1 (iii), Step 5 of its proof: "The directions `η^rot` are
independent of `K_B` and of each other, since `η_E = E X_a` and `η_D = −Y D` determine `X_a` and
`Y`. For a full `A` they have dimension `d_model (d_model − 1)`." The definitions are in
`OneBlock/LearnedSkip.lean`. The rotations of `h_0` and `h_1` by `e^{τ X_0}`, `e^{τ X_1}` with
antisymmetric `X_0`, `X_1` preserve the function when the skip moves as `A ↦ G_0⁻¹ A G_1`
(`eval_cob`, `Symmetry/ChangeOfBasis.lean`, with `rmsNorm_mul_orthogonal`); their directions and
the directions of the symmetries inside the block are flat and independent, which bounds the
functional dimension.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Flat directions of the family whose skips are parameters -/

omit [DecidableEq d] in
/-- Helper (the twin of `mem_flat_of_hasDerivAt'`): if a curve `γ` through `p` with velocity `v`
keeps the function near `τ = 0`, then `v` is flat. -/
private theorem mem_flatSkips_of_hasDerivAt_lsb {A : Arch T d L}
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V)
    (γ : ℝ → Params A dIn dOut × V) (v : Params A dIn dOut × V) (hγ : HasDerivAt γ v 0)
    (hγ0 : γ 0 = p)
    (hconst : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ x : Matrix T dIn ℝ,
      evalSkips A ι (γ τ) x = evalSkips A ι p x) :
    v ∈ flatSkips A ι p := by
  rw [flatSkips, Submodule.mem_iInf]
  intro x
  rw [LinearMap.mem_ker]
  show fderiv ℝ (fun p' => evalSkips A ι p' x) p v = 0
  by_cases hx : DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p
  · -- the chain rule: `τ ↦ F_{γ(τ)}(x)` has derivative `D_p F(x) v` at `0`
    have hl : HasFDerivAt (fun p' => evalSkips A ι p' x)
        (fderiv ℝ (fun p' => evalSkips A ι p' x) p) (γ 0) := by
      rw [hγ0]
      exact hx.hasFDerivAt
    have h1 := hl.comp_hasDerivAt (0 : ℝ) hγ
    -- the same map is constant near `0`, so its derivative there is `0`
    have h2 : HasDerivAt ((fun p' => evalSkips A ι p' x) ∘ γ) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (evalSkips A ι p x)).congr_of_eventuallyEq
        (hconst.mono fun τ hτ => hτ x)
    exact h1.unique h2
  · -- not differentiable at `p`: Mathlib's derivative is `0`
    rw [fderiv_zero_of_not_differentiableAt hx, _root_.zero_apply]

/-! ### The rotations `exp (τ X_ℓ)` (copies of the private helpers of
`Dimension/UpperBoundRMSNorm.lean`) -/

-- As in Mathlib's `MatrixExponential.lean`: without this option the instances of the operator
-- norm (e.g. `CompleteSpace`) are not found.
set_option backward.isDefEq.respectTransparency false in
/-- The derivative at `τ = 0` of an entry of `exp (τ Y)` is the entry of `Y` (computed with the
operator norm, under which matrices form a normed ring). -/
private theorem hasDerivAt_exp_smul_apply_lsb (Y : Matrix d d ℝ) (i j : d) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) i j) (Y i j) 0 := by
  let _ : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℝ ℝ i j)).hasFDerivAt.comp_hasDerivAt 0 h

/-- With the elementwise norm, the derivative of a matrix-valued function is taken entry by
entry. -/
private theorem hasDerivAt_matrix_lsb {m n : Type*} [Fintype m] [Fintype n] {f : ℝ → Matrix m n ℝ}
    {f' : Matrix m n ℝ} {x : ℝ} (h : ∀ i j, HasDerivAt (fun τ => f τ i j) (f' i j) x) :
    HasDerivAt f f' x :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 (h i)

/-- The derivative of `τ ↦ M exp (τ Y)` at `0` is `M Y`. -/
private theorem hasDerivAt_mul_exp_lsb {m : Type*} [Fintype m] (M : Matrix m d ℝ)
    (Y : Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => M * NormedSpace.exp (τ • Y)) (M * Y) 0 :=
  hasDerivAt_matrix_lsb fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_apply_lsb Y k j).const_mul (M i k)

/-- The derivative of `τ ↦ exp (τ Y) M` at `0` is `Y M`. -/
private theorem hasDerivAt_exp_mul_lsb {n : Type*} [Fintype n] (Y : Matrix d d ℝ)
    (M : Matrix d n ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) * M) (Y * M) 0 :=
  hasDerivAt_matrix_lsb fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_apply_lsb Y i k).mul_const (M k j)

-- See `hasDerivAt_exp_smul_apply_lsb` for this option.
set_option backward.isDefEq.respectTransparency false in
/-- The derivative of `τ ↦ exp (-τ Y) S exp (τ Z)` at `0` is `−Y S + S Z` (the product rule,
with the operator norm). -/
private theorem hasDerivAt_exp_mul_exp_lsb (Y Z S : Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • -Y) * S * NormedSpace.exp (τ • Z))
      (-(Y * S) + S * Z) 0 := by
  let _ : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-Y) (0 : ℝ)
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)
  have h := (h1.mul_const S).fun_mul h2
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at h
  rw [neg_mul] at h
  exact h

/-- `exp (τ Y) exp (-τ Y) = 1`. -/
private theorem exp_smul_mul_exp_smul_neg_lsb (Y : Matrix d d ℝ) (τ : ℝ) :
    NormedSpace.exp (τ • Y) * NormedSpace.exp (τ • -Y) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).neg_right.smul_left τ).smul_right τ),
    smul_neg, add_neg_cancel, NormedSpace.exp_zero]

/-- The invertible matrix `exp (τ Y)`, with inverse `exp (-τ Y)`. -/
private noncomputable def expGL_lsb (Y : Matrix d d ℝ) (τ : ℝ) : GL d ℝ :=
  ⟨NormedSpace.exp (τ • Y), NormedSpace.exp (τ • -Y), exp_smul_mul_exp_smul_neg_lsb Y τ,
    by simpa only [neg_neg] using exp_smul_mul_exp_smul_neg_lsb (-Y) τ⟩

/-- `exp (0 Y) = 1`. -/
private theorem expGL_zero_lsb (Y : Matrix d d ℝ) : expGL_lsb Y 0 = 1 := by
  apply Units.ext
  change NormedSpace.exp ((0 : ℝ) • Y) = 1
  rw [zero_smul, NormedSpace.exp_zero]

/-- For antisymmetric `Y`, `exp (τ Y)` is orthogonal: `exp (τ Y)ᵀ = exp (τ Yᵀ) = exp (-τ Y)`. -/
private theorem expGL_mem_orthogonalGroup_lsb {Y : Matrix d d ℝ} (hY : Yᵀ = -Y) (τ : ℝ) :
    (expGL_lsb Y τ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  change (NormedSpace.exp (τ • Y))ᵀ * NormedSpace.exp (τ • Y) = 1
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, hY]
  simpa only [neg_neg] using exp_smul_mul_exp_smul_neg_lsb (-Y) τ

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The curve `τ ↦ θ.cob (exp (τ X_ℓ)) (exp (τ X_ℓ))` passes through `θ` at `τ = 0`. -/
private theorem cob_expGL_zero_lsb {A : Arch T d L} (θ : Params A dIn dOut)
    (X : Fin (L + 1) → Matrix d d ℝ) :
    θ.cob (fun ℓ => expGL_lsb (X ℓ) 0) (fun ℓ => expGL_lsb (X ℓ) 0) = θ := by
  simp only [expGL_zero_lsb]
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [Params.cob, inv_one, Units.val_one, Matrix.mul_one, Matrix.one_mul]

omit [Fintype T] in
/-- The curve `τ ↦ θ.cob (exp (τ X_ℓ)) (exp (τ X_ℓ))` has velocity `cobDir θ X` at `τ = 0`. -/
private theorem hasDerivAt_cob_expGL_lsb {A : Arch T d L} (θ : Params A dIn dOut)
    (X : Fin (L + 1) → Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => θ.cob (fun ℓ => expGL_lsb (X ℓ) τ) (fun ℓ => expGL_lsb (X ℓ) τ))
      (cobDir θ X) 0 := by
  -- The norm of the parameters is that of the tuple of their components.
  let e : Params A dIn dOut ≃L[ℝ] Params.Prod A dIn dOut :=
    Params.linearEquivProd.toContinuousLinearEquiv
  -- Componentwise: `E exp (τ X_0)`, `exp (-τ X_{ℓ-1}) W_read^ℓ`, `W_write^ℓ exp (τ X_ℓ)`,
  -- `exp (-τ X_L) D`.
  have key : HasDerivAt
      (fun τ : ℝ => e (θ.cob (fun ℓ => expGL_lsb (X ℓ) τ) (fun ℓ => expGL_lsb (X ℓ) τ)))
      (e (cobDir θ X)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · exact hasDerivAt_mul_exp_lsb θ.E (X 0)
    · exact hasDerivAt_pi.2 fun ℓ =>
        (hasDerivAt_exp_mul_lsb (-X ℓ.castSucc) (θ.read ℓ)).congr_deriv (Matrix.neg_mul _ _)
    · exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_mul_exp_lsb (θ.write ℓ) (X ℓ.succ)
    · exact (hasDerivAt_exp_mul_lsb (-X (Fin.last L)) θ.D).congr_deriv (Matrix.neg_mul _ _)
  -- Back to the parameters through `e⁻¹`.
  exact e.symm.hasFDerivAt.comp_hasDerivAt (0 : ℝ) key

/-- **The rotations are flat** (Proposition 3.2 under pre-RMSNorm with the skips as parameters):
for antisymmetric `X_ℓ`, the orthogonal changes of basis `G_ℓ = exp (τ X_ℓ)` together with
`S_ℓ ↦ G_{ℓ-1}⁻¹ S_ℓ G_ℓ` keep the function, so their direction
`(cobDir θ X, −X_{ℓ-1} S_ℓ + S_ℓ X_ℓ)` is flat. -/
private theorem rot_mem_flatSkips_lsb {A : Arch T d L} {ε : ℝ} (hA : A.χ = rmsNorm ε)
    (θ : Params A dIn dOut) (S : Fin L → Matrix d d ℝ) (X : Fin (L + 1) → Matrix d d ℝ)
    (hX : ∀ ℓ, (X ℓ)ᵀ = -X ℓ) :
    (cobDir θ X, fun ℓ => -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ)
      ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S) := by
  -- the curve `τ ↦ (θ.cob G_τ G_τ, cobSkip S G_τ)` with `G_τ ℓ = exp (τ X_ℓ)` and its velocity
  have hγ : HasDerivAt (fun τ : ℝ => (θ.cob (fun ℓ => expGL_lsb (X ℓ) τ)
      (fun ℓ => expGL_lsb (X ℓ) τ), cobSkip S (fun ℓ => expGL_lsb (X ℓ) τ)))
      (cobDir θ X, fun ℓ => -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ) 0 :=
    (hasDerivAt_cob_expGL_lsb θ X).prodMk
      (hasDerivAt_pi.2 fun ℓ => hasDerivAt_exp_mul_exp_lsb (X ℓ.castSucc) (X ℓ.succ) (S ℓ))
  refine mem_flatSkips_of_hasDerivAt_lsb _ _ _ _ hγ ?_ ?_
  · -- at `τ = 0` the curve is at `(θ, S)`
    refine Prod.ext (cob_expGL_zero_lsb θ X) ?_
    show cobSkip S (fun ℓ => expGL_lsb (X ℓ) 0) = S
    funext ℓ
    simp only [cobSkip, expGL_zero_lsb, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  · -- along the curve the function is kept: pre-RMSNorm commutes with the orthogonal `G_τ ℓ`
    refine Filter.Eventually.of_forall fun τ x => ?_
    have hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (expGL_lsb (X ℓ) τ : Matrix d d ℝ))
        = A.χ h * (expGL_lsb (X ℓ) τ : Matrix d d ℝ) := by
      intro ℓ h
      rw [hA]
      exact rmsNorm_mul_orthogonal ε (expGL_mem_orthogonalGroup_lsb (hX ℓ) τ) h
    exact eval_cob (M := S) (θ := θ) (G := fun ℓ => expGL_lsb (X ℓ) τ)
      (K := fun ℓ => expGL_lsb (X ℓ) τ) (x := x) hχ

/-! ### The symmetries inside the block -/

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper (the private `eval_eq_of_blocks_ibl` of `Symmetry/InsideBlocks.lean`): two parameters
with the same `E`, the same `D` and the same output of every block on every hidden state compute
the same function, for any stream matrices. -/
private theorem eval_eq_of_blocks_lsb {A : Arch T d L} (θ₁ θ₂ : Params A dIn dOut)
    (hE : θ₂.E = θ₁.E) (hD : θ₂.D = θ₁.D)
    (hb : ∀ ℓ (h : Matrix T d ℝ),
      A.f ℓ (h * θ₂.read ℓ) * θ₂.write ℓ = A.f ℓ (h * θ₁.read ℓ) * θ₁.write ℓ)
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval A S θ₂ x = eval A S θ₁ x := by
  -- the hidden states agree, by induction along the network
  have hh : ∀ ℓ : Fin (L + 1), hidden A S θ₂ x ℓ = hidden A S θ₁ x ℓ := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => rw [hidden_zero, hidden_zero, hE]
    | succ ℓ ih => rw [hidden_succ, hidden_succ, ih, hb]
  -- hence the outputs agree
  rw [eval, eval, hh, hD]

omit [DecidableEq d] in
/-- A direction `η` of a symmetry inside the blocks, with the skips not moving, is flat: the
curve `τ ↦ (γ τ, S)` keeps `E`, `D` and the map of every block. -/
private theorem insideBlocks_mem_flatSkips_lsb {A : Arch T d L} {θ η : Params A dIn dOut}
    (h : InsideBlocks A θ η) (S : Fin L → Matrix d d ℝ) :
    (η, 0) ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S) := by
  obtain ⟨γ, h0, hd, hev⟩ := h
  refine mem_flatSkips_of_hasDerivAt_lsb _ _ (fun τ => (γ τ, S)) _
    (hd.prodMk (hasDerivAt_const (0 : ℝ) S)) (by simp only [h0]) ?_
  filter_upwards [hev] with τ hτ x
  exact eval_eq_of_blocks_lsb θ (γ τ) hτ.1 hτ.2.1 hτ.2.2 S x

omit [DecidableEq d] in
/-- The directions `(u, 0)`, `u` in the span of the directions of symmetries inside the blocks,
are flat (the flat directions form a subspace). -/
private theorem span_mem_flatSkips_lsb {A : Arch T d L} {θ u : Params A dIn dOut}
    (hu : u ∈ Submodule.span ℝ {η | InsideBlocks A θ η}) (S : Fin L → Matrix d d ℝ) :
    (u, 0) ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S) := by
  have hle : Submodule.span ℝ {η | InsideBlocks A θ η}
      ≤ (flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S)).comap
        (LinearMap.inl ℝ (Params A dIn dOut) (Fin L → Matrix d d ℝ)) :=
    Submodule.span_le.2 fun η hη => insideBlocks_mem_flatSkips_lsb hη S
  exact hle hu

omit [Fintype T] [DecidableEq d] in
/-- The directions spanned by directions of symmetries inside the blocks have `E` component `0`
(the copy of the private `E_eq_zero_of_mem_span_ibl`). -/
private theorem E_eq_zero_of_mem_span_lsb {A : Arch T d L} {θ v : Params A dIn dOut}
    (hv : v ∈ Submodule.span ℝ {η | InsideBlocks A θ η}) : v.E = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact InsideBlocks.E_eq_zero hx
  | zero => rfl
  | add x y _ _ hx hy => rw [Params.add_E, hx, hy, add_zero]
  | smul a x _ hx => rw [Params.smul_E, hx, smul_zero]

omit [Fintype T] [DecidableEq d] in
/-- The directions spanned by directions of symmetries inside the blocks have `D` component
`0`. -/
private theorem D_eq_zero_of_mem_span_lsb {A : Arch T d L} {θ v : Params A dIn dOut}
    (hv : v ∈ Submodule.span ℝ {η | InsideBlocks A θ η}) : v.D = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact InsideBlocks.D_eq_zero hx
  | zero => rfl
  | add x y _ _ hx hy => rw [Params.add_D, hx, hy, add_zero]
  | smul a x _ hx => rw [Params.smul_D, hx, smul_zero]

/-! ### Independence -/

/-- Helper (the private `cancel_left_of_rank_ibl`): a matrix `M` of rank equal to its number of
columns cancels on the left, `M X = M Y → X = Y` (its kernel is `0` by rank–nullity). -/
private theorem cancel_left_of_rank_lsb {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

/-- A matrix `M` of rank equal to its number of rows cancels on the right, `X M = Y M → X = Y`
(transpose, and cancel `Mᵀ` on the left). -/
private theorem cancel_right_of_rank_lsb {m n k : Type*} [Fintype m] [Fintype n]
    (M : Matrix n m ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix k n ℝ}
    (h : X * M = Y * M) : X = Y := by
  have h' := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul] at h'
  have hMt : Mᵀ.rank = Fintype.card n := by rw [Matrix.rank_transpose, hM]
  exact Matrix.transpose_injective (cancel_left_of_rank_lsb Mᵀ hMt h')

/-- The direction of the skips under the changes of basis `X`: `S_ℓ ↦ −X_{ℓ-1} S_ℓ + S_ℓ X_ℓ`,
linear in `X`. -/
private noncomputable def skipDirLin_lsb (S : Fin L → Matrix d d ℝ) :
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

/-- **The upper bound for one block with a full learned skip under pre-RMSNorm (`ε > 0`):** if `E`
and `D` have rank `d` and `U` is a space spanned by directions of symmetries inside the block,
then `fd + d (d − 1) + dim U ≤ P + d²`, where `P` counts the weights without the skip: the
orthogonal changes of basis at `h_0` and at `h_1` act independently, with `A ↦ G_0⁻¹ A G_1`. -/
theorem funDimLearned_add_le_rmsNorm {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
    (hE : p.1.E.rank = Fintype.card d) (hD : p.1.D.rank = Fintype.card d)
    (U : Submodule ℝ (Params A dIn dOut))
    (hU : U ≤ Submodule.span ℝ {η | InsideBlocks A p.1 η}) :
    funDimLearned A p + (Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ U)
      ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
  -- The families `X = (X_0, X_1)` of antisymmetric matrices, as matrices.
  let Ψ : (Fin (1 + 1) → antisymmetric d) →ₗ[ℝ] (Fin (1 + 1) → Matrix d d ℝ) :=
    LinearMap.compLeft (antisymmetric d).subtype (Fin (1 + 1))
  -- The linear map `(X, u) ↦ (cobDir θ X, −X_0 S + S X_1) + (u, 0)`.
  let Φ : (Fin (1 + 1) → antisymmetric d) × U →ₗ[ℝ]
      Params A dIn dOut × (Fin 1 → Matrix d d ℝ) :=
    (((cobDirLin p.1).comp Ψ).prod ((skipDirLin_lsb p.2).comp Ψ)).coprod
      ((LinearMap.inl ℝ (Params A dIn dOut) (Fin 1 → Matrix d d ℝ)).comp U.subtype)
  -- Its directions are flat: the rotations are (Step 1), and so are the symmetries inside the
  -- block (Step 2).
  have hflat : LinearMap.range Φ
      ≤ flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p := by
    rintro _ ⟨⟨X, u⟩, rfl⟩
    rw [LinearMap.coprod_apply]
    exact Submodule.add_mem _
      (rot_mem_flatSkips_lsb hA p.1 p.2 (fun ℓ => (X ℓ : Matrix d d ℝ)) fun ℓ => (X ℓ).2)
      (span_mem_flatSkips_lsb (hU u.2) p.2)
  -- It is injective (Step 3): `u` has `E` and `D` components `0`, so the `E` component `E X_0`
  -- gives `X_0`, the `D` component `−X_1 D` gives `X_1`, and then the rest gives `u`.
  have hinj : Function.Injective Φ := by
    rintro ⟨X, u⟩ ⟨Y, u'⟩ h
    have h1 : cobDir p.1 (fun ℓ => (X ℓ : Matrix d d ℝ)) + (u : Params A dIn dOut)
        = cobDir p.1 (fun ℓ => (Y ℓ : Matrix d d ℝ)) + (u' : Params A dIn dOut) :=
      congrArg Prod.fst h
    have hu0 := E_eq_zero_of_mem_span_lsb (hU u.2)
    have hu0' := E_eq_zero_of_mem_span_lsb (hU u'.2)
    have hv0 := D_eq_zero_of_mem_span_lsb (hU u.2)
    have hv0' := D_eq_zero_of_mem_span_lsb (hU u'.2)
    -- the embedding: `E X_0 = E Y_0`
    have hX0 : (X 0 : Matrix d d ℝ) = Y 0 := by
      have h2 := congrArg Params.E h1
      rw [Params.add_E, Params.add_E, hu0, hu0', add_zero, add_zero] at h2
      exact cancel_left_of_rank_lsb p.1.E hE h2
    -- the readout: `−X_1 D = −Y_1 D`
    have hX1 : (X (Fin.last 1) : Matrix d d ℝ) = Y (Fin.last 1) := by
      have h2 := congrArg Params.D h1
      rw [Params.add_D, Params.add_D, hv0, hv0', add_zero, add_zero] at h2
      have h3 : -((X (Fin.last 1) : Matrix d d ℝ) * p.1.D)
          = -((Y (Fin.last 1) : Matrix d d ℝ) * p.1.D) := h2
      exact cancel_right_of_rank_lsb p.1.D hD (neg_inj.1 h3)
    have hXY : X = Y := by
      refine funext fun ℓ => Subtype.ext ?_
      fin_cases ℓ
      exacts [hX0, hX1]
    subst hXY
    exact Prod.ext rfl (Subtype.ext (add_left_cancel h1))
  -- The source has dimension `2 · d (d − 1) / 2 + dim U = d (d − 1) + dim U`.
  have hdim : Module.finrank ℝ ((Fin (1 + 1) → antisymmetric d) × U)
      = Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ U := by
    rw [Module.finrank_prod,
      Module.finrank_pi_fintype (R := ℝ) (ι := Fin (1 + 1)) (M := fun _ => antisymmetric d),
      finrank_antisymmetric, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
    generalize Fintype.card d * (Fintype.card d - 1) = n at h2 ⊢
    omega
  -- So the flat directions have dimension at least `d (d − 1) + dim U`.
  have hmono : Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ U
      ≤ Module.finrank ℝ (flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p) :=
    calc Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ U
        = Module.finrank ℝ ((Fin (1 + 1) → antisymmetric d) × U) := hdim.symm
      _ = Module.finrank ℝ (LinearMap.range Φ) := (LinearMap.finrank_range_of_inj hinj).symm
      _ ≤ _ := Submodule.finrank_mono hflat
  -- Step 4: `fd + dim(flat) = P + d²`.
  have hχ : Differentiable ℝ A.χ := by
    rw [hA]
    exact differentiable_rmsNorm hε
  have hsum : funDimLearned A p
      + Module.finrank ℝ (flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p)
      = Module.finrank ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) :=
    funDimSkips_add_finrank_flatSkips A _ hf hχ p
  have hP : Module.finrank ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
      = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_matrix]
    simp [sq]
  calc funDimLearned A p + (Fintype.card d * (Fintype.card d - 1) + Module.finrank ℝ U)
      ≤ funDimLearned A p
        + Module.finrank ℝ (flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p) :=
        Nat.add_le_add_left hmono _
    _ = Module.finrank ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) := hsum
    _ = _ := hP

end Skips
