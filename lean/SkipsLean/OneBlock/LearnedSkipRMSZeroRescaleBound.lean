import SkipsLean.OneBlock.LearnedSkipRMSZeroBound
import SkipsLean.Dimension.UpperBoundTransformerRescale
import SkipsLean.OneBlock.ResidualRMSZeroRescaleGeneric
import SkipsLean.OneBlock.ResidualRMSZeroReGLUGeneric

/-!
# One ReLU, ReLU² or ReGLU block with a learned skip under pre-RMSNorm with `ε = 0`: "at most"

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. […] For `ε = 0` it exceeds that of the residual
network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and
ReGLU blocks." Its proof, "The case `ε = 0`": "the scalings of `h_0` and `h_1` are symmetries
too, since `N_ε(c h) = N_ε(h)` for `c > 0`. […] For the learned skip, `η^rot` and `K_B` are flat,
which gives at least `d_model (d_model − 1) + 2` […] dimensions besides `K_B`".

Here the half "at most" for ReLU, ReLU² and ReGLU blocks and a full learned skip:

* the bound for one block with a full learned skip and any space `U` of directions of symmetries
  inside the block, for `ε = 0`: the rotation and the scaling of `h_0` and of `h_1` and `U` are
  flat at every input and independent, so `fd ≤ P + d² − (d(d−1) + 2) − dim U` (the twin for
  `ε = 0` of `funDimLearned_add_le_rmsNorm'`, `OneBlock/LearnedSkipOn.lean`, which counts the
  rotations only);
* with `U` the rescalings of the hidden units (`s` dimensions) and the value for the residual
  network (`OneBlock/ResidualRMSZeroRescaleGeneric.lean`,
  `OneBlock/ResidualRMSZeroReGLUGeneric.lean`): at almost every weights and skip `(θ, A)` the
  functional dimension with the learned skip `A` exceeds that of the residual network with the
  weights `θ` by at most `d(d+1)/2 − 1`.

The functional dimensions are Lean's `funDimLearned` and `funDim` (all inputs). For the residual
network `funDim` is the paper's functional dimension (a batch of the paper's inputs has the same
rank) and for the network with the learned skip `funDimLearned` is at least the paper's, so the
inequality gives the paper's "at most". Not stated: the equality; the upper triangular skip.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]


/-! ### Flat directions of the family whose skips are parameters -/

omit [Nonempty T] [DecidableEq d] in
/-- Helper (copy of the private `mem_flatSkips_of_hasDerivAt_lso` of
`OneBlock/LearnedSkipOn.lean`): if a curve `γ` through `p` with velocity `v` keeps the function
near `τ = 0`, then `v` is flat. -/
private theorem mem_flatSkips_of_hasDerivAt_lzr {L : ℕ} {A : Arch T d L} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V) (γ : ℝ → Params A dIn dOut × V) (v : Params A dIn dOut × V)
    (hγ : HasDerivAt γ v 0) (hγ0 : γ 0 = p)
    (hconst : ∀ᶠ τ in nhds (0 : ℝ), ∀ x : Matrix T dIn ℝ,
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
`OneBlock/LearnedSkipOn.lean`) -/

-- As in Mathlib's `MatrixExponential.lean`: without this option the instances of the operator
-- norm (e.g. `CompleteSpace`) are not found.
set_option backward.isDefEq.respectTransparency false in
/-- Helper: the derivative at `τ = 0` of an entry of `exp (τ Y)` is the entry of `Y` (computed
with the operator norm, under which matrices form a normed ring). -/
private theorem hasDerivAt_exp_smul_apply_lzr (Y : Matrix d d ℝ) (i j : d) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) i j) (Y i j) 0 := by
  let _ : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℝ ℝ i j)).hasFDerivAt.comp_hasDerivAt 0 h

/-- Helper: with the elementwise norm, the derivative of a matrix-valued function is taken entry
by entry. -/
private theorem hasDerivAt_matrix_lzr {m n : Type*} [Fintype m] [Fintype n]
    {f : ℝ → Matrix m n ℝ} {f' : Matrix m n ℝ} {x : ℝ}
    (h : ∀ i j, HasDerivAt (fun τ => f τ i j) (f' i j) x) :
    HasDerivAt f f' x :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 (h i)

/-- Helper: the derivative of `τ ↦ M exp (τ Y)` at `0` is `M Y`. -/
private theorem hasDerivAt_mul_exp_lzr {m : Type*} [Fintype m] (M : Matrix m d ℝ)
    (Y : Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => M * NormedSpace.exp (τ • Y)) (M * Y) 0 :=
  hasDerivAt_matrix_lzr fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_apply_lzr Y k j).const_mul (M i k)

/-- Helper: the derivative of `τ ↦ exp (τ Y) M` at `0` is `Y M`. -/
private theorem hasDerivAt_exp_mul_lzr {n : Type*} [Fintype n] (Y : Matrix d d ℝ)
    (M : Matrix d n ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) * M) (Y * M) 0 :=
  hasDerivAt_matrix_lzr fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_apply_lzr Y i k).mul_const (M k j)

-- See `hasDerivAt_exp_smul_apply_lzr` for this option.
set_option backward.isDefEq.respectTransparency false in
/-- Helper: the derivative of `τ ↦ exp (-τ Y) S exp (τ Z)` at `0` is `−Y S + S Z` (the product
rule, with the operator norm). -/
private theorem hasDerivAt_exp_mul_exp_lzr (Y Z S : Matrix d d ℝ) :
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

/-- Helper: `exp (τ Y) exp (-τ Y) = 1`. -/
private theorem exp_smul_mul_exp_smul_neg_lzr (Y : Matrix d d ℝ) (τ : ℝ) :
    NormedSpace.exp (τ • Y) * NormedSpace.exp (τ • -Y) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).neg_right.smul_left τ).smul_right τ),
    smul_neg, add_neg_cancel, NormedSpace.exp_zero]

/-- Helper: the invertible matrix `exp (τ Y)`, with inverse `exp (-τ Y)`. -/
private noncomputable def expGL_lzr (Y : Matrix d d ℝ) (τ : ℝ) : GL d ℝ :=
  ⟨NormedSpace.exp (τ • Y), NormedSpace.exp (τ • -Y), exp_smul_mul_exp_smul_neg_lzr Y τ,
    by simpa only [neg_neg] using exp_smul_mul_exp_smul_neg_lzr (-Y) τ⟩

/-- Helper: `exp (0 Y) = 1`. -/
private theorem expGL_zero_lzr (Y : Matrix d d ℝ) : expGL_lzr Y 0 = 1 := by
  apply Units.ext
  change NormedSpace.exp ((0 : ℝ) • Y) = 1
  rw [zero_smul, NormedSpace.exp_zero]

/-- Helper: for antisymmetric `Y`, `exp (τ Y)` is orthogonal: `exp (τ Y)ᵀ = exp (-τ Y)`. -/
private theorem expGL_mem_orthogonalGroup_lzr {Y : Matrix d d ℝ} (hY : Yᵀ = -Y) (τ : ℝ) :
    (expGL_lzr Y τ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  change (NormedSpace.exp (τ • Y))ᵀ * NormedSpace.exp (τ • Y) = 1
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, hY]
  simpa only [neg_neg] using exp_smul_mul_exp_smul_neg_lzr (-Y) τ

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the curve `τ ↦ θ.cob (exp (τ X_ℓ)) (exp (τ X_ℓ))` passes through `θ` at `τ = 0`. -/
private theorem cob_expGL_zero_lzr {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut)
    (X : Fin (L + 1) → Matrix d d ℝ) :
    θ.cob (fun ℓ => expGL_lzr (X ℓ) 0) (fun ℓ => expGL_lzr (X ℓ) 0) = θ := by
  simp only [expGL_zero_lzr]
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [Params.cob, inv_one, Units.val_one, Matrix.mul_one, Matrix.one_mul]

omit [Fintype T] [Nonempty T] in
/-- Helper: the curve `τ ↦ θ.cob (exp (τ X_ℓ)) (exp (τ X_ℓ))` has velocity `cobDir θ X` at
`τ = 0`. -/
private theorem hasDerivAt_cob_expGL_lzr {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut)
    (X : Fin (L + 1) → Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => θ.cob (fun ℓ => expGL_lzr (X ℓ) τ) (fun ℓ => expGL_lzr (X ℓ) τ))
      (cobDir θ X) 0 := by
  -- The norm of the parameters is that of the tuple of their components.
  let e : Params A dIn dOut ≃L[ℝ] Params.Prod A dIn dOut :=
    Params.linearEquivProd.toContinuousLinearEquiv
  -- Componentwise: `E exp (τ X_0)`, `exp (-τ X_{ℓ-1}) W_read^ℓ`, `W_write^ℓ exp (τ X_ℓ)`,
  -- `exp (-τ X_L) D`.
  have key : HasDerivAt
      (fun τ : ℝ => e (θ.cob (fun ℓ => expGL_lzr (X ℓ) τ) (fun ℓ => expGL_lzr (X ℓ) τ)))
      (e (cobDir θ X)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · exact hasDerivAt_mul_exp_lzr θ.E (X 0)
    · exact hasDerivAt_pi.2 fun ℓ =>
        (hasDerivAt_exp_mul_lzr (-X ℓ.castSucc) (θ.read ℓ)).congr_deriv (Matrix.neg_mul _ _)
    · exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_mul_exp_lzr (θ.write ℓ) (X ℓ.succ)
    · exact (hasDerivAt_exp_mul_lzr (-X (Fin.last L)) θ.D).congr_deriv (Matrix.neg_mul _ _)
  -- Back to the parameters through `e⁻¹`.
  exact e.symm.hasFDerivAt.comp_hasDerivAt (0 : ℝ) key

omit [Nonempty T] in
/-- Helper (copy of the private `rot_mem_flatSkips_lso`): **the rotations are flat**: for
antisymmetric `X_ℓ`, the orthogonal changes of basis `G_ℓ = exp (τ X_ℓ)` together with
`S_ℓ ↦ G_{ℓ-1}⁻¹ S_ℓ G_ℓ` keep the function, so their direction
`(cobDir θ X, −X_{ℓ-1} S_ℓ + S_ℓ X_ℓ)` is flat. -/
private theorem rot_mem_flatSkips_lzr {L : ℕ} {A : Arch T d L} {ε : ℝ} (hA : A.χ = rmsNorm ε)
    (θ : Params A dIn dOut) (S : Fin L → Matrix d d ℝ) (X : Fin (L + 1) → Matrix d d ℝ)
    (hX : ∀ ℓ, (X ℓ)ᵀ = -X ℓ) :
    (cobDir θ X, fun ℓ => -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ)
      ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S) := by
  -- the curve `τ ↦ (θ.cob G_τ G_τ, cobSkip S G_τ)` with `G_τ ℓ = exp (τ X_ℓ)` and its velocity
  have hγ : HasDerivAt (fun τ : ℝ => (θ.cob (fun ℓ => expGL_lzr (X ℓ) τ)
      (fun ℓ => expGL_lzr (X ℓ) τ), cobSkip S (fun ℓ => expGL_lzr (X ℓ) τ)))
      (cobDir θ X, fun ℓ => -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ) 0 :=
    (hasDerivAt_cob_expGL_lzr θ X).prodMk
      (hasDerivAt_pi.2 fun ℓ => hasDerivAt_exp_mul_exp_lzr (X ℓ.castSucc) (X ℓ.succ) (S ℓ))
  refine mem_flatSkips_of_hasDerivAt_lzr _ _ _ _ hγ ?_ ?_
  · -- at `τ = 0` the curve is at `(θ, S)`
    refine Prod.ext (cob_expGL_zero_lzr θ X) ?_
    show cobSkip S (fun ℓ => expGL_lzr (X ℓ) 0) = S
    funext ℓ
    simp only [cobSkip, expGL_zero_lzr, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  · -- along the curve the function is kept: pre-RMSNorm commutes with the orthogonal `G_τ ℓ`
    refine Filter.Eventually.of_forall fun τ x => ?_
    have hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (expGL_lzr (X ℓ) τ : Matrix d d ℝ))
        = A.χ h * (expGL_lzr (X ℓ) τ : Matrix d d ℝ) := by
      intro ℓ h
      rw [hA]
      exact rmsNorm_mul_orthogonal ε (expGL_mem_orthogonalGroup_lzr (hX ℓ) τ) h
    exact eval_cob (M := S) (θ := θ) (G := fun ℓ => expGL_lzr (X ℓ) τ)
      (K := fun ℓ => expGL_lzr (X ℓ) τ) (x := x) hχ

/-! ### The scalings `e^{τ β_ℓ}` of the hidden states (`ε = 0`) -/

/-- Helper (copy of the private `scalarGL_rz` of `Dimension/UpperBoundRMSNormZero.lean`): the
invertible scalar matrix `c • 1`, for `c ≠ 0`. -/
private noncomputable def scalarGL_lzr (c : ℝ) (hc : c ≠ 0) : GL d ℝ :=
  ⟨c • 1, c⁻¹ • 1, by simp [smul_smul, hc], by simp [smul_smul, hc]⟩

/-- Helper (the private `scaleCurve_rz` of `Dimension/UpperBoundRMSNormZero.lean`): the curve of
the scales, written out: `E ↦ e^{τ β_0} E`, `W_write^ℓ ↦ e^{τ β_ℓ} W_write^ℓ`, the reads and `D`
unchanged. -/
private noncomputable def scaleCurve_lzr {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut)
    (β : Fin (L + 1) → ℝ) (τ : ℝ) : Params A dIn dOut where
  E := Real.exp (τ * β 0) • θ.E
  read := θ.read
  write ℓ := Real.exp (τ * β ℓ.succ) • θ.write ℓ
  D := θ.D

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the curve passes through `θ` at `τ = 0`. -/
private theorem scaleCurve_zero_lzr {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut)
    (β : Fin (L + 1) → ℝ) : scaleCurve_lzr θ β 0 = θ := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [scaleCurve_lzr, zero_mul, Real.exp_zero, one_smul]

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: the curve is the change of basis `G_ℓ = e^{τ β_ℓ} 1` at the writes and `K_ℓ = 1` at
the reads. -/
private theorem scaleCurve_eq_cob_lzr {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut)
    (β : Fin (L + 1) → ℝ) (τ : ℝ) :
    scaleCurve_lzr θ β τ = θ.cob (fun ℓ => scalarGL_lzr (Real.exp (τ * β ℓ)) (Real.exp_ne_zero _))
      (fun _ => 1) := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · show Real.exp (τ * β 0) • θ.E = θ.E * (Real.exp (τ * β 0) • (1 : Matrix d d ℝ))
    rw [Matrix.mul_smul, Matrix.mul_one]
  · show θ.read ℓ = (↑(1 : GL d ℝ)⁻¹ : Matrix d d ℝ) * θ.read ℓ
    rw [inv_one, Units.val_one, Matrix.one_mul]
  · show Real.exp (τ * β ℓ.succ) • θ.write ℓ
      = θ.write ℓ * (Real.exp (τ * β ℓ.succ) • (1 : Matrix d d ℝ))
    rw [Matrix.mul_smul, Matrix.mul_one]
  · show θ.D = (↑(1 : GL d ℝ)⁻¹ : Matrix d d ℝ) * θ.D
    rw [inv_one, Units.val_one, Matrix.one_mul]

/-- Helper: the skips along the scales: `G_{ℓ-1}⁻¹ S_ℓ G_ℓ = e^{τ (β_ℓ − β_{ℓ-1})} S_ℓ` for
`G_ℓ = e^{τ β_ℓ} 1`. -/
private theorem cobSkip_scalarGL_lzr {L : ℕ} (S : Fin L → Matrix d d ℝ) (β : Fin (L + 1) → ℝ)
    (τ : ℝ) :
    cobSkip S (fun ℓ => scalarGL_lzr (Real.exp (τ * β ℓ)) (Real.exp_ne_zero _))
      = fun ℓ => Real.exp (τ * (β ℓ.succ - β ℓ.castSucc)) • S ℓ := by
  funext ℓ
  show (Real.exp (τ * β ℓ.castSucc))⁻¹ • (1 : Matrix d d ℝ) * S ℓ
      * (Real.exp (τ * β ℓ.succ) • (1 : Matrix d d ℝ)) = _
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_sub,
    Real.exp_sub, div_eq_mul_inv]

/-- Helper (copy of the private `hasDerivAt_exp_mul_const_rz`): `τ ↦ e^{τ a} b` has derivative
`a b` at `τ = 0`. -/
private theorem hasDerivAt_exp_mul_const_lzr (a b : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.exp (τ * a) * b) (a * b) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const a).exp.mul_const b
  simpa using h

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper (copy of the private `hasDerivAt_scaleCurve_rz`): the curve has velocity
`scaleDir θ β` at `τ = 0`, entry by entry. -/
private theorem hasDerivAt_scaleCurve_lzr {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut)
    (β : Fin (L + 1) → ℝ) :
    HasDerivAt (scaleCurve_lzr θ β) (scaleDir θ β) 0 := by
  have hprod : HasDerivAt (fun τ : ℝ => Params.linearEquivProd (scaleCurve_lzr θ β τ))
      (Params.linearEquivProd (scaleDir θ β)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · -- the entries of the embedding are `e^{τ β_0} E_ik`
      exact hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun k =>
        hasDerivAt_exp_mul_const_lzr (β 0) (θ.E i k)
    · -- the reads do not move
      exact hasDerivAt_const (0 : ℝ) θ.read
    · -- the entries of the writes are `e^{τ β_ℓ} W_ik`
      exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun k =>
        hasDerivAt_exp_mul_const_lzr (β ℓ.succ) (θ.write ℓ i k)
    · -- the readout does not move
      exact hasDerivAt_const (0 : ℝ) θ.D
  -- back from the tuples of components to the parameters
  exact (LinearMap.toContinuousLinearMap
    (Params.linearEquivProd (A := A) (dIn := dIn)
      (dOut := dOut)).symm.toLinearMap).hasFDerivAt.comp_hasDerivAt 0 hprod

omit [DecidableEq d] in
/-- Helper: `τ ↦ e^{τ c} M` has derivative `c M` at `τ = 0`, entry by entry. -/
private theorem hasDerivAt_exp_smul_lzr (c : ℝ) (M : Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => Real.exp (τ * c) • M) (c • M) 0 :=
  hasDerivAt_matrix_lzr fun i j => hasDerivAt_exp_mul_const_lzr c (M i j)

omit [Nonempty T] in
/-- **The scalings are flat** (Proposition 3.2 for `ε = 0` with the skips as parameters): the
changes of basis `G_ℓ = e^{τ β_ℓ} 1`, `K_ℓ = 1`, together with `S_ℓ ↦ G_{ℓ-1}⁻¹ S_ℓ G_ℓ`, keep the
function, since `N_0(h c) = N_0(h)` for `c > 0`; so their direction
`(scaleDir θ β, (β_ℓ − β_{ℓ-1}) S_ℓ)` is flat. -/
private theorem scale_mem_flatSkips_lzr {L : ℕ} {A : Arch T d L} (hA : A.χ = rmsNorm 0)
    (θ : Params A dIn dOut) (S : Fin L → Matrix d d ℝ) (β : Fin (L + 1) → ℝ) :
    (scaleDir θ β, fun ℓ => (β ℓ.succ - β ℓ.castSucc) • S ℓ)
      ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S) := by
  -- the curve `τ ↦ (scaleCurve θ β τ, e^{τ (β_ℓ − β_{ℓ-1})} S_ℓ)` and its velocity
  have hγ : HasDerivAt (fun τ : ℝ => (scaleCurve_lzr θ β τ,
      fun ℓ => Real.exp (τ * (β ℓ.succ - β ℓ.castSucc)) • S ℓ))
      (scaleDir θ β, fun ℓ => (β ℓ.succ - β ℓ.castSucc) • S ℓ) 0 :=
    (hasDerivAt_scaleCurve_lzr θ β).prodMk
      (hasDerivAt_pi.2 fun ℓ => hasDerivAt_exp_smul_lzr _ (S ℓ))
  refine mem_flatSkips_of_hasDerivAt_lzr _ _ _ _ hγ ?_ ?_
  · -- at `τ = 0` the curve is at `(θ, S)`
    refine Prod.ext (scaleCurve_zero_lzr θ β) ?_
    funext ℓ
    show Real.exp (0 * (β ℓ.succ - β ℓ.castSucc)) • S ℓ = S ℓ
    rw [zero_mul, Real.exp_zero, one_smul]
  · -- along the curve the function is kept: `N_0` forgets the positive scale `e^{τ β_ℓ}`
    refine Filter.Eventually.of_forall fun τ x => ?_
    have hχ : ∀ ℓ (h : Matrix T d ℝ),
        A.χ (h * ((scalarGL_lzr (Real.exp (τ * β ℓ)) (Real.exp_ne_zero _) : GL d ℝ)
          : Matrix d d ℝ))
          = A.χ h * ((1 : GL d ℝ) : Matrix d d ℝ) := by
      intro ℓ h
      rw [hA, Units.val_one]
      exact rmsNorm_zero_mul_smul_orthogonal (Real.exp_pos _) (one_mem _) h
    have h1 := eval_cob (M := S) (θ := θ)
      (G := fun ℓ => scalarGL_lzr (Real.exp (τ * β ℓ)) (Real.exp_ne_zero _))
      (K := fun _ => 1) (x := x) hχ
    rw [← scaleCurve_eq_cob_lzr, cobSkip_scalarGL_lzr] at h1
    exact h1

/-! ### The symmetries inside the block -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (copy of the private `eval_eq_of_blocks_lso`): two parameters with the same `E`, the
same `D` and the same output of every block on every hidden state compute the same function, for
any stream matrices. -/
private theorem eval_eq_of_blocks_lzr {L : ℕ} {A : Arch T d L} (θ₁ θ₂ : Params A dIn dOut)
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

omit [Nonempty T] [DecidableEq d] in
/-- Helper (copy of the private `insideBlocks_mem_flatSkips_lso`): a direction `η` of a symmetry
inside the blocks, with the skips not moving, is flat. -/
private theorem insideBlocks_mem_flatSkips_lzr {L : ℕ} {A : Arch T d L}
    {θ η : Params A dIn dOut} (h : InsideBlocks A θ η) (S : Fin L → Matrix d d ℝ) :
    (η, 0) ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S) := by
  obtain ⟨γ, h0, hd, hev⟩ := h
  refine mem_flatSkips_of_hasDerivAt_lzr _ _ (fun τ => (γ τ, S)) _
    (hd.prodMk (hasDerivAt_const (0 : ℝ) S)) (by simp only [h0]) ?_
  filter_upwards [hev] with τ hτ x
  exact eval_eq_of_blocks_lzr θ (γ τ) hτ.1 hτ.2.1 hτ.2.2 S x

omit [Nonempty T] [DecidableEq d] in
/-- Helper (copy of the private `span_mem_flatSkips_lso`): the directions `(u, 0)`, `u` in the
span of the directions of symmetries inside the blocks, are flat. -/
private theorem span_mem_flatSkips_lzr {L : ℕ} {A : Arch T d L} {θ u : Params A dIn dOut}
    (hu : u ∈ Submodule.span ℝ {η | InsideBlocks A θ η}) (S : Fin L → Matrix d d ℝ) :
    (u, 0) ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S) := by
  have hle : Submodule.span ℝ {η | InsideBlocks A θ η}
      ≤ (flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S)).comap
        (LinearMap.inl ℝ (Params A dIn dOut) (Fin L → Matrix d d ℝ)) :=
    Submodule.span_le.2 fun η hη => insideBlocks_mem_flatSkips_lzr hη S
  exact hle hu

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper (copy of the private `E_eq_zero_of_mem_span_lso`): the directions spanned by directions
of symmetries inside the blocks have `E` component `0`. -/
private theorem E_eq_zero_of_mem_span_lzr {L : ℕ} {A : Arch T d L} {θ v : Params A dIn dOut}
    (hv : v ∈ Submodule.span ℝ {η | InsideBlocks A θ η}) : v.E = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact InsideBlocks.E_eq_zero hx
  | zero => rfl
  | add x y _ _ hx hy => rw [Params.add_E, hx, hy, add_zero]
  | smul a x _ hx => rw [Params.smul_E, hx, smul_zero]

/-! ### Independence -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of the private `cancel_left_of_rank_rz`): a matrix `M` of rank equal to its
number of columns cancels on the left, `M X = M Y → X = Y`. -/
private theorem cancel_left_of_rank_lzr {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

omit [Fintype T] [Nonempty T] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of the private `antisymm_add_smul_one_inj_rz`): an antisymmetric matrix plus a
scalar matrix determines both, since the diagonal of an antisymmetric matrix vanishes. -/
private theorem antisymm_add_smul_one_inj_lzr [Nonempty d] {X X' : Matrix d d ℝ}
    (hX : Xᵀ = -X) (hX' : X'ᵀ = -X') {b b' : ℝ}
    (h : X + b • (1 : Matrix d d ℝ) = X' + b' • 1) : X = X' ∧ b = b' := by
  obtain ⟨k⟩ := ‹Nonempty d›
  -- the diagonal entries of an antisymmetric matrix vanish
  have hd : ∀ {Z : Matrix d d ℝ}, Zᵀ = -Z → Z k k = 0 := fun {Z} hZ => by
    have := congrFun (congrFun hZ k) k
    rw [transpose_apply, Matrix.neg_apply] at this
    linarith
  -- the entry `(k, k)` gives `b = b'`, and then `X = X'`
  have hk := congrFun (congrFun h k) k
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    hd hX, hd hX', zero_add] at hk
  subst hk
  exact ⟨add_right_cancel h, rfl⟩

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of the private `mul_add_smul_inj_rz`): if `M` has rank `d`, then `M X + b M`
with antisymmetric `X` determines `X` and `b`: it is `M (X + b 1)`. -/
private theorem mul_add_smul_inj_lzr [Nonempty d] {m : Type*} (M : Matrix m d ℝ)
    (hM : M.rank = Fintype.card d) {X X' : Matrix d d ℝ} (hX : Xᵀ = -X) (hX' : X'ᵀ = -X')
    {b b' : ℝ} (h : M * X + b • M = M * X' + b' • M) : X = X' ∧ b = b' := by
  have h' : M * (X + b • (1 : Matrix d d ℝ)) = M * (X' + b' • 1) := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
    exact h
  exact antisymm_add_smul_one_inj_lzr hX hX' (cancel_left_of_rank_lzr M hM h')

/-- Helper (copy of the private `skipDirLin_lso`): the direction of the skips under the changes of
basis `X`: `S_ℓ ↦ −X_{ℓ-1} S_ℓ + S_ℓ X_ℓ`, linear in `X`. -/
private noncomputable def skipDirLin_lzr {L : ℕ} (S : Fin L → Matrix d d ℝ) :
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

/-- Helper (copy of the private `scaleDirLin_rz`): `β ↦ scaleDir θ β` is linear. -/
private noncomputable def scaleDirLin_lzr {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut) :
    (Fin (L + 1) → ℝ) →ₗ[ℝ] Params A dIn dOut where
  toFun := scaleDir θ
  map_add' β β' := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.add_E, Params.add_read, Params.add_write, Params.add_D,
        Pi.add_apply, add_smul, add_zero]
  map_smul' c β := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        Pi.smul_apply, smul_eq_mul, mul_smul, smul_zero, RingHom.id_apply]

/-- Helper: the direction of the skips under the scales `β`: `S_ℓ ↦ (β_ℓ − β_{ℓ-1}) S_ℓ`, linear
in `β`. -/
private noncomputable def scaleSkipLin_lzr {L : ℕ} (S : Fin L → Matrix d d ℝ) :
    (Fin (L + 1) → ℝ) →ₗ[ℝ] (Fin L → Matrix d d ℝ) where
  toFun β ℓ := (β ℓ.succ - β ℓ.castSucc) • S ℓ
  map_add' β β' := by
    funext ℓ
    simp only [Pi.add_apply]
    rw [add_sub_add_comm, add_smul]
  map_smul' c β := by
    funext ℓ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← mul_sub, mul_smul]

omit [Nonempty T] in
/-- **Proof of Theorem B.1 (iii) of the skips paper, "The case `ε = 0`", the bound for the learned
skip with symmetries inside the block:** for one block with a full learned skip `A` that is
invertible, under pre-RMSNorm with `ε = 0`, if `E` has rank `d ≥ 1` and `U` is a subspace of the
span of the directions of symmetries inside the block, then `fd + (d(d−1) + 2) + dim U ≤ P + d²`, where `P`
counts the weights without the skip. -/
theorem funDimLearned_add_le_rmsNorm_zero' {A : Arch T d 1} [Nonempty d] (hA : A.χ = rmsNorm 0)
    (p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
    (hE : p.1.E.rank = Fintype.card d) (hR : IsUnit (p.2 0).det)
    (U : Submodule ℝ (Params A dIn dOut))
    (hU : U ≤ Submodule.span ℝ {η | InsideBlocks A p.1 η}) :
    funDimLearned A p + ((Fintype.card d * (Fintype.card d - 1) + 2) + Module.finrank ℝ U)
      ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
  -- The families `X = (X_0, X_1)` of antisymmetric matrices, as matrices.
  let Ψ : (Fin (1 + 1) → antisymmetric d) →ₗ[ℝ] (Fin (1 + 1) → Matrix d d ℝ) :=
    LinearMap.compLeft (antisymmetric d).subtype (Fin (1 + 1))
  -- The linear map `((X, β), u) ↦ (cobDir θ X, −X_0 A + A X_1)
  -- + (scaleDir θ β, (β_1 − β_0) A) + (u, 0)`.
  let Φ : ((Fin (1 + 1) → antisymmetric d) × (Fin (1 + 1) → ℝ)) × U →ₗ[ℝ]
      Params A dIn dOut × (Fin 1 → Matrix d d ℝ) :=
    ((((cobDirLin p.1).comp Ψ).prod ((skipDirLin_lzr p.2).comp Ψ)).coprod
      ((scaleDirLin_lzr p.1).prod (scaleSkipLin_lzr p.2))).coprod
      ((LinearMap.inl ℝ (Params A dIn dOut) (Fin 1 → Matrix d d ℝ)).comp U.subtype)
  -- Its directions are flat: the rotations and the scalings of `h_0` and `h_1` are, and so are
  -- the symmetries inside the block.
  have hflat : LinearMap.range Φ
      ≤ flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p := by
    rintro _ ⟨⟨⟨X, β⟩, u⟩, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (rot_mem_flatSkips_lzr hA p.1 p.2 (fun ℓ => (X ℓ : Matrix d d ℝ)) fun ℓ => (X ℓ).2)
      (scale_mem_flatSkips_lzr hA p.1 p.2 β))
      (span_mem_flatSkips_lzr (hU u.2) p.2)
  -- It is injective: `u` has `E` component `0` and skip component `0`, so the `E` component
  -- `E (X_0 + β_0 I)` gives `X_0` and `β_0`, the skip component then gives `A (X_1 + β_1 I)`,
  -- hence `X_1` and `β_1` (`A` invertible), and then the rest gives `u`.
  have hinj : Function.Injective Φ := by
    rintro ⟨⟨X, β⟩, u⟩ ⟨⟨Y, β'⟩, u'⟩ h
    have h1 : cobDir p.1 (fun ℓ => (X ℓ : Matrix d d ℝ)) + scaleDir p.1 β
          + (u : Params A dIn dOut)
        = cobDir p.1 (fun ℓ => (Y ℓ : Matrix d d ℝ)) + scaleDir p.1 β'
          + (u' : Params A dIn dOut) :=
      congrArg Prod.fst h
    have h2 : -((X 0 : Matrix d d ℝ) * p.2 0) + p.2 0 * (X 1 : Matrix d d ℝ)
          + (β 1 - β 0) • p.2 0 + 0
        = -((Y 0 : Matrix d d ℝ) * p.2 0) + p.2 0 * (Y 1 : Matrix d d ℝ)
          + (β' 1 - β' 0) • p.2 0 + 0 :=
      congrFun (congrArg Prod.snd h) 0
    have hu0 := E_eq_zero_of_mem_span_lzr (hU u.2)
    have hu0' := E_eq_zero_of_mem_span_lzr (hU u'.2)
    -- the embedding: `E X_0 + β_0 E = E Y_0 + β'_0 E`
    have hE0 : p.1.E * (X 0 : Matrix d d ℝ) + β 0 • p.1.E
        = p.1.E * (Y 0 : Matrix d d ℝ) + β' 0 • p.1.E := by
      have h3 := congrArg Params.E h1
      rw [Params.add_E, Params.add_E, Params.add_E, Params.add_E, hu0, hu0', add_zero,
        add_zero] at h3
      exact h3
    obtain ⟨hX0, hβ0⟩ := mul_add_smul_inj_lzr p.1.E hE (X 0).2 (Y 0).2 hE0
    -- the skip: `A X_1 + (β_1 − β_0) A = A Y_1 + (β'_1 − β_0) A`, and `A` has rank `d`
    have hR' : (p.2 0).rank = Fintype.card d :=
      Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 hR)
    have hS : p.2 0 * (X 1 : Matrix d d ℝ) + (β 1 - β' 0) • p.2 0
        = p.2 0 * (Y 1 : Matrix d d ℝ) + (β' 1 - β' 0) • p.2 0 := by
      rw [hX0, hβ0, add_zero, add_zero, add_assoc, add_assoc] at h2
      exact add_left_cancel h2
    obtain ⟨hX1, hβ1⟩ := mul_add_smul_inj_lzr (p.2 0) hR' (X 1).2 (Y 1).2 hS
    have hXY : X = Y := by
      refine funext fun ℓ => Subtype.ext ?_
      fin_cases ℓ
      exacts [hX0, hX1]
    have hββ : β = β' := by
      funext ℓ
      fin_cases ℓ
      exacts [hβ0, sub_left_inj.1 hβ1]
    subst hXY hββ
    exact Prod.ext rfl (Subtype.ext (add_left_cancel h1))
  -- The source has dimension `2 (d (d − 1)/2 + 1) + dim U = d (d − 1) + 2 + dim U`.
  have hdim : Module.finrank ℝ (((Fin (1 + 1) → antisymmetric d) × (Fin (1 + 1) → ℝ)) × U)
      = (Fintype.card d * (Fintype.card d - 1) + 2) + Module.finrank ℝ U := by
    rw [Module.finrank_prod, Module.finrank_prod,
      Module.finrank_pi_fintype (R := ℝ) (ι := Fin (1 + 1)) (M := fun _ => antisymmetric d),
      finrank_antisymmetric, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Module.finrank_fin_fun]
    have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
    generalize Fintype.card d * (Fintype.card d - 1) = n at h2 ⊢
    omega
  -- So the flat directions have dimension at least `d (d − 1) + 2 + dim U`.
  have hmono : (Fintype.card d * (Fintype.card d - 1) + 2) + Module.finrank ℝ U
      ≤ Module.finrank ℝ (flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p) :=
    calc (Fintype.card d * (Fintype.card d - 1) + 2) + Module.finrank ℝ U
        = Module.finrank ℝ (((Fin (1 + 1) → antisymmetric d) × (Fin (1 + 1) → ℝ)) × U) :=
          hdim.symm
      _ = Module.finrank ℝ (LinearMap.range Φ) := (LinearMap.finrank_range_of_inj hinj).symm
      _ ≤ _ := Submodule.finrank_mono hflat
  -- `fd + dim(flat) = P + d²`, with no hypothesis of differentiability.
  have hsum : funDimLearned A p
      + Module.finrank ℝ (flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p)
      = Module.finrank ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) :=
    funDimSkips_add_finrank_flatSkips' A _ p
  have hP : Module.finrank ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
      = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_matrix]
    simp [sq]
  calc funDimLearned A p
        + ((Fintype.card d * (Fintype.card d - 1) + 2) + Module.finrank ℝ U)
      ≤ funDimLearned A p
        + Module.finrank ℝ (flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p) :=
        Nat.add_le_add_left hmono _
    _ = Module.finrank ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) := hsum
    _ = _ := hP

/-! ### At almost every weights and skip -/

omit [DecidableEq d] in
/-- Helper (copy of the private `borelSpace_skips_lsk` of `OneBlock/LearnedSkipKinds.lean`): the
skips `Fin 1 → Matrix d d ℝ` carry the Borel σ-algebra of their norm topology. -/
private theorem borelSpace_skips_lzr : BorelSpace (Fin 1 → Matrix d d ℝ) :=
  inferInstanceAs (BorelSpace (Fin 1 → d → d → ℝ))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper (copy of the private `ae_fst_lsk` of `OneBlock/LearnedSkipKinds.lean`): a condition on
the weights that holds at almost every `θ` holds at almost every `(θ, v)`: the preimage of a null
set under the onto linear map `(θ, v) ↦ θ` is a null set. -/
private theorem ae_fst_lzr {A : Arch T d 1} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] (hB : BorelSpace V)
    (μ : Measure (Params A dIn dOut × V)) (hμ : μ.IsAddHaarMeasure) {Q : Params A dIn dOut → Prop}
    (h : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), Q θ) :
    ∀ᵐ p ∂μ, Q p.1 := by
  -- a measurable null set `N` outside which `Q` holds
  rw [ae_iff] at h
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null h
  have hc : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), θ ∈ Nᶜ :=
    measure_eq_zero_iff_ae_notMem.1 hN0
  have h1 := (ae_comp_linearMap_mem_iff (LinearMap.fst ℝ (Params A dIn dOut) V) μ
    Measure.addHaar (LinearMap.fst_surjective) hN.compl).2 hc
  refine h1.mono fun p hp => ?_
  by_contra hq
  exact hp (hsub hq)

/-- Helper (copy of the private `ae_isUnit_det_lsa` of `OneBlock/LearnedSkipAttention.lean`): if
a square matrix that depends linearly on a point of `E` is the identity at one point, it is
invertible at almost every point. -/
private theorem ae_isUnit_det_lzr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] (hB : BorelSpace E) (μ : Measure E)
    (hμ : μ.IsAddHaarMeasure) (Φ : E →ₗ[ℝ] Matrix d d ℝ) (x₀ : E) (h₀ : Φ x₀ = 1) :
    ∀ᵐ x ∂μ, IsUnit (Φ x).det := by
  -- the entries are linear, so the determinant is analytic
  have hentry : ∀ i j, AnalyticOnNhd ℝ (fun x => Φ x i j) Set.univ := fun i j =>
    (LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℝ ℝ i j) ∘ₗ Φ)).analyticOnNhd _
  have hφ : AnalyticOnNhd ℝ (fun x => (Φ x).det) Set.univ := by
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (σ i) i)
  -- it is `1` at `x₀`, so its zero set is null
  have hnull := measure_zeroSet_of_analytic μ hφ ⟨x₀, by rw [h₀, Matrix.det_one]; exact one_ne_zero⟩
  rw [ae_iff]
  simpa only [isUnit_iff_ne_zero, not_not] using hnull

/-- Helper (copy of the private `half_add_half_lsk`): `d (d + 1)/2 + d (d − 1)/2 = d²` (both
products are even). -/
private theorem half_add_half_lzr (n : ℕ) : n * (n + 1) / 2 + n * (n - 1) / 2 = n ^ 2 := by
  have h1 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  have h3 : n * (n + 1) + n * (n - 1) = 2 * n ^ 2 := by
    cases n with
    | zero => rfl
    | succ m => rw [Nat.add_sub_cancel]; ring
  generalize n * (n + 1) = y at h1 h3 ⊢
  generalize n * (n - 1) = x at h2 h3 ⊢
  generalize n ^ 2 = q at h3 ⊢
  omega

omit [Nonempty T] in
/-- Helper (the common part of the three corollaries): if at almost every `θ` a condition `Q`
holds that gives a space of dimension `s` of directions of symmetries inside the block, and the
residual network has `fd + (d(d−1)/2 + 1 + s) = P`, then at almost every `(θ, A)` the functional
dimension with the learned skip `A` is at most that of the residual network plus
`d(d+1)/2 − 1`: `E` has rank `d` and `A` is invertible there, so the bound for the learned skip
applies. -/
private theorem ae_le_residual_add_lzr {A : Arch T d 1}
    (μ : Measure (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))) [hμ : μ.IsAddHaarMeasure]
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    {s : ℕ} {Q : Params A dIn dOut → Prop}
    (hQ : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), Q θ)
    (hV : ∀ θ, Q θ → ∃ V : Submodule ℝ (Params A dIn dOut),
      V ≤ Submodule.span ℝ {η | InsideBlocks A θ η} ∧ Module.finrank ℝ V = s)
    (hres : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)),
      funDim A 1 θ + (Fintype.card d * (Fintype.card d - 1) / 2 + 1 + s)
        = Module.finrank ℝ (Params A dIn dOut)) :
    ∀ᵐ p ∂μ, funDimLearned A p
      ≤ funDim A 1 p.1 + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := borelSpace_skips_lzr
  have hBp : BorelSpace (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) := Prod.borelSpace
  -- at almost every `(θ, A)`: `E` of rank `d`, `Q θ`, and the value of the residual network
  have hθ := ae_fst_lzr hBs μ hμ
    (((ae_rank_E_ubt (A := A) Measure.addHaar hdIn).and hQ).and hres)
  -- at almost every `(θ, A)`, moreover the skip `A_0` is invertible
  have hdet : ∀ᵐ p ∂μ, IsUnit (p.2 0).det :=
    ae_isUnit_det_lzr hBp μ hμ
      ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix d d ℝ) 0)
        ∘ₗ (LinearMap.snd ℝ _ (Fin 1 → Matrix d d ℝ))) (0, fun _ => 1) rfl
  filter_upwards [hθ, hdet] with p hp hR
  obtain ⟨⟨hE, hq⟩, hr⟩ := hp
  -- the bound for the learned skip with `U = V`
  obtain ⟨V, hVle, hVdim⟩ := hV p.1 hq
  have h := funDimLearned_add_le_rmsNorm_zero' hA p hE hR V hVle
  rw [hVdim] at h
  -- `d(d−1)` is even, and `d(d+1)/2 + d(d−1)/2 = d²`
  have e1 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  have e2 := half_add_half_lzr (Fintype.card d)
  generalize Fintype.card d * (Fintype.card d + 1) = y at e2 ⊢
  generalize Fintype.card d * (Fintype.card d - 1) = x at h hr e1 e2
  generalize Fintype.card d ^ 2 = q at h e2
  omega

variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one ReLU block:** for `d_in,
d_out ≥ d ≥ 2` and a block with at least one hidden unit, at almost every weights and full learned
skip `(θ, A)` the functional dimension exceeds that of the residual network with the weights `θ` by
at most `d(d+1)/2 − 1`. -/
theorem ae_funDimLearned_le_residual_add_relu_oneBlock_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp relu (rmsNorm 0) hid) p
      ≤ funDim (Arch.mlp relu (rmsNorm 0) hid) 1 p.1
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- where no read column vanishes, the rescalings of the hidden units span `s = card (hid 0)`
  -- dimensions of directions of symmetries inside the block
  refine ae_le_residual_add_lzr μ rfl hd hdIn (s := Fintype.card (hid 0))
    (ae_read_col_ne_zero (σ := relu) (χ := rmsNorm 0) (hid := hid) (T := T) (d := d)
      (dIn := dIn) (dOut := dOut) Measure.addHaar) (fun θ hθ => ?_)
    (ae_funDim_relu_oneBlock_residual_rmsNorm_zero Measure.addHaar hd hdIn hdOut)
  obtain ⟨V, hVle, -, hVdim⟩ := mlp_part_ubr relu_homogeneous θ hθ
  exact ⟨V, hVle, by rw [hVdim, Fin.sum_univ_one]⟩

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one ReLU² block:** for
`d_in, d_out ≥ d ≥ 2` and a block with at least one hidden unit, at almost every weights and full
learned skip `(θ, A)` the functional dimension exceeds that of the residual network with the
weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimLearned_le_residual_add_reluSq_oneBlock_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp reluSq (rmsNorm 0) hid) p
      ≤ funDim (Arch.mlp reluSq (rmsNorm 0) hid) 1 p.1
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- where no read column vanishes, the rescalings of the hidden units span `s = card (hid 0)`
  -- dimensions of directions of symmetries inside the block
  refine ae_le_residual_add_lzr μ rfl hd hdIn (s := Fintype.card (hid 0))
    (ae_read_col_ne_zero (σ := reluSq) (χ := rmsNorm 0) (hid := hid) (T := T) (d := d)
      (dIn := dIn) (dOut := dOut) Measure.addHaar) (fun θ hθ => ?_)
    (ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero Measure.addHaar hd hdIn hdOut)
  obtain ⟨V, hVle, -, hVdim⟩ := mlp_part_ubr reluSq_homogeneous θ hθ
  exact ⟨V, hVle, by rw [hVdim, Fin.sum_univ_one]⟩

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one ReGLU block:** for
`d_in, d_out ≥ d ≥ 2` and a block with at least one hidden unit, at almost every weights and full
learned skip `(θ, A)` the functional dimension exceeds that of the residual network with the
weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimLearned_le_residual_add_reglu_oneBlock_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.gated relu (rmsNorm 0) hid) p
      ≤ funDim (Arch.gated relu (rmsNorm 0) hid) 1 p.1
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- where no value column and no gate column of the read vanishes, the rescalings of the values
  -- and of the gates span `s = 2 card (hid 0)` dimensions of directions of symmetries inside the
  -- block
  refine ae_le_residual_add_lzr μ rfl hd hdIn (s := 2 * Fintype.card (hid 0))
    ((ae_value_ne_zero (σ := relu) (χ := rmsNorm 0) (hid := hid) (T := T) (d := d)
      (dIn := dIn) (dOut := dOut) Measure.addHaar).and
      (ae_gate_ne_zero (σ := relu) (χ := rmsNorm 0) (hid := hid) (T := T) (d := d)
        (dIn := dIn) (dOut := dOut) Measure.addHaar)) (fun θ hθ => ?_)
    (ae_funDim_reglu_oneBlock_residual_rmsNorm_zero Measure.addHaar hd hdIn hdOut)
  obtain ⟨V, hVle, -, hVdim⟩ := gate_part_ubr relu_homogeneous θ hθ.1 hθ.2
  exact ⟨V, hVle, by rw [hVdim, Fin.sum_univ_one]⟩

end Skips
