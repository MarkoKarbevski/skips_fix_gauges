import SkipsLean.OneBlock.LearnedSkipTriangularRMSZeroBound
import SkipsLean.OneBlock.LearnedSkipTriangularRescale

/-!
# An upper triangular learned skip against a full one, on a batch: the same rank

Paper (skips paper), proof of Theorem B.1 (iii): "For an upper triangular `A`, view the network
as the network with a full `A` restricted to triangular skips: its flat directions are those of
the full network whose entry `η_A` is upper triangular." And Step 5: "For an upper triangular
`A`, `A Y − X_a A` must be upper triangular, which determines `Y` from `X_a` […]. So `K(θ)` is
larger than for the residual network by `d_model (d_model − 1)/2`, respectively `0`, while the
network has `d_model²`, respectively `d_model (d_model + 1)/2`, more parameters. In both cases
the functional dimension is larger by `d_model (d_model + 1)/2`."

In Lean the comparison of the two families is made on a batch of inputs, as in
`OneBlock/LearnedSkipTriangularRescale.lean` for `ε > 0` (the private
`jacobianRankSkips_tri_eq_ltr`): at an invertible upper triangular skip `R`, the Jacobian of the
family of upper triangular skips on a batch is the Jacobian `J` of the family of all skips
composed with the inclusion, and every direction of the skip is a triangular one plus `−X_0 R`
with `X_0` antisymmetric, the direction of the rotation of `h_0` by `X_0`, which is flat for every
`ε` and which `J` kills. So the two Jacobians have the same range. Here this is stated

* for every real `ε`, on a batch at whose inputs the output with a full skip is a differentiable
  function of the weights and the skip;
* for `ε = 0`, on a batch of inputs at which no normalized row vanishes (`learnedZeroDomain`) and
  the fixed map of the block is differentiable at the normalized read.

With it the values for the full skip at `ε = 0` carry over to the upper triangular skip:
`P + d² − (d(d−1) + 2) − s = P + d(d+1)/2 − (d(d−1)/2 + 2) − s`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [LinearOrder d] [Fintype dIn] [Fintype dOut]

/-! ### Helpers: the output is differentiable in the weights and the skip at an input of
`learnedZeroDomain` (copies of the private helpers of
`OneBlock/LearnedSkipTriangularRMSZeroBound.lean`) -/

/-- Helper (a copy of the private `differentiableAt_matMul_lzt`): the product of two matrix-valued
maps that are differentiable at a point is differentiable there. -/
private theorem differentiableAt_matMul_ltk {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : P → Matrix m n ℝ} {g : P → Matrix n p ℝ} {y : P}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    DifferentiableAt ℝ (fun y => f y * g y) y := by
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.differentiableAt.comp y hf).clm_apply hg

omit [Fintype T] [Nonempty T] [DecidableEq d] [LinearOrder d] [Fintype dOut] in
/-- Helper (a copy of the private `eval_eq_lzt`): the function of one block under
pre-RMSNorm with the skip `S 0`, `F(x) = N_0(x E S + f(N_0(x E) W_read) W_write) D`. -/
private theorem eval_eq_ltk {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (S : Fin 1 → Matrix d d ℝ) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    eval A S θ x = rmsNorm 0 (x * θ.E * S 0
      + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) * θ.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]

omit [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper (a copy of the private `differentiableAt_evalSkips_lzt`): at an input `x`
at which no normalized row vanishes and `f` is differentiable at `N_0(x E) W_read`, the output with
the full learned skip is a differentiable function of `(θ, R)`. -/
private theorem differentiableAt_evalSkips_ltk {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ)
    (x : Matrix T dIn ℝ) (hx : x ∈ learnedZeroDomain A θ R)
    (hfx : DifferentiableAt ℝ (A.f 0) (rmsNorm 0 (x * θ.E) * θ.read 0)) :
    DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x) (θ, R) := by
  have e : (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x)
      = fun p => rmsNorm 0 (x * p.1.E * p.2 0
          + A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0) * p.1.write 0) * p.1.D :=
    funext fun p => eval_eq_ltk hA p.2 p.1 x
  rw [e]
  -- the weights and the skip are linear, hence differentiable, functions of `(θ, R)`
  have hE : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.E) (θ, R) :=
    ((LinearMap.toContinuousLinearMap (Params.linE (A := A) (dIn := dIn) (dOut := dOut))).comp
      (ContinuousLinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))).differentiableAt
  have hR : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.read 0) (θ, R) :=
    ((LinearMap.toContinuousLinearMap
      (Params.linRead (A := A) (dIn := dIn) (dOut := dOut) 0)).comp
      (ContinuousLinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))).differentiableAt
  have hW : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.write 0) (θ, R) :=
    ((LinearMap.toContinuousLinearMap
      (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) 0)).comp
      (ContinuousLinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))).differentiableAt
  have hD : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.D) (θ, R) :=
    ((LinearMap.toContinuousLinearMap (Params.linD (A := A) (dIn := dIn) (dOut := dOut))).comp
      (ContinuousLinearMap.fst ℝ _ (Fin 1 → Matrix d d ℝ))).differentiableAt
  have hS : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.2 0) (θ, R) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix d d ℝ) 0).comp
      (ContinuousLinearMap.snd ℝ (Params A dIn dOut) _)).differentiableAt
  -- `x E`, `N_0(x E)` (no row of `x E` is zero), `N_0(x E) W_read`, `f(…)`
  have h1 : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => x * p.1.E) (θ, R) :=
    differentiableAt_matMul_ltk (differentiableAt_const x) hE
  have h2 : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => rmsNorm 0 (x * p.1.E)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E) (θ, R) (analyticAt_rmsNorm_zero (x * θ.E) hx.1).differentiableAt h1
  have h3 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm 0 (x * p.1.E) * p.1.read 0) (θ, R) :=
    differentiableAt_matMul_ltk h2 hR
  have h4 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm 0 (x * p.1.E) * p.1.read 0) (θ, R) hfx h3
  -- `h_1 = x E S + f(…) W_write`, `N_0(h_1)` (no row of `h_1` is zero) and `N_0(h_1) D`
  have h5 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E * p.2 0 + A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0) * p.1.write 0) (θ, R) :=
    (differentiableAt_matMul_ltk h1 hS).add (differentiableAt_matMul_ltk h4 hW)
  have h6 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm 0 (x * p.1.E * p.2 0
        + A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0) * p.1.write 0)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E * p.2 0 + A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0) * p.1.write 0) (θ, R)
      (analyticAt_rmsNorm_zero _ hx.2).differentiableAt h5
  exact differentiableAt_matMul_ltk h6 hD

/-! ### Helpers: the rotations are flat, and every direction of the skip is an upper triangular one
plus a flat one (copies of the private helpers of `OneBlock/LearnedSkipTriangularRescale.lean`) -/

omit [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper (a copy of the private `mem_flatSkips_of_hasDerivAt_lst`): if a curve `γ` through `p`
with velocity `v` keeps the function near `τ = 0`, then `v` is flat. -/
private theorem mem_flatSkips_of_hasDerivAt_ltk {L : ℕ} {A : Arch T d L}
    (p : Params A dIn dOut × (Fin L → Matrix d d ℝ))
    (γ : ℝ → Params A dIn dOut × (Fin L → Matrix d d ℝ))
    (v : Params A dIn dOut × (Fin L → Matrix d d ℝ)) (hγ : HasDerivAt γ v 0) (hγ0 : γ 0 = p)
    (hconst : ∀ᶠ τ in nhds (0 : ℝ), ∀ x : Matrix T dIn ℝ,
      evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (γ τ) x
        = evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p x) :
    v ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p := by
  unfold flatSkips
  refine (Submodule.mem_iInf _).2 fun x => ?_
  rw [LinearMap.mem_ker]
  show fderiv ℝ (fun p' => evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p' x)
    p v = 0
  by_cases hx : DifferentiableAt ℝ (fun p' : Params A dIn dOut × (Fin L → Matrix d d ℝ) =>
    evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p' x) p
  · -- the chain rule: `τ ↦ F_{γ(τ)}(x)` has derivative `D_p F(x) v` at `0`
    have hl : HasFDerivAt (fun p' =>
        evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p' x)
        (fderiv ℝ (fun p' =>
          evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p' x) p) (γ 0) := by
      rw [hγ0]
      exact hx.hasFDerivAt
    have h1 := hl.comp_hasDerivAt (0 : ℝ) hγ
    -- the same map is constant near `0`, so its derivative there is `0`
    have h2 : HasDerivAt ((fun p' =>
        evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p' x) ∘ γ) 0 0 :=
      (hasDerivAt_const (0 : ℝ)
        (evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p x)).congr_of_eventuallyEq
        (hconst.mono fun τ hτ => hτ x)
    exact h1.unique h2
  · -- not differentiable at `p`: Mathlib's derivative is `0`
    rw [fderiv_zero_of_not_differentiableAt hx, _root_.zero_apply]

-- As in Mathlib's `MatrixExponential.lean`: without this option the instances of the operator
-- norm (e.g. `CompleteSpace`) are not found.
omit [LinearOrder d] in
set_option backward.isDefEq.respectTransparency false in
/-- Helper (a copy of the private `hasDerivAt_exp_smul_apply_lst`): the derivative at `τ = 0` of an
entry of `exp (τ Y)` is the entry of `Y` (computed with the operator norm). -/
private theorem hasDerivAt_exp_smul_apply_ltk (Y : Matrix d d ℝ) (i j : d) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) i j) (Y i j) 0 := by
  let _ : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℝ ℝ i j)).hasFDerivAt.comp_hasDerivAt 0 h

omit [LinearOrder d] in
/-- Helper (a copy of the private `hasDerivAt_matrix_lst`): with the elementwise norm, the
derivative of a matrix-valued function is taken entry by entry. -/
private theorem hasDerivAt_matrix_ltk {m n : Type*} [Fintype m] [Fintype n] {f : ℝ → Matrix m n ℝ}
    {f' : Matrix m n ℝ} {x : ℝ} (h : ∀ i j, HasDerivAt (fun τ => f τ i j) (f' i j) x) :
    HasDerivAt f f' x :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 (h i)

omit [LinearOrder d] in
/-- Helper (a copy of the private `hasDerivAt_mul_exp_lst`): the derivative of
`τ ↦ M exp (τ Y)` at `0` is `M Y`. -/
private theorem hasDerivAt_mul_exp_ltk {m : Type*} [Fintype m] (M : Matrix m d ℝ)
    (Y : Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => M * NormedSpace.exp (τ • Y)) (M * Y) 0 :=
  hasDerivAt_matrix_ltk fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_apply_ltk Y k j).const_mul (M i k)

omit [LinearOrder d] in
/-- Helper (a copy of the private `hasDerivAt_exp_mul_lst`): the derivative of
`τ ↦ exp (τ Y) M` at `0` is `Y M`. -/
private theorem hasDerivAt_exp_mul_ltk {n : Type*} [Fintype n] (Y : Matrix d d ℝ)
    (M : Matrix d n ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) * M) (Y * M) 0 :=
  hasDerivAt_matrix_ltk fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_apply_ltk Y i k).mul_const (M k j)

-- See `hasDerivAt_exp_smul_apply_ltk` for this option.
omit [LinearOrder d] in
set_option backward.isDefEq.respectTransparency false in
/-- Helper (a copy of the private `hasDerivAt_exp_mul_exp_lst`): the derivative of
`τ ↦ exp (-τ Y) S exp (τ Z)` at `0` is `−Y S + S Z`. -/
private theorem hasDerivAt_exp_mul_exp_ltk (Y Z S : Matrix d d ℝ) :
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

omit [LinearOrder d] in
/-- Helper (a copy of the private `exp_smul_mul_exp_smul_neg_lst`): `exp (τ Y) exp (-τ Y) = 1`. -/
private theorem exp_smul_mul_exp_smul_neg_ltk (Y : Matrix d d ℝ) (τ : ℝ) :
    NormedSpace.exp (τ • Y) * NormedSpace.exp (τ • -Y) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).neg_right.smul_left τ).smul_right τ),
    smul_neg, add_neg_cancel, NormedSpace.exp_zero]

omit [LinearOrder d] in
/-- Helper (a copy of the private `expGL_lst`): the invertible matrix `exp (τ Y)`, with inverse
`exp (-τ Y)`. -/
private noncomputable def expGL_ltk (Y : Matrix d d ℝ) (τ : ℝ) : GL d ℝ :=
  ⟨NormedSpace.exp (τ • Y), NormedSpace.exp (τ • -Y), exp_smul_mul_exp_smul_neg_ltk Y τ,
    by simpa only [neg_neg] using exp_smul_mul_exp_smul_neg_ltk (-Y) τ⟩

omit [LinearOrder d] in
/-- Helper (a copy of the private `expGL_zero_lst`): `exp (0 Y) = 1`. -/
private theorem expGL_zero_ltk (Y : Matrix d d ℝ) : expGL_ltk Y 0 = 1 := by
  apply Units.ext
  change NormedSpace.exp ((0 : ℝ) • Y) = 1
  rw [zero_smul, NormedSpace.exp_zero]

omit [LinearOrder d] in
/-- Helper (a copy of the private `expGL_mem_orthogonalGroup_lst`): for antisymmetric `Y`,
`exp (τ Y)` is orthogonal. -/
private theorem expGL_mem_orthogonalGroup_ltk {Y : Matrix d d ℝ} (hY : Yᵀ = -Y) (τ : ℝ) :
    (expGL_ltk Y τ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  change (NormedSpace.exp (τ • Y))ᵀ * NormedSpace.exp (τ • Y) = 1
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, hY]
  simpa only [neg_neg] using exp_smul_mul_exp_smul_neg_ltk (-Y) τ

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] [LinearOrder d] in
/-- Helper (a copy of the private `cob_expGL_zero_lst`): the curve
`τ ↦ θ.cob (exp (τ X_ℓ)) (exp (τ X_ℓ))` passes through `θ` at `τ = 0`. -/
private theorem cob_expGL_zero_ltk {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut)
    (X : Fin (L + 1) → Matrix d d ℝ) :
    θ.cob (fun ℓ => expGL_ltk (X ℓ) 0) (fun ℓ => expGL_ltk (X ℓ) 0) = θ := by
  simp only [expGL_zero_ltk]
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [Params.cob, inv_one, Units.val_one, Matrix.mul_one, Matrix.one_mul]

omit [Fintype T] [Nonempty T] [LinearOrder d] in
/-- Helper (a copy of the private `hasDerivAt_cob_expGL_lst`): the curve
`τ ↦ θ.cob (exp (τ X_ℓ)) (exp (τ X_ℓ))` has velocity `cobDir θ X` at `τ = 0`. -/
private theorem hasDerivAt_cob_expGL_ltk {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut)
    (X : Fin (L + 1) → Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => θ.cob (fun ℓ => expGL_ltk (X ℓ) τ) (fun ℓ => expGL_ltk (X ℓ) τ))
      (cobDir θ X) 0 := by
  -- The norm of the parameters is that of the tuple of their components.
  let e : Params A dIn dOut ≃L[ℝ] Params.Prod A dIn dOut :=
    Params.linearEquivProd.toContinuousLinearEquiv
  -- Componentwise: `E exp (τ X_0)`, `exp (-τ X_{ℓ-1}) W_read^ℓ`, `W_write^ℓ exp (τ X_ℓ)`,
  -- `exp (-τ X_L) D`.
  have key : HasDerivAt
      (fun τ : ℝ => e (θ.cob (fun ℓ => expGL_ltk (X ℓ) τ) (fun ℓ => expGL_ltk (X ℓ) τ)))
      (e (cobDir θ X)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · exact hasDerivAt_mul_exp_ltk θ.E (X 0)
    · exact hasDerivAt_pi.2 fun ℓ =>
        (hasDerivAt_exp_mul_ltk (-X ℓ.castSucc) (θ.read ℓ)).congr_deriv (Matrix.neg_mul _ _)
    · exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_mul_exp_ltk (θ.write ℓ) (X ℓ.succ)
    · exact (hasDerivAt_exp_mul_ltk (-X (Fin.last L)) θ.D).congr_deriv (Matrix.neg_mul _ _)
  -- Back to the parameters through `e⁻¹`.
  exact e.symm.hasFDerivAt.comp_hasDerivAt (0 : ℝ) key

omit [Nonempty T] [LinearOrder d] in
/-- Helper (a copy of the private `rot_mem_flatSkips_lst`; the rotations are flat with no
hypothesis on the blocks): for antisymmetric `X_ℓ`, the direction
`(cobDir θ X, −X_{ℓ-1} S_ℓ + S_ℓ X_ℓ)` of the orthogonal changes of basis `exp (τ X_ℓ)` is flat. -/
private theorem rot_mem_flatSkips_ltk {L : ℕ} {ε : ℝ} {A : Arch T d L}
    (hA : A.χ = rmsNorm ε)
    (θ : Params A dIn dOut) (S : Fin L → Matrix d d ℝ) (X : Fin (L + 1) → Matrix d d ℝ)
    (hX : ∀ ℓ, (X ℓ)ᵀ = -X ℓ) :
    (cobDir θ X, fun ℓ => -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ)
      ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S) := by
  -- the curve `τ ↦ (θ.cob G_τ G_τ, cobSkip S G_τ)` with `G_τ ℓ = exp (τ X_ℓ)` and its velocity
  have hγ : HasDerivAt (fun τ : ℝ => (θ.cob (fun ℓ => expGL_ltk (X ℓ) τ)
      (fun ℓ => expGL_ltk (X ℓ) τ), cobSkip S (fun ℓ => expGL_ltk (X ℓ) τ)))
      (cobDir θ X, fun ℓ => -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ) 0 :=
    (hasDerivAt_cob_expGL_ltk θ X).prodMk
      (hasDerivAt_pi.2 fun ℓ => hasDerivAt_exp_mul_exp_ltk (X ℓ.castSucc) (X ℓ.succ) (S ℓ))
  refine mem_flatSkips_of_hasDerivAt_ltk _ _ _ hγ ?_ ?_
  · -- at `τ = 0` the curve is at `(θ, S)`
    refine Prod.ext (cob_expGL_zero_ltk θ X) ?_
    show cobSkip S (fun ℓ => expGL_ltk (X ℓ) 0) = S
    funext ℓ
    simp only [cobSkip, expGL_zero_ltk, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  · -- along the curve the function is kept: pre-RMSNorm commutes with the orthogonal `G_τ ℓ`
    refine Filter.Eventually.of_forall fun τ x => ?_
    have hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (expGL_ltk (X ℓ) τ : Matrix d d ℝ))
        = A.χ h * (expGL_ltk (X ℓ) τ : Matrix d d ℝ) := by
      intro ℓ h
      rw [hA]
      exact rmsNorm_mul_orthogonal ε (expGL_mem_orthogonalGroup_ltk (hX ℓ) τ) h
    exact eval_cob (M := S) (θ := θ) (G := fun ℓ => expGL_ltk (X ℓ) τ)
      (K := fun ℓ => expGL_ltk (X ℓ) τ) (x := x) hχ

omit [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper (as the private `fderiv_batch_flat_lst`, with the differentiability only at the inputs
of the batch): a flat direction is in the kernel of the Jacobian on a batch of inputs at which the
output is differentiable. -/
private theorem fderiv_batch_flat_ltk {L : ℕ} {A : Arch T d L}
    (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hdiff : ∀ i, DifferentiableAt ℝ (fun p' : Params A dIn dOut × (Fin L → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p' (X i)) p)
    {w : Params A dIn dOut × (Fin L → Matrix d d ℝ)}
    (hw : w ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p) :
    fderiv ℝ (fun p' : Params A dIn dOut × (Fin L → Matrix d d ℝ) => fun i : Fin n =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p' (X i)) p w = 0 := by
  -- the derivative of the outputs on the batch is the tuple of the derivatives of the outputs
  have h : fderiv ℝ (fun p' : Params A dIn dOut × (Fin L → Matrix d d ℝ) => fun i : Fin n =>
        evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p' (X i)) p =
      ContinuousLinearMap.pi fun i => fderiv ℝ (fun p' =>
        evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p' (X i)) p :=
    fderiv_pi hdiff
  rw [h]
  funext i
  unfold flatSkips at hw
  exact LinearMap.mem_ker.1 (Submodule.mem_iInf _ |>.1 hw (X i))

/-! ### Helpers: every direction of the skip is an upper triangular one plus `X_0 R` -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [LinearOrder d] [Fintype dIn]
  [Fintype dOut] in
/-- Helper (a copy of the private `half_add_half_lst`): `d (d + 1)/2 + d (d − 1)/2 = d²` (both
products are even). -/
private theorem half_add_half_ltk (n : ℕ) : n * (n + 1) / 2 + n * (n - 1) / 2 = n ^ 2 := by
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

/-- Helper (as in the private `lowerLin_injective_lst`): for `R` invertible and upper triangular,
an antisymmetric `X` with `X R` upper triangular is `0`: `X = (X R) R⁻¹` is upper triangular, and
an antisymmetric upper triangular matrix vanishes. -/
private theorem eq_zero_of_mul_blockTriangular_ltk {R X : Matrix d d ℝ}
    (hRt : R.BlockTriangular id) (hR : IsUnit R.det) (hX : Xᵀ = -X)
    (hXR : (X * R).BlockTriangular id) : X = 0 := by
  -- `X = (X R) R⁻¹` is upper triangular: the inverse of an upper triangular matrix is
  have : Invertible R := R.invertibleOfIsUnitDet hR
  have h2 : X.BlockTriangular id := by
    have h := hXR.mul (Matrix.blockTriangular_inv_of_blockTriangular hRt)
    rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hR, Matrix.mul_one] at h
  -- an antisymmetric upper triangular matrix is `0`
  have hX' : ∀ i j, X j i = -X i j := fun i j => by
    have h := congrFun (congrFun hX i) j
    rwa [transpose_apply, Matrix.neg_apply] at h
  ext i j
  show X i j = 0
  rcases lt_trichotomy i j with h | rfl | h
  · rw [hX' j i, h2 h, neg_zero]
  · have := hX' i i
    linarith
  · exact h2 h

omit [LinearOrder d] in
/-- Helper: the linear map `(X, U) ↦ U − X R` on pairs of an antisymmetric and an upper triangular
matrix. -/
private def decompLin_ltk (R : Matrix d d ℝ) :
    antisymmetric d × upperTriangular d →ₗ[ℝ] Matrix d d ℝ where
  toFun p := (p.2 : Matrix d d ℝ) - (p.1 : Matrix d d ℝ) * R
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.add_mul]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Matrix.smul_mul, smul_sub,
      RingHom.id_apply]

/-- Helper: for `R` invertible and upper triangular, `(X, U) ↦ U − X R` is onto: it is injective
(`U = X R` makes `X R` upper triangular, so `X = 0` and `U = 0`), between spaces of the same
dimension `d (d − 1)/2 + d (d + 1)/2 = d²`. -/
private theorem decompLin_surjective_ltk {R : Matrix d d ℝ} (hRt : R.BlockTriangular id)
    (hR : IsUnit R.det) : Function.Surjective (decompLin_ltk R) := by
  have hinj : Function.Injective (decompLin_ltk R) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨X, U⟩ h
    have h' : (U : Matrix d d ℝ) - (X : Matrix d d ℝ) * R = 0 := LinearMap.mem_ker.1 h
    have hU : (U : Matrix d d ℝ) = (X : Matrix d d ℝ) * R := sub_eq_zero.1 h'
    have hXR : ((X : Matrix d d ℝ) * R).BlockTriangular id := by
      rw [← hU]
      exact U.2
    have hX0 : (X : Matrix d d ℝ) = 0 := eq_zero_of_mul_blockTriangular_ltk hRt hR X.2 hXR
    have hU0 : (U : Matrix d d ℝ) = 0 := by rw [hU, hX0, Matrix.zero_mul]
    exact Prod.ext (Subtype.ext hX0) (Subtype.ext hU0)
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj
  rw [Module.finrank_prod, finrank_antisymmetric, finrank_upperTriangular, Module.finrank_matrix,
    Module.finrank_self, mul_one, add_comm, half_add_half_ltk, sq]

/-- Helper (the form of the private `exists_add_mul_mem_upperTriangular_lst`): for `R` invertible
and upper triangular, every `a` is upper triangular after adding `X R` for some antisymmetric
`X`. -/
private theorem exists_add_mul_mem_ltk {R : Matrix d d ℝ} (hRt : R.BlockTriangular id)
    (hR : IsUnit R.det) (a : Matrix d d ℝ) :
    ∃ X : antisymmetric d, a + (X : Matrix d d ℝ) * R ∈ upperTriangular d := by
  obtain ⟨⟨X, U⟩, h⟩ := decompLin_surjective_ltk hRt hR a
  refine ⟨X, ?_⟩
  have h' : (U : Matrix d d ℝ) - (X : Matrix d d ℝ) * R = a := h
  rw [← h', sub_add_cancel]
  exact U.2

omit [Nonempty T] in
/-- Helper (a copy of the private `exists_sub_mem_flatSkips_lst`): at an invertible upper
triangular skip `R`, every direction `w` of the family of all skips is a direction `(η', a')` with
an upper triangular `a'` plus a flat direction: the rotation of `h_0` by an antisymmetric `X_0`
moves the skip by `−X_0 R`. -/
private theorem exists_sub_mem_flatSkips_ltk {ε : ℝ} {A : Arch T d 1}
    (hA : A.χ = rmsNorm ε)
    (θ : Params A dIn dOut) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) (w : Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) :
    ∃ u : Params A dIn dOut × (Fin 1 → upperTriangular d),
      w - (u.1, triSkips d 1 u.2) ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ))
        (θ, fun ℓ => (R ℓ : Matrix d d ℝ)) := by
  -- `X_0` antisymmetric with `a_0 + X_0 R_0` upper triangular
  obtain ⟨X₀, hX₀⟩ := exists_add_mul_mem_ltk (R 0).2 hR (w.2 0)
  -- the rotation of `h_0` by `X_0`, and none of `h_1`: a flat direction
  let X : Fin (1 + 1) → Matrix d d ℝ := Fin.cons (X₀ : Matrix d d ℝ) fun _ => 0
  have hX : ∀ ℓ, (X ℓ)ᵀ = -X ℓ := by
    intro ℓ
    refine Fin.cases ?_ (fun i => ?_) ℓ
    · exact X₀.2
    · simp only [X, Fin.cons_succ, transpose_zero, neg_zero]
  have hrot := rot_mem_flatSkips_ltk hA θ (fun ℓ => (R ℓ : Matrix d d ℝ)) X hX
  let u : Params A dIn dOut × (Fin 1 → upperTriangular d) :=
    (w.1 - cobDir θ X, fun _ => ⟨w.2 0 + (X₀ : Matrix d d ℝ) * R 0, hX₀⟩)
  refine ⟨u, ?_⟩
  -- `w` minus the triangular direction `u` is that flat direction
  have heq : w - (u.1, triSkips d 1 u.2)
      = (cobDir θ X, fun ℓ => -(X ℓ.castSucc * (R ℓ : Matrix d d ℝ))
          + (R ℓ : Matrix d d ℝ) * X ℓ.succ) := by
    refine Prod.ext ?_ (funext fun ℓ => ?_)
    · exact sub_sub_cancel _ _
    · obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
      show w.2 0 - (w.2 0 + (X₀ : Matrix d d ℝ) * R 0)
        = -(X (Fin.castSucc 0) * (R 0 : Matrix d d ℝ)) + (R 0 : Matrix d d ℝ) * X (Fin.succ 0)
      simp only [X, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Matrix.mul_zero, add_zero,
        sub_add_cancel_left]
  rw [heq]
  exact hrot

/-- **One block under pre-RMSNorm (every real `ε`), at an invertible upper triangular skip `R`,
on a batch:** if at every input of the batch the output with a full skip is a differentiable
function of the weights and the skip at `(θ, R)`, the Jacobian of the family of upper triangular
skips on the batch has the rank of the Jacobian of the family of all skips. -/
theorem jacobianRankSkips_tri_eq_of_differentiableAt {A : Arch T d 1} {ε : ℝ}
    (hA : A.χ = rmsNorm ε) (θ : Params A dIn dOut) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hdiff : ∀ i, DifferentiableAt ℝ
      (fun p' : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
        evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p' (X i))
      (θ, fun ℓ => (R ℓ : Matrix d d ℝ))) :
    jacobianRankSkips A (triSkips d 1) X (θ, R)
      = jacobianRankSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X
          (θ, fun ℓ => (R ℓ : Matrix d d ℝ)) := by
  -- the inclusion `m : (θ, v) ↦ (θ, v)` of the triangular family into the full one
  let m : Params A dIn dOut × (Fin 1 → upperTriangular d)
      →L[ℝ] Params A dIn dOut × (Fin 1 → Matrix d d ℝ) :=
    (ContinuousLinearMap.id ℝ (Params A dIn dOut)).prodMap (triSkips d 1)
  -- the outputs on the batch: `G` for all skips, `G ∘ m` for the triangular ones
  let G : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) → Fin n → Matrix T dOut ℝ :=
    fun p' i => evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p' (X i)
  -- `G` is differentiable at `m (θ, R)`, so the Jacobian of `G ∘ m` is `J ∘ m`
  have hG : DifferentiableAt ℝ G (m (θ, R)) := differentiableAt_pi.2 hdiff
  have hd : fderiv ℝ (G ∘ m) (θ, R) = (fderiv ℝ G (m (θ, R))).comp m :=
    (hG.hasFDerivAt.comp (θ, R) m.hasFDerivAt).fderiv
  show Module.finrank ℝ (LinearMap.range (fderiv ℝ (G ∘ m) (θ, R)).toLinearMap)
    = Module.finrank ℝ (LinearMap.range (fderiv ℝ G (m (θ, R))).toLinearMap)
  rw [hd]
  -- `range (J ∘ m) ⊆ range J`, and conversely
  refine le_antisymm (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _))
    (Submodule.finrank_mono ?_)
  -- every value `J w` is `J (m u)`, with `w − m u` flat
  rintro _ ⟨w, rfl⟩
  obtain ⟨u, hu⟩ := exists_sub_mem_flatSkips_ltk hA θ R hR w
  refine ⟨u, ?_⟩
  have h0 := fderiv_batch_flat_ltk _ X hdiff hu
  rw [map_sub] at h0
  exact (sub_eq_zero.1 h0).symm

/-- **One block under pre-RMSNorm with `ε = 0`, at an invertible upper triangular skip `R`, on a
batch of inputs at which no normalized row vanishes and the fixed map of the block is
differentiable at the normalized read:** the Jacobian of the family of upper triangular skips has
the rank of the Jacobian of the family of all skips. -/
theorem jacobianRankSkips_tri_eq_learned_rmsNorm_zero {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (θ : Params A dIn dOut) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i, X i ∈ learnedZeroDomain A θ fun ℓ => (R ℓ : Matrix d d ℝ))
    (hfx : ∀ i, DifferentiableAt ℝ (A.f 0) (rmsNorm 0 (X i * θ.E) * θ.read 0)) :
    jacobianRankSkips A (triSkips d 1) X (θ, R)
      = jacobianRankSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X
          (θ, fun ℓ => (R ℓ : Matrix d d ℝ)) := by
  -- at every input of the batch the output with a full skip is differentiable in `(θ, R)`
  exact jacobianRankSkips_tri_eq_of_differentiableAt hA θ R hR X fun i =>
    differentiableAt_evalSkips_ltk hA θ _ (X i) (hX i) (hfx i)

end Skips
