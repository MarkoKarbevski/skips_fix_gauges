import SkipsLean.OneBlock.LearnedSkipTriangular
import SkipsLean.OneBlock.LearnedSkipRescale
import SkipsLean.OneBlock.LearnedSkipReGLU

/-!
# One ReLU, ReLU² or ReGLU block with an upper triangular learned skip under pre-RMSNorm

Paper (skips paper): Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. For generic parameters and `ε > 0`, its functional
dimension exceeds that of the residual network of part (ii) by exactly `d_model (d_model + 1)/2`,
and it satisfies the equality condition." Its proof: "For an upper triangular `A`, view the network
as the network with a full `A` restricted to triangular skips: its flat directions are those of the
full network whose entry `η_A` is upper triangular." Appendix B, "Notation and flat directions":
"For the ReLU-type activations, `F(θ, x)` is differentiable in `θ` at the inputs `x` at which no
hidden unit sits at its kink, which form an open set of full measure, and 'every input' means every
such input."

For these blocks the statements are in the paper's own sense, on the inputs with no hidden unit at
its kink:

* `funDimSkipsOn A ι p U`: the largest rank of the Jacobian in the weights and the skips over the
  finite batches of inputs of the set `U` (for `U` the inputs off the kinks: the paper's functional
  dimension of a network with ReLU-type blocks);
* at one parameter, under the generic conditions of the residual statements and for an invertible
  upper triangular skip: a batch of inputs off the kinks on which the Jacobian of the triangular
  family has the rank `P + d (d + 1)/2 − d (d − 1)/2 − s`; no batch of such inputs has a larger
  rank; so `funDimSkipsOn` has this value (the equality condition: `P + d (d + 1)/2` parameters,
  symmetries of dimension `d (d − 1)/2 + s`), with `s = d_hidden` for ReLU and ReLU² and
  `s = 2 d_hidden` for ReGLU;
* for `d_in, d_out ≥ d ≥ 2`: the same at almost every `(θ, A)`, `A` upper triangular, and
  `d (d + 1)/2` more than the residual network at almost every `θ'`.

The route: on a batch of inputs off the kinks both families are differentiable, the Jacobian of the
triangular family is that of the full family restricted to triangular directions of the skip, and
every direction of the skip is a triangular one plus `−X_0 A` with `X_0` antisymmetric, whose
rotation direction is flat (as in `funDimLearnedTri_eq_funDimLearned`); so the two Jacobians have
the same range, and the values for the full skip (`OneBlock/LearnedSkipRescale.lean`,
`OneBlock/LearnedSkipReGLU.lean`) carry over. The value of Lean's `funDimLearnedTri`, which also
uses the inputs on the kinks at which the output happens to be differentiable, is not stated.
Numeric check: `learned_skip_relu_attention_check_2026-11-24.py`. Not stated: `ε = 0`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [LinearOrder d] [Fintype dIn] [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **The functional dimension on a set of inputs,** for the network whose skips are parameters: the
largest rank of the Jacobian in the weights and the skips over the finite batches of inputs of `U`.
For `U` the inputs with no hidden unit at its kink this is the paper's functional dimension of a
network with ReLU-type blocks. -/
noncomputable def funDimSkipsOn {L : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V)
    (U : Set (Matrix T dIn ℝ)) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
    r = jacobianRankSkips A ι X p}

/-! ### Helpers: the output is differentiable in the weights and the skip at an input at which the
block is differentiable (copies of the private helpers of `OneBlock/LearnedSkipGain.lean`) -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [LinearOrder d] [Fintype dIn]
  [Fintype dOut] in
/-- Helper (a copy of the private `differentiableAt_matMul_lsn`): the product of two matrix-valued
maps that are differentiable at a point is differentiable there. -/
private theorem differentiableAt_matMul_ltr {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : P → Matrix m n ℝ} {g : P → Matrix n p ℝ} {y : P}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    DifferentiableAt ℝ (fun y => f y * g y) y := by
  -- matrix multiplication as a bilinear map
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  -- the same map with continuous linear maps (all spaces are finite-dimensional)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.differentiableAt.comp y hf).clm_apply hg

omit [Fintype T] [Nonempty T] [DecidableEq d] [LinearOrder d] [Fintype dOut] in
/-- Helper (a copy of the private `eval_eq_lsn`): the function of one block under pre-RMSNorm with
the skip `S 0`, `F(x) = N_ε(x E S + f(N_ε(x E) W_read) W_write) D`. -/
private theorem eval_eq_ltr {A : Arch T d 1} (hA : A.χ = rmsNorm ε)
    (S : Fin 1 → Matrix d d ℝ) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    eval A S θ x = rmsNorm ε (x * θ.E * S 0
      + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * θ.write 0) * θ.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]

omit [Nonempty T] [LinearOrder d] in
/-- Helper (a copy of the private `differentiableAt_evalSkips_lsn`): at an input `x` at which `f`
is differentiable at `N_ε(x E) W_read`, the output with the full learned skip is a differentiable
function of `(θ, R)`. -/
private theorem differentiableAt_evalSkips_ltr {A : Arch T d 1} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ)
    (x : Matrix T dIn ℝ)
    (hfx : DifferentiableAt ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)) :
    DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x) (θ, R) := by
  have e : (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x)
      = fun p => rmsNorm ε (x * p.1.E * p.2 0
          + A.f 0 (rmsNorm ε (x * p.1.E) * p.1.read 0) * p.1.write 0) * p.1.D :=
    funext fun p => eval_eq_ltr hA p.2 p.1 x
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
  -- `x E`, `N_ε(x E)`, `N_ε(x E) W_read`, `f(…)`
  have h1 : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => x * p.1.E) (θ, R) :=
    differentiableAt_matMul_ltr (differentiableAt_const x) hE
  have h2 : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => rmsNorm ε (x * p.1.E)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E) (θ, R) (differentiable_rmsNorm hε _) h1
  have h3 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm ε (x * p.1.E) * p.1.read 0) (θ, R) :=
    differentiableAt_matMul_ltr h2 hR
  have h4 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      A.f 0 (rmsNorm ε (x * p.1.E) * p.1.read 0)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm ε (x * p.1.E) * p.1.read 0) (θ, R) hfx h3
  -- `h_1 = x E S + f(…) W_write`, `N_ε(h_1)` and `N_ε(h_1) D`
  have h5 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E * p.2 0 + A.f 0 (rmsNorm ε (x * p.1.E) * p.1.read 0) * p.1.write 0) (θ, R) :=
    (differentiableAt_matMul_ltr h1 hS).add (differentiableAt_matMul_ltr h4 hW)
  have h6 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm ε (x * p.1.E * p.2 0
        + A.f 0 (rmsNorm ε (x * p.1.E) * p.1.read 0) * p.1.write 0)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E * p.2 0 + A.f 0 (rmsNorm ε (x * p.1.E) * p.1.read 0) * p.1.write 0) (θ, R)
      (differentiable_rmsNorm hε _) h5
  exact differentiableAt_matMul_ltr h6 hD

/-! ### Helpers: the rotations are flat (copies of the private helpers of
`OneBlock/LearnedSkipTriangular.lean`) -/

section Rotations

variable {L : ℕ}

omit [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper (a copy of the private `mem_flatSkips_of_hasDerivAt_lst`): if a curve `γ` through `p`
with velocity `v` keeps the function near `τ = 0`, then `v` is flat. -/
private theorem mem_flatSkips_of_hasDerivAt_ltr {A : Arch T d L}
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
private theorem hasDerivAt_exp_smul_apply_ltr (Y : Matrix d d ℝ) (i j : d) :
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
private theorem hasDerivAt_matrix_ltr {m n : Type*} [Fintype m] [Fintype n] {f : ℝ → Matrix m n ℝ}
    {f' : Matrix m n ℝ} {x : ℝ} (h : ∀ i j, HasDerivAt (fun τ => f τ i j) (f' i j) x) :
    HasDerivAt f f' x :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 (h i)

omit [LinearOrder d] in
/-- Helper (a copy of the private `hasDerivAt_mul_exp_lst`): the derivative of
`τ ↦ M exp (τ Y)` at `0` is `M Y`. -/
private theorem hasDerivAt_mul_exp_ltr {m : Type*} [Fintype m] (M : Matrix m d ℝ)
    (Y : Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => M * NormedSpace.exp (τ • Y)) (M * Y) 0 :=
  hasDerivAt_matrix_ltr fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_apply_ltr Y k j).const_mul (M i k)

omit [LinearOrder d] in
/-- Helper (a copy of the private `hasDerivAt_exp_mul_lst`): the derivative of
`τ ↦ exp (τ Y) M` at `0` is `Y M`. -/
private theorem hasDerivAt_exp_mul_ltr {n : Type*} [Fintype n] (Y : Matrix d d ℝ)
    (M : Matrix d n ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) * M) (Y * M) 0 :=
  hasDerivAt_matrix_ltr fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_apply_ltr Y i k).mul_const (M k j)

-- See `hasDerivAt_exp_smul_apply_ltr` for this option.
omit [LinearOrder d] in
set_option backward.isDefEq.respectTransparency false in
/-- Helper (a copy of the private `hasDerivAt_exp_mul_exp_lst`): the derivative of
`τ ↦ exp (-τ Y) S exp (τ Z)` at `0` is `−Y S + S Z`. -/
private theorem hasDerivAt_exp_mul_exp_ltr (Y Z S : Matrix d d ℝ) :
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
private theorem exp_smul_mul_exp_smul_neg_ltr (Y : Matrix d d ℝ) (τ : ℝ) :
    NormedSpace.exp (τ • Y) * NormedSpace.exp (τ • -Y) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).neg_right.smul_left τ).smul_right τ),
    smul_neg, add_neg_cancel, NormedSpace.exp_zero]

omit [LinearOrder d] in
/-- Helper (a copy of the private `expGL_lst`): the invertible matrix `exp (τ Y)`, with inverse
`exp (-τ Y)`. -/
private noncomputable def expGL_ltr (Y : Matrix d d ℝ) (τ : ℝ) : GL d ℝ :=
  ⟨NormedSpace.exp (τ • Y), NormedSpace.exp (τ • -Y), exp_smul_mul_exp_smul_neg_ltr Y τ,
    by simpa only [neg_neg] using exp_smul_mul_exp_smul_neg_ltr (-Y) τ⟩

omit [LinearOrder d] in
/-- Helper (a copy of the private `expGL_zero_lst`): `exp (0 Y) = 1`. -/
private theorem expGL_zero_ltr (Y : Matrix d d ℝ) : expGL_ltr Y 0 = 1 := by
  apply Units.ext
  change NormedSpace.exp ((0 : ℝ) • Y) = 1
  rw [zero_smul, NormedSpace.exp_zero]

omit [LinearOrder d] in
/-- Helper (a copy of the private `expGL_mem_orthogonalGroup_lst`): for antisymmetric `Y`,
`exp (τ Y)` is orthogonal. -/
private theorem expGL_mem_orthogonalGroup_ltr {Y : Matrix d d ℝ} (hY : Yᵀ = -Y) (τ : ℝ) :
    (expGL_ltr Y τ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  change (NormedSpace.exp (τ • Y))ᵀ * NormedSpace.exp (τ • Y) = 1
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, hY]
  simpa only [neg_neg] using exp_smul_mul_exp_smul_neg_ltr (-Y) τ

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] [LinearOrder d] in
/-- Helper (a copy of the private `cob_expGL_zero_lst`): the curve
`τ ↦ θ.cob (exp (τ X_ℓ)) (exp (τ X_ℓ))` passes through `θ` at `τ = 0`. -/
private theorem cob_expGL_zero_ltr {A : Arch T d L} (θ : Params A dIn dOut)
    (X : Fin (L + 1) → Matrix d d ℝ) :
    θ.cob (fun ℓ => expGL_ltr (X ℓ) 0) (fun ℓ => expGL_ltr (X ℓ) 0) = θ := by
  simp only [expGL_zero_ltr]
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [Params.cob, inv_one, Units.val_one, Matrix.mul_one, Matrix.one_mul]

omit [Fintype T] [Nonempty T] [LinearOrder d] in
/-- Helper (a copy of the private `hasDerivAt_cob_expGL_lst`): the curve
`τ ↦ θ.cob (exp (τ X_ℓ)) (exp (τ X_ℓ))` has velocity `cobDir θ X` at `τ = 0`. -/
private theorem hasDerivAt_cob_expGL_ltr {A : Arch T d L} (θ : Params A dIn dOut)
    (X : Fin (L + 1) → Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => θ.cob (fun ℓ => expGL_ltr (X ℓ) τ) (fun ℓ => expGL_ltr (X ℓ) τ))
      (cobDir θ X) 0 := by
  -- The norm of the parameters is that of the tuple of their components.
  let e : Params A dIn dOut ≃L[ℝ] Params.Prod A dIn dOut :=
    Params.linearEquivProd.toContinuousLinearEquiv
  -- Componentwise: `E exp (τ X_0)`, `exp (-τ X_{ℓ-1}) W_read^ℓ`, `W_write^ℓ exp (τ X_ℓ)`,
  -- `exp (-τ X_L) D`.
  have key : HasDerivAt
      (fun τ : ℝ => e (θ.cob (fun ℓ => expGL_ltr (X ℓ) τ) (fun ℓ => expGL_ltr (X ℓ) τ)))
      (e (cobDir θ X)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · exact hasDerivAt_mul_exp_ltr θ.E (X 0)
    · exact hasDerivAt_pi.2 fun ℓ =>
        (hasDerivAt_exp_mul_ltr (-X ℓ.castSucc) (θ.read ℓ)).congr_deriv (Matrix.neg_mul _ _)
    · exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_mul_exp_ltr (θ.write ℓ) (X ℓ.succ)
    · exact (hasDerivAt_exp_mul_ltr (-X (Fin.last L)) θ.D).congr_deriv (Matrix.neg_mul _ _)
  -- Back to the parameters through `e⁻¹`.
  exact e.symm.hasFDerivAt.comp_hasDerivAt (0 : ℝ) key

omit [Nonempty T] [LinearOrder d] in
/-- Helper (a copy of the private `rot_mem_flatSkips_lst`; the rotations are flat with no
hypothesis on the blocks): for antisymmetric `X_ℓ`, the direction
`(cobDir θ X, −X_{ℓ-1} S_ℓ + S_ℓ X_ℓ)` of the orthogonal changes of basis `exp (τ X_ℓ)` is flat. -/
private theorem rot_mem_flatSkips_ltr {A : Arch T d L} (hA : A.χ = rmsNorm ε)
    (θ : Params A dIn dOut) (S : Fin L → Matrix d d ℝ) (X : Fin (L + 1) → Matrix d d ℝ)
    (hX : ∀ ℓ, (X ℓ)ᵀ = -X ℓ) :
    (cobDir θ X, fun ℓ => -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ)
      ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S) := by
  -- the curve `τ ↦ (θ.cob G_τ G_τ, cobSkip S G_τ)` with `G_τ ℓ = exp (τ X_ℓ)` and its velocity
  have hγ : HasDerivAt (fun τ : ℝ => (θ.cob (fun ℓ => expGL_ltr (X ℓ) τ)
      (fun ℓ => expGL_ltr (X ℓ) τ), cobSkip S (fun ℓ => expGL_ltr (X ℓ) τ)))
      (cobDir θ X, fun ℓ => -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ) 0 :=
    (hasDerivAt_cob_expGL_ltr θ X).prodMk
      (hasDerivAt_pi.2 fun ℓ => hasDerivAt_exp_mul_exp_ltr (X ℓ.castSucc) (X ℓ.succ) (S ℓ))
  refine mem_flatSkips_of_hasDerivAt_ltr _ _ _ hγ ?_ ?_
  · -- at `τ = 0` the curve is at `(θ, S)`
    refine Prod.ext (cob_expGL_zero_ltr θ X) ?_
    show cobSkip S (fun ℓ => expGL_ltr (X ℓ) 0) = S
    funext ℓ
    simp only [cobSkip, expGL_zero_ltr, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  · -- along the curve the function is kept: pre-RMSNorm commutes with the orthogonal `G_τ ℓ`
    refine Filter.Eventually.of_forall fun τ x => ?_
    have hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (expGL_ltr (X ℓ) τ : Matrix d d ℝ))
        = A.χ h * (expGL_ltr (X ℓ) τ : Matrix d d ℝ) := by
      intro ℓ h
      rw [hA]
      exact rmsNorm_mul_orthogonal ε (expGL_mem_orthogonalGroup_ltr (hX ℓ) τ) h
    exact eval_cob (M := S) (θ := θ) (G := fun ℓ => expGL_ltr (X ℓ) τ)
      (K := fun ℓ => expGL_ltr (X ℓ) τ) (x := x) hχ

omit [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper (as the private `fderiv_batch_flat_lst`, with the differentiability only at the inputs
of the batch): a flat direction is in the kernel of the Jacobian on a batch of inputs at which the
output is differentiable. -/
private theorem fderiv_batch_flat_ltr {A : Arch T d L}
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

end Rotations

/-! ### Helpers: every direction of the skip is an upper triangular one plus `X_0 R` -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [LinearOrder d] [Fintype dIn]
  [Fintype dOut] in
/-- Helper (a copy of the private `half_add_half_lst`): `d (d + 1)/2 + d (d − 1)/2 = d²` (both
products are even). -/
private theorem half_add_half_ltr (n : ℕ) : n * (n + 1) / 2 + n * (n - 1) / 2 = n ^ 2 := by
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
private theorem eq_zero_of_mul_blockTriangular_ltr {R X : Matrix d d ℝ}
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
private def decompLin_ltr (R : Matrix d d ℝ) :
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
private theorem decompLin_surjective_ltr {R : Matrix d d ℝ} (hRt : R.BlockTriangular id)
    (hR : IsUnit R.det) : Function.Surjective (decompLin_ltr R) := by
  have hinj : Function.Injective (decompLin_ltr R) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨X, U⟩ h
    have h' : (U : Matrix d d ℝ) - (X : Matrix d d ℝ) * R = 0 := LinearMap.mem_ker.1 h
    have hU : (U : Matrix d d ℝ) = (X : Matrix d d ℝ) * R := sub_eq_zero.1 h'
    have hXR : ((X : Matrix d d ℝ) * R).BlockTriangular id := by
      rw [← hU]
      exact U.2
    have hX0 : (X : Matrix d d ℝ) = 0 := eq_zero_of_mul_blockTriangular_ltr hRt hR X.2 hXR
    have hU0 : (U : Matrix d d ℝ) = 0 := by rw [hU, hX0, Matrix.zero_mul]
    exact Prod.ext (Subtype.ext hX0) (Subtype.ext hU0)
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj
  rw [Module.finrank_prod, finrank_antisymmetric, finrank_upperTriangular, Module.finrank_matrix,
    Module.finrank_self, mul_one, add_comm, half_add_half_ltr, sq]

/-- Helper (the form of the private `exists_add_mul_mem_upperTriangular_lst`): for `R` invertible
and upper triangular, every `a` is upper triangular after adding `X R` for some antisymmetric
`X`. -/
private theorem exists_add_mul_mem_ltr {R : Matrix d d ℝ} (hRt : R.BlockTriangular id)
    (hR : IsUnit R.det) (a : Matrix d d ℝ) :
    ∃ X : antisymmetric d, a + (X : Matrix d d ℝ) * R ∈ upperTriangular d := by
  obtain ⟨⟨X, U⟩, h⟩ := decompLin_surjective_ltr hRt hR a
  refine ⟨X, ?_⟩
  have h' : (U : Matrix d d ℝ) - (X : Matrix d d ℝ) * R = a := h
  rw [← h', sub_add_cancel]
  exact U.2

omit [Nonempty T] in
/-- Helper (a copy of the private `exists_sub_mem_flatSkips_lst`): at an invertible upper
triangular skip `R`, every direction `w` of the family of all skips is a direction `(η', a')` with
an upper triangular `a'` plus a flat direction: the rotation of `h_0` by an antisymmetric `X_0`
moves the skip by `−X_0 R`. -/
private theorem exists_sub_mem_flatSkips_ltr {A : Arch T d 1} (hA : A.χ = rmsNorm ε)
    (θ : Params A dIn dOut) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) (w : Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) :
    ∃ u : Params A dIn dOut × (Fin 1 → upperTriangular d),
      w - (u.1, triSkips d 1 u.2) ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ))
        (θ, fun ℓ => (R ℓ : Matrix d d ℝ)) := by
  -- `X_0` antisymmetric with `a_0 + X_0 R_0` upper triangular
  obtain ⟨X₀, hX₀⟩ := exists_add_mul_mem_ltr (R 0).2 hR (w.2 0)
  -- the rotation of `h_0` by `X_0`, and none of `h_1`: a flat direction
  let X : Fin (1 + 1) → Matrix d d ℝ := Fin.cons (X₀ : Matrix d d ℝ) fun _ => 0
  have hX : ∀ ℓ, (X ℓ)ᵀ = -X ℓ := by
    intro ℓ
    refine Fin.cases ?_ (fun i => ?_) ℓ
    · exact X₀.2
    · simp only [X, Fin.cons_succ, transpose_zero, neg_zero]
  have hrot := rot_mem_flatSkips_ltr hA θ (fun ℓ => (R ℓ : Matrix d d ℝ)) X hX
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

/-! ### The common core: one block under pre-RMSNorm, on a set `U` of inputs at which the block is
differentiable -/

omit [Nonempty T] in
/-- Helper (the triangular family against the full family on a batch): on a batch of inputs at
which the block is differentiable, at an invertible upper triangular skip `R`, the Jacobian of the
triangular family has the rank of the Jacobian of the full family. It is the Jacobian `J` of the
full family composed with the inclusion `m`, and every direction `w` is `m u` plus a flat
direction, which `J` kills. -/
private theorem jacobianRankSkips_tri_eq_ltr {A : Arch T d 1} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (θ : Params A dIn dOut) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hfx : ∀ i, DifferentiableAt ℝ (A.f 0) (rmsNorm ε (X i * θ.E) * θ.read 0)) :
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
  have hdiff : ∀ i, DifferentiableAt ℝ (fun p' : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p' (X i))
        (θ, fun ℓ => (R ℓ : Matrix d d ℝ)) := fun i =>
    differentiableAt_evalSkips_ltr hε hA θ _ (X i) (hfx i)
  have hG : DifferentiableAt ℝ G (m (θ, R)) := differentiableAt_pi.2 hdiff
  have hd : fderiv ℝ (G ∘ m) (θ, R) = (fderiv ℝ G (m (θ, R))).comp m :=
    (hG.hasFDerivAt.comp (θ, R) m.hasFDerivAt).fderiv
  show Module.finrank ℝ (LinearMap.range (fderiv ℝ (G ∘ m) (θ, R)).toLinearMap)
    = Module.finrank ℝ (LinearMap.range (fderiv ℝ G (m (θ, R))).toLinearMap)
  rw [hd]
  refine le_antisymm (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _))
    (Submodule.finrank_mono ?_)
  -- every value `J w` is `J (m u)`, with `w − m u` flat
  rintro _ ⟨w, rfl⟩
  obtain ⟨u, hu⟩ := exists_sub_mem_flatSkips_ltr hA θ R hR w
  refine ⟨u, ?_⟩
  have h0 := fderiv_batch_flat_ltr _ X hdiff hu
  rw [map_sub] at h0
  exact (sub_eq_zero.1 h0).symm

omit [Nonempty T] in
/-- Helper (no batch of inputs of `U` has a larger rank): if the full family has the value
`fd + (d (d − 1) + s) = P + d²` at `(θ, R)`, then on every batch of inputs at which the block is
differentiable the triangular family has `rank + (d (d − 1)/2 + s) ≤ P + d (d + 1)/2`. -/
private theorem jacobianRankSkips_tri_add_le_ltr {A : Arch T d 1} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (θ : Params A dIn dOut) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) {s : ℕ}
    (hval : funDimLearned A (θ, fun ℓ => (R ℓ : Matrix d d ℝ))
        + (Fintype.card d * (Fintype.card d - 1) + s)
      = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hfx : ∀ i, DifferentiableAt ℝ (A.f 0) (rmsNorm ε (X i * θ.E) * θ.read 0)) :
    jacobianRankSkips A (triSkips d 1) X (θ, R) + (Fintype.card d * (Fintype.card d - 1) / 2 + s)
      ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the rank of the full family on the batch is at most its functional dimension
  have hle : jacobianRankSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X
      (θ, fun ℓ => (R ℓ : Matrix d d ℝ)) ≤ funDimLearned A (θ, fun ℓ => (R ℓ : Matrix d d ℝ)) :=
    le_csSup ⟨Module.finrank ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)), by
      rintro _ ⟨n, X, rfl⟩
      exact LinearMap.finrank_range_le _⟩ ⟨n, X, rfl⟩
  rw [jacobianRankSkips_tri_eq_ltr hε hA θ R hR X hfx]
  -- `d (d + 1)/2 + d (d − 1)/2 = d²` and `2 (d (d − 1)/2) = d (d − 1)`
  have h1 := half_add_half_ltr (Fintype.card d)
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  generalize Fintype.card d * (Fintype.card d + 1) = y at h1 ⊢
  generalize Fintype.card d * (Fintype.card d - 1) = x at h1 h2 hval ⊢
  generalize Fintype.card d ^ 2 = q at h1 hval
  omega

omit [Nonempty T] in
/-- Helper (a batch with this rank): a batch of inputs at which the block is differentiable on
which the full family has `rank + (d (d − 1) + s) = P + d²` gives the triangular family
`rank + (d (d − 1)/2 + s) = P + d (d + 1)/2` on the same batch. -/
private theorem exists_jacobianRankSkips_tri_ltr {A : Arch T d 1} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (θ : Params A dIn dOut) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) (U : Set (Matrix T dIn ℝ))
    (hfx : ∀ x ∈ U, DifferentiableAt ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)) {s : ℕ}
    (hex : ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      jacobianRankSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X
          (θ, fun ℓ => (R ℓ : Matrix d d ℝ)) + (Fintype.card d * (Fintype.card d - 1) + s)
        = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      jacobianRankSkips A (triSkips d 1) X (θ, R)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + s)
        = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d * (Fintype.card d + 1) / 2 := by
  obtain ⟨n, X, hX, hr⟩ := hex
  refine ⟨n, X, hX, ?_⟩
  rw [jacobianRankSkips_tri_eq_ltr hε hA θ R hR X fun i => hfx (X i) (hX i)]
  -- `d (d + 1)/2 + d (d − 1)/2 = d²` and `2 (d (d − 1)/2) = d (d − 1)`
  have h1 := half_add_half_ltr (Fintype.card d)
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  generalize Fintype.card d * (Fintype.card d + 1) = y at h1 ⊢
  generalize Fintype.card d * (Fintype.card d - 1) = x at h1 h2 hr ⊢
  generalize Fintype.card d ^ 2 = q at h1 hr
  omega

omit [Fintype T] [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper (the supremum in `funDimSkipsOn`): if one batch of inputs of `U` has
`rank + k = N` and every batch of inputs of `U` has `rank + k ≤ N`, then
`funDimSkipsOn + k = N` (a set of naturals that contains its upper bound). -/
private theorem funDimSkipsOn_add_eq_ltr {L : ℕ} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (p : Params A dIn dOut × V) (U : Set (Matrix T dIn ℝ)) {k N : ℕ}
    (hex : ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      jacobianRankSkips A ι X p + k = N)
    (hle : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) →
      jacobianRankSkips A ι X p + k ≤ N) :
    funDimSkipsOn A ι p U + k = N := by
  obtain ⟨n, X, hX, hr⟩ := hex
  -- the rank on `X` bounds every rank on a batch of inputs of `U`
  have hb : ∀ r ∈ {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      r = jacobianRankSkips A ι X p}, r ≤ jacobianRankSkips A ι X p := by
    rintro _ ⟨m, Y, hY, rfl⟩
    have := hle m Y hY
    omega
  have h1 : funDimSkipsOn A ι p U ≤ jacobianRankSkips A ι X p := by
    unfold funDimSkipsOn
    exact csSup_le ⟨_, n, X, hX, rfl⟩ hb
  have h2 : jacobianRankSkips A ι X p ≤ funDimSkipsOn A ι p U := by
    unfold funDimSkipsOn
    exact le_csSup ⟨_, hb⟩ ⟨n, X, hX, rfl⟩
  omega

/-! ### Helpers: the blocks are differentiable off the kinks (as the private helpers of
`OneBlock/ResidualRMSRescale.lean` and `OneBlock/ResidualRMSReGLU.lean`) -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper (a copy of the private `rmsNorm_mul_apply_rres`): `N_ε` scales every row:
`(N_ε(h) W)_{t i} = (‖h_t‖²/d + ε)^{-1/2} (h W)_{t i}`. -/
private theorem rmsNorm_mul_apply_ltr {n : Type*} [Fintype n] (h : Matrix T d ℝ)
    (W : Matrix d n ℝ) (t : T) (i : n) :
    (rmsNorm ε h * W) t i
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ * (h * W) t i := by
  simp only [Matrix.mul_apply, Finset.mul_sum, rmsNorm, rmsRow, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul, mul_assoc]

omit [DecidableEq d] [LinearOrder d] in
/-- Helper (a copy of the private `inv_sqrt_pos_rres`): the factor of `N_ε` is positive for
`ε > 0`. -/
private theorem inv_sqrt_pos_ltr (hε : 0 < ε) (v : d → ℝ) :
    0 < (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε))⁻¹ := by
  have h0 : 0 ≤ (v ⬝ᵥ v) / (Fintype.card d : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)) (Nat.cast_nonneg _)
  exact inv_pos.2 (Real.sqrt_pos.2 (by linarith))

omit [Nonempty T] [DecidableEq d] [LinearOrder d] [Fintype dOut] in
/-- Helper (as `differentiableAt_eval_rres`): at an input of `noKinkRMS θ` the map of the block is
differentiable at the pre-activations `N_ε(x E) W_read`, which have no zero entry (`N_ε` scales the
rows of `x E` by positive numbers) and at which `σ` is differentiable entry by entry. -/
private theorem differentiableAt_f_mlp_ltr (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ noKinkRMS θ) :
    DifferentiableAt ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid).f 0)
      (rmsNorm ε (x * θ.E) * θ.read 0) := by
  have hP : ∀ t i, (rmsNorm ε (x * θ.E) * θ.read 0) t i ≠ 0 := by
    intro t i
    rw [rmsNorm_mul_apply_ltr]
    exact mul_ne_zero (inv_sqrt_pos_ltr hε _).ne' (hx t i)
  generalize rmsNorm ε (x * θ.E) * θ.read 0 = P at hP ⊢
  refine differentiableAt_pi.2 fun t => differentiableAt_pi.2 fun i => ?_
  have hent : Differentiable ℝ (fun M : Matrix T (hid 0) ℝ => M t i) :=
    differentiable_pi.1 (differentiable_pi.1 differentiable_id t) i
  have h := (hσ _ (hP t i)).differentiableAt.comp P (hent P)
  exact h

omit [Nonempty T] [DecidableEq d] [LinearOrder d] [Fintype dOut] in
/-- Helper (as `differentiableAt_eval_rglu`): at an input of `noKinkGateRMS θ` the map of the
ReGLU block is differentiable at the pre-activations `N_ε(x E) W_read`, whose gates are positive
multiples of those of `x E W_read`, so not at the kink. -/
private theorem differentiableAt_f_reglu_ltr (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (x : Matrix T dIn ℝ) (hx : x ∈ noKinkGateRMS θ) :
    DifferentiableAt ℝ ((Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid).f 0)
      (rmsNorm ε (x * θ.E) * θ.read 0) := by
  have hM : ∀ t i, (rmsNorm ε (x * θ.E) * θ.read 0) t (Sum.inl i) ≠ 0 := by
    intro t i
    rw [rmsNorm_mul_apply_ltr]
    exact mul_ne_zero (inv_sqrt_pos_ltr hε _).ne' (hx t i)
  generalize rmsNorm ε (x * θ.E) * θ.read 0 = M at hM ⊢
  refine differentiableAt_pi.2 fun t => differentiableAt_pi.2 fun i => ?_
  have he : ∀ j, Differentiable ℝ (fun N : Matrix T (hid 0 ⊕ hid 0) ℝ => N t j) := fun j =>
    differentiable_pi.1 (differentiable_pi.1 differentiable_id t) j
  have h := ((hasDerivAt_relu (hM t i)).differentiableAt.comp M (he (Sum.inl i) M)).mul
    (he (Sum.inr i) M)
  exact h

/-! ### Helpers: almost every `(θ, A)`, `A` upper triangular -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper (a copy of the private `ae_fst_lsr`): a condition on the weights that holds at almost
every `θ` holds at almost every `(θ, v)`. -/
private theorem ae_fst_ltr {A : Arch T d 1} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] (hB : BorelSpace V)
    (μ : Measure (Params A dIn dOut × V)) (hμ : μ.IsAddHaarMeasure) {Q : Params A dIn dOut → Prop}
    (h : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), Q θ) :
    ∀ᵐ p ∂μ, Q p.1 := by
  rw [ae_iff] at h
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null h
  have hc : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), θ ∈ Nᶜ :=
    measure_eq_zero_iff_ae_notMem.1 hN0
  have h1 := (ae_comp_linearMap_mem_iff (LinearMap.fst ℝ (Params A dIn dOut) V) μ
    Measure.addHaar (LinearMap.fst_surjective) hN.compl).2 hc
  refine h1.mono fun p hp => ?_
  by_contra hq
  exact hp (hsub hq)

omit [LinearOrder d] in
/-- Helper (a copy of the private `ae_isUnit_det_lsr`): if a square matrix that depends linearly on
a point of `E` is the identity at one point, it is invertible at almost every point. -/
private theorem ae_isUnit_det_ltr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

omit [Fintype T] [Nonempty T] in
/-- Helper: at almost every `(θ, A)`, `A` upper triangular, a condition on the weights that holds
at almost every `θ` holds, and `A` is invertible (its determinant is a polynomial in the entries,
`1` at `A = 1`). -/
private theorem ae_generic_tri_ltr {A : Arch T d 1}
    (μ : Measure (Params A dIn dOut × (Fin 1 → upperTriangular d))) [hμ : μ.IsAddHaarMeasure]
    {Q : Params A dIn dOut → Prop}
    (h : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), Q θ) :
    ∀ᵐ p ∂μ, Q p.1 ∧ IsUnit (p.2 0 : Matrix d d ℝ).det := by
  have hBt : BorelSpace (Fin 1 → upperTriangular d) := inferInstance
  have hBp : BorelSpace (Params A dIn dOut × (Fin 1 → upperTriangular d)) := Prod.borelSpace
  have h1 := ae_fst_ltr hBt μ hμ h
  have h2 := ae_isUnit_det_ltr hBp μ hμ
    ((upperTriangular d).subtype ∘ₗ (LinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 1 => upperTriangular d) 0)
      ∘ₗ (LinearMap.snd ℝ (Params A dIn dOut) (Fin 1 → upperTriangular d)))
    (0, fun _ => ⟨1, Matrix.blockTriangular_one⟩) rfl
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

/-- **Theorem B.1 (iii) for the upper triangular skip, in the paper's own sense, for ReLU-type MLP
blocks, at one parameter:** under the conditions `OneBlockGenericRMS`, for an invertible upper
triangular skip, a finite batch of inputs with no hidden unit at its kink on which the Jacobian in
the weights and the triangular skip has the rank `P + d (d + 1)/2 − d (d − 1)/2 − s`. -/
theorem exists_jacobianRankSkips_tri_mlp_rescale_rmsNorm
    {k : ℕ} (hk : k ≠ 0) (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0)) [Nonempty (hid 0)]
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkRMS θ) ∧
      jacobianRankSkips (Arch.mlp σ (rmsNorm ε) hid) (triSkips d 1) X (θ, R)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
          + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **No batch of inputs off the kinks has a larger rank,** for ReLU-type MLP blocks with an upper
triangular learned skip, at one parameter: under the conditions `OneBlockGenericRMS`, for an
invertible upper triangular skip and every finite batch of inputs with no hidden unit at its kink,
the rank of the Jacobian in the weights and the triangular skip is at most `P + d (d + 1)/2 − d (d −
1)/2 − s`. -/
theorem jacobianRankSkips_tri_add_le_mlp_rescale_rmsNorm
    {k : ℕ} (hk : k ≠ 0) (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0)) [Nonempty (hid 0)]
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (hX : ∀ i, X i ∈ noKinkRMS θ) :
    jacobianRankSkips (Arch.mlp σ (rmsNorm ε) hid) (triSkips d 1) X (θ, R)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) for the upper triangular skip, for ReLU-type MLP blocks, at one parameter:**
under the conditions `OneBlockGenericRMS`, for an invertible upper triangular skip, the functional
dimension on the inputs with no hidden unit at its kink is `P + d (d + 1)/2 − d (d − 1)/2 − s`. -/
theorem funDimSkipsOn_tri_mlp_rescale_rmsNorm
    {k : ℕ} (hk : k ≠ 0) (hε : 0 < ε)
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k d d (hid 0)) [Nonempty (hid 0)]
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) :
    funDimSkipsOn (Arch.mlp σ (rmsNorm ε) hid) (triSkips d 1) (θ, R) (noKinkRMS θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one ReLU block with an upper triangular learned skip,
`ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and a block of any width with at least one hidden unit, at
almost every `(θ, A)`, `A` upper triangular, the functional dimension on the inputs with no hidden
unit at its kink is `P + d (d + 1)/2 − d (d − 1)/2 − d_hidden`. -/
theorem ae_funDimSkipsOn_tri_relu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp relu (rmsNorm ε) hid) (triSkips d 1) p (noKinkRMS p.1)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly `d (d +
1)/2`", for one ReLU block with an upper triangular learned skip, `ε > 0`:** at almost every `(θ,
A)`, `A` upper triangular, and almost every `θ'`, the functional dimension on the inputs with no
hidden unit at its kink is that of the residual network at `θ'` plus `d (d + 1)/2`. -/
theorem ae_funDimSkipsOn_tri_relu_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimSkipsOn (Arch.mlp relu (rmsNorm ε) hid) (triSkips d 1) p (noKinkRMS
        p.1)
      = funDim (Arch.mlp relu (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one ReLU² block with an upper triangular learned
skip, `ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and a block of any width with at least one hidden unit,
at almost every `(θ, A)`, `A` upper triangular, the functional dimension on the inputs with no
hidden unit at its kink is `P + d (d + 1)/2 − d (d − 1)/2 − d_hidden`. -/
theorem ae_funDimSkipsOn_tri_reluSq_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp reluSq (rmsNorm ε) hid) (triSkips d 1) p (noKinkRMS p.1)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly `d (d +
1)/2`", for one ReLU² block with an upper triangular learned skip, `ε > 0`:** at almost every `(θ,
A)`, `A` upper triangular, and almost every `θ'`, the functional dimension on the inputs with no
hidden unit at its kink is that of the residual network at `θ'` plus `d (d + 1)/2`. -/
theorem ae_funDimSkipsOn_tri_reluSq_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimSkipsOn (Arch.mlp reluSq (rmsNorm ε) hid) (triSkips d 1) p (noKinkRMS
        p.1)
      = funDim (Arch.mlp reluSq (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) for the upper triangular skip, in the paper's own sense, for a ReGLU block,
at one parameter:** under the conditions `OneBlockGenericReGLURMS`, for an invertible upper
triangular skip, a finite batch of inputs with no gate at its kink on which the Jacobian in the
weights and the triangular skip has the rank `P + d (d + 1)/2 − d (d − 1)/2 − 2 d_hidden`. -/
theorem exists_jacobianRankSkips_tri_reglu_rmsNorm
    (hε : 0 < ε) [Nonempty (hid 0)]
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateRMS θ) ∧
      jacobianRankSkips (Arch.gated relu (rmsNorm ε) hid) (triSkips d 1) X (θ, R)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
          + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **No batch of inputs off the kinks has a larger rank,** for a ReGLU block with an upper
triangular learned skip, at one parameter: under the conditions `OneBlockGenericReGLURMS`, for an
invertible upper triangular skip and every finite batch of inputs with no gate at its kink, the rank
of the Jacobian in the weights and the triangular skip is at most `P + d (d + 1)/2 − d (d − 1)/2 − 2
d_hidden`. -/
theorem jacobianRankSkips_tri_add_le_reglu_rmsNorm
    (hε : 0 < ε) [Nonempty (hid 0)]
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (hX : ∀ i, X i ∈ noKinkGateRMS θ) :
    jacobianRankSkips (Arch.gated relu (rmsNorm ε) hid) (triSkips d 1) X (θ, R)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * Fintype.card (hid 0))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) for the upper triangular skip, for a ReGLU block, at one parameter:** under
the conditions `OneBlockGenericReGLURMS`, for an invertible upper triangular skip, the functional
dimension on the inputs with no gate at its kink is `P + d (d + 1)/2 − d (d − 1)/2 − 2 d_hidden`. -/
theorem funDimSkipsOn_tri_reglu_rmsNorm
    (hε : 0 < ε) [Nonempty (hid 0)]
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) :
    funDimSkipsOn (Arch.gated relu (rmsNorm ε) hid) (triSkips d 1) (θ, R) (noKinkGateRMS θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one ReGLU block with an upper triangular learned
skip, `ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and a block of any width with at least one hidden unit,
at almost every `(θ, A)`, `A` upper triangular, the functional dimension on the inputs with no gate
at its kink is `P + d (d + 1)/2 − d (d − 1)/2 − 2 d_hidden`. -/
theorem ae_funDimSkipsOn_tri_reglu_rmsNorm (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.gated relu (rmsNorm ε) hid) (triSkips d 1) p (noKinkGateRMS p.1)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly `d (d +
1)/2`", for one ReGLU block with an upper triangular learned skip, `ε > 0`:** at almost every `(θ,
A)`, `A` upper triangular, and almost every `θ'`, the functional dimension on the inputs with no
gate at its kink is that of the residual network at `θ'` plus `d (d + 1)/2`. -/
theorem ae_funDimSkipsOn_tri_reglu_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimSkipsOn (Arch.gated relu (rmsNorm ε) hid) (triSkips d 1) p
        (noKinkGateRMS p.1)
      = funDim (Arch.gated relu (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

end Skips
