import SkipsLean.OneBlock.LearnedSkipOn
import SkipsLean.OneBlock.ResidualRMSStepsOn

/-!
# One block with a full learned skip under pre-RMSNorm: Steps 1 to 3 of Part (iii)

Paper (skips paper): proof of Theorem B.1 (iii) (the last sentence of Theorem 4.6 (ii) in the main
text), for `ε > 0` and no biases. The network is

  `h_1 = x E A + g(x)`, `g(x) = B(N_ε(x E))`, `B(n) = f(n W_read) W_write`, `y = N_ε(h_1) D`,

with a full learned skip `A`. "Let `η` be flat. […] Steps 1 and 2 of part (ii) run with `E A` in
place of `E`, which has rank `d_model` since `A` is invertible for generic parameters:
`η_D = −Y D` with `Y` antisymmetric, and `D_θ h_1 η = h_1 Y` at every input. Step 3: the skip. At
the inputs `t w` of Step 2, `D_θ h_1 η = t w (η_E A + E η_A) + O(1)` and
`h_1 Y = t w E A Y + O(1)`, so `η_E A + E η_A = E A Y`. Multiplying on the left by `I − E E⁺` gives
`(I − E E⁺) η_E = 0`, as `A` is invertible, so `η_E = E X` with `X = E⁺ η_E`, and then
`η_A = A Y − X A`. At every input `D_θ h_1 η = x E A Y + D_θ g η` and
`h_1 Y = x E A Y + g(x) Y`, so `D_θ g η = g(x) Y`."

Stated here once, in the generality of `exists_antisymm_of_flatOn_residual_rmsNorm`
(`OneBlock/ResidualRMSStepsOn.lean`, the same steps for the identity skip): for a fixed map `f`
that is continuously differentiable on an open set `V` of pre-activations which is invariant under
the scaling of every row by a positive number, and for a direction `(η, η_A)` of the weights and
the skip that is flat at the inputs `x` with `x E W_read ∈ V`. For a ReLU-type block `V` is the set
of the matrices with no zero entry (no hidden unit at its kink); for a block that is continuously
differentiable everywhere `V` is everything and the direction is flat at every input. The skip is
`R 0` (the paper's `A`), and `ρ 0` is the paper's `η_A`.

The conclusion is that of Step 3: an antisymmetric `Y` and a matrix `X` with `η_E = E X`,
`η_A = A Y − X A`, `η_D = −Y D`, and `D_θ g η = g(x) Y` at these inputs, where
`D_θ g η = 𝐃f(n W_read)(𝐃N_ε(x E)(x E X) W_read + n η_read) W_write + f(n W_read) η_write` at
`n = N_ε(x E)`. With the identity skip and `η_A = 0` this gives `X = Y`, and the statement is
`exists_antisymm_of_flatOn_residual_rmsNorm`. Step 4 of the paper (the symmetric part of `X`
vanishes) depends on the kind of block: `OneBlock/LearnedSkipRescale.lean` and its siblings.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

section HelpersLss

open Filter
open scoped Topology

/-! ### Step 0: the chain rule along a line of weights and skips, at an input of `U` -/

/-- Helper: the output `g(x) = f(N_ε(x E) W_read) W_write` of the block. -/
private noncomputable def gOne_lss (A : Arch T d 1) (ε : ℝ) (θ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T d ℝ :=
  A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * θ.write 0

/-- Helper: the derivative of `g(x)` along `η`. -/
private noncomputable def dgOne_lss (A : Arch T d 1) (ε : ℝ) (θ η : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T d ℝ :=
  fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
      (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * η.E) * θ.read 0
        + rmsNorm ε (x * θ.E) * η.read 0) * θ.write 0
    + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * η.write 0

/-- Helper: the hidden state `h_1 = x E S + g(x)` of one block with the skip `S`. -/
private noncomputable def hOne_lss (A : Arch T d 1) (ε : ℝ) (θ : Params A dIn dOut)
    (S : Matrix d d ℝ) (x : Matrix T dIn ℝ) : Matrix T d ℝ :=
  x * θ.E * S + gOne_lss A ε θ x

/-- Helper: the derivative `k(x) = x η_E S + x E σ + D_θ g η` of `h_1` along `(η, σ)` (Step 0). -/
private noncomputable def kOne_lss (A : Arch T d 1) (ε : ℝ) (θ η : Params A dIn dOut)
    (S σ : Matrix d d ℝ) (x : Matrix T dIn ℝ) : Matrix T d ℝ :=
  x * η.E * S + x * θ.E * σ + dgOne_lss A ε θ η x

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the function of one block with the skip `R 0` under pre-RMSNorm,
`F(x) = N_ε(h_1) D`. -/
private theorem eval_eq_lss {A : Arch T d 1} {ε : ℝ} (hA : A.χ = rmsNorm ε)
    (R : Fin 1 → Matrix d d ℝ) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    eval A R θ x = rmsNorm ε (hOne_lss A ε θ (R 0) x) * θ.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]
  rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product rule for matrices depending on one real variable. -/
private theorem hasDerivAt_mul_lss {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {P : ℝ → Matrix m n ℝ} {Q : ℝ → Matrix n p ℝ} {P' P0 : Matrix m n ℝ} {Q' Q0 : Matrix n p ℝ}
    {τ : ℝ} (hP : HasDerivAt P P' τ) (hQ : HasDerivAt Q Q' τ) (hP0 : P τ = P0) (hQ0 : Q τ = Q0) :
    HasDerivAt (fun s => P s * Q s) (P' * Q0 + P0 * Q') τ := by
  subst hP0 hQ0
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  have hPe : ∀ k, HasDerivAt (fun s => P s i k) (P' i k) τ := fun k =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hP i) k
  have hQe : ∀ k, HasDerivAt (fun s => Q s k j) (Q' k j) τ := fun k =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hQ k) j
  have h : HasDerivAt (fun s => ∑ k, P s i k * Q s k j)
      (∑ k, (P' i k * Q τ k j + P τ i k * Q' k j)) τ :=
    HasDerivAt.fun_sum (u := Finset.univ) (A := fun k s => P s i k * Q s k j)
      fun k _ => (hPe k).mul (hQe k)
  refine h.congr_deriv ?_
  simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `τ ↦ M + τ N` has the derivative `N` at `0`. -/
private theorem hasDerivAt_affine_lss {m n : Type*} [Fintype m] [Fintype n]
    (M N : Matrix m n ℝ) : HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

omit [Nonempty T] [Fintype dOut] in
/-- Helper (Step 0): along the line `(θ + τ η, S + τ σ)`, the hidden state `h_1` has the
derivative `k(x)` at `τ = 0`, if `f` is differentiable at `N_ε(x E) W_read`. -/
private theorem hasDerivAt_hOne_line_lss {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (θ η : Params A dIn dOut) (S σ : Matrix d d ℝ) (x : Matrix T dIn ℝ)
    (hfx : DifferentiableAt ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)) :
    HasDerivAt (fun τ : ℝ => hOne_lss A ε (θ + τ • η) (S + τ • σ) x)
      (kOne_lss A ε θ η S σ x) 0 := by
  -- `x E(τ)`
  have hE : HasDerivAt (fun τ : ℝ => x * (θ + τ • η).E) (x * η.E) 0 := by
    have h := hasDerivAt_mul_lss (hasDerivAt_const (0 : ℝ) x) (hasDerivAt_affine_lss θ.E η.E)
      (P0 := x) (Q0 := θ.E) rfl (by simp)
    rw [Matrix.zero_mul, zero_add] at h
    exact h
  -- `x E(τ) S(τ)`
  have hES := hasDerivAt_mul_lss hE (hasDerivAt_affine_lss S σ) (P0 := x * θ.E) (Q0 := S)
    (by simp) (by simp)
  -- `N_ε(x E(τ))`
  have hN : HasDerivAt (fun τ : ℝ => rmsNorm ε (x * (θ + τ • η).E))
      (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * η.E)) 0 :=
    ((differentiable_rmsNorm hε) (x * θ.E)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hE
      (by simp)
  -- `N_ε(x E(τ)) W_read(τ)`
  have hNR := hasDerivAt_mul_lss hN (hasDerivAt_affine_lss (θ.read 0) (η.read 0))
    (P0 := rmsNorm ε (x * θ.E)) (Q0 := θ.read 0) (by simp) (by simp)
  -- `f(N_ε(x E(τ)) W_read(τ))`: `f` is differentiable at the point of `τ = 0`
  have hF := hfx.hasFDerivAt.comp_hasDerivAt_of_eq 0 hNR (by simp)
  -- `f(…) W_write(τ)`
  have hFW := hasDerivAt_mul_lss hF (hasDerivAt_affine_lss (θ.write 0) (η.write 0))
    (P0 := A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0)) (Q0 := θ.write 0) (by simp) (by simp)
  exact hES.add hFW

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two matrix-valued maps that are differentiable at a point is
differentiable there (matrix multiplication is a continuous bilinear map). -/
private theorem differentiableAt_matMul_lss {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
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

omit [Nonempty T] in
/-- Helper: at an input `x` at which `f` is differentiable at `N_ε(x E) W_read`, the output is a
differentiable function of the weights and the skip at `(θ, R)`. -/
private theorem differentiableAt_evalSkips_lss {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ)
    (x : Matrix T dIn ℝ) (hfx : DifferentiableAt ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)) :
    DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x) (θ, R) := by
  have e : (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x)
      = fun p => rmsNorm ε (hOne_lss A ε p.1 (p.2 0) x) * p.1.D := by
    funext p
    exact eval_eq_lss hA p.2 p.1 x
  rw [e]
  -- the weights and the skip are linear, hence differentiable, functions of `(θ, R)`
  have hE : Differentiable ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.E) :=
    (LinearMap.toContinuousLinearMap
      (Params.linE (A := A) (dIn := dIn) (dOut := dOut))).differentiable.comp differentiable_fst
  have hRd : Differentiable ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.read 0) :=
    (LinearMap.toContinuousLinearMap
      (Params.linRead (A := A) (dIn := dIn) (dOut := dOut) 0)).differentiable.comp
      differentiable_fst
  have hW : Differentiable ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.write 0) :=
    (LinearMap.toContinuousLinearMap
      (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) 0)).differentiable.comp
      differentiable_fst
  have hD : Differentiable ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.1.D) :=
    (LinearMap.toContinuousLinearMap
      (Params.linD (A := A) (dIn := dIn) (dOut := dOut))).differentiable.comp differentiable_fst
  have hS : Differentiable ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => p.2 0) :=
    differentiable_pi.1 differentiable_snd 0
  have hN := differentiable_rmsNorm (T := T) (d := d) hε
  -- `x E`, `N_ε(x E) W_read`, `f(…)`
  have hxE : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => x * p.1.E) (θ, R) :=
    differentiableAt_matMul_lss (differentiableAt_const x) (hE _)
  have h2 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm ε (x * p.1.E) * p.1.read 0) (θ, R) :=
    differentiableAt_matMul_lss
      (DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
        x * p.1.E) (θ, R) (hN _) hxE) (hRd _)
  have h4 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      A.f 0 (rmsNorm ε (x * p.1.E) * p.1.read 0)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm ε (x * p.1.E) * p.1.read 0) (θ, R) hfx h2
  -- `h_1`, `N_ε(h_1)` and `N_ε(h_1) D`
  have h5 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      hOne_lss A ε p.1 (p.2 0) x) (θ, R) :=
    (differentiableAt_matMul_lss hxE (hS _)).add (differentiableAt_matMul_lss h4 (hW _))
  have h6 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm ε (hOne_lss A ε p.1 (p.2 0) x)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      hOne_lss A ε p.1 (p.2 0) x) (θ, R) (hN _) h5
  exact differentiableAt_matMul_lss h6 (hD _)

omit [Nonempty T] [DecidableEq d] in
/-- Helper: the chain rule along the line `τ ↦ p + τ q` of weights and skips. -/
private theorem hasDerivAt_evalSkips_line_lss (A : Arch T d 1)
    (p q : Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) (x : Matrix T dIn ℝ)
    (hdiff : DifferentiableAt ℝ (fun p' : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p' x) p) :
    HasDerivAt (fun τ : ℝ =>
        evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (p + τ • q) x)
      (fderiv ℝ (fun p' : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
        evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p' x) p q) 0 := by
  have hline : HasDerivAt (fun τ : ℝ => p + τ • q) q 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const q).const_add p
    rw [one_smul] at h
    exact h
  have h0 : p = p + (0 : ℝ) • q := by rw [zero_smul, add_zero]
  exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline h0

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: a direction that is flat at the inputs of `U` has derivative `0` at an input of `U`. -/
private theorem fderiv_eq_zero_of_flatSkipsOn_lss {A : Arch T d 1} {θ η : Params A dIn dOut}
    {R ρ : Fin 1 → Matrix d d ℝ} {U : Set (Matrix T dIn ℝ)}
    (hη : (η, ρ) ∈ flatSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R) U)
    {x : Matrix T dIn ℝ} (hx : x ∈ U) :
    fderiv ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x) (θ, R) (η, ρ) = 0 :=
  LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hη x) hx)

omit [Nonempty T] in
/-- Helper (Step 0): at an input `x` at which `f` is differentiable at `N_ε(x E) W_read` and
along which `(η, ρ)` is flat, `𝐃N_ε(h_1) k(x) D + N_ε(h_1) η_D = 0`. -/
private theorem flat_eq_lss {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (θ η : Params A dIn dOut) (R ρ : Fin 1 → Matrix d d ℝ) (x : Matrix T dIn ℝ)
    (hfx : DifferentiableAt ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0))
    (h0 : fderiv ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x) (θ, R) (η, ρ) = 0) :
    fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (hOne_lss A ε θ (R 0) x)
        (kOne_lss A ε θ η (R 0) (ρ 0) x) * θ.D
      + rmsNorm ε (hOne_lss A ε θ (R 0) x) * η.D = 0 := by
  -- flatness: the derivative along the line is `0`
  have h1 := hasDerivAt_evalSkips_line_lss A (θ, R) (η, ρ) x
    (differentiableAt_evalSkips_lss hε hA θ R x hfx)
  rw [h0] at h1
  -- the same derivative by the chain rule
  have hh := hasDerivAt_hOne_line_lss hε θ η (R 0) (ρ 0) x hfx
  have hN := ((differentiable_rmsNorm (T := T) (d := d) hε) (hOne_lss A ε θ (R 0) x)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hh (by simp)
  have h2 := hasDerivAt_mul_lss hN (hasDerivAt_affine_lss θ.D η.D)
    (P0 := rmsNorm ε (hOne_lss A ε θ (R 0) x)) (Q0 := θ.D) (by simp) (by simp)
  have e : (fun τ : ℝ =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) ((θ, R) + τ • (η, ρ)) x)
      = fun τ => rmsNorm ε (hOne_lss A ε (θ + τ • η) (R 0 + τ • ρ 0) x) * (θ.D + τ • η.D) := by
    funext τ
    show eval A (R + τ • ρ) (θ + τ • η) x = _
    rw [eval_eq_lss hA]
    rfl
  rw [e] at h1
  exact h2.unique h1

/-! ### Step 1: algebra of the final normalization -/

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `0 ≤ ⟨v, v⟩`. -/
private theorem dot_self_nonneg_lss (v : d → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- Helper: the coefficient `μ(v) = ⟨v Y, v⟩ / (d ε)` of Step 1. -/
private noncomputable def mu_lss (ε : ℝ) (Y : Matrix d d ℝ) (v : d → ℝ) : ℝ :=
  (v ᵥ* Y ⬝ᵥ v) / ((Fintype.card d : ℝ) * ε)

/-- Helper: the matrix whose row `t` is `μ(h_t) h_t`. -/
private noncomputable def muScale_lss (ε : ℝ) (Y : Matrix d d ℝ) (h : Matrix T d ℝ) :
    Matrix T d ℝ :=
  Matrix.of fun t => mu_lss ε Y (h t) • h t

omit [Nonempty T] in
/-- Helper (Step 1): `𝐃N_ε(h) (h Y + μ ⊙ h) = N_ε(h) Y`. -/
private theorem fderiv_rmsNorm_muScale_lss {ε : ℝ} (hε : 0 < ε)
    (hd : (0 : ℝ) < Fintype.card d) (h : Matrix T d ℝ) (Y : Matrix d d ℝ) :
    fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) h (h * Y + muScale_lss ε Y h)
      = rmsNorm ε h * Y := by
  rw [fderiv_rmsNorm_apply hε]
  funext t i
  have hpos : 0 < (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε := by
    have := dot_self_nonneg_lss (h t)
    positivity
  have hR : (rmsNorm ε h * Y) t
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ • (h t ᵥ* Y) := by
    rw [Matrix.mul_apply_eq_vecMul]
    show rmsRow ε (h t) ᵥ* Y = _
    rw [rmsRow, Matrix.smul_vecMul]
  have hU : (h * Y + muScale_lss ε Y h) t = h t ᵥ* Y + mu_lss ε Y (h t) • h t := by
    rfl
  rw [hR]
  simp only [Matrix.of_apply, hU]
  have hs2 := Real.sq_sqrt hpos.le
  have hs := Real.sqrt_pos.2 hpos
  generalize Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε) = s at hs hs2
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct_add,
    dotProduct_smul, mu_lss]
  rw [dotProduct_comm (h t) (h t ᵥ* Y)]
  field_simp
  have hs2' : s ^ 2 * (Fintype.card d : ℝ) = h t ⬝ᵥ h t + ε * Fintype.card d := by
    rw [hs2]
    field_simp
  linear_combination ((h t ᵥ* Y ⬝ᵥ h t) * h t i) * hs2'

/-! ### Linear algebra -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix `Z` with `u Z = 0` for every row vector `u` is `0`. -/
private theorem eq_zero_of_vecMul_lss {m n : Type*} [Fintype m] [DecidableEq m]
    {Z : Matrix m n ℝ} (h : ∀ u : m → ℝ, u ᵥ* Z = 0) : Z = 0 := by
  ext i j
  have := congrFun (h (Pi.single i 1)) j
  rwa [Matrix.single_one_vecMul, Matrix.row_apply] at this

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper (polarisation): if `⟨u Y, u⟩ = 0` for every `u`, then `Yᵀ = -Y`. -/
private theorem transpose_eq_neg_lss {Y : Matrix d d ℝ} (h : ∀ u : d → ℝ, u ᵥ* Y ⬝ᵥ u = 0) :
    Yᵀ = -Y := by
  ext i j
  have hii := h (Pi.single i 1)
  have hjj := h (Pi.single j 1)
  have hij := h (Pi.single i 1 + Pi.single j 1)
  simp only [Matrix.add_vecMul, dotProduct_add, Matrix.single_one_vecMul,
    dotProduct_single_one, Pi.add_apply, Matrix.row_apply] at hii hjj hij
  simp only [Matrix.transpose_apply, Matrix.neg_apply]
  linarith

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: for `ε > 0`, `N_ε(h) Z = 0` implies `h Z = 0` (each row is rescaled by a positive
number). -/
private theorem mul_eq_zero_of_rmsNorm_mul_lss {ε : ℝ} (hε : 0 < ε) {m : Type*} [Fintype m]
    (h : Matrix T d ℝ) (Z : Matrix d m ℝ) (hZ : rmsNorm ε h * Z = 0) : h * Z = 0 := by
  funext t
  have hpos : 0 < (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε := by
    have := dot_self_nonneg_lss (h t)
    positivity
  have hrow : (rmsNorm ε h * Z) t
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ • (h t ᵥ* Z) := by
    rw [Matrix.mul_apply_eq_vecMul]
    show rmsRow ε (h t) ᵥ* Z = _
    rw [rmsRow, Matrix.smul_vecMul]
  have h0 : (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ • (h t ᵥ* Z) = 0 := by
    rw [← hrow]
    exact congrFun hZ t
  rw [Matrix.mul_apply_eq_vecMul]
  exact (smul_eq_zero.1 h0).resolve_left (inv_ne_zero (Real.sqrt_pos.2 hpos).ne')

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dOut] in
/-- Helper: row `t` of `w M`, for the input `w` whose rows all equal `w₀`, is `w₀ M`. -/
private theorem constRows_mul_lss {m : Type*} (w₀ : dIn → ℝ) (M : Matrix dIn m ℝ) (t : T) :
    ((Matrix.of fun _ : T => w₀) * M) t = w₀ ᵥ* M := by
  rw [Matrix.mul_apply_eq_vecMul]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `μ ⊙ h` is homogeneous of degree `3`. -/
private theorem muScale_smul_lss (ε : ℝ) (Y : Matrix d d ℝ) (c : ℝ) (h : Matrix T d ℝ) :
    muScale_lss ε Y (c • h) = c ^ 3 • muScale_lss ε Y h := by
  funext t i
  show mu_lss ε Y (c • h t) * (c * h t i) = c ^ 3 * (mu_lss ε Y (h t) * h t i)
  simp only [mu_lss, Matrix.smul_vecMul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `h ↦ μ ⊙ h` is continuous. -/
private theorem continuous_muScale_lss (ε : ℝ) (Y : Matrix d d ℝ) :
    Continuous (muScale_lss (T := T) ε Y) := by
  refine continuous_pi fun t => continuous_pi fun i => ?_
  show Continuous fun h : Matrix T d ℝ => mu_lss ε Y (h t) * h t i
  unfold mu_lss
  have h1 : Continuous fun h : Matrix T d ℝ => h t := continuous_apply t
  exact (((h1.matrix_vecMul continuous_const).dotProduct h1).div_const _).mul
    ((continuous_apply i).comp h1)

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: if `S` is invertible, `w E ≠ 0` gives `w E S ≠ 0`. -/
private theorem vecMul_mul_ne_zero_lss {E : Matrix dIn d ℝ} {S : Matrix d d ℝ}
    (hS : IsUnit S.det) {w : dIn → ℝ} (hw : w ᵥ* E ≠ 0) : w ᵥ* (E * S) ≠ 0 := by
  intro h
  apply hw
  have e := congrArg (· ᵥ* S⁻¹) h
  simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS,
    Matrix.mul_one, Matrix.zero_vecMul] at e
  exact e

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: if `E` has rank `d` and `S` is invertible, every row vector is a `w E S`. -/
private theorem exists_vecMul_mul_eq_lss {E : Matrix dIn d ℝ} {S : Matrix d d ℝ}
    (hE : E.rank = Fintype.card d) (hS : IsUnit S.det) (u : d → ℝ) :
    ∃ w : dIn → ℝ, w ᵥ* (E * S) = u := by
  classical
  obtain ⟨w, hw⟩ := Matrix.vecMul_surjective_iff_rank_eq_card.2 hE (u ᵥ* S⁻¹)
  have hw' : w ᵥ* E = u ᵥ* S⁻¹ := hw
  refine ⟨w, ?_⟩
  rw [← Matrix.vecMul_vecMul, hw', Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hS,
    Matrix.vecMul_one]

/-! ### The open cone `V`, and an open set of rows -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: scaling the rows of `h` by positive numbers scales the rows of `h M` by the same
numbers, so it keeps `h M` in `V`. -/
private theorem rowScale_mul_mem_lss {m r : Type*} [Fintype m] {V : Set (Matrix T r ℝ)}
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    {h : Matrix T m ℝ} {M : Matrix m r ℝ} (hM : h * M ∈ V) {c : T → ℝ} (hc : ∀ t, 0 < c t) :
    (Matrix.of fun t => c t • h t) * M ∈ V := by
  have e : (Matrix.of fun t => c t • h t) * M = Matrix.of fun t i => c t * (h * M) t i := by
    ext t i
    simp only [Matrix.mul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc]
  rw [e]
  exact hVs _ hM c hc

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: for `ε > 0`, `h M ∈ V` gives `N_ε(h) M ∈ V` (`N_ε` scales every row by a positive
number). -/
private theorem rmsNorm_mul_mem_lss {ε : ℝ} (hε : 0 < ε) {r : Type*} {V : Set (Matrix T r ℝ)}
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    {h : Matrix T d ℝ} {M : Matrix d r ℝ} (hM : h * M ∈ V) : rmsNorm ε h * M ∈ V :=
  rowScale_mul_mem_lss hVs hM
    (c := fun t => (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹)
    fun t => inv_pos.2 (Real.sqrt_pos.2 (by have := dot_self_nonneg_lss (h t); positivity))

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: for `s > 0`, `x M ∈ V` gives `(s x) M ∈ V`. -/
private theorem smul_mul_mem_lss {m r : Type*} [Fintype m] {V : Set (Matrix T r ℝ)}
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    {x : Matrix T m ℝ} {M : Matrix m r ℝ} (hx : x * M ∈ V) {s : ℝ} (hs : 0 < s) :
    (s • x) * M ∈ V := by
  have e : (s • x) * M = Matrix.of fun t i => (fun _ : T => s) t * (x * M) t i := by
    rw [Matrix.smul_mul]
    rfl
  rw [e]
  exact hVs _ hx _ fun _ => hs

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: around a point `w₀` of an open set `G`, the points `w₀ ± δ v` lie in `G` for some
`δ > 0`. -/
private theorem exists_add_sub_mem_lss {m : Type*} [Fintype m] {G : Set (m → ℝ)}
    (hG : IsOpen G) {w₀ : m → ℝ} (hw₀ : w₀ ∈ G) (v : m → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ w₀ + δ • v ∈ G ∧ w₀ - δ • v ∈ G := by
  have hc : Continuous fun δ : ℝ => w₀ + δ • v :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : (fun δ : ℝ => w₀ + δ • v) ⁻¹' G ∈ 𝓝 (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hG.mem_nhds hw₀)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hmem
  have hr2 := half_pos hr
  refine ⟨r / 2, hr2, hball ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hr2]
    linarith
  · have h := hball (show -(r / 2) ∈ Metric.ball (0 : ℝ) r by
      rw [Metric.mem_ball, dist_zero_right, norm_neg, Real.norm_eq_abs, abs_of_pos hr2]
      linarith)
    rwa [Set.mem_preimage, neg_smul, ← sub_eq_add_neg] at h

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Steps 1 and 3): a matrix `K` with `w K = 0` for every `w` of a nonempty open set is
`0` (`w ↦ w K` is linear: `w₀ K = 0` and `(w₀ + δ v) K = 0` give `v K = 0`). -/
private theorem eq_zero_of_vecMul_on_lss {m n : Type*} [Fintype m] [DecidableEq m]
    {G : Set (m → ℝ)} (hG : IsOpen G) (hne : G.Nonempty) {K : Matrix m n ℝ}
    (h : ∀ w ∈ G, w ᵥ* K = 0) : K = 0 := by
  obtain ⟨w₀, hw₀⟩ := hne
  refine eq_zero_of_vecMul_lss fun v => ?_
  obtain ⟨δ, hδ, hδG, -⟩ := exists_add_sub_mem_lss hG hw₀ v
  have e := h _ hδG
  rw [Matrix.add_vecMul, h w₀ hw₀, zero_add, Matrix.smul_vecMul] at e
  exact (smul_eq_zero.1 e).resolve_left hδ.ne'

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 2): the quadratic form `w ↦ ⟨w M Y, w M⟩` vanishes everywhere if it vanishes on
a nonempty open set (`q(w₀ + δ v) + q(w₀ - δ v) = 2 q(w₀) + 2 δ² q(v)`). -/
private theorem quad_zero_of_isOpen_lss {m : Type*} [Fintype m] {G : Set (m → ℝ)}
    (hG : IsOpen G) (hne : G.Nonempty) {E : Matrix m d ℝ} {Y : Matrix d d ℝ}
    (h : ∀ w ∈ G, (w ᵥ* E) ᵥ* Y ⬝ᵥ (w ᵥ* E) = 0) (v : m → ℝ) :
    (v ᵥ* E) ᵥ* Y ⬝ᵥ (v ᵥ* E) = 0 := by
  obtain ⟨w₀, hw₀⟩ := hne
  obtain ⟨δ, hδ, hp, hm⟩ := exists_add_sub_mem_lss hG hw₀ v
  have e0 := h w₀ hw₀
  have ep := h _ hp
  have em := h _ hm
  simp only [Matrix.add_vecMul, Matrix.sub_vecMul, Matrix.smul_vecMul, dotProduct_add,
    add_dotProduct, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul] at ep em
  have e : (2 * δ ^ 2) * ((v ᵥ* E) ᵥ* Y ⬝ᵥ (v ᵥ* E)) = 0 := by
    linear_combination ep + em - 2 * e0
  have hδ2 : 2 * δ ^ 2 ≠ 0 := by positivity
  exact (mul_eq_zero.1 e).resolve_left hδ2

/-! ### Rays `x = s w`, `s → ∞` -/

/-- Helper: `c(v, y) = (‖v‖²/d + ε y²)^{-1/2}`; along the ray `s v`, `N_ε(s v) = c(v, 1/s) v`. -/
private noncomputable def c_lss (ε : ℝ) (v : d → ℝ) (y : ℝ) : ℝ :=
  (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε * y ^ 2))⁻¹

/-- Helper: the matrix with rows `c(a_t, y) a_t`, which is `N_ε(s a)` at `y = 1/s`. -/
private noncomputable def n_lss (ε : ℝ) (a : Matrix T d ℝ) (y : ℝ) : Matrix T d ℝ :=
  Matrix.of fun t => c_lss ε (a t) y • a t

/-- Helper: the matrix that is `𝐃N_ε(s a)(s b)` at `y = 1/s`. -/
private noncomputable def dn_lss (ε : ℝ) (a b : Matrix T d ℝ) (y : ℝ) : Matrix T d ℝ :=
  Matrix.of fun t => c_lss ε (a t) y • b t
    - ((a t ⬝ᵥ b t) / (Fintype.card d : ℝ) * c_lss ε (a t) y ^ 3) • a t

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `(‖s v‖²/d + ε)^{-1/2} = c(v, 1/s) / s` for `s > 0`. -/
private theorem inv_sqrt_smul_lss {ε s : ℝ} (hs : 0 < s) (v : d → ℝ) :
    (Real.sqrt ((s • v) ⬝ᵥ (s • v) / (Fintype.card d : ℝ) + ε))⁻¹ = c_lss ε v s⁻¹ * s⁻¹ := by
  unfold c_lss
  have e : (s • v) ⬝ᵥ (s • v) / (Fintype.card d : ℝ) + ε
      = s ^ 2 * ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε * s⁻¹ ^ 2) := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    field_simp
  rw [e, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le, mul_inv, mul_comm]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `N_ε(s a) = n(1/s)` for `s > 0`. -/
private theorem rmsNorm_smul_lss {ε s : ℝ} (hs : 0 < s) (a : Matrix T d ℝ) :
    rmsNorm ε (s • a) = n_lss ε a s⁻¹ := by
  funext t i
  show (Real.sqrt ((s • a t) ⬝ᵥ (s • a t) / (Fintype.card d : ℝ) + ε))⁻¹ * (s * a t i)
    = c_lss ε (a t) s⁻¹ * a t i
  rw [inv_sqrt_smul_lss hs, mul_assoc, inv_mul_cancel_left₀ hs.ne']

omit [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: `𝐃N_ε(s a)(s b) = dn(1/s)` for `s > 0`. -/
private theorem fderiv_rmsNorm_smul_lss {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s)
    (a b : Matrix T d ℝ) :
    fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (s • a) (s • b) = dn_lss ε a b s⁻¹ := by
  rw [fderiv_rmsNorm_apply hε]
  funext t i
  show (Real.sqrt ((s • a t) ⬝ᵥ (s • a t) / (Fintype.card d : ℝ) + ε))⁻¹ * (s * b t i)
      - ((s • a t) ⬝ᵥ (s • b t) / (Fintype.card d : ℝ)
        * (Real.sqrt ((s • a t) ⬝ᵥ (s • a t) / (Fintype.card d : ℝ) + ε))⁻¹ ^ 3) * (s * a t i)
    = c_lss ε (a t) s⁻¹ * b t i
      - ((a t ⬝ᵥ b t) / (Fintype.card d : ℝ) * c_lss ε (a t) s⁻¹ ^ 3) * a t i
  rw [inv_sqrt_smul_lss hs, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  field_simp

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `‖v‖²/d > 0` if `v ≠ 0`. -/
private theorem dot_self_div_pos_lss {v : d → ℝ} (hv : v ≠ 0) :
    0 < (v ⬝ᵥ v) / (Fintype.card d : ℝ) := by
  have h1 : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (dot_self_nonneg_lss v) (Ne.symm (mt dotProduct_self_eq_zero.1 hv))
  have h2 : (0 : ℝ) < Fintype.card d := by
    obtain ⟨i, -⟩ := Function.ne_iff.1 hv
    exact_mod_cast Fintype.card_pos_iff.2 ⟨i⟩
  positivity

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `c(v, 0) > 0` if `v ≠ 0`. -/
private theorem c_zero_pos_lss {ε : ℝ} {v : d → ℝ} (hv : v ≠ 0) : 0 < c_lss ε v 0 := by
  unfold c_lss
  refine inv_pos.2 (Real.sqrt_pos.2 ?_)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
  exact dot_self_div_pos_lss hv

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `y ↦ c(v, y)` is continuous at `0` if `v ≠ 0`. -/
private theorem continuousAt_c_lss {ε : ℝ} {v : d → ℝ} (hv : v ≠ 0) :
    ContinuousAt (c_lss ε v) 0 := by
  have hpos := dot_self_div_pos_lss hv
  have hc : Continuous fun y : ℝ => Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε * y ^ 2) := by
    fun_prop
  refine hc.continuousAt.inv₀ ?_
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
  exact (Real.sqrt_pos.2 hpos).ne'

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `n` and `dn` are continuous at `0` if every row of `a` is nonzero. -/
private theorem continuousAt_n_dn_lss {ε : ℝ} {a : Matrix T d ℝ} (ha : ∀ t, a t ≠ 0)
    (b : Matrix T d ℝ) : ContinuousAt (n_lss ε a) 0 ∧ ContinuousAt (dn_lss ε a b) 0 := by
  constructor
  · refine continuousAt_pi.2 fun t => continuousAt_pi.2 fun i => ?_
    show ContinuousAt (fun y => c_lss ε (a t) y * a t i) 0
    exact (continuousAt_c_lss (ha t)).mul continuousAt_const
  · refine continuousAt_pi.2 fun t => continuousAt_pi.2 fun i => ?_
    show ContinuousAt (fun y => c_lss ε (a t) y * b t i
      - ((a t ⬝ᵥ b t) / (Fintype.card d : ℝ) * c_lss ε (a t) y ^ 3) * a t i) 0
    exact ((continuousAt_c_lss (ha t)).mul continuousAt_const).sub
      ((continuousAt_const.mul ((continuousAt_c_lss (ha t)).pow 3)).mul continuousAt_const)

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if every row of `a` is nonzero and `a M ∈ V`, the limit `n(0) M` of `N_ε(s a) M` is in
`V` (`n(0)` scales the rows of `a` by positive numbers). -/
private theorem n_zero_mul_mem_lss {ε : ℝ} {r : Type*} {V : Set (Matrix T r ℝ)}
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    {a : Matrix T d ℝ} (ha : ∀ t, a t ≠ 0) {M : Matrix d r ℝ} (hM : a * M ∈ V) :
    n_lss ε a 0 * M ∈ V :=
  rowScale_mul_mem_lss hVs hM (c := fun t => c_lss ε (a t) 0) fun t => c_zero_pos_lss (ha t)

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (Step 2, large inputs): if every row of `w E` is nonzero and `f` is continuous at the
limit `n(0) W_read`, then `g(s w) / s → 0` as `s → ∞`. -/
private theorem tendsto_gOne_ray_lss {A : Arch T d 1} {ε : ℝ} (θ : Params A dIn dOut)
    (w : Matrix T dIn ℝ) (hw : ∀ t, (w * θ.E) t ≠ 0)
    (hfc : ContinuousAt (A.f 0) (n_lss ε (w * θ.E) 0 * θ.read 0)) :
    Tendsto (fun s : ℝ => s⁻¹ • gOne_lss A ε θ (s • w)) atTop (𝓝 0) := by
  have hn := (continuousAt_n_dn_lss (ε := ε) hw (w * θ.E)).1
  have hR : Continuous fun M : Matrix T d ℝ => M * θ.read 0 :=
    continuous_id.matrix_mul continuous_const
  have hW : Continuous fun N : Matrix T (A.w 0) ℝ => N * θ.write 0 :=
    continuous_id.matrix_mul continuous_const
  -- `Ψ(y) = f(n(y) W_read) W_write`, continuous at `0`
  have h1 : ContinuousAt (fun y => n_lss ε (w * θ.E) y * θ.read 0) 0 :=
    ContinuousAt.comp (f := n_lss ε (w * θ.E)) (x := 0) hR.continuousAt hn
  have h2 : ContinuousAt (fun y => A.f 0 (n_lss ε (w * θ.E) y * θ.read 0)) 0 :=
    ContinuousAt.comp (f := fun y => n_lss ε (w * θ.E) y * θ.read 0) (x := 0) hfc h1
  have hΨ : ContinuousAt (fun y => A.f 0 (n_lss ε (w * θ.E) y * θ.read 0) * θ.write 0) 0 :=
    ContinuousAt.comp (f := fun y => A.f 0 (n_lss ε (w * θ.E) y * θ.read 0)) (x := 0)
      hW.continuousAt h2
  have hlim := tendsto_inv_atTop_zero.smul (hΨ.tendsto.comp tendsto_inv_atTop_zero)
  rw [zero_smul] at hlim
  refine hlim.congr' ((eventually_gt_atTop 0).mono fun s hs => ?_)
  -- `g(s w) = Ψ(1/s)`
  show s⁻¹ • (A.f 0 (n_lss ε (w * θ.E) s⁻¹ * θ.read 0) * θ.write 0)
    = s⁻¹ • gOne_lss A ε θ (s • w)
  rw [gOne_lss, Matrix.smul_mul, rmsNorm_smul_lss hs]

omit [Nonempty T] [Fintype dOut] in
/-- Helper (Steps 2 and 3, large inputs): if every row of `w E` is nonzero and `f` and its
derivative are continuous at the limit `n(0) W_read`, then `(D_θ g η)(s w) / s → 0`. -/
private theorem tendsto_dgOne_ray_lss {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (θ η : Params A dIn dOut) (w : Matrix T dIn ℝ) (hw : ∀ t, (w * θ.E) t ≠ 0)
    (hfc : ContinuousAt (A.f 0) (n_lss ε (w * θ.E) 0 * θ.read 0))
    (hfdc : ContinuousAt (fderiv ℝ (A.f 0)) (n_lss ε (w * θ.E) 0 * θ.read 0)) :
    Tendsto (fun s : ℝ => s⁻¹ • dgOne_lss A ε θ η (s • w)) atTop (𝓝 0) := by
  obtain ⟨hn, hdn⟩ := continuousAt_n_dn_lss (ε := ε) hw (w * η.E)
  have hR : ∀ M : Matrix d (A.r 0) ℝ, Continuous fun N : Matrix T d ℝ => N * M := fun M =>
    continuous_id.matrix_mul continuous_const
  have h1 : ContinuousAt (fun y => n_lss ε (w * θ.E) y * θ.read 0) 0 :=
    ContinuousAt.comp (f := n_lss ε (w * θ.E)) (x := 0) (hR _).continuousAt hn
  have h2 : ContinuousAt (fun y => dn_lss ε (w * θ.E) (w * η.E) y * θ.read 0
      + n_lss ε (w * θ.E) y * η.read 0) 0 :=
    (ContinuousAt.comp (f := dn_lss ε (w * θ.E) (w * η.E)) (x := 0) (hR _).continuousAt hdn).add
      (ContinuousAt.comp (f := n_lss ε (w * θ.E)) (x := 0) (hR _).continuousAt hn)
  have h3 := (ContinuousAt.comp (f := fun y => n_lss ε (w * θ.E) y * θ.read 0) (x := (0 : ℝ))
    hfdc h1).clm_apply h2
  have hW : ∀ M : Matrix (A.w 0) d ℝ, Continuous fun N : Matrix T (A.w 0) ℝ => N * M := fun M =>
    continuous_id.matrix_mul continuous_const
  have h4 := ContinuousAt.comp (f := fun y => n_lss ε (w * θ.E) y * θ.read 0) (x := (0 : ℝ))
    hfc h1
  have hΦ := (ContinuousAt.comp (x := (0 : ℝ)) (hW (θ.write 0)).continuousAt h3).add
    (ContinuousAt.comp (x := (0 : ℝ)) (hW (η.write 0)).continuousAt h4)
  have hlim := tendsto_inv_atTop_zero.smul (hΦ.tendsto.comp tendsto_inv_atTop_zero)
  rw [zero_smul] at hlim
  refine hlim.congr' ((eventually_gt_atTop 0).mono fun s hs => ?_)
  -- `(D_θ g η)(s w) = Φ(1/s)`
  show s⁻¹ • (fderiv ℝ (A.f 0) (n_lss ε (w * θ.E) s⁻¹ * θ.read 0)
      (dn_lss ε (w * θ.E) (w * η.E) s⁻¹ * θ.read 0 + n_lss ε (w * θ.E) s⁻¹ * η.read 0)
        * θ.write 0
      + A.f 0 (n_lss ε (w * θ.E) s⁻¹ * θ.read 0) * η.write 0)
    = s⁻¹ • dgOne_lss A ε θ η (s • w)
  rw [dgOne_lss, Matrix.smul_mul, Matrix.smul_mul, rmsNorm_smul_lss hs,
    fderiv_rmsNorm_smul_lss hε hs]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (Steps 1 and 2, large inputs): `h_1(s w) / s → w E S` as `s → ∞`. -/
private theorem tendsto_hOne_ray_lss {A : Arch T d 1} {ε : ℝ} (θ : Params A dIn dOut)
    (S : Matrix d d ℝ) (w : Matrix T dIn ℝ) (hw : ∀ t, (w * θ.E) t ≠ 0)
    (hfc : ContinuousAt (A.f 0) (n_lss ε (w * θ.E) 0 * θ.read 0)) :
    Tendsto (fun s : ℝ => s⁻¹ • hOne_lss A ε θ S (s • w)) atTop (𝓝 (w * θ.E * S)) := by
  have hlim := (tendsto_const_nhds (x := w * θ.E * S)).add (tendsto_gOne_ray_lss θ w hw hfc)
  rw [add_zero] at hlim
  refine hlim.congr' ((eventually_gt_atTop 0).mono fun s hs => ?_)
  -- `h_1(s w) = s (w E S) + g(s w)`
  show w * θ.E * S + s⁻¹ • gOne_lss A ε θ (s • w) = s⁻¹ • hOne_lss A ε θ S (s • w)
  rw [hOne_lss, smul_add, Matrix.smul_mul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hs.ne',
    one_smul]

omit [Nonempty T] [Fintype dOut] in
/-- Helper (Steps 2 and 3, large inputs): `k(s w) / s → w η_E S + w E σ` as `s → ∞`. -/
private theorem tendsto_kOne_ray_lss {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (θ η : Params A dIn dOut) (S σ : Matrix d d ℝ) (w : Matrix T dIn ℝ)
    (hw : ∀ t, (w * θ.E) t ≠ 0)
    (hfc : ContinuousAt (A.f 0) (n_lss ε (w * θ.E) 0 * θ.read 0))
    (hfdc : ContinuousAt (fderiv ℝ (A.f 0)) (n_lss ε (w * θ.E) 0 * θ.read 0)) :
    Tendsto (fun s : ℝ => s⁻¹ • kOne_lss A ε θ η S σ (s • w)) atTop
      (𝓝 (w * η.E * S + w * θ.E * σ)) := by
  have hlim := (tendsto_const_nhds (x := w * η.E * S + w * θ.E * σ)).add
    (tendsto_dgOne_ray_lss hε θ η w hw hfc hfdc)
  rw [add_zero] at hlim
  refine hlim.congr' ((eventually_gt_atTop 0).mono fun s hs => ?_)
  -- `k(s w) = s (w η_E S + w E σ) + (D_θ g η)(s w)`
  show w * η.E * S + w * θ.E * σ + s⁻¹ • dgOne_lss A ε θ η (s • w)
    = s⁻¹ • kOne_lss A ε θ η S σ (s • w)
  simp only [kOne_lss, smul_add, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

end HelpersLss

/-- **Proof of Theorem B.1 (iii) of the skips paper, Steps 1 to 3, for one block with a full
learned skip under pre-RMSNorm, `ε > 0`:** let `f` be continuously differentiable on an open set
`V` that is invariant under positive scalings of the rows, let `E` and `D` have rank `d`, let the
skip `A = R 0` be invertible, and let some input with equal rows have its pre-activation
`x E W_read` in `V`. If the direction `(η, η_A)` of the weights and the skip is flat at every input
`x` with `x E W_read ∈ V`, there are a matrix `X` and an antisymmetric `Y` with `η_E = E X`,
`η_A = A Y − X A`, `η_D = −Y D`, and at every such input the derivative of the output
`g(x) = f(N_ε(x E) W_read) W_write` of the block along `η` is `g(x) Y`. -/
theorem exists_of_flatSkipsOn_learned_rmsNorm {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (V : Set (Matrix T (A.r 0) ℝ)) (hV : IsOpen V)
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    (hf : ContDiffOn ℝ 1 (A.f 0) V) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) (hR : IsUnit (R 0).det)
    (hw : ∃ w : dIn → ℝ, (Matrix.of fun _ : T => w) * θ.E * θ.read 0 ∈ V)
    (η : Params A dIn dOut) (ρ : Fin 1 → Matrix d d ℝ)
    (hη : (η, ρ) ∈ flatSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
      {x | x * θ.E * θ.read 0 ∈ V}) :
    ∃ X Y : Matrix d d ℝ, Yᵀ = -Y ∧ η.E = θ.E * X ∧ ρ 0 = R 0 * Y - X * R 0 ∧
      η.D = -(Y * θ.D) ∧
      ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
        fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
            (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * θ.E * X)
                * θ.read 0
              + rmsNorm ε (x * θ.E) * η.read 0) * θ.write 0
          + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * η.write 0
          = A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * θ.write 0 * Y := by
  -- no coordinates: every matrix with a side indexed by `d` is `0`
  rcases isEmpty_or_nonempty d with hd0 | hd0
  · refine ⟨0, 0, ?_, ?_, ?_, ?_, fun x _ => ?_⟩ <;> funext i j
    · exact isEmptyElim i
    · exact isEmptyElim j
    · exact isEmptyElim i
    · exact isEmptyElim i
    · exact isEmptyElim j
  classical
  have hd : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos
  -- at an input `x` of `U` (`x E W_read ∈ V`), `N_ε(x E) W_read` is in the open set `V` (a
  -- positive scaling of the rows of `x E W_read`), so `f` is differentiable there
  have hfx : ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
      DifferentiableAt ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0) := fun x hx =>
    (hf.contDiffAt (hV.mem_nhds (rmsNorm_mul_mem_lss hε hVs hx))).differentiableAt one_ne_zero
  -- a right inverse `D⁺` of `D`, and `Y = -η_D D⁺`
  obtain ⟨Dp, hDp⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1
    (Matrix.mulVec_surjective_iff_rank_eq_card.2 hD)
  obtain ⟨Y, hYdef⟩ : ∃ Y : Matrix d d ℝ, Y = -(η.D * Dp) := ⟨_, rfl⟩
  -- Step 0 for `(η, ρ)` at the inputs of `U`: `𝐃N_ε(h_1) k D + N_ε(h_1) η_D = 0`
  have h0 : ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
      fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (hOne_lss A ε θ (R 0) x)
          (kOne_lss A ε θ η (R 0) (ρ 0) x) * θ.D
        + rmsNorm ε (hOne_lss A ε θ (R 0) x) * η.D = 0 := fun x hx =>
    flat_eq_lss hε hA θ η R ρ x (hfx x hx) (fderiv_eq_zero_of_flatSkipsOn_lss hη hx)
  -- Step 1: times `D⁺`, `𝐃N_ε(h_1) k = N_ε(h_1) Y`
  have hNY : ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
      fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (hOne_lss A ε θ (R 0) x)
        (kOne_lss A ε θ η (R 0) (ρ 0) x) = rmsNorm ε (hOne_lss A ε θ (R 0) x) * Y := by
    intro x hx
    have e := congrArg (· * Dp) (h0 x hx)
    simp only [Matrix.add_mul, Matrix.mul_assoc, hDp, Matrix.mul_one, Matrix.zero_mul] at e
    rw [hYdef, Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left e
  -- hence `k = h_1 Y + μ ⊙ h_1`, since `𝐃N_ε(h_1)` is injective
  have hk : ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V → kOne_lss A ε θ η (R 0) (ρ 0) x
      = hOne_lss A ε θ (R 0) x * Y + muScale_lss ε Y (hOne_lss A ε θ (R 0) x) := fun x hx =>
    injective_fderiv_rmsNorm hε _ (by rw [hNY x hx, fderiv_rmsNorm_muScale_lss hε hd])
  -- and, substituting back, `N_ε(h_1) (Y D + η_D) = 0`, so `h_1 (Y D + η_D) = 0`
  have hZ : ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
      hOne_lss A ε θ (R 0) x * (Y * θ.D + η.D) = 0 := by
    intro x hx
    refine mul_eq_zero_of_rmsNorm_mul_lss hε _ _ ?_
    have e := h0 x hx
    rw [hNY x hx] at e
    rw [Matrix.mul_add, ← Matrix.mul_assoc]
    exact e
  -- the rows `w₀` with `w₀ E ≠ 0` and `w₀ E W_read ∈ V` (all rows equal to `w₀`): an open set `G`
  have hc1 : Continuous fun w₀ : dIn → ℝ => (Matrix.of fun _ : T => w₀) * θ.E * θ.read 0 :=
    ((continuous_pi fun _ => continuous_id).matrix_mul continuous_const).matrix_mul
      continuous_const
  obtain ⟨G, hGdef⟩ : ∃ G : Set (dIn → ℝ),
      G = {w₀ | (Matrix.of fun _ : T => w₀) * θ.E * θ.read 0 ∈ V ∧ w₀ ᵥ* θ.E ≠ 0} := ⟨_, rfl⟩
  have hGo : IsOpen G := by
    rw [hGdef]
    exact (hV.preimage hc1).inter
      (isOpen_ne_fun (continuous_id.matrix_vecMul continuous_const) continuous_const)
  -- `G` is not empty: from `w₀` of `hw`, move along a `u` with `u E ≠ 0` if `w₀ E = 0`
  have hGne : G.Nonempty := by
    obtain ⟨w₀, hw₀⟩ := hw
    rw [hGdef]
    by_cases h : w₀ ᵥ* θ.E = 0
    · obtain ⟨u, hu⟩ := Matrix.vecMul_surjective_iff_rank_eq_card.2 hE (fun _ => 1)
      obtain ⟨δ, hδ, hδV, -⟩ := exists_add_sub_mem_lss (hV.preimage hc1) hw₀ u
      have hu' : u ᵥ* θ.E = fun _ => 1 := hu
      refine ⟨w₀ + δ • u, hδV, ?_⟩
      rw [Matrix.add_vecMul, h, zero_add, Matrix.smul_vecMul, hu']
      intro h1
      have h2 := congrFun h1 (Classical.arbitrary d)
      simp only [Pi.smul_apply, smul_eq_mul, mul_one, Pi.zero_apply] at h2
      exact hδ.ne' h2
    · exact ⟨w₀, hw₀, h⟩
  -- along the ray `s w`, `w` with all rows `w₀ ∈ G`: the inputs `s w` are in `U`, the rows of
  -- `w E` are nonzero, and `f` and its derivative are continuous at the limit `n(0) W_read ∈ V`
  have hray : ∀ w₀ ∈ G,
      (∀ s : ℝ, 0 < s → (s • Matrix.of fun _ : T => w₀) * θ.E * θ.read 0 ∈ V) ∧
      (∀ t, ((Matrix.of fun _ : T => w₀) * θ.E) t ≠ 0) ∧
      ContinuousAt (A.f 0) (n_lss ε ((Matrix.of fun _ : T => w₀) * θ.E) 0 * θ.read 0) ∧
      ContinuousAt (fderiv ℝ (A.f 0))
        (n_lss ε ((Matrix.of fun _ : T => w₀) * θ.E) 0 * θ.read 0) := by
    intro w₀ hw₀
    rw [hGdef] at hw₀
    have hrows : ∀ t, ((Matrix.of fun _ : T => w₀) * θ.E) t ≠ 0 := fun t => by
      rw [constRows_mul_lss]
      exact hw₀.2
    have hP := hV.mem_nhds (n_zero_mul_mem_lss (ε := ε) hVs hrows hw₀.1)
    refine ⟨fun s hs => ?_, hrows, hf.continuousOn.continuousAt hP,
      (hf.continuousOn_fderiv_of_isOpen hV le_rfl).continuousAt hP⟩
    rw [Matrix.smul_mul]
    exact smul_mul_mem_lss hVs hw₀.1 hs
  -- at the inputs `s w`, `s → ∞`: `(w₀ E S)(Y D + η_D) = 0` for `w₀ ∈ G`, hence
  -- `E S (Y D + η_D) = 0` (linear in `w₀`, on an open set), and `η_D = -Y D` since `E S` has
  -- rank `d`
  have hZ0 : Y * θ.D + η.D = 0 := by
    have h1 : ∀ w₀ ∈ G, w₀ ᵥ* (θ.E * R 0 * (Y * θ.D + η.D)) = 0 := by
      intro w₀ hw₀
      obtain ⟨hU, hrows, hfc, -⟩ := hray w₀ hw₀
      have hc : Continuous fun M : Matrix T d ℝ => M * (Y * θ.D + η.D) :=
        continuous_id.matrix_mul continuous_const
      have hlim := (hc.tendsto _).comp (tendsto_hOne_ray_lss θ (R 0) _ hrows hfc)
      have hlim0 : Filter.Tendsto
          (fun s : ℝ => (s⁻¹ • hOne_lss A ε θ (R 0) (s • Matrix.of fun _ : T => w₀))
            * (Y * θ.D + η.D)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.congr' ((Filter.eventually_gt_atTop 0).mono fun s hs => by
          dsimp only
          rw [Matrix.smul_mul, hZ _ (hU s hs), smul_zero])
      have e := tendsto_nhds_unique hlim hlim0
      rw [Matrix.mul_assoc (Matrix.of fun _ : T => w₀) θ.E (R 0)] at e
      rw [← Matrix.vecMul_vecMul,
        ← constRows_mul_lss (T := T) w₀ (θ.E * R 0) (Classical.arbitrary T),
        ← Matrix.mul_apply_eq_vecMul, e]
      rfl
    have h2 := eq_zero_of_vecMul_on_lss hGo hGne h1
    refine eq_zero_of_vecMul_lss fun u => ?_
    obtain ⟨w₀, rfl⟩ := exists_vecMul_mul_eq_lss hE hR u
    rw [Matrix.vecMul_vecMul, h2, Matrix.vecMul_zero]
  have hYD : η.D = -(Y * θ.D) := eq_neg_of_add_eq_zero_right hZ0
  -- Step 2: the terms of order `s³` at the inputs `s w` give `⟨v Y, v⟩ = 0` for `v = w₀ E S`,
  -- `w₀ ∈ G`; a quadratic form that vanishes on an open set vanishes, and every `u` is a `w₀ E S`
  have hq : ∀ u : d → ℝ, u ᵥ* Y ⬝ᵥ u = 0 := by
    have h1 : ∀ w₀ ∈ G, (w₀ ᵥ* (θ.E * R 0)) ᵥ* Y ⬝ᵥ (w₀ ᵥ* (θ.E * R 0)) = 0 := by
      intro w₀ hw₀
      obtain ⟨hU, hrows, hfc, hfdc⟩ := hray w₀ hw₀
      have hu := tendsto_hOne_ray_lss θ (R 0) _ hrows hfc
      have hv := tendsto_kOne_ray_lss hε θ η (R 0) (ρ 0) _ hrows hfc hfdc
      have h1 := ((continuous_muScale_lss ε Y).tendsto _).comp hu
      have hc : Continuous fun M : Matrix T d ℝ => M * Y :=
        continuous_id.matrix_mul continuous_const
      have h2 := (tendsto_inv_atTop_zero.pow 2).smul (hv.sub ((hc.tendsto _).comp hu))
      rw [zero_pow two_ne_zero, zero_smul] at h2
      -- the identity of Step 1 at `s w`, divided by `s³`
      have heq : ∀ s : ℝ, 0 < s →
          (s⁻¹) ^ 2 • (s⁻¹ • kOne_lss A ε θ η (R 0) (ρ 0) (s • Matrix.of fun _ : T => w₀)
            - (s⁻¹ • hOne_lss A ε θ (R 0) (s • Matrix.of fun _ : T => w₀)) * Y)
          = muScale_lss ε Y (s⁻¹ • hOne_lss A ε θ (R 0) (s • Matrix.of fun _ : T => w₀)) := by
        intro s hs
        rw [hk _ (hU s hs), muScale_smul_lss, Matrix.smul_mul, smul_add, add_sub_cancel_left,
          smul_smul, ← pow_succ]
      have h12 := tendsto_nhds_unique h1 (h2.congr' ((Filter.eventually_gt_atTop 0).mono heq))
      -- row `t`: `μ(w₀ E S) w₀ E S = 0` with `w₀ E S ≠ 0`
      have hrow : mu_lss ε Y (((Matrix.of fun _ : T => w₀) * θ.E * R 0) (Classical.arbitrary T))
          • ((Matrix.of fun _ : T => w₀) * θ.E * R 0) (Classical.arbitrary T) = 0 :=
        congrFun h12 (Classical.arbitrary T)
      rw [Matrix.mul_assoc, constRows_mul_lss] at hrow
      have hne : w₀ ᵥ* (θ.E * R 0) ≠ 0 := by
        refine vecMul_mul_ne_zero_lss hR ?_
        rw [← constRows_mul_lss (T := T) w₀ θ.E (Classical.arbitrary T)]
        exact hrows _
      have hmu := (smul_eq_zero.1 hrow).resolve_right hne
      unfold mu_lss at hmu
      exact (div_eq_zero_iff.1 hmu).resolve_right (mul_pos hd hε).ne'
    intro u
    obtain ⟨v, rfl⟩ := exists_vecMul_mul_eq_lss hE hR u
    exact quad_zero_of_isOpen_lss hGo hGne h1 v
  have hY : Yᵀ = -Y := transpose_eq_neg_lss hq
  -- `μ = 0` for an antisymmetric `Y`, so `k = h_1 Y` at every input of `U`
  have hk2 : ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
      kOne_lss A ε θ η (R 0) (ρ 0) x = hOne_lss A ε θ (R 0) x * Y := by
    intro x hx
    have hμ : muScale_lss ε Y (hOne_lss A ε θ (R 0) x) = 0 := by
      funext t i
      show mu_lss ε Y (hOne_lss A ε θ (R 0) x t) * hOne_lss A ε θ (R 0) x t i = 0
      rw [mu_lss, hq, zero_div, zero_mul]
    rw [hk x hx, hμ, add_zero]
  -- Step 3: the terms of order `s` at the inputs `s w` give `w₀ (η_E S + E σ) = w₀ E S Y` for
  -- `w₀ ∈ G`, hence `η_E S + E σ = E S Y`
  have hES : η.E * R 0 + θ.E * ρ 0 = θ.E * R 0 * Y := by
    have hK : η.E * R 0 + θ.E * ρ 0 - θ.E * R 0 * Y = 0 := by
      refine eq_zero_of_vecMul_on_lss hGo hGne fun w₀ hw₀ => ?_
      obtain ⟨hU, hrows, hfc, hfdc⟩ := hray w₀ hw₀
      have hc : Continuous fun M : Matrix T d ℝ => M * Y :=
        continuous_id.matrix_mul continuous_const
      have hlim := (hc.tendsto _).comp (tendsto_hOne_ray_lss θ (R 0) _ hrows hfc)
      have hv := tendsto_kOne_ray_lss hε θ η (R 0) (ρ 0) _ hrows hfc hfdc
      have e := tendsto_nhds_unique hv
        (hlim.congr' ((Filter.eventually_gt_atTop 0).mono fun s hs => by
          show (s⁻¹ • hOne_lss A ε θ (R 0) (s • Matrix.of fun _ : T => w₀)) * Y
            = s⁻¹ • kOne_lss A ε θ η (R 0) (ρ 0) (s • Matrix.of fun _ : T => w₀)
          rw [hk2 _ (hU s hs), Matrix.smul_mul]))
      have hK0 : (Matrix.of fun _ : T => w₀) * (η.E * R 0 + θ.E * ρ 0 - θ.E * R 0 * Y) = 0 := by
        simp only [Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc]
        exact sub_eq_zero.2 e
      have e2 := congrFun hK0 (Classical.arbitrary T)
      rwa [constRows_mul_lss] at e2
    exact sub_eq_zero.1 hK
  -- `X = S Y S⁻¹ - σ S⁻¹`: then `η_E = E X` and `σ = S Y - X S`
  obtain ⟨X, hXdef⟩ : ∃ X : Matrix d d ℝ, X = R 0 * Y * (R 0)⁻¹ - ρ 0 * (R 0)⁻¹ := ⟨_, rfl⟩
  have hEX : η.E = θ.E * X := by
    calc η.E = η.E * R 0 * (R 0)⁻¹ := (Matrix.mul_nonsing_inv_cancel_right _ _ hR).symm
      _ = (θ.E * R 0 * Y - θ.E * ρ 0) * (R 0)⁻¹ := by rw [← hES, add_sub_cancel_right]
      _ = θ.E * X := by
        rw [hXdef]
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  have hρ : ρ 0 = R 0 * Y - X * R 0 := by
    rw [hXdef, Matrix.sub_mul, Matrix.nonsing_inv_mul_cancel_right _ _ hR,
      Matrix.nonsing_inv_mul_cancel_right _ _ hR, sub_sub_cancel]
  refine ⟨X, Y, hY, hEX, hρ, hYD, fun x hx => ?_⟩
  -- at an input of `U`: `k = x E S Y + D_θ g η` and `h_1 Y = x E S Y + g(x) Y`
  have e := hk2 x hx
  have hxs : x * η.E * R 0 + x * θ.E * ρ 0 = x * θ.E * R 0 * Y := by
    rw [Matrix.mul_assoc x η.E, Matrix.mul_assoc x θ.E (ρ 0), ← Matrix.mul_add, hES]
    simp only [Matrix.mul_assoc]
  rw [kOne_lss, hOne_lss, Matrix.add_mul, hxs] at e
  have e2 := add_left_cancel e
  rw [dgOne_lss, gOne_lss, hEX, ← Matrix.mul_assoc x θ.E X] at e2
  exact e2

end Skips
