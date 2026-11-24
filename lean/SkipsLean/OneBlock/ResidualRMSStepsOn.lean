import SkipsLean.OneBlock.ResidualRMSSteps

/-!
# One residual block under pre-RMSNorm, Steps 1 to 3, for a block that is smooth on an open cone

Paper (skips paper): proof of Theorem B.1 (ii), Steps 1 to 3, for `ε > 0` and no biases, as in
`OneBlock/ResidualRMSSteps.lean`, where the fixed map `f` of the block is continuously
differentiable everywhere and the direction `η` is flat at every input.

For ReLU, ReLU² and ReGLU blocks the paper takes the same steps at the inputs at which no hidden
unit sits at its kink ("Notation and flat directions": "For the ReLU-type activations, `F(θ, x)`
is differentiable in `θ` at the inputs `x` at which no hidden unit sits at its kink, which form an
open set of full measure, and 'every input' means every such input"), and in Step 4: "For the
ReLU-type activations without biases the kinks lie on hyperplanes through the center of the
ball".

Stated here: the statement of `exists_antisymm_of_flat_residual_rmsNorm` for a fixed map `f` that
is continuously differentiable on an open set `V` of pre-activations that is invariant under the
scaling of every row by a positive number (for a ReLU block: the matrices with no zero entry),
and for a direction `η` that is flat at the inputs `x` with `x E W_read ∈ V`. One input with equal
rows must lie in this set (the steps use the rays `x = s w`, `s → ∞`, with `w` in an open set).
The conclusion is that of the earlier statement, at these inputs: an antisymmetric `Y` with
`η_E = E Y`, `η_D = −Y D`, and the derivative of `n ↦ f(n W_read) W_write` along the entries of
`η' = η − η^Y` vanishes at `n = N_ε(x E)`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

section HelpersSon

open Filter
open scoped Topology

/-! ### Step 0: the chain rule along a line of parameters, at an input of `U` -/

/-- Helper: the hidden state `h_1 = x E + f(N_ε(x E) W_read) W_write` of one residual block. -/
private noncomputable def hOne_son (A : Arch T d 1) (ε : ℝ) (θ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T d ℝ :=
  x * θ.E + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * θ.write 0

/-- Helper: the derivative `k(x)` of `h_1` along `η` (Step 0). -/
private noncomputable def kOne_son (A : Arch T d 1) (ε : ℝ) (θ η : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T d ℝ :=
  x * η.E + fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
      (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * η.E) * θ.read 0
        + rmsNorm ε (x * θ.E) * η.read 0) * θ.write 0
    + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * η.write 0

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the function of one residual block under pre-RMSNorm, `F_θ(x) = N_ε(h_1) D`. -/
private theorem eval_eq_son {A : Arch T d 1} {ε : ℝ} (hA : A.χ = rmsNorm ε)
    (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    eval A 1 θ x = rmsNorm ε (hOne_son A ε θ x) * θ.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]
  simp only [Pi.one_apply, Matrix.mul_one]
  rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product rule for matrices depending on one real variable. -/
private theorem hasDerivAt_mul_son {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
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
private theorem hasDerivAt_affine_son {m n : Type*} [Fintype m] [Fintype n]
    (M N : Matrix m n ℝ) : HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

omit [Nonempty T] [Fintype dOut] in
/-- Helper (Step 0): along the line `θ + τ η`, the hidden state `h_1` has the derivative `k(x)`
at `τ = 0`, if `f` is differentiable at `N_ε(x E) W_read`. -/
private theorem hasDerivAt_hOne_line_son {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (θ η : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (hfx : DifferentiableAt ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)) :
    HasDerivAt (fun τ : ℝ => hOne_son A ε (θ + τ • η) x) (kOne_son A ε θ η x) 0 := by
  -- `x E(τ)`
  have hE : HasDerivAt (fun τ : ℝ => x * (θ + τ • η).E) (x * η.E) 0 := by
    have h := hasDerivAt_mul_son (hasDerivAt_const (0 : ℝ) x) (hasDerivAt_affine_son θ.E η.E)
      (P0 := x) (Q0 := θ.E) rfl (by simp)
    rw [Matrix.zero_mul, zero_add] at h
    exact h
  -- `N_ε(x E(τ))`
  have hN : HasDerivAt (fun τ : ℝ => rmsNorm ε (x * (θ + τ • η).E))
      (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * η.E)) 0 :=
    ((differentiable_rmsNorm hε) (x * θ.E)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hE
      (by simp)
  -- `N_ε(x E(τ)) W_read(τ)`
  have hNR := hasDerivAt_mul_son hN (hasDerivAt_affine_son (θ.read 0) (η.read 0))
    (P0 := rmsNorm ε (x * θ.E)) (Q0 := θ.read 0) (by simp) (by simp)
  -- `f(N_ε(x E(τ)) W_read(τ))`: `f` is differentiable at the point of `τ = 0`
  have hF := hfx.hasFDerivAt.comp_hasDerivAt_of_eq 0 hNR (by simp)
  -- `f(…) W_write(τ)`
  have hFW := hasDerivAt_mul_son hF (hasDerivAt_affine_son (θ.write 0) (η.write 0))
    (P0 := A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0)) (Q0 := θ.write 0) (by simp) (by simp)
  have h := hE.add hFW
  rw [← add_assoc] at h
  exact h

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two matrix-valued maps that are differentiable at a point is
differentiable there (matrix multiplication is a continuous bilinear map). -/
private theorem differentiableAt_matMul_son {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
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
differentiable function of the parameters at `θ`. -/
private theorem differentiableAt_eval_son {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (hfx : DifferentiableAt ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)) :
    DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' x) θ := by
  have e : (fun θ' : Params A dIn dOut => eval A 1 θ' x)
      = fun θ' => rmsNorm ε (hOne_son A ε θ' x) * θ'.D :=
    funext fun θ' => eval_eq_son hA θ' x
  rw [e]
  -- the weights are linear, hence differentiable, functions of the parameters
  have hE : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => θ'.E) θ :=
    (LinearMap.toContinuousLinearMap
      (Params.linE (A := A) (dIn := dIn) (dOut := dOut))).differentiableAt
  have hR : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => θ'.read 0) θ :=
    (LinearMap.toContinuousLinearMap
      (Params.linRead (A := A) (dIn := dIn) (dOut := dOut) 0)).differentiableAt
  have hW : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => θ'.write 0) θ :=
    (LinearMap.toContinuousLinearMap
      (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) 0)).differentiableAt
  have hD : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => θ'.D) θ :=
    (LinearMap.toContinuousLinearMap
      (Params.linD (A := A) (dIn := dIn) (dOut := dOut))).differentiableAt
  -- `x E`, `N_ε(x E)` and `N_ε(x E) W_read`
  have h1 : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => x * θ'.E) θ :=
    differentiableAt_matMul_son (differentiableAt_const x) hE
  have h2 : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => rmsNorm ε (x * θ'.E)) θ :=
    DifferentiableAt.comp (f := fun θ' : Params A dIn dOut => x * θ'.E) θ
      (differentiable_rmsNorm hε _) h1
  have h3 : DifferentiableAt ℝ
      (fun θ' : Params A dIn dOut => rmsNorm ε (x * θ'.E) * θ'.read 0) θ :=
    differentiableAt_matMul_son h2 hR
  -- `f` is differentiable at `N_ε(x E) W_read`
  have h4 : DifferentiableAt ℝ
      (fun θ' : Params A dIn dOut => A.f 0 (rmsNorm ε (x * θ'.E) * θ'.read 0)) θ :=
    DifferentiableAt.comp (f := fun θ' : Params A dIn dOut => rmsNorm ε (x * θ'.E) * θ'.read 0)
      θ hfx h3
  -- `h_1`, `N_ε(h_1)` and `N_ε(h_1) D`
  have h5 : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => hOne_son A ε θ' x) θ :=
    h1.add (differentiableAt_matMul_son h4 hW)
  have h6 : DifferentiableAt ℝ
      (fun θ' : Params A dIn dOut => rmsNorm ε (hOne_son A ε θ' x)) θ :=
    DifferentiableAt.comp (f := fun θ' : Params A dIn dOut => hOne_son A ε θ' x) θ
      (differentiable_rmsNorm hε _) h5
  exact differentiableAt_matMul_son h6 hD

omit [Fintype T] [Nonempty T] in
/-- Helper: a direction that is flat at the inputs of `U` has derivative `0` at an input of `U`. -/
private theorem fderiv_eq_zero_of_flatOn_son {A : Arch T d 1} {θ η : Params A dIn dOut}
    {U : Set (Matrix T dIn ℝ)} (hη : η ∈ flatOn A 1 θ U) {x : Matrix T dIn ℝ} (hx : x ∈ U) :
    fderiv ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' x) θ η = 0 :=
  LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hη x) hx)

omit [Nonempty T] in
/-- Helper (Step 0): at an input `x` at which `f` is differentiable at `N_ε(x E) W_read` and
along which `η` is flat, `𝐃N_ε(h_1) k(x) D + N_ε(h_1) η_D = 0`. -/
private theorem flat_eq_son {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (θ η : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (hfx : DifferentiableAt ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0))
    (h0 : fderiv ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' x) θ η = 0) :
    fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (hOne_son A ε θ x) (kOne_son A ε θ η x)
        * θ.D + rmsNorm ε (hOne_son A ε θ x) * η.D = 0 := by
  -- flatness: the derivative along the line is `0`
  have h1 := hasDerivAt_eval_line (A := A) 1 θ η x (differentiableAt_eval_son hε hA θ x hfx)
  rw [h0] at h1
  -- the same derivative by the chain rule
  have hh := hasDerivAt_hOne_line_son hε θ η x hfx
  have hN := ((differentiable_rmsNorm (T := T) (d := d) hε) (hOne_son A ε θ x)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hh (by simp)
  have h2 := hasDerivAt_mul_son hN (hasDerivAt_affine_son θ.D η.D)
    (P0 := rmsNorm ε (hOne_son A ε θ x)) (Q0 := θ.D) (by simp) (by simp)
  have e : (fun τ : ℝ => eval A 1 (θ + τ • η) x)
      = fun τ => rmsNorm ε (hOne_son A ε (θ + τ • η) x) * (θ.D + τ • η.D) := by
    funext τ
    rw [eval_eq_son hA]
    rfl
  rw [e] at h1
  exact h2.unique h1

/-! ### Step 1: algebra of the final normalization -/

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `0 ≤ ⟨v, v⟩`. -/
private theorem dot_self_nonneg_son (v : d → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- Helper: the coefficient `μ(v) = ⟨v Y, v⟩ / (d ε)` of Step 1. -/
private noncomputable def mu_son (ε : ℝ) (Y : Matrix d d ℝ) (v : d → ℝ) : ℝ :=
  (v ᵥ* Y ⬝ᵥ v) / ((Fintype.card d : ℝ) * ε)

/-- Helper: the matrix whose row `t` is `μ(h_t) h_t`. -/
private noncomputable def muScale_son (ε : ℝ) (Y : Matrix d d ℝ) (h : Matrix T d ℝ) :
    Matrix T d ℝ :=
  Matrix.of fun t => mu_son ε Y (h t) • h t

omit [Nonempty T] in
/-- Helper (Step 1): `𝐃N_ε(h) (h Y + μ ⊙ h) = N_ε(h) Y`. -/
private theorem fderiv_rmsNorm_muScale_son {ε : ℝ} (hε : 0 < ε)
    (hd : (0 : ℝ) < Fintype.card d) (h : Matrix T d ℝ) (Y : Matrix d d ℝ) :
    fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) h (h * Y + muScale_son ε Y h)
      = rmsNorm ε h * Y := by
  rw [fderiv_rmsNorm_apply hε]
  funext t i
  have hpos : 0 < (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε := by
    have := dot_self_nonneg_son (h t)
    positivity
  have hR : (rmsNorm ε h * Y) t
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ • (h t ᵥ* Y) := by
    rw [Matrix.mul_apply_eq_vecMul]
    show rmsRow ε (h t) ᵥ* Y = _
    rw [rmsRow, Matrix.smul_vecMul]
  have hU : (h * Y + muScale_son ε Y h) t = h t ᵥ* Y + mu_son ε Y (h t) • h t := by
    rfl
  rw [hR]
  simp only [Matrix.of_apply, hU]
  have hs2 := Real.sq_sqrt hpos.le
  have hs := Real.sqrt_pos.2 hpos
  generalize Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε) = s at hs hs2
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct_add,
    dotProduct_smul, mu_son]
  rw [dotProduct_comm (h t) (h t ᵥ* Y)]
  field_simp
  have hs2' : s ^ 2 * (Fintype.card d : ℝ) = h t ⬝ᵥ h t + ε * Fintype.card d := by
    rw [hs2]
    field_simp
  linear_combination ((h t ᵥ* Y ⬝ᵥ h t) * h t i) * hs2'

/-! ### Linear algebra -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix `Z` with `u Z = 0` for every row vector `u` is `0`. -/
private theorem eq_zero_of_vecMul_son {m n : Type*} [Fintype m] [DecidableEq m]
    {Z : Matrix m n ℝ} (h : ∀ u : m → ℝ, u ᵥ* Z = 0) : Z = 0 := by
  ext i j
  have := congrFun (h (Pi.single i 1)) j
  rwa [Matrix.single_one_vecMul, Matrix.row_apply] at this

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper (polarisation): if `⟨u Y, u⟩ = 0` for every `u`, then `Yᵀ = -Y`. -/
private theorem transpose_eq_neg_son {Y : Matrix d d ℝ} (h : ∀ u : d → ℝ, u ᵥ* Y ⬝ᵥ u = 0) :
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
private theorem mul_eq_zero_of_rmsNorm_mul_son {ε : ℝ} (hε : 0 < ε) {m : Type*} [Fintype m]
    (h : Matrix T d ℝ) (Z : Matrix d m ℝ) (hZ : rmsNorm ε h * Z = 0) : h * Z = 0 := by
  funext t
  have hpos : 0 < (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε := by
    have := dot_self_nonneg_son (h t)
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
private theorem constRows_mul_son {m : Type*} (w₀ : dIn → ℝ) (M : Matrix dIn m ℝ) (t : T) :
    ((Matrix.of fun _ : T => w₀) * M) t = w₀ ᵥ* M := by
  rw [Matrix.mul_apply_eq_vecMul]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `μ ⊙ h` is homogeneous of degree `3`. -/
private theorem muScale_smul_son (ε : ℝ) (Y : Matrix d d ℝ) (c : ℝ) (h : Matrix T d ℝ) :
    muScale_son ε Y (c • h) = c ^ 3 • muScale_son ε Y h := by
  funext t i
  show mu_son ε Y (c • h t) * (c * h t i) = c ^ 3 * (mu_son ε Y (h t) * h t i)
  simp only [mu_son, Matrix.smul_vecMul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `h ↦ μ ⊙ h` is continuous. -/
private theorem continuous_muScale_son (ε : ℝ) (Y : Matrix d d ℝ) :
    Continuous (muScale_son (T := T) ε Y) := by
  refine continuous_pi fun t => continuous_pi fun i => ?_
  show Continuous fun h : Matrix T d ℝ => mu_son ε Y (h t) * h t i
  unfold mu_son
  have h1 : Continuous fun h : Matrix T d ℝ => h t := continuous_apply t
  exact (((h1.matrix_vecMul continuous_const).dotProduct h1).div_const _).mul
    ((continuous_apply i).comp h1)

/-! ### The open cone `V`, and an open set of rows -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: scaling the rows of `h` by positive numbers scales the rows of `h M` by the same
numbers, so it keeps `h M` in `V`. -/
private theorem rowScale_mul_mem_son {m r : Type*} [Fintype m] {V : Set (Matrix T r ℝ)}
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
private theorem rmsNorm_mul_mem_son {ε : ℝ} (hε : 0 < ε) {r : Type*} {V : Set (Matrix T r ℝ)}
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    {h : Matrix T d ℝ} {M : Matrix d r ℝ} (hM : h * M ∈ V) : rmsNorm ε h * M ∈ V :=
  rowScale_mul_mem_son hVs hM
    (c := fun t => (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹)
    fun t => inv_pos.2 (Real.sqrt_pos.2 (by have := dot_self_nonneg_son (h t); positivity))

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: for `s > 0`, `x M ∈ V` gives `(s x) M ∈ V`. -/
private theorem smul_mul_mem_son {m r : Type*} [Fintype m] {V : Set (Matrix T r ℝ)}
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
private theorem exists_add_sub_mem_son {m : Type*} [Fintype m] {G : Set (m → ℝ)}
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
private theorem eq_zero_of_vecMul_on_son {m n : Type*} [Fintype m] [DecidableEq m]
    {G : Set (m → ℝ)} (hG : IsOpen G) (hne : G.Nonempty) {K : Matrix m n ℝ}
    (h : ∀ w ∈ G, w ᵥ* K = 0) : K = 0 := by
  obtain ⟨w₀, hw₀⟩ := hne
  refine eq_zero_of_vecMul_son fun v => ?_
  obtain ⟨δ, hδ, hδG, -⟩ := exists_add_sub_mem_son hG hw₀ v
  have e := h _ hδG
  rw [Matrix.add_vecMul, h w₀ hw₀, zero_add, Matrix.smul_vecMul] at e
  exact (smul_eq_zero.1 e).resolve_left hδ.ne'

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 2): the quadratic form `w ↦ ⟨w E Y, w E⟩` vanishes everywhere if it vanishes on
a nonempty open set (`q(w₀ + δ v) + q(w₀ - δ v) = 2 q(w₀) + 2 δ² q(v)`). -/
private theorem quad_zero_of_isOpen_son {m : Type*} [Fintype m] {G : Set (m → ℝ)}
    (hG : IsOpen G) (hne : G.Nonempty) {E : Matrix m d ℝ} {Y : Matrix d d ℝ}
    (h : ∀ w ∈ G, (w ᵥ* E) ᵥ* Y ⬝ᵥ (w ᵥ* E) = 0) (v : m → ℝ) :
    (v ᵥ* E) ᵥ* Y ⬝ᵥ (v ᵥ* E) = 0 := by
  obtain ⟨w₀, hw₀⟩ := hne
  obtain ⟨δ, hδ, hp, hm⟩ := exists_add_sub_mem_son hG hw₀ v
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
private noncomputable def c_son (ε : ℝ) (v : d → ℝ) (y : ℝ) : ℝ :=
  (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε * y ^ 2))⁻¹

/-- Helper: the matrix with rows `c(a_t, y) a_t`, which is `N_ε(s a)` at `y = 1/s`. -/
private noncomputable def n_son (ε : ℝ) (a : Matrix T d ℝ) (y : ℝ) : Matrix T d ℝ :=
  Matrix.of fun t => c_son ε (a t) y • a t

/-- Helper: the matrix that is `𝐃N_ε(s a)(s b)` at `y = 1/s`. -/
private noncomputable def dn_son (ε : ℝ) (a b : Matrix T d ℝ) (y : ℝ) : Matrix T d ℝ :=
  Matrix.of fun t => c_son ε (a t) y • b t
    - ((a t ⬝ᵥ b t) / (Fintype.card d : ℝ) * c_son ε (a t) y ^ 3) • a t

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `(‖s v‖²/d + ε)^{-1/2} = c(v, 1/s) / s` for `s > 0`. -/
private theorem inv_sqrt_smul_son {ε s : ℝ} (hs : 0 < s) (v : d → ℝ) :
    (Real.sqrt ((s • v) ⬝ᵥ (s • v) / (Fintype.card d : ℝ) + ε))⁻¹ = c_son ε v s⁻¹ * s⁻¹ := by
  unfold c_son
  have e : (s • v) ⬝ᵥ (s • v) / (Fintype.card d : ℝ) + ε
      = s ^ 2 * ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε * s⁻¹ ^ 2) := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    field_simp
  rw [e, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le, mul_inv, mul_comm]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `N_ε(s a) = n(1/s)` for `s > 0`. -/
private theorem rmsNorm_smul_son {ε s : ℝ} (hs : 0 < s) (a : Matrix T d ℝ) :
    rmsNorm ε (s • a) = n_son ε a s⁻¹ := by
  funext t i
  show (Real.sqrt ((s • a t) ⬝ᵥ (s • a t) / (Fintype.card d : ℝ) + ε))⁻¹ * (s * a t i)
    = c_son ε (a t) s⁻¹ * a t i
  rw [inv_sqrt_smul_son hs, mul_assoc, inv_mul_cancel_left₀ hs.ne']

omit [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: `𝐃N_ε(s a)(s b) = dn(1/s)` for `s > 0`. -/
private theorem fderiv_rmsNorm_smul_son {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s)
    (a b : Matrix T d ℝ) :
    fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (s • a) (s • b) = dn_son ε a b s⁻¹ := by
  rw [fderiv_rmsNorm_apply hε]
  funext t i
  show (Real.sqrt ((s • a t) ⬝ᵥ (s • a t) / (Fintype.card d : ℝ) + ε))⁻¹ * (s * b t i)
      - ((s • a t) ⬝ᵥ (s • b t) / (Fintype.card d : ℝ)
        * (Real.sqrt ((s • a t) ⬝ᵥ (s • a t) / (Fintype.card d : ℝ) + ε))⁻¹ ^ 3) * (s * a t i)
    = c_son ε (a t) s⁻¹ * b t i
      - ((a t ⬝ᵥ b t) / (Fintype.card d : ℝ) * c_son ε (a t) s⁻¹ ^ 3) * a t i
  rw [inv_sqrt_smul_son hs, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  field_simp

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `‖v‖²/d > 0` if `v ≠ 0`. -/
private theorem dot_self_div_pos_son {v : d → ℝ} (hv : v ≠ 0) :
    0 < (v ⬝ᵥ v) / (Fintype.card d : ℝ) := by
  have h1 : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (dot_self_nonneg_son v) (Ne.symm (mt dotProduct_self_eq_zero.1 hv))
  have h2 : (0 : ℝ) < Fintype.card d := by
    obtain ⟨i, -⟩ := Function.ne_iff.1 hv
    exact_mod_cast Fintype.card_pos_iff.2 ⟨i⟩
  positivity

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `c(v, 0) > 0` if `v ≠ 0`. -/
private theorem c_son_zero_pos {ε : ℝ} {v : d → ℝ} (hv : v ≠ 0) : 0 < c_son ε v 0 := by
  unfold c_son
  refine inv_pos.2 (Real.sqrt_pos.2 ?_)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
  exact dot_self_div_pos_son hv

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `y ↦ c(v, y)` is continuous at `0` if `v ≠ 0`. -/
private theorem continuousAt_c_son {ε : ℝ} {v : d → ℝ} (hv : v ≠ 0) :
    ContinuousAt (c_son ε v) 0 := by
  have hpos := dot_self_div_pos_son hv
  have hc : Continuous fun y : ℝ => Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε * y ^ 2) := by
    fun_prop
  refine hc.continuousAt.inv₀ ?_
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
  exact (Real.sqrt_pos.2 hpos).ne'

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `n` and `dn` are continuous at `0` if every row of `a` is nonzero. -/
private theorem continuousAt_n_dn_son {ε : ℝ} {a : Matrix T d ℝ} (ha : ∀ t, a t ≠ 0)
    (b : Matrix T d ℝ) : ContinuousAt (n_son ε a) 0 ∧ ContinuousAt (dn_son ε a b) 0 := by
  constructor
  · refine continuousAt_pi.2 fun t => continuousAt_pi.2 fun i => ?_
    show ContinuousAt (fun y => c_son ε (a t) y * a t i) 0
    exact (continuousAt_c_son (ha t)).mul continuousAt_const
  · refine continuousAt_pi.2 fun t => continuousAt_pi.2 fun i => ?_
    show ContinuousAt (fun y => c_son ε (a t) y * b t i
      - ((a t ⬝ᵥ b t) / (Fintype.card d : ℝ) * c_son ε (a t) y ^ 3) * a t i) 0
    exact ((continuousAt_c_son (ha t)).mul continuousAt_const).sub
      ((continuousAt_const.mul ((continuousAt_c_son (ha t)).pow 3)).mul continuousAt_const)

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if every row of `a` is nonzero and `a M ∈ V`, the limit `n(0) M` of `N_ε(s a) M` is in
`V` (`n(0)` scales the rows of `a` by positive numbers). -/
private theorem n_son_zero_mul_mem {ε : ℝ} {r : Type*} {V : Set (Matrix T r ℝ)}
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    {a : Matrix T d ℝ} (ha : ∀ t, a t ≠ 0) {M : Matrix d r ℝ} (hM : a * M ∈ V) :
    n_son ε a 0 * M ∈ V :=
  rowScale_mul_mem_son hVs hM (c := fun t => c_son ε (a t) 0) fun t => c_son_zero_pos (ha t)

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (Step 2, large inputs): if every row of `w E` is nonzero and `f` is continuous at the
limit `n(0) W_read`, then `h_1(s w) / s → w E` as `s → ∞`. -/
private theorem tendsto_hOne_ray_son {A : Arch T d 1} {ε : ℝ} (θ : Params A dIn dOut)
    (w : Matrix T dIn ℝ) (hw : ∀ t, (w * θ.E) t ≠ 0)
    (hfc : ContinuousAt (A.f 0) (n_son ε (w * θ.E) 0 * θ.read 0)) :
    Tendsto (fun s : ℝ => s⁻¹ • hOne_son A ε θ (s • w)) atTop (𝓝 (w * θ.E)) := by
  have hn := (continuousAt_n_dn_son (ε := ε) hw (w * θ.E)).1
  have hR : Continuous fun M : Matrix T d ℝ => M * θ.read 0 :=
    continuous_id.matrix_mul continuous_const
  have hW : Continuous fun N : Matrix T (A.w 0) ℝ => N * θ.write 0 :=
    continuous_id.matrix_mul continuous_const
  -- `Ψ(y) = f(n(y) W_read) W_write`, continuous at `0`
  have h1 : ContinuousAt (fun y => n_son ε (w * θ.E) y * θ.read 0) 0 :=
    ContinuousAt.comp (f := n_son ε (w * θ.E)) (x := 0) hR.continuousAt hn
  have h2 : ContinuousAt (fun y => A.f 0 (n_son ε (w * θ.E) y * θ.read 0)) 0 :=
    ContinuousAt.comp (f := fun y => n_son ε (w * θ.E) y * θ.read 0) (x := 0) hfc h1
  have hΨ : ContinuousAt (fun y => A.f 0 (n_son ε (w * θ.E) y * θ.read 0) * θ.write 0) 0 :=
    ContinuousAt.comp (f := fun y => A.f 0 (n_son ε (w * θ.E) y * θ.read 0)) (x := 0)
      hW.continuousAt h2
  have hlim := (tendsto_const_nhds (x := w * θ.E)).add
    (tendsto_inv_atTop_zero.smul (hΨ.tendsto.comp tendsto_inv_atTop_zero))
  rw [zero_smul, add_zero] at hlim
  refine hlim.congr' ((eventually_gt_atTop 0).mono fun s hs => ?_)
  -- `h_1(s w) = s (w E) + Ψ(1/s)`
  show w * θ.E + s⁻¹ • (A.f 0 (n_son ε (w * θ.E) s⁻¹ * θ.read 0) * θ.write 0)
    = s⁻¹ • hOne_son A ε θ (s • w)
  rw [hOne_son, Matrix.smul_mul, rmsNorm_smul_son hs, smul_add, smul_smul,
    inv_mul_cancel₀ hs.ne', one_smul]

omit [Nonempty T] [Fintype dOut] in
/-- Helper (Steps 2 and 3, large inputs): if every row of `w E` is nonzero and `f` and its
derivative are continuous at the limit `n(0) W_read`, then `k(s w) / s → w η_E` as `s → ∞`. -/
private theorem tendsto_kOne_ray_son {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (θ η : Params A dIn dOut) (w : Matrix T dIn ℝ) (hw : ∀ t, (w * θ.E) t ≠ 0)
    (hfc : ContinuousAt (A.f 0) (n_son ε (w * θ.E) 0 * θ.read 0))
    (hfdc : ContinuousAt (fderiv ℝ (A.f 0)) (n_son ε (w * θ.E) 0 * θ.read 0)) :
    Tendsto (fun s : ℝ => s⁻¹ • kOne_son A ε θ η (s • w)) atTop (𝓝 (w * η.E)) := by
  obtain ⟨hn, hdn⟩ := continuousAt_n_dn_son (ε := ε) hw (w * η.E)
  have hR : ∀ M : Matrix d (A.r 0) ℝ, Continuous fun N : Matrix T d ℝ => N * M := fun M =>
    continuous_id.matrix_mul continuous_const
  have h1 : ContinuousAt (fun y => n_son ε (w * θ.E) y * θ.read 0) 0 :=
    ContinuousAt.comp (f := n_son ε (w * θ.E)) (x := 0) (hR _).continuousAt hn
  have h2 : ContinuousAt (fun y => dn_son ε (w * θ.E) (w * η.E) y * θ.read 0
      + n_son ε (w * θ.E) y * η.read 0) 0 :=
    (ContinuousAt.comp (f := dn_son ε (w * θ.E) (w * η.E)) (x := 0) (hR _).continuousAt hdn).add
      (ContinuousAt.comp (f := n_son ε (w * θ.E)) (x := 0) (hR _).continuousAt hn)
  have h3 := (ContinuousAt.comp (f := fun y => n_son ε (w * θ.E) y * θ.read 0) (x := (0 : ℝ))
    hfdc h1).clm_apply h2
  have hW : ∀ M : Matrix (A.w 0) d ℝ, Continuous fun N : Matrix T (A.w 0) ℝ => N * M := fun M =>
    continuous_id.matrix_mul continuous_const
  have h4 := ContinuousAt.comp (f := fun y => n_son ε (w * θ.E) y * θ.read 0) (x := (0 : ℝ))
    hfc h1
  have hΦ := (ContinuousAt.comp (x := (0 : ℝ)) (hW (θ.write 0)).continuousAt h3).add
    (ContinuousAt.comp (x := (0 : ℝ)) (hW (η.write 0)).continuousAt h4)
  have hlim := (tendsto_const_nhds (x := w * η.E)).add
    (tendsto_inv_atTop_zero.smul (hΦ.tendsto.comp tendsto_inv_atTop_zero))
  rw [zero_smul, add_zero] at hlim
  refine hlim.congr' ((eventually_gt_atTop 0).mono fun s hs => ?_)
  -- `k(s w) = s (w η_E) + Φ(1/s)`
  show w * η.E + s⁻¹ • (fderiv ℝ (A.f 0) (n_son ε (w * θ.E) s⁻¹ * θ.read 0)
      (dn_son ε (w * θ.E) (w * η.E) s⁻¹ * θ.read 0 + n_son ε (w * θ.E) s⁻¹ * η.read 0)
        * θ.write 0
      + A.f 0 (n_son ε (w * θ.E) s⁻¹ * θ.read 0) * η.write 0) = s⁻¹ • kOne_son A ε θ η (s • w)
  rw [kOne_son, Matrix.smul_mul, Matrix.smul_mul, rmsNorm_smul_son hs,
    fderiv_rmsNorm_smul_son hε hs, add_assoc, smul_add (s⁻¹) (s • (w * η.E)), smul_smul,
    inv_mul_cancel₀ hs.ne', one_smul]

end HelpersSon

/-- **Proof of Theorem B.1 (ii), Steps 1 to 3, for a block that is smooth on an open cone of
pre-activations:** let `ε > 0`, let `f` be continuously differentiable on an open set `V` that is
invariant under positive scalings of the rows, let `E` and `D` have rank `d`, and let some input
with equal rows have its pre-activation `x E W_read` in `V`. If `η` is flat at every input `x`
with `x E W_read ∈ V`, there is an antisymmetric `Y` with `η_E = E Y`, `η_D = −Y D`, and at every
such input the derivative of `n ↦ f(n W_read) W_write` along `η_read + Y W_read`,
`η_write − W_write Y` vanishes at `n = N_ε(x E)`. -/
theorem exists_antisymm_of_flatOn_residual_rmsNorm {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (V : Set (Matrix T (A.r 0) ℝ)) (hV : IsOpen V)
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    (hf : ContDiffOn ℝ 1 (A.f 0) V) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∃ w : dIn → ℝ, (Matrix.of fun _ : T => w) * θ.E * θ.read 0 ∈ V)
    (η : Params A dIn dOut) (hη : η ∈ flatOn A 1 θ {x | x * θ.E * θ.read 0 ∈ V}) :
    ∃ Y : Matrix d d ℝ, Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D) ∧
      ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
        fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
            (rmsNorm ε (x * θ.E) * (η.read 0 + Y * θ.read 0)) * θ.write 0
          + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * (η.write 0 - θ.write 0 * Y) = 0 := by
  -- no coordinates: every matrix with a side indexed by `d` is `0`
  rcases isEmpty_or_nonempty d with hd0 | hd0
  · refine ⟨0, ?_, ?_, ?_, fun x _ => ?_⟩ <;> funext i j
    · exact isEmptyElim i
    · exact isEmptyElim j
    · exact isEmptyElim i
    · exact isEmptyElim j
  classical
  have hd : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos
  -- at an input `x` of `U` (`x E W_read ∈ V`), `N_ε(x E) W_read` is in the open set `V` (a
  -- positive scaling of the rows of `x E W_read`), so `f` is differentiable there
  have hfx : ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
      DifferentiableAt ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0) := fun x hx =>
    (hf.contDiffAt (hV.mem_nhds (rmsNorm_mul_mem_son hε hVs hx))).differentiableAt one_ne_zero
  -- a right inverse `D⁺` of `D`, and `Y = -η_D D⁺`
  obtain ⟨Dp, hDp⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1
    (Matrix.mulVec_surjective_iff_rank_eq_card.2 hD)
  obtain ⟨Y, hYdef⟩ : ∃ Y : Matrix d d ℝ, Y = -(η.D * Dp) := ⟨_, rfl⟩
  -- Step 0 for `η` at the inputs of `U`: `𝐃N_ε(h_1) k D + N_ε(h_1) η_D = 0`
  have h0 : ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
      fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (hOne_son A ε θ x) (kOne_son A ε θ η x)
        * θ.D + rmsNorm ε (hOne_son A ε θ x) * η.D = 0 := fun x hx =>
    flat_eq_son hε hA θ η x (hfx x hx) (fderiv_eq_zero_of_flatOn_son hη hx)
  -- Step 1: times `D⁺`, `𝐃N_ε(h_1) k = N_ε(h_1) Y`
  have hNY : ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
      fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (hOne_son A ε θ x)
        (kOne_son A ε θ η x) = rmsNorm ε (hOne_son A ε θ x) * Y := by
    intro x hx
    have e := congrArg (· * Dp) (h0 x hx)
    simp only [Matrix.add_mul, Matrix.mul_assoc, hDp, Matrix.mul_one, Matrix.zero_mul] at e
    rw [hYdef, Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left e
  -- hence `k = h_1 Y + μ ⊙ h_1`, since `𝐃N_ε(h_1)` is injective
  have hk : ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V → kOne_son A ε θ η x
      = hOne_son A ε θ x * Y + muScale_son ε Y (hOne_son A ε θ x) := fun x hx =>
    injective_fderiv_rmsNorm hε _ (by rw [hNY x hx, fderiv_rmsNorm_muScale_son hε hd])
  -- and, substituting back, `N_ε(h_1) (Y D + η_D) = 0`, so `h_1 (Y D + η_D) = 0`
  have hZ : ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
      hOne_son A ε θ x * (Y * θ.D + η.D) = 0 := by
    intro x hx
    refine mul_eq_zero_of_rmsNorm_mul_son hε _ _ ?_
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
      obtain ⟨δ, hδ, hδV, -⟩ := exists_add_sub_mem_son (hV.preimage hc1) hw₀ u
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
      ContinuousAt (A.f 0) (n_son ε ((Matrix.of fun _ : T => w₀) * θ.E) 0 * θ.read 0) ∧
      ContinuousAt (fderiv ℝ (A.f 0))
        (n_son ε ((Matrix.of fun _ : T => w₀) * θ.E) 0 * θ.read 0) := by
    intro w₀ hw₀
    rw [hGdef] at hw₀
    have hrows : ∀ t, ((Matrix.of fun _ : T => w₀) * θ.E) t ≠ 0 := fun t => by
      rw [constRows_mul_son]
      exact hw₀.2
    have hP := hV.mem_nhds (n_son_zero_mul_mem (ε := ε) hVs hrows hw₀.1)
    refine ⟨fun s hs => ?_, hrows, hf.continuousOn.continuousAt hP,
      (hf.continuousOn_fderiv_of_isOpen hV le_rfl).continuousAt hP⟩
    rw [Matrix.smul_mul]
    exact smul_mul_mem_son hVs hw₀.1 hs
  -- at the inputs `s w`, `s → ∞`: `(w₀ E)(Y D + η_D) = 0` for `w₀ ∈ G`, hence `E (Y D + η_D) = 0`
  -- (linear in `w₀`, on an open set), and `η_D = -Y D` since `E` has rank `d`
  have hZ0 : Y * θ.D + η.D = 0 := by
    have h1 : ∀ w₀ ∈ G, w₀ ᵥ* (θ.E * (Y * θ.D + η.D)) = 0 := by
      intro w₀ hw₀
      obtain ⟨hU, hrows, hfc, -⟩ := hray w₀ hw₀
      have hc : Continuous fun M : Matrix T d ℝ => M * (Y * θ.D + η.D) :=
        continuous_id.matrix_mul continuous_const
      have hlim := (hc.tendsto _).comp (tendsto_hOne_ray_son θ _ hrows hfc)
      have hlim0 : Filter.Tendsto
          (fun s : ℝ => (s⁻¹ • hOne_son A ε θ (s • Matrix.of fun _ : T => w₀)) * (Y * θ.D + η.D))
          Filter.atTop (nhds 0) :=
        tendsto_const_nhds.congr' ((Filter.eventually_gt_atTop 0).mono fun s hs => by
          dsimp only
          rw [Matrix.smul_mul, hZ _ (hU s hs), smul_zero])
      have e := tendsto_nhds_unique hlim hlim0
      rw [← Matrix.vecMul_vecMul, ← constRows_mul_son (T := T) w₀ θ.E (Classical.arbitrary T),
        ← Matrix.mul_apply_eq_vecMul, e]
      rfl
    have h2 := eq_zero_of_vecMul_on_son hGo hGne h1
    refine eq_zero_of_vecMul_son fun u => ?_
    obtain ⟨w₀, rfl⟩ := Matrix.vecMul_surjective_iff_rank_eq_card.2 hE u
    rw [Matrix.vecMul_vecMul, h2, Matrix.vecMul_zero]
  have hYD : η.D = -(Y * θ.D) := eq_neg_of_add_eq_zero_right hZ0
  -- Step 2: the terms of order `s³` at the inputs `s w` give `⟨w₀ E Y, w₀ E⟩ = 0` for `w₀ ∈ G`;
  -- a quadratic form that vanishes on an open set vanishes, and every `u` is a `w₀ E`
  have hq : ∀ u : d → ℝ, u ᵥ* Y ⬝ᵥ u = 0 := by
    have h1 : ∀ w₀ ∈ G, (w₀ ᵥ* θ.E) ᵥ* Y ⬝ᵥ (w₀ ᵥ* θ.E) = 0 := by
      intro w₀ hw₀
      obtain ⟨hU, hrows, hfc, hfdc⟩ := hray w₀ hw₀
      have hu := tendsto_hOne_ray_son θ _ hrows hfc
      have hv := tendsto_kOne_ray_son hε θ η _ hrows hfc hfdc
      have h1 := ((continuous_muScale_son ε Y).tendsto _).comp hu
      have hc : Continuous fun M : Matrix T d ℝ => M * Y :=
        continuous_id.matrix_mul continuous_const
      have h2 := (tendsto_inv_atTop_zero.pow 2).smul (hv.sub ((hc.tendsto _).comp hu))
      rw [zero_pow two_ne_zero, zero_smul] at h2
      -- the identity of Step 1 at `s w`, divided by `s³`
      have heq : ∀ s : ℝ, 0 < s →
          (s⁻¹) ^ 2 • (s⁻¹ • kOne_son A ε θ η (s • Matrix.of fun _ : T => w₀)
            - (s⁻¹ • hOne_son A ε θ (s • Matrix.of fun _ : T => w₀)) * Y)
          = muScale_son ε Y (s⁻¹ • hOne_son A ε θ (s • Matrix.of fun _ : T => w₀)) := by
        intro s hs
        rw [hk _ (hU s hs), muScale_smul_son, Matrix.smul_mul, smul_add, add_sub_cancel_left,
          smul_smul, ← pow_succ]
      have h12 := tendsto_nhds_unique h1 (h2.congr' ((Filter.eventually_gt_atTop 0).mono heq))
      -- row `t`: `μ(w₀ E) w₀ E = 0` with `w₀ E ≠ 0`
      have hrow : mu_son ε Y (((Matrix.of fun _ : T => w₀) * θ.E) (Classical.arbitrary T))
          • ((Matrix.of fun _ : T => w₀) * θ.E) (Classical.arbitrary T) = 0 :=
        congrFun h12 (Classical.arbitrary T)
      rw [constRows_mul_son] at hrow
      have hne : w₀ ᵥ* θ.E ≠ 0 := by
        rw [← constRows_mul_son (T := T) w₀ θ.E (Classical.arbitrary T)]
        exact hrows _
      have hmu := (smul_eq_zero.1 hrow).resolve_right hne
      unfold mu_son at hmu
      exact (div_eq_zero_iff.1 hmu).resolve_right (mul_pos hd hε).ne'
    intro u
    obtain ⟨v, rfl⟩ := Matrix.vecMul_surjective_iff_rank_eq_card.2 hE u
    exact quad_zero_of_isOpen_son hGo hGne h1 v
  have hY : Yᵀ = -Y := transpose_eq_neg_son hq
  -- Step 3: `η' = η - η^Y` is flat at the inputs of `U`
  obtain ⟨η', hη'def⟩ : ∃ η', η' = η - cobDir θ (fun _ => Y) := ⟨_, rfl⟩
  have hη' : η' ∈ flatOn A 1 θ {x | x * θ.E * θ.read 0 ∈ V} := hη'def ▸
    Submodule.sub_mem _ hη
      (flat_le_flatOn θ _ (cobDir_const_mem_flat_residual_rmsNorm' θ ε hA Y hY))
  have hη'E : η'.E = η.E - θ.E * Y := by
    rw [hη'def]
    rfl
  have hη'r : η'.read 0 = η.read 0 + Y * θ.read 0 := by
    rw [hη'def]
    show η.read 0 - -(Y * θ.read 0) = _
    exact sub_neg_eq_add _ _
  have hη'w : η'.write 0 = η.write 0 - θ.write 0 * Y := by
    rw [hη'def]
    rfl
  have hη'D : η'.D = 0 := by
    rw [hη'def]
    show η.D - -(Y * θ.D) = 0
    rw [hYD, sub_neg_eq_add, neg_add_cancel]
  -- `η'_D = 0`, so Step 0 gives `𝐃N_ε(h_1) k' D = 0`, hence `k' = 0` at every input of `U`
  have hk' : ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V → kOne_son A ε θ η' x = 0 := by
    intro x hx
    have e := flat_eq_son hε hA θ η' x (hfx x hx) (fderiv_eq_zero_of_flatOn_son hη' hx)
    rw [hη'D, Matrix.mul_zero, add_zero] at e
    have e2 := congrArg (· * Dp) e
    simp only [Matrix.mul_assoc, hDp, Matrix.mul_one, Matrix.zero_mul] at e2
    exact injective_fderiv_rmsNorm hε _ (by rw [e2, map_zero])
  -- at the inputs `s w`, `w₀ ∈ G`: `w₀ η'_E = 0`; linear in `w₀` on an open set, so `η'_E = 0`
  have hE' : η'.E = 0 := by
    refine eq_zero_of_vecMul_on_son hGo hGne fun w₀ hw₀ => ?_
    obtain ⟨hU, hrows, hfc, hfdc⟩ := hray w₀ hw₀
    have e := tendsto_nhds_unique (tendsto_kOne_ray_son hε θ η' _ hrows hfc hfdc)
      ((tendsto_const_nhds (x := (0 : Matrix T d ℝ))).congr'
        ((Filter.eventually_gt_atTop 0).mono fun s hs => by
          dsimp only
          rw [hk' _ (hU s hs), smul_zero]))
    have e2 := congrFun e (Classical.arbitrary T)
    rwa [constRows_mul_son] at e2
  refine ⟨Y, hY, ?_, hYD, fun x hx => ?_⟩
  · rw [hη'E] at hE'
    exact sub_eq_zero.1 hE'
  · -- with `η'_E = 0`, `k'(x) = 0` is the last clause
    have e := hk' x hx
    unfold kOne_son at e
    rw [hE', Matrix.mul_zero, map_zero, Matrix.zero_mul, zero_add, zero_add, hη'r, hη'w] at e
    exact e


end Skips
