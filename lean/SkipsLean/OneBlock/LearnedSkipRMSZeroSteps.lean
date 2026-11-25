import SkipsLean.OneBlock.LearnedSkipSteps
import SkipsLean.OneBlock.ResidualRMSZeroStepsOn
import SkipsLean.OneBlock.LearnedSkipRMSZeroBound
import SkipsLean.OneBlock.SkiplessRMSZeroReadout

/-!
# One block with a full learned skip under pre-RMSNorm with `ε = 0`: Steps 1 to 3 of Part (iii)

Paper (skips paper), proof of Theorem B.1 (iii), "The case `ε = 0`". The network is

  `h_1 = x E A + g(x)`, `g(x) = B(N_0(x E))`, `B(n) = f(n W_read) W_write`, `y = N_0(h_1) D`,

with a full learned skip `A`. "Now `N_ε` maps onto the sphere of radius `√d_model`, and the
scalings of `h_0` and `h_1` are symmetries too, since `N_ε(c h) = N_ε(h)` for `c > 0`. In Step 1,
`DN_ε(h)` vanishes along `h`, so `D_θ h_1 η = h_1 Y + μ h_1` with a number `μ` at each input. `Y`
is again antisymmetric, since `N_ε(h_1) Y` must be orthogonal to `h_1`, which is
`t w E A + O(1)` at the inputs `t w`. At these inputs `g` and its derivative along `η` do not
depend on `t`, since `N_ε(t w E) = N_ε(w E)`. The terms of order `t` give `w Λ = μ_w w E A` with
`Λ = η_E A + E η_A − E A Y` and a number `μ_w`, for all `w` in an open set. Adding to `w` a
vector `w_0` with `w_0 E = 0` leaves `w E A` unchanged, so `w_0 Λ` is a multiple of `w E A` for
every such `w`, hence `w_0 Λ = 0`, and `Λ = E Λ′` with `Λ′ = E⁺ Λ`. Every vector `v = w E` of an
open set is then a left eigenvector of `Λ′ A⁻¹`, which is therefore `c I` for a number `c`, as in
the proof of Lemma A.2: `η_E A + E η_A = E A (Y + c I)`. The constant terms then give `μ = c`
wherever `w E A` and `g(w)` are linearly independent. Steps 3 and 4 run with `Y + c I` in place
of `Y`".

Stated here once, in the generality of `exists_of_flatSkipsOn_learned_rmsNorm`
(`OneBlock/LearnedSkipSteps.lean`, the same steps for `ε > 0`) and of
`exists_antisymm_scale_of_flatOn_residual_rmsNorm_zero_on` (`OneBlock/ResidualRMSZeroStepsOn.lean`,
the case `ε = 0` for the identity skip): for a fixed map `f` that is continuously differentiable
on an open set `V` of pre-activations which is invariant under the scaling of every row by a
positive number (ReLU, ReLU² and ReGLU blocks off their kinks; everything for a smooth block), and
for a direction `(η, η_A)` of the weights and the skip that is flat at the inputs `x` at which no
normalized row vanishes (`learnedZeroDomain`) and `x E W_read ∈ V`. The skip is `R 0` (the paper's
`A`), and `ρ 0` is the paper's `η_A`.

The conclusion is that of Step 3 with `Y + c I` in place of `Y`: a matrix `X`, an antisymmetric
`Y` and a number `c` with `η_E = E X`, `η_A = A (Y + c I) − X A`, `η_D = −Y D`, and
`D_θ g η = g(x) (Y + c I)` at every input `x` with `x E W_read ∈ V` at which, for every token, the
rows of `x E A` and of `g(x)` are linearly independent, where
`D_θ g η = 𝐃f(n W_read)(𝐃N_0(x E)(x E X) W_read + n η_read) W_write + f(n W_read) η_write` at
`n = N_0(x E)`. (No more is claimed: where the rows are not independent, the proof gives only
that the difference is parallel to `h_1`.) The condition on generic parameters is a hypothesis:
one such input exists. With the identity skip and `η_A = 0` this gives `X = Y + c I`, the
statement for the residual network. Step 4 (the symmetric part of `X` is a multiple of `I`)
depends on the kind of block.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

section HelpersLzs

open Filter
open scoped Topology

/-! ### RMSNorm with `ε = 0` at matrices without a zero row (copies of the `_rzo` helpers of
`OneBlock/ResidualRMSZeroStepsOn.lean`) -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `N_0` forgets a positive scale, `N_0(s a) = N_0(a)` for `s > 0`. -/
private theorem rmsNorm_zero_smul_lzs {s : ℝ} (hs : 0 < s) (a : Matrix T d ℝ) :
    rmsNorm 0 (s • a) = rmsNorm 0 a := by
  funext t
  show rmsRow 0 (s • a t) = rmsRow 0 (a t)
  unfold rmsRow
  have e : Real.sqrt ((s • a t ⬝ᵥ s • a t) / (Fintype.card d : ℝ) + 0)
      = s * Real.sqrt ((a t ⬝ᵥ a t) / (Fintype.card d : ℝ) + 0) := by
    have e1 : (s • a t ⬝ᵥ s • a t) / (Fintype.card d : ℝ) + 0
        = s ^ 2 * ((a t ⬝ᵥ a t) / (Fintype.card d : ℝ) + 0) := by
      rw [smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul, add_zero]
      ring
    rw [e1, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]
  rw [e, mul_inv, smul_smul, mul_comm s⁻¹, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `N_0` is differentiable at a matrix without a zero row. -/
private theorem differentiableAt_rmsNorm_zero_lzs {h : Matrix T d ℝ} (hh : ∀ t, h t ≠ 0) :
    DifferentiableAt ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h :=
  (analyticAt_rmsNorm_zero h hh).differentiableAt

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `𝐃N_0(s a)(s b) = 𝐃N_0(a)(b)` for `s > 0`, at `a` without a zero row. -/
private theorem fderiv_rmsNorm_zero_smul_lzs {s : ℝ} (hs : 0 < s) {a : Matrix T d ℝ}
    (ha : ∀ t, a t ≠ 0) (b : Matrix T d ℝ) :
    fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (s • a) (s • b)
      = fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) a b := by
  have hsa : ∀ t, (s • a) t ≠ 0 := fun t => by
    show s • a t ≠ 0
    exact smul_ne_zero hs.ne' (ha t)
  have h1 := (differentiableAt_rmsNorm_zero_lzs hsa).hasFDerivAt.comp a
    ((hasFDerivAt_id a).const_smul s)
  have e : (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) ∘ HSMul.hSMul s = rmsNorm 0 := by
    funext v
    exact rmsNorm_zero_smul_lzs hs v
  rw [e] at h1
  have h2 : fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) a b
      = fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (s • a) (s • b) :=
    DFunLike.congr_fun h1.fderiv b
  exact h2.symm

/-! ### The open cone `V` (copies of the `_rzo` helpers) -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: scaling the rows of `h` by positive numbers scales the rows of `h M` by the same
numbers, so it keeps `h M` in `V`. -/
private theorem rowScale_mul_mem_lzs {m r : Type*} [Fintype m] {V : Set (Matrix T r ℝ)}
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    {h : Matrix T m ℝ} {M : Matrix m r ℝ} (hM : h * M ∈ V) {c : T → ℝ} (hc : ∀ t, 0 < c t) :
    (Matrix.of fun t => c t • h t) * M ∈ V := by
  have e : (Matrix.of fun t => c t • h t) * M = Matrix.of fun t i => c t * (h * M) t i := by
    ext t i
    simp only [Matrix.mul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc]
  rw [e]
  exact hVs _ hM c hc

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: for `s > 0`, `x M ∈ V` gives `(s x) M ∈ V`. -/
private theorem smul_mul_mem_lzs {m r : Type*} [Fintype m] {V : Set (Matrix T r ℝ)}
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    {x : Matrix T m ℝ} {M : Matrix m r ℝ} (hx : x * M ∈ V) {s : ℝ} (hs : 0 < s) :
    (s • x) * M ∈ V := by
  have e : (s • x) * M = Matrix.of fun t i => (fun _ : T => s) t * (x * M) t i := by
    rw [Matrix.smul_mul]
    rfl
  rw [e]
  exact hVs _ hx _ fun _ => hs

/-! ### Step 0: the chain rule along a line of weights and skips, at an input of `U` -/

/-- Helper: the block `g(a) = f(N_0(a) W_read) W_write`, as a function of `a = x E`. -/
private noncomputable def gOne_lzs (A : Arch T d 1) (θ : Params A dIn dOut) (a : Matrix T d ℝ) :
    Matrix T d ℝ :=
  A.f 0 (rmsNorm 0 a * θ.read 0) * θ.write 0

/-- Helper: the derivative of the block along `η`, at `a = x E` and `b = x η_E`:
`𝐃f(N_0(a) W_read)(𝐃N_0(a)(b) W_read + N_0(a) η_read) W_write + f(N_0(a) W_read) η_write`. -/
private noncomputable def gam_lzs (A : Arch T d 1) (θ η : Params A dIn dOut)
    (a b : Matrix T d ℝ) : Matrix T d ℝ :=
  fderiv ℝ (A.f 0) (rmsNorm 0 a * θ.read 0)
      (fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) a b * θ.read 0
        + rmsNorm 0 a * η.read 0) * θ.write 0
    + A.f 0 (rmsNorm 0 a * θ.read 0) * η.write 0

/-- Helper: the hidden state `h_1 = x E S + g(x E)` of one block with the skip `S`. -/
private noncomputable def hOne_lzs (A : Arch T d 1) (θ : Params A dIn dOut) (S : Matrix d d ℝ)
    (x : Matrix T dIn ℝ) : Matrix T d ℝ :=
  x * θ.E * S + gOne_lzs A θ (x * θ.E)

/-- Helper: the derivative `k(x) = x η_E S + x E σ + γ(x E, x η_E)` of `h_1` along `(η, σ)`. -/
private noncomputable def kOne_lzs (A : Arch T d 1) (θ η : Params A dIn dOut)
    (S σ : Matrix d d ℝ) (x : Matrix T dIn ℝ) : Matrix T d ℝ :=
  x * η.E * S + x * θ.E * σ + gam_lzs A θ η (x * θ.E) (x * η.E)

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (a copy of the private `eval_eq_lzt`): the function of one block under pre-RMSNorm with
`ε = 0` and the skip `S 0`, `F(x) = N_0(x E S + f(N_0(x E) W_read) W_write) D`. -/
private theorem eval_eq_lzs {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (S : Fin 1 → Matrix d d ℝ) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    eval A S θ x = rmsNorm 0 (x * θ.E * S 0
      + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) * θ.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product rule for matrices depending on one real variable. -/
private theorem hasDerivAt_mul_lzs {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
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
private theorem hasDerivAt_affine_lzs {m n : Type*} [Fintype m] [Fintype n]
    (M N : Matrix m n ℝ) : HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (Step 0): along the line `(θ + τ η, S + τ σ)`, the hidden state `h_1` has the
derivative `k(x)` at `τ = 0`, if no row of `x E` vanishes and `f` is differentiable at
`N_0(x E) W_read`. -/
private theorem hasDerivAt_hOne_line_lzs {A : Arch T d 1} (θ η : Params A dIn dOut)
    (S σ : Matrix d d ℝ) (x : Matrix T dIn ℝ) (hx : ∀ t, (x * θ.E) t ≠ 0)
    (hfx : DifferentiableAt ℝ (A.f 0) (rmsNorm 0 (x * θ.E) * θ.read 0)) :
    HasDerivAt (fun τ : ℝ => hOne_lzs A (θ + τ • η) (S + τ • σ) x)
      (kOne_lzs A θ η S σ x) 0 := by
  -- `x E(τ)`
  have hE : HasDerivAt (fun τ : ℝ => x * (θ + τ • η).E) (x * η.E) 0 := by
    have h := hasDerivAt_mul_lzs (hasDerivAt_const (0 : ℝ) x) (hasDerivAt_affine_lzs θ.E η.E)
      (P0 := x) (Q0 := θ.E) rfl (by simp)
    rw [Matrix.zero_mul, zero_add] at h
    exact h
  -- `x E(τ) S(τ)`
  have hES := hasDerivAt_mul_lzs hE (hasDerivAt_affine_lzs S σ) (P0 := x * θ.E) (Q0 := S)
    (by simp) (by simp)
  -- `N_0(x E(τ))`
  have hN : HasDerivAt (fun τ : ℝ => rmsNorm 0 (x * (θ + τ • η).E))
      (fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * η.E)) 0 :=
    (differentiableAt_rmsNorm_zero_lzs hx).hasFDerivAt.comp_hasDerivAt_of_eq 0 hE (by simp)
  -- `N_0(x E(τ)) W_read(τ)`
  have hNR := hasDerivAt_mul_lzs hN (hasDerivAt_affine_lzs (θ.read 0) (η.read 0))
    (P0 := rmsNorm 0 (x * θ.E)) (Q0 := θ.read 0) (by simp) (by simp)
  -- `f(N_0(x E(τ)) W_read(τ))`: `f` is differentiable at the point of `τ = 0`
  have hF := hfx.hasFDerivAt.comp_hasDerivAt_of_eq 0 hNR (by simp)
  -- `f(…) W_write(τ)`
  have hFW := hasDerivAt_mul_lzs hF (hasDerivAt_affine_lzs (θ.write 0) (η.write 0))
    (P0 := A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0)) (Q0 := θ.write 0) (by simp) (by simp)
  exact hES.add hFW

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two matrix-valued maps that are differentiable at a point is
differentiable there (matrix multiplication is a continuous bilinear map). -/
private theorem differentiableAt_matMul_lzs {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
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

omit [Nonempty T] [DecidableEq d] in
/-- Helper (a copy of the private `differentiableAt_evalSkips_lzt`): at an input `x` at which no
normalized row vanishes and `f` is differentiable at `N_0(x E) W_read`, the output with the full
learned skip is a differentiable function of `(θ, R)`. -/
private theorem differentiableAt_evalSkips_lzs {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ)
    (x : Matrix T dIn ℝ) (hx : x ∈ learnedZeroDomain A θ R)
    (hfx : DifferentiableAt ℝ (A.f 0) (rmsNorm 0 (x * θ.E) * θ.read 0)) :
    DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x) (θ, R) := by
  have e : (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x)
      = fun p => rmsNorm 0 (x * p.1.E * p.2 0
          + A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0) * p.1.write 0) * p.1.D :=
    funext fun p => eval_eq_lzs hA p.2 p.1 x
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
    differentiableAt_matMul_lzs (differentiableAt_const x) hE
  have h2 : DifferentiableAt ℝ
      (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) => rmsNorm 0 (x * p.1.E)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E) (θ, R) (analyticAt_rmsNorm_zero (x * θ.E) hx.1).differentiableAt h1
  have h3 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm 0 (x * p.1.E) * p.1.read 0) (θ, R) :=
    differentiableAt_matMul_lzs h2 hR
  have h4 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm 0 (x * p.1.E) * p.1.read 0) (θ, R) hfx h3
  -- `h_1 = x E S + f(…) W_write`, `N_0(h_1)` (no row of `h_1` is zero) and `N_0(h_1) D`
  have h5 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E * p.2 0 + A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0) * p.1.write 0) (θ, R) :=
    (differentiableAt_matMul_lzs h1 hS).add (differentiableAt_matMul_lzs h4 hW)
  have h6 : DifferentiableAt ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      rmsNorm 0 (x * p.1.E * p.2 0
        + A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0) * p.1.write 0)) (θ, R) :=
    DifferentiableAt.comp (f := fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      x * p.1.E * p.2 0 + A.f 0 (rmsNorm 0 (x * p.1.E) * p.1.read 0) * p.1.write 0) (θ, R)
      (analyticAt_rmsNorm_zero _ hx.2).differentiableAt h5
  exact differentiableAt_matMul_lzs h6 hD

omit [Nonempty T] [DecidableEq d] in
/-- Helper: the chain rule along the line `τ ↦ p + τ q` of weights and skips. -/
private theorem hasDerivAt_evalSkips_line_lzs (A : Arch T d 1)
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
private theorem fderiv_eq_zero_of_flatSkipsOn_lzs {A : Arch T d 1} {θ η : Params A dIn dOut}
    {R ρ : Fin 1 → Matrix d d ℝ} {U : Set (Matrix T dIn ℝ)}
    (hη : (η, ρ) ∈ flatSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R) U)
    {x : Matrix T dIn ℝ} (hx : x ∈ U) :
    fderiv ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x) (θ, R) (η, ρ) = 0 :=
  LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hη x) hx)

omit [Nonempty T] [DecidableEq d] in
/-- Helper (Step 0): at an input `x` of `learnedZeroDomain` at which `f` is differentiable at
`N_0(x E) W_read` and along which `(η, ρ)` is flat, `𝐃N_0(h_1) k(x) D + N_0(h_1) η_D = 0`. -/
private theorem flat_eq_lzs {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (θ η : Params A dIn dOut) (R ρ : Fin 1 → Matrix d d ℝ) (x : Matrix T dIn ℝ)
    (hx : x ∈ learnedZeroDomain A θ R)
    (hfx : DifferentiableAt ℝ (A.f 0) (rmsNorm 0 (x * θ.E) * θ.read 0))
    (h0 : fderiv ℝ (fun p : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p x) (θ, R) (η, ρ) = 0) :
    fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (hOne_lzs A θ (R 0) x)
        (kOne_lzs A θ η (R 0) (ρ 0) x) * θ.D
      + rmsNorm 0 (hOne_lzs A θ (R 0) x) * η.D = 0 := by
  -- flatness: the derivative along the line is `0`
  have h1 := hasDerivAt_evalSkips_line_lzs A (θ, R) (η, ρ) x
    (differentiableAt_evalSkips_lzs hA θ R x hx hfx)
  rw [h0] at h1
  -- the same derivative by the chain rule
  have hx2 : ∀ t, hOne_lzs A θ (R 0) x t ≠ 0 := hx.2
  have hh := hasDerivAt_hOne_line_lzs θ η (R 0) (ρ 0) x hx.1 hfx
  have hN := (differentiableAt_rmsNorm_zero_lzs (T := T) (d := d) hx2).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hh (by simp)
  have h2 := hasDerivAt_mul_lzs hN (hasDerivAt_affine_lzs θ.D η.D)
    (P0 := rmsNorm 0 (hOne_lzs A θ (R 0) x)) (Q0 := θ.D) (by simp) (by simp)
  have e : (fun τ : ℝ =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) ((θ, R) + τ • (η, ρ)) x)
      = fun τ => rmsNorm 0 (hOne_lzs A (θ + τ • η) (R 0 + τ • ρ 0) x) * (θ.D + τ • η.D) := by
    funext τ
    show eval A (R + τ • ρ) (θ + τ • η) x = _
    rw [eval_eq_lzs hA]
    rfl
  rw [e] at h1
  exact h2.unique h1

/-! ### Step 1: the rows of `𝐃N_0(h) k = N_0(h) M` (copies of the `_rzo` helpers) -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `⟨v, v⟩ > 0` and `⟨v, v⟩ / d > 0` for a row `v ≠ 0`. -/
private theorem dot_self_pos_lzs {v : d → ℝ} (hv : v ≠ 0) :
    0 < v ⬝ᵥ v ∧ 0 < (v ⬝ᵥ v) / (Fintype.card d : ℝ) := by
  have h1 : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j))
      (fun h => hv (dotProduct_self_eq_zero.1 h.symm))
  obtain ⟨j, -⟩ := Function.ne_iff.1 hv
  have h2 : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩)
  exact ⟨h1, div_pos h1 h2⟩

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: at `h` without a zero row, `h M ∈ V` gives `N_0(h) M ∈ V` (`N_0` scales every row by
a positive number). -/
private theorem rmsNorm_zero_mul_mem_lzs {r : Type*} {V : Set (Matrix T r ℝ)}
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    {h : Matrix T d ℝ} (hh : ∀ t, h t ≠ 0) {M : Matrix d r ℝ} (hM : h * M ∈ V) :
    rmsNorm 0 h * M ∈ V :=
  rowScale_mul_mem_lzs hVs hM
    (c := fun t => (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + 0))⁻¹)
    fun t => inv_pos.2 (Real.sqrt_pos.2 (by rw [add_zero]; exact (dot_self_pos_lzs (hh t)).2))

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the real identity behind the rows of Step 1: from
`ρ⁻¹ a − (K/n) ρ⁻³ c = ρ⁻¹ b` with `ρ² = H/n` follows `a = b + (K/H) c`. -/
private theorem real_row_lzs {a b c K H n ρ : ℝ} (hρ : 0 < ρ) (hH : 0 < H) (hn : 0 < n)
    (h2 : ρ ^ 2 = H / n) (e : ρ⁻¹ * a - (K / n * ρ⁻¹ ^ 3) * c = ρ⁻¹ * b) :
    a = b + K / H * c := by
  have hρn : ρ ^ 2 * n = H := by rw [h2]; field_simp
  have e1 : ρ ^ 2 * n * a - K * c = ρ ^ 2 * n * b := by
    have e2 := congrArg (fun z => z * (ρ ^ 3 * n)) e
    simp only [sub_mul] at e2
    field_simp at e2
    linear_combination e2
  rw [hρn] at e1
  field_simp
  linear_combination e1

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 1): at `h` without a zero row, `𝐃N_0(h) k = N_0(h) M` gives, row by row,
`k_t = h_t M + μ_t h_t` with `μ_t = ⟨h_t, k_t⟩ / ⟨h_t, h_t⟩`. -/
private theorem row_of_fderiv_rmsNorm_zero_lzs {h k : Matrix T d ℝ} (hh : ∀ t, h t ≠ 0)
    {M : Matrix d d ℝ}
    (e : fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h k = rmsNorm 0 h * M) (t : T) :
    k t = h t ᵥ* M + ((h t ⬝ᵥ k t) / (h t ⬝ᵥ h t)) • h t := by
  rw [fderiv_rmsNorm_zero_apply h k hh] at e
  obtain ⟨hH, hq⟩ := dot_self_pos_lzs (hh t)
  have hn : (0 : ℝ) < Fintype.card d := by
    obtain ⟨j, -⟩ := Function.ne_iff.1 (hh t)
    exact Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩)
  have hs2 := Real.sq_sqrt hq.le
  have hs := Real.sqrt_pos.2 hq
  funext i
  have ei := congrFun (congrFun e t) i
  have hR : (rmsNorm 0 h * M) t i
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ * (h t ᵥ* M) i := by
    rw [Matrix.mul_apply_eq_vecMul]
    show (rmsRow 0 (h t) ᵥ* M) i = _
    rw [rmsRow, add_zero, Matrix.smul_vecMul]
    rfl
  rw [hR] at ei
  simp only [Matrix.of_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ei
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact real_row_lzs hs hH hn hs2 ei

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 1): if `k = h M + μ h` with `h ≠ 0`, then `⟨h M, h⟩ = 0`. -/
private theorem quad_of_row_lzs {h k : d → ℝ} (hh : h ≠ 0) {M : Matrix d d ℝ}
    (e : k = h ᵥ* M + ((h ⬝ᵥ k) / (h ⬝ᵥ h)) • h) : h ᵥ* M ⬝ᵥ h = 0 := by
  have hH := (dot_self_pos_lzs hh).1
  have e1 := congrArg (fun v => h ⬝ᵥ v) e
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at e1
  rw [div_mul_cancel₀ _ hH.ne'] at e1
  rw [dotProduct_comm]
  linarith

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `N_0(h) Z = 0` implies `h Z = 0` at `h` without a zero row (each row is rescaled by a
positive number). -/
private theorem mul_eq_zero_of_rmsNorm_zero_mul_lzs {m : Type*} [Fintype m]
    {h : Matrix T d ℝ} (hh : ∀ t, h t ≠ 0) (Z : Matrix d m ℝ) (hZ : rmsNorm 0 h * Z = 0) :
    h * Z = 0 := by
  funext t
  have hq := (dot_self_pos_lzs (hh t)).2
  have hrow : (rmsNorm 0 h * Z) t
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ • (h t ᵥ* Z) := by
    rw [Matrix.mul_apply_eq_vecMul]
    show rmsRow 0 (h t) ᵥ* Z = _
    rw [rmsRow, add_zero, Matrix.smul_vecMul]
  have h0 : (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ • (h t ᵥ* Z) = 0 := by
    rw [← hrow]
    exact congrFun hZ t
  rw [Matrix.mul_apply_eq_vecMul]
  exact (smul_eq_zero.1 h0).resolve_left (inv_ne_zero (Real.sqrt_pos.2 hq).ne')

/-! ### The rays `x = s w`, `s > 0` -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a nonzero row of `M S` comes from a nonzero row of `M`. -/
private theorem row_ne_zero_of_mul_lzs (M : Matrix T d ℝ) (S : Matrix d d ℝ) (t : T)
    (h : (M * S) t ≠ 0) : M t ≠ 0 := by
  intro h0
  apply h
  rw [Matrix.mul_apply_eq_vecMul, h0, Matrix.zero_vecMul]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: `h_1(s w) = s (w E S) + g(w E)` for `s > 0` (`N_0(s w E) = N_0(w E)`). -/
private theorem hOne_smul_lzs {A : Arch T d 1} (θ : Params A dIn dOut) (S : Matrix d d ℝ)
    (w : Matrix T dIn ℝ) {s : ℝ} (hs : 0 < s) :
    hOne_lzs A θ S (s • w) = s • (w * θ.E * S) + gOne_lzs A θ (w * θ.E) := by
  unfold hOne_lzs gOne_lzs
  simp only [Matrix.smul_mul]
  rw [rmsNorm_zero_smul_lzs hs]

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: `k(s w) = s (w η_E S + w E σ) + γ(w E, w η_E)` for `s > 0`, if no row of `w E`
vanishes. -/
private theorem kOne_smul_lzs {A : Arch T d 1} (θ η : Params A dIn dOut) (S σ : Matrix d d ℝ)
    (w : Matrix T dIn ℝ) (hw : ∀ t, (w * θ.E) t ≠ 0) {s : ℝ} (hs : 0 < s) :
    kOne_lzs A θ η S σ (s • w)
      = s • (w * η.E * S + w * θ.E * σ) + gam_lzs A θ η (w * θ.E) (w * η.E) := by
  unfold kOne_lzs gam_lzs
  simp only [Matrix.smul_mul, smul_add]
  rw [rmsNorm_zero_smul_lzs hs, fderiv_rmsNorm_zero_smul_lzs hs hw]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: if, for every token, the rows of `w E S` and of `g(w E)` are linearly independent,
then `s w ∈ learnedZeroDomain` for every `s > 0`. -/
private theorem smul_mem_domain_lzs {A : Arch T d 1} {θ : Params A dIn dOut}
    {R : Fin 1 → Matrix d d ℝ} {w : Matrix T dIn ℝ}
    (hw : ∀ t, LinearIndependent ℝ ![(w * θ.E * R 0) t, gOne_lzs A θ (w * θ.E) t]) {s : ℝ}
    (hs : 0 < s) : s • w ∈ learnedZeroDomain A θ R := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rw [Matrix.smul_mul]
    exact smul_ne_zero hs.ne' (row_ne_zero_of_mul_lzs _ (R 0) t ((hw t).ne_zero 0))
  · show hOne_lzs A θ (R 0) (s • w) t ≠ 0
    rw [hOne_smul_lzs θ (R 0) w hs]
    intro h0
    have := (LinearIndependent.pair_iff.1 (hw t)) s 1 (by rw [one_smul]; exact h0)
    exact hs.ne' this.1

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 1 on a ray): a quadratic polynomial `s ↦ ⟨(s a + b) Y, s a + b⟩` that vanishes
for `s > 0` has leading coefficient `⟨a Y, a⟩ = 0`. -/
private theorem quad_ray_lzs {a b : d → ℝ} {Y : Matrix d d ℝ}
    (h : ∀ s : ℝ, 0 < s → (s • a + b) ᵥ* Y ⬝ᵥ (s • a + b) = 0) : a ᵥ* Y ⬝ᵥ a = 0 := by
  have h1 := h 1 one_pos
  have h2 := h 2 two_pos
  have h3 := h 3 three_pos
  simp only [Matrix.add_vecMul, Matrix.smul_vecMul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, one_smul] at h1 h2 h3
  linear_combination (h3 - 2 * h2 + h1) / 2

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 1 on a ray): `(s a + b) Z = 0` for `s > 0` gives `a Z = 0`. -/
private theorem lin_ray_lzs {m : Type*} [Fintype m] {a b : d → ℝ} {Z : Matrix d m ℝ}
    (h : ∀ s : ℝ, 0 < s → (s • a + b) ᵥ* Z = 0) : a ᵥ* Z = 0 := by
  have h1 := h 1 one_pos
  have h2 := h 2 two_pos
  rw [Matrix.add_vecMul, Matrix.smul_vecMul] at h1 h2
  linear_combination (norm := module) h2 - h1

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (on a ray): if `a, b` are linearly independent and `s p + q` is a multiple of
`s a + b` for every `s > 0`, then `p = c a` and `q = c b` for one number `c`. -/
private theorem three_ray_lzs {V : Type*} [AddCommGroup V] [Module ℝ V] {a b p q : V}
    (hab : LinearIndependent ℝ ![a, b])
    (h : ∀ s : ℝ, 0 < s → ∃ μ : ℝ, s • p + q = μ • (s • a + b)) :
    ∃ c : ℝ, p = c • a ∧ q = c • b := by
  obtain ⟨μ₁, h1⟩ := h 1 one_pos
  obtain ⟨μ₂, h2⟩ := h 2 two_pos
  obtain ⟨μ₃, h3⟩ := h 3 three_pos
  have key : (3 * μ₃ - 4 * μ₂ + μ₁) • a + (μ₃ - 2 * μ₂ + μ₁) • b = 0 := by
    linear_combination (norm := module) (2 : ℝ) • h2 - h3 - h1
  obtain ⟨k1, k2⟩ := LinearIndependent.pair_iff.1 hab _ _ key
  obtain rfl : μ₂ = μ₁ := by linarith
  refine ⟨μ₂, ?_, ?_⟩
  · linear_combination (norm := module) h2 - h1
  · linear_combination (norm := module) (2 : ℝ) • h1 - h2

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 2 on a ray): if `a, b` are linearly independent and
`s P + Q = (s a + b) Y + μ (s a + b)` with a number `μ` for every `s > 0`, then
`P − a Y = c a` and `Q − b Y = c b` for one number `c`. -/
private theorem three_ray_Y_lzs {a b P Q : d → ℝ} {Y : Matrix d d ℝ}
    (hab : LinearIndependent ℝ ![a, b])
    (h : ∀ s : ℝ, 0 < s → ∃ μ : ℝ, s • P + Q = (s • a + b) ᵥ* Y + μ • (s • a + b)) :
    ∃ c : ℝ, P - a ᵥ* Y = c • a ∧ Q - b ᵥ* Y = c • b := by
  refine three_ray_lzs hab fun s hs => ?_
  obtain ⟨μ, e⟩ := h s hs
  refine ⟨μ, ?_⟩
  rw [Matrix.add_vecMul, Matrix.smul_vecMul] at e
  linear_combination (norm := module) e

/-! ### Linear algebra on an open set of inputs (copies of the `_rzo` helpers) -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: around a point `w₀` of an open set `G`, the points `w₀ ± δ v` lie in `G` for some
`δ > 0`. -/
private theorem exists_add_sub_mem_lzs {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {G : Set X} (hG : IsOpen G) {w₀ : X} (hw₀ : w₀ ∈ G) (v : X) :
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
/-- Helper: a matrix `Z` with `u Z = 0` for every row vector `u` is `0`. -/
private theorem eq_zero_of_vecMul_lzs {m n : Type*} [Fintype m] [DecidableEq m]
    {Z : Matrix m n ℝ} (h : ∀ u : m → ℝ, u ᵥ* Z = 0) : Z = 0 := by
  ext i j
  have := congrFun (h (Pi.single i 1)) j
  rwa [Matrix.single_one_vecMul, Matrix.row_apply] at this

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper (polarisation): if `⟨u Y, u⟩ = 0` for every `u`, then `Yᵀ = -Y`. -/
private theorem transpose_eq_neg_lzs {Y : Matrix d d ℝ} (h : ∀ u : d → ℝ, u ᵥ* Y ⬝ᵥ u = 0) :
    Yᵀ = -Y := by
  ext i j
  have hii := h (Pi.single i 1)
  have hjj := h (Pi.single j 1)
  have hij := h (Pi.single i 1 + Pi.single j 1)
  simp only [Matrix.add_vecMul, dotProduct_add, Matrix.single_one_vecMul,
    dotProduct_single_one, Pi.add_apply, Matrix.row_apply] at hii hjj hij
  simp only [Matrix.transpose_apply, Matrix.neg_apply]
  linarith

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: row `t` of `(w + δ V) M` is `(w M)_t + δ (V M)_t`. -/
private theorem row_add_mul_lzs {m n : Type*} [Fintype m] (w V : Matrix T m ℝ)
    (M : Matrix m n ℝ) (δ : ℝ) (t : T) :
    ((w + δ • V) * M) t = (w * M) t + δ • (V * M) t := by
  rw [Matrix.add_mul, Matrix.smul_mul]
  rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: row `t` of `(w - δ V) M` is `(w M)_t - δ (V M)_t`. -/
private theorem row_sub_mul_lzs {m n : Type*} [Fintype m] (w V : Matrix T m ℝ)
    (M : Matrix m n ℝ) (δ : ℝ) (t : T) :
    ((w - δ • V) * M) t = (w * M) t - δ • (V * M) t := by
  rw [Matrix.sub_mul, Matrix.smul_mul]
  rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: row `t` of `V M`, for the matrix `V` whose rows all equal `u`, is `u M`. -/
private theorem constRows_mul_lzs {m n : Type*} [Fintype m] (u : m → ℝ) (M : Matrix m n ℝ)
    (t : T) : ((Matrix.of fun _ : T => u) * M) t = u ᵥ* M := by
  rw [Matrix.mul_apply_eq_vecMul]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: row `t` of `w (P S + E σ − E S Y)` is `(w P S + w E σ)_t − (w E S)_t Y`. -/
private theorem row_lam_lzs {m : Type*} [Fintype m] (w : Matrix T m ℝ) (P E : Matrix m d ℝ)
    (S σ Y : Matrix d d ℝ) (t : T) :
    (w * (P * S + E * σ - E * S * Y)) t = (w * P * S + w * E * σ) t - (w * E * S) t ᵥ* Y := by
  have e : w * (P * S + E * σ - E * S * Y) = (w * P * S + w * E * σ) - w * E * S * Y := by
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_assoc]
  rw [e, ← Matrix.mul_apply_eq_vecMul]
  rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 1): a matrix `K` with `w K = 0` for every `w` of a nonempty open set is `0`. -/
private theorem eq_zero_of_mul_on_lzs {m n : Type*} [Fintype m] [DecidableEq m]
    {O : Set (Matrix T m ℝ)} (hO : IsOpen O) {w₀ : Matrix T m ℝ} (hw₀ : w₀ ∈ O)
    {K : Matrix m n ℝ} (h : ∀ w ∈ O, w * K = 0) : K = 0 := by
  refine eq_zero_of_vecMul_lzs fun u => ?_
  obtain ⟨δ, hδ, hp, -⟩ := exists_add_sub_mem_lzs hO hw₀ (Matrix.of fun _ : T => u)
  have e := congrFun (h _ hp) (Classical.arbitrary T)
  rw [row_add_mul_lzs, h w₀ hw₀, constRows_mul_lzs] at e
  have e2 : δ • (u ᵥ* K) = 0 := by
    rw [← zero_add (δ • (u ᵥ* K))]
    exact e
  exact (smul_eq_zero.1 e2).resolve_left hδ.ne'

omit [Nonempty T] [Fintype dOut] in
/-- Helper (Step 1): if `⟨(w E)_t Y, (w E)_t⟩ = 0` for every `w` of a nonempty open set and one
token `t`, and `E` has a left inverse, then `⟨u Y, u⟩ = 0` for every `u`
(`q(a + δ x) + q(a - δ x) = 2 q(a) + 2 δ² q(x)`). -/
private theorem quad_zero_on_lzs {O : Set (Matrix T dIn ℝ)} (hO : IsOpen O)
    {w₀ : Matrix T dIn ℝ} (hw₀ : w₀ ∈ O) (t : T) {E : Matrix dIn d ℝ} {Ep : Matrix d dIn ℝ}
    (hEp : Ep * E = 1) {Y : Matrix d d ℝ} (h : ∀ w ∈ O, (w * E) t ᵥ* Y ⬝ᵥ (w * E) t = 0)
    (u : d → ℝ) : u ᵥ* Y ⬝ᵥ u = 0 := by
  obtain ⟨δ, hδ, hp, hm⟩ := exists_add_sub_mem_lzs hO hw₀ (Matrix.of fun _ : T => u ᵥ* Ep)
  have e0 := h w₀ hw₀
  have ep := h _ hp
  have em := h _ hm
  rw [row_add_mul_lzs, constRows_mul_lzs, Matrix.vecMul_vecMul, hEp, Matrix.vecMul_one] at ep
  rw [row_sub_mul_lzs, constRows_mul_lzs, Matrix.vecMul_vecMul, hEp, Matrix.vecMul_one] at em
  simp only [Matrix.add_vecMul, Matrix.sub_vecMul, Matrix.smul_vecMul, dotProduct_add,
    add_dotProduct, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul] at ep em
  have e : (2 * δ ^ 2) * (u ᵥ* Y ⬝ᵥ u) = 0 := by
    linear_combination ep + em - 2 * e0
  have hδ2 : 2 * δ ^ 2 ≠ 0 := by positivity
  exact (mul_eq_zero.1 e).resolve_left hδ2

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 3): the algebra at `w₀ ± δ V`: if `p₀ = c₀ a`, `p₀ ± δ y = c± (a ± δ x)` and
`x, a` are linearly independent, then `y = c₀ x`. -/
private theorem prop_aux_lzs {V : Type*} [AddCommGroup V] [Module ℝ V] {a x p₀ y : V}
    {c₀ cp cm δ : ℝ} (hδ : δ ≠ 0) (hxa : LinearIndependent ℝ ![x, a]) (h0 : p₀ = c₀ • a)
    (hp : p₀ + δ • y = cp • (a + δ • x)) (hm : p₀ - δ • y = cm • (a - δ • x)) :
    y = c₀ • x := by
  have key : (δ * (cp - cm)) • x + (cp + cm - 2 * c₀) • a = 0 := by
    linear_combination (norm := module) (2 : ℝ) • h0 - hp - hm
  obtain ⟨k1, k2⟩ := LinearIndependent.pair_iff.1 hxa _ _ key
  have hc : cp = cm := by
    have := (mul_eq_zero.1 k1).resolve_left hδ
    linarith
  subst hc
  have hc0 : cp = c₀ := by linarith
  subst hc0
  have e : δ • (y - cp • x) = 0 := by
    linear_combination (norm := module) hp - h0
  rw [smul_eq_zero] at e
  exact sub_eq_zero.1 (e.resolve_left hδ)

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: for `d ≥ 2` and `a ≠ 0` there is a row `b` that is not a multiple of `a`. -/
private theorem exists_not_mul_lzs (hd : 2 ≤ Fintype.card d) {a : d → ℝ} (ha : a ≠ 0) :
    ∃ b : d → ℝ, ∀ μ : ℝ, μ • a ≠ b := by
  by_contra hcon
  push Not at hcon
  have htop : Submodule.span ℝ {a} = ⊤ :=
    Submodule.eq_top_iff'.2 fun b => by
      obtain ⟨μ, hμ⟩ := hcon b
      exact Submodule.mem_span_singleton.2 ⟨μ, hμ⟩
  have h1 := finrank_span_singleton (K := ℝ) ha
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
  omega

omit [Nonempty T] [Fintype dOut] in
/-- Helper (Step 3): if, for every `w` of an open set containing `w₀` and one token `t`,
`(w M)_t` is a multiple of `(w E)_t`, with `(w₀ E)_t ≠ 0`, `d ≥ 2` and `E` with a left inverse,
then `M = c E` for one number `c`. -/
private theorem exists_eq_smul_on_lzs (hd : 2 ≤ Fintype.card d) {O : Set (Matrix T dIn ℝ)}
    (hO : IsOpen O) {w₀ : Matrix T dIn ℝ} (hw₀ : w₀ ∈ O) (t : T) {E M : Matrix dIn d ℝ}
    {Ep : Matrix d dIn ℝ} (hEp : Ep * E = 1) (ha : (w₀ * E) t ≠ 0)
    (h : ∀ w ∈ O, ∃ c : ℝ, (w * M) t = c • (w * E) t) : ∃ c : ℝ, M = c • E := by
  classical
  obtain ⟨c₀, h0⟩ := h w₀ hw₀
  -- at every `V` with `(V E)_t` independent of `a = (w₀ E)_t`: `(V M)_t = c₀ (V E)_t`
  have good : ∀ V : Matrix T dIn ℝ, (∀ μ : ℝ, μ • (w₀ * E) t ≠ (V * E) t) →
      (V * M) t = c₀ • (V * E) t := by
    intro V hV
    obtain ⟨δ, hδ, hp, hm⟩ := exists_add_sub_mem_lzs hO hw₀ V
    obtain ⟨cp, ep⟩ := h _ hp
    obtain ⟨cm, em⟩ := h _ hm
    rw [row_add_mul_lzs, row_add_mul_lzs] at ep
    rw [row_sub_mul_lzs, row_sub_mul_lzs] at em
    refine prop_aux_lzs hδ.ne' ?_ h0 ep em
    rw [linearIndependent_fin2]
    exact ⟨ha, hV⟩
  -- a row `b` that is not a multiple of `a`, and `V_b` with `(V_b E)_t = b`
  obtain ⟨b, hb⟩ := exists_not_mul_lzs hd ha
  have hVb : ((Matrix.of fun _ : T => b ᵥ* Ep) * E) t = b := by
    rw [constRows_mul_lzs, Matrix.vecMul_vecMul, hEp, Matrix.vecMul_one]
  refine ⟨c₀, sub_eq_zero.1 (eq_zero_of_vecMul_lzs fun u => ?_)⟩
  rw [Matrix.vecMul_sub, Matrix.vecMul_smul, sub_eq_zero]
  by_cases hu : ∀ μ : ℝ, μ • (w₀ * E) t ≠ u ᵥ* E
  · -- `u E` is not a multiple of `a`
    have e := good (Matrix.of fun _ : T => u) (by rw [constRows_mul_lzs]; exact hu)
    rwa [constRows_mul_lzs, constRows_mul_lzs] at e
  · -- `u E = μ a`: then `(u + b Ep) E = μ a + b` is not a multiple of `a`, nor is `b`
    push Not at hu
    obtain ⟨μ, hμ⟩ := hu
    have e1 := good (Matrix.of fun _ : T => u + b ᵥ* Ep) (by
      intro ν hν
      rw [constRows_mul_lzs, Matrix.add_vecMul, Matrix.vecMul_vecMul, hEp, Matrix.vecMul_one,
        ← hμ] at hν
      exact hb (ν - μ) (by rw [sub_smul, hν]; abel))
    have e2 := good (Matrix.of fun _ : T => b ᵥ* Ep) (by rw [hVb]; exact hb)
    rw [constRows_mul_lzs, constRows_mul_lzs, Matrix.add_vecMul, Matrix.add_vecMul] at e1
    rw [constRows_mul_lzs, constRows_mul_lzs] at e2
    rw [e2, smul_add] at e1
    exact add_right_cancel e1

/-! ### The good inputs form an open set -/

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the inputs `w` with `w E W_read ∈ V` at which, for every token, the rows of `w E S` and
of `g(w E)` are linearly independent form an open set (`f` is continuous at `N_0(w E) W_read`, a
positive scaling of the rows of `w E W_read ∈ V`, and linear independence is an open condition). -/
private theorem isOpen_good_lzs {A : Arch T d 1} {V : Set (Matrix T (A.r 0) ℝ)} (hV : IsOpen V)
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    (hf : ContinuousOn (A.f 0) V) (θ : Params A dIn dOut) (S : Matrix d d ℝ) :
    IsOpen {w : Matrix T dIn ℝ | w * θ.E * θ.read 0 ∈ V ∧
      ∀ t, LinearIndependent ℝ ![(w * θ.E * S) t, gOne_lzs A θ (w * θ.E) t]} := by
  rw [isOpen_iff_mem_nhds]
  intro w₀ hw₀
  have hrows : ∀ t, (w₀ * θ.E) t ≠ 0 := fun t =>
    row_ne_zero_of_mul_lzs _ S t ((hw₀.2 t).ne_zero 0)
  have hc1 : Continuous fun w : Matrix T dIn ℝ => w * θ.E :=
    continuous_id.matrix_mul continuous_const
  have hc1S : Continuous fun w : Matrix T dIn ℝ => w * θ.E * S :=
    hc1.matrix_mul continuous_const
  have hc3 : Continuous fun w : Matrix T dIn ℝ => w * θ.E * θ.read 0 :=
    hc1.matrix_mul continuous_const
  have hR : Continuous fun M : Matrix T d ℝ => M * θ.read 0 :=
    continuous_id.matrix_mul continuous_const
  have hW : Continuous fun M : Matrix T (A.w 0) ℝ => M * θ.write 0 :=
    continuous_id.matrix_mul continuous_const
  -- `f` is continuous at `N_0(w₀ E) W_read`, a point of the open set `V`
  have hfc : ContinuousAt (A.f 0) (rmsNorm 0 (w₀ * θ.E) * θ.read 0) :=
    hf.continuousAt (hV.mem_nhds (rmsNorm_zero_mul_mem_lzs hVs hrows hw₀.1))
  have hc2 : ContinuousAt (fun w : Matrix T dIn ℝ => gOne_lzs A θ (w * θ.E)) w₀ := by
    have hN : ContinuousAt (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (w₀ * θ.E) :=
      (analyticAt_rmsNorm_zero _ hrows).continuousAt
    have h1 : ContinuousAt (fun w : Matrix T dIn ℝ => rmsNorm 0 (w * θ.E)) w₀ :=
      ContinuousAt.comp (f := fun w : Matrix T dIn ℝ => w * θ.E) (x := w₀) hN hc1.continuousAt
    have h2 : ContinuousAt (fun w : Matrix T dIn ℝ => rmsNorm 0 (w * θ.E) * θ.read 0) w₀ :=
      ContinuousAt.comp (f := fun w : Matrix T dIn ℝ => rmsNorm 0 (w * θ.E)) (x := w₀)
        hR.continuousAt h1
    have h3 : ContinuousAt
        (fun w : Matrix T dIn ℝ => A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0)) w₀ :=
      ContinuousAt.comp (f := fun w : Matrix T dIn ℝ => rmsNorm 0 (w * θ.E) * θ.read 0)
        (x := w₀) hfc h2
    exact ContinuousAt.comp (f := fun w : Matrix T dIn ℝ => A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0))
      (x := w₀) hW.continuousAt h3
  have ht : ∀ t, ∀ᶠ w in 𝓝 w₀,
      LinearIndependent ℝ ![(w * θ.E * S) t, gOne_lzs A θ (w * θ.E) t] := by
    intro t
    have hpair : ContinuousAt
        (fun w : Matrix T dIn ℝ => ![(w * θ.E * S) t, gOne_lzs A θ (w * θ.E) t]) w₀ := by
      refine continuousAt_pi.2 fun i => ?_
      fin_cases i
      · exact ((continuous_apply t).comp hc1S).continuousAt
      · exact ContinuousAt.comp (f := fun w : Matrix T dIn ℝ => gOne_lzs A θ (w * θ.E))
          (x := w₀) (continuous_apply t).continuousAt hc2
    exact hpair.eventually_mem (isOpen_setOfPred_linearIndependent.mem_nhds (hw₀.2 t))
  -- `w E W_read ∈ V` near `w₀`
  have hVn : ∀ᶠ w in 𝓝 w₀, w * θ.E * θ.read 0 ∈ V :=
    hc3.continuousAt.eventually_mem (hV.mem_nhds hw₀.1)
  exact hVn.and (Filter.eventually_all.2 ht)

end HelpersLzs

/-- **Proof of Theorem B.1 (iii) of the skips paper, "The case `ε = 0`", Steps 1 to 3, for one
block with a full learned skip:** let `ε = 0`, `d ≥ 2`, let `f` be continuously differentiable on
an open set `V` that is invariant under positive scalings of the rows, let `E` and `D` have rank
`d`, let the skip `A = R 0` be invertible, and let some input `w` with `w E W_read ∈ V` have, for
every token, the rows of `w E A` and of `g(w) = f(N_0(w E) W_read) W_write` linearly independent.
If the direction `(η, η_A)` of the weights and the skip is flat at every input `x` at which no
normalized row vanishes and `x E W_read ∈ V`, there are a matrix `X`, an antisymmetric `Y` and a
number `c` with `η_E = E X`, `η_A = A (Y + c I) − X A`, `η_D = −Y D`, and at every input `x` with
`x E W_read ∈ V` whose rows of `x E A` and of `g(x)` are linearly independent for every token,
the derivative of the output `g(x)` of the block along `η` is `g(x) (Y + c I)`. -/
theorem exists_of_flatSkipsOn_learned_rmsNorm_zero_on {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (V : Set (Matrix T (A.r 0) ℝ)) (hV : IsOpen V)
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    (hf : ContDiffOn ℝ 1 (A.f 0) V) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) (hR : IsUnit (R 0).det)
    (hw : ∃ w : Matrix T dIn ℝ, w * θ.E * θ.read 0 ∈ V ∧ ∀ t, LinearIndependent ℝ
      ![(w * θ.E * R 0) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t])
    (η : Params A dIn dOut) (ρ : Fin 1 → Matrix d d ℝ)
    (hη : (η, ρ) ∈ flatSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
      (learnedZeroDomain A θ R ∩ {x | x * θ.E * θ.read 0 ∈ V})) :
    ∃ (X Y : Matrix d d ℝ) (c : ℝ), Yᵀ = -Y ∧ η.E = θ.E * X ∧
      ρ 0 = R 0 * (Y + c • 1) - X * R 0 ∧ η.D = -(Y * θ.D) ∧
      ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
        (∀ t, LinearIndependent ℝ
          ![(x * θ.E * R 0) t, (A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) t]) →
        fderiv ℝ (A.f 0) (rmsNorm 0 (x * θ.E) * θ.read 0)
            (fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * θ.E * X)
                * θ.read 0
              + rmsNorm 0 (x * θ.E) * η.read 0) * θ.write 0
          + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * η.write 0
          = A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0 * (Y + c • 1) := by
  classical
  -- at an input `x` without a zero row of `x E` and with `x E W_read ∈ V`, `N_0(x E) W_read` is a
  -- positive scaling of the rows of `x E W_read`, so it lies in the open set `V`, and `f` is
  -- differentiable there
  have hfx : ∀ x : Matrix T dIn ℝ, (∀ t, (x * θ.E) t ≠ 0) → x * θ.E * θ.read 0 ∈ V →
      DifferentiableAt ℝ (A.f 0) (rmsNorm 0 (x * θ.E) * θ.read 0) := fun x hx0 hx =>
    (hf.contDiffAt (hV.mem_nhds (rmsNorm_zero_mul_mem_lzs hVs hx0 hx))).differentiableAt
      one_ne_zero
  -- a right inverse `D⁺` of `D`, a left inverse `E⁺` of `E` (both have rank `d`), and the left
  -- inverse `A⁻¹ E⁺` of `E A`
  obtain ⟨Dp, hDp⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1
    (Matrix.mulVec_surjective_iff_rank_eq_card.2 hD)
  obtain ⟨Ep, hEp⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.1
    (Matrix.vecMul_surjective_iff_rank_eq_card.2 hE)
  have hEAp : ((R 0)⁻¹ * Ep) * (θ.E * R 0) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Ep, hEp, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ hR]
  -- the inputs `U` at which `(η, ρ)` is flat
  obtain ⟨U, hUdef⟩ : ∃ U : Set (Matrix T dIn ℝ),
      U = learnedZeroDomain A θ R ∩ {x | x * θ.E * θ.read 0 ∈ V} := ⟨_, rfl⟩
  have hηU : (η, ρ) ∈ flatSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R) U := by
    rw [hUdef]
    exact hη
  have hUmem : ∀ x ∈ U, x ∈ learnedZeroDomain A θ R ∧ x * θ.E * θ.read 0 ∈ V := by
    rw [hUdef]
    exact fun x hx => hx
  have hmemU : ∀ x ∈ learnedZeroDomain A θ R, x * θ.E * θ.read 0 ∈ V → x ∈ U := by
    rw [hUdef]
    exact fun x hx1 hx2 => ⟨hx1, hx2⟩
  -- the good inputs `O`: `w E W_read ∈ V`, and for every token the rows of `w E A` and `g(w)` are
  -- independent; `O` is open and contains `w₀`, and `s w ∈ U` for `w ∈ O`, `s > 0`
  obtain ⟨O, hOdef⟩ : ∃ O : Set (Matrix T dIn ℝ), O = {w : Matrix T dIn ℝ |
      w * θ.E * θ.read 0 ∈ V ∧
        ∀ t, LinearIndependent ℝ ![(w * θ.E * R 0) t, gOne_lzs A θ (w * θ.E) t]} := ⟨_, rfl⟩
  have hOo : IsOpen O := hOdef ▸ isOpen_good_lzs hV hVs hf.continuousOn θ (R 0)
  obtain ⟨w₀, hw₀⟩ := hw
  have hw₀O : w₀ ∈ O := by
    rw [hOdef]
    exact hw₀
  have hOV : ∀ w ∈ O, w * θ.E * θ.read 0 ∈ V := fun w hw => by
    rw [hOdef] at hw
    exact hw.1
  have hind : ∀ w ∈ O, ∀ t,
      LinearIndependent ℝ ![(w * θ.E * R 0) t, gOne_lzs A θ (w * θ.E) t] := fun w hw => by
    rw [hOdef] at hw
    exact hw.2
  have hrowsA : ∀ w ∈ O, ∀ t, (w * θ.E * R 0) t ≠ 0 := fun w hw t => (hind w hw t).ne_zero 0
  have hrows : ∀ w ∈ O, ∀ t, (w * θ.E) t ≠ 0 := fun w hw t =>
    row_ne_zero_of_mul_lzs _ (R 0) t (hrowsA w hw t)
  have hU : ∀ w ∈ O, ∀ s : ℝ, 0 < s → s • w ∈ U := fun w hw s hs =>
    hmemU _ (smul_mem_domain_lzs (hind w hw) hs) (by
      rw [Matrix.smul_mul]
      exact smul_mul_mem_lzs hVs (hOV w hw) hs)
  have t₀ : T := Classical.arbitrary T
  -- Step 1 at an input `x` of `U`: with `Y = -η_D D⁺`, `𝐃N_0(h_1) k = N_0(h_1) Y`, so
  -- `k_t = h_t Y + μ_t h_t`, and `h_1 (Y D + η_D) = 0`
  obtain ⟨Y, hYdef⟩ : ∃ Y : Matrix d d ℝ, Y = -(η.D * Dp) := ⟨_, rfl⟩
  have step1 : ∀ x ∈ U,
      (∀ t, kOne_lzs A θ η (R 0) (ρ 0) x t = hOne_lzs A θ (R 0) x t ᵥ* Y
        + ((hOne_lzs A θ (R 0) x t ⬝ᵥ kOne_lzs A θ η (R 0) (ρ 0) x t)
          / (hOne_lzs A θ (R 0) x t ⬝ᵥ hOne_lzs A θ (R 0) x t)) • hOne_lzs A θ (R 0) x t) ∧
      hOne_lzs A θ (R 0) x * (Y * θ.D + η.D) = 0 := by
    intro x hx
    obtain ⟨hxD, hxV⟩ := hUmem x hx
    have hx2 : ∀ t, hOne_lzs A θ (R 0) x t ≠ 0 := hxD.2
    have h0 := flat_eq_lzs hA θ η R ρ x hxD (hfx x hxD.1 hxV)
      (fderiv_eq_zero_of_flatSkipsOn_lzs hηU hx)
    have hNY : fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (hOne_lzs A θ (R 0) x)
        (kOne_lzs A θ η (R 0) (ρ 0) x) = rmsNorm 0 (hOne_lzs A θ (R 0) x) * Y := by
      have e := congrArg (· * Dp) h0
      simp only [Matrix.add_mul, Matrix.mul_assoc, hDp, Matrix.mul_one, Matrix.zero_mul] at e
      rw [hYdef, Matrix.mul_neg]
      exact eq_neg_of_add_eq_zero_left e
    refine ⟨row_of_fderiv_rmsNorm_zero_lzs hx2 hNY, ?_⟩
    refine mul_eq_zero_of_rmsNorm_zero_mul_lzs hx2 _ ?_
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← hNY]
    exact h0
  -- Step 1 on the rays `s w`, `w ∈ O`: `⟨(w E A)_t Y, (w E A)_t⟩ = 0` and
  -- `(w E A)(Y D + η_D) = 0`; `E A` has the left inverse `A⁻¹ E⁺`, so `Y` is antisymmetric and
  -- `η_D = -Y D`
  have hq : ∀ w ∈ O, (w * (θ.E * R 0)) t₀ ᵥ* Y ⬝ᵥ (w * (θ.E * R 0)) t₀ = 0 := by
    intro w hw
    rw [← Matrix.mul_assoc]
    refine quad_ray_lzs (b := gOne_lzs A θ (w * θ.E) t₀) fun s hs => ?_
    have hx := hU w hw s hs
    have hx2 : ∀ t, hOne_lzs A θ (R 0) (s • w) t ≠ 0 := (hUmem _ hx).1.2
    have e := quad_of_row_lzs (hx2 t₀) ((step1 _ hx).1 t₀)
    rw [hOne_smul_lzs θ (R 0) w hs] at e
    exact e
  have hY : Yᵀ = -Y := transpose_eq_neg_lzs (quad_zero_on_lzs hOo hw₀O t₀ hEAp hq)
  have hZ : ∀ w ∈ O, w * (θ.E * R 0 * (Y * θ.D + η.D)) = 0 := by
    intro w hw
    funext t
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_apply_eq_vecMul]
    refine lin_ray_lzs (b := gOne_lzs A θ (w * θ.E) t) fun s hs => ?_
    have e := congrFun (step1 _ (hU w hw s hs)).2 t
    rw [hOne_smul_lzs θ (R 0) w hs, Matrix.mul_apply_eq_vecMul] at e
    exact e
  have hZ0 : Y * θ.D + η.D = 0 := by
    have e := eq_zero_of_mul_on_lzs hOo hw₀O hZ
    calc Y * θ.D + η.D = ((R 0)⁻¹ * Ep) * (θ.E * R 0) * (Y * θ.D + η.D) := by
          rw [hEAp, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, e, Matrix.mul_zero]
  have hYD : η.D = -(Y * θ.D) := eq_neg_of_add_eq_zero_right hZ0
  -- Step 2, on the rays `s w`, `w ∈ O`: the terms of order `s` and the constant terms of
  -- `k_t = h_t Y + μ h_t` give `(w Λ₀)_t − (w E A)_t Y = c (w E A)_t` and `γ_t − g_t Y = c g_t`,
  -- with `Λ₀ = η_E A + E ρ` and one number `c`
  have step2 : ∀ w ∈ O, ∀ t, ∃ c : ℝ,
      (w * η.E * R 0 + w * θ.E * ρ 0) t - (w * θ.E * R 0) t ᵥ* Y = c • (w * θ.E * R 0) t ∧
      gam_lzs A θ η (w * θ.E) (w * η.E) t - gOne_lzs A θ (w * θ.E) t ᵥ* Y
        = c • gOne_lzs A θ (w * θ.E) t := by
    intro w hw t
    refine three_ray_Y_lzs (hind w hw t) fun s hs => ?_
    have e := (step1 _ (hU w hw s hs)).1 t
    rw [kOne_smul_lzs θ η (R 0) (ρ 0) w (hrows w hw) hs, hOne_smul_lzs θ (R 0) w hs] at e
    exact ⟨_, e⟩
  -- Step 3: `Λ = η_E A + E ρ − E A Y` has `(w Λ)_t` a multiple of `(w E A)_t` on `O`, so
  -- `Λ = c E A`, that is `η_E A + E ρ = E A (Y + c I)`
  obtain ⟨c, hc⟩ : ∃ c : ℝ, η.E * R 0 + θ.E * ρ 0 - θ.E * R 0 * Y = c • (θ.E * R 0) := by
    refine exists_eq_smul_on_lzs hd hOo hw₀O t₀ hEAp ?_ fun w hw => ?_
    · rw [← Matrix.mul_assoc]
      exact hrowsA w₀ hw₀O t₀
    · obtain ⟨c, h1, -⟩ := step2 w hw t₀
      refine ⟨c, ?_⟩
      rw [row_lam_lzs, ← Matrix.mul_assoc w θ.E (R 0)]
      exact h1
  have hES : η.E * R 0 + θ.E * ρ 0 = θ.E * R 0 * (Y + c • 1) := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, ← hc]
    abel
  -- Step 4: `X = A (Y + c I) A⁻¹ − ρ A⁻¹`; then `η_E = E X` and `ρ = A (Y + c I) − X A`
  obtain ⟨X, hXdef⟩ : ∃ X : Matrix d d ℝ,
      X = R 0 * (Y + c • 1) * (R 0)⁻¹ - ρ 0 * (R 0)⁻¹ := ⟨_, rfl⟩
  have hEX : η.E = θ.E * X := by
    calc η.E = η.E * R 0 * (R 0)⁻¹ := (Matrix.mul_nonsing_inv_cancel_right _ _ hR).symm
      _ = (θ.E * R 0 * (Y + c • 1) - θ.E * ρ 0) * (R 0)⁻¹ := by
          rw [← hES, add_sub_cancel_right]
      _ = θ.E * X := by
        rw [hXdef]
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  have hρ : ρ 0 = R 0 * (Y + c • 1) - X * R 0 := by
    rw [hXdef, Matrix.sub_mul, Matrix.nonsing_inv_mul_cancel_right _ _ hR,
      Matrix.nonsing_inv_mul_cancel_right _ _ hR, sub_sub_cancel]
  refine ⟨X, Y, c, hY, hEX, hρ, hYD, fun x hxV hxind => ?_⟩
  -- the last clause: an input `x` of it is in `O`; Step 2 at `w = x` with the number `c` of
  -- Step 3 gives `γ(x) = g(x) (Y + c I)`
  have hxO : x ∈ O := by
    rw [hOdef]
    exact ⟨hxV, hxind⟩
  have hgam : gam_lzs A θ η (x * θ.E) (x * η.E) = gOne_lzs A θ (x * θ.E) * (Y + c • 1) := by
    funext t
    obtain ⟨c', h1, h2⟩ := step2 x hxO t
    have h3 := row_lam_lzs x η.E θ.E (R 0) (ρ 0) Y t
    rw [hc, Matrix.mul_smul, ← Matrix.mul_assoc] at h3
    have e : c' • (x * θ.E * R 0) t = c • (x * θ.E * R 0) t := h1.symm.trans h3.symm
    have hcc : c' = c := by
      have e2 : (c' - c) • (x * θ.E * R 0) t = 0 := by rw [sub_smul, e, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 e2).resolve_right (hrowsA x hxO t))
    rw [Matrix.mul_apply_eq_vecMul, Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_one,
      ← hcc, ← h2]
    abel
  rw [hEX, ← Matrix.mul_assoc x θ.E X] at hgam
  exact hgam


end Skips
