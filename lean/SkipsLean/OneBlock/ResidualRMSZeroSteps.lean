import SkipsLean.OneBlock.ResidualRMSStepsOn
import SkipsLean.Dimension.UpperBoundResidualRMSNormZero
import Mathlib.Analysis.Normed.Module.Connected
import SkipsLean.Depth.SuffixZero

/-!
# One residual block under pre-RMSNorm with `ε = 0`: the flat directions

Paper (skips paper), proof of Theorem B.1 (v): "With `ε = 0`, `N_ε(h) = √d_model h/‖h‖` ignores the
length of each token, so the block reads only rows on the sphere of radius `√d_model`. Let `V_θ`
be the space of directions that move only the weights of the block and leave its output unchanged
to first order at every input whose rows lie on this sphere; it contains the symmetries inside the
block. We show that the flat directions of the residual network are those of `CO(d_model)` and
those of `V_θ` […].
The residual network. Write `h_1 = x E + g(x)`, with `g(x) = f(N_ε(x E) W_read) W_write`, and
`y = N_ε(h_1) D`, and let `η` be flat. Step 1 of part (ii) runs as before, except that with
`ε = 0` the derivative `DN_ε(h)` projects onto the vectors orthogonal to `h` and scales by
`√d_model/‖h‖`, so its kernel is spanned by `h`. Hence `N_ε(h_1) Y` is orthogonal to `h_1`; as
`h_1` takes every value in an open set, `Y_s = 0`, and `D_θ h_1 η = h_1 Y + μ(x) h_1` with a
number `μ(x)`, for attention one per token. […] Take the inputs `x = t w` with `t > 0`. […] For
generic parameters `w E` and `g(w)` are linearly independent for all `w` in an open set, since
otherwise the block would map every point of the sphere to a multiple of itself. […] and
`η′_E = c E` with one number `c`. The scaling `E ↦ (1 + τ) E`, `W_write ↦ (1 + τ) W_write`
multiplies `h_1` by `1 + τ` and is the scale in `CO(d_model)`. Subtracting `c` times its direction
leaves a flat `η″` that moves only the weights of the block, with `D_θ g η″ = 0` at the inputs
`t w`. Their normalized rows cover an open set of the sphere, and the derivative of the block along
`η″` is analytic on the sphere, so `η″ ∈ V_θ`."

"Notation and flat directions" (Appendix B): with `ε = 0`, "every input" excludes the inputs at
which a row of a hidden state that is normalized vanishes.

Stated here, for a fixed map `f` of the block that is analytic everywhere (tanh, GELU, SwiGLU,
GeGLU and attention blocks): the set `U_θ` of the inputs at which no row of `x E` and no row of
`h_1` vanishes (`residualZeroDomain`); and the conclusion of the passage for a direction `η` that
is flat at the inputs of `U_θ`: an antisymmetric `Y` and a number `c` with `η_E = E (Y + c I)`,
`η_D = −Y D`, and the direction `η − η^Y − c η^{scale}`, which moves only the weights of the block
(read `η_read + Y W_read`, write `η_write − W_write (Y + c I)`), has derivative zero at every `n`
whose rows lie on the sphere of radius `√d`. The condition of the paper on generic parameters is
a hypothesis: some input `w` at which, for every token, the rows of `w E` and of `g(w)` are
linearly independent. `d ≥ 2` is the Scope's and is needed (for `d = 1` the step "`η′_E = c E`"
fails).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The inputs of a residual network of one block under pre-RMSNorm with `ε = 0` at which no
normalized row vanishes:** no row of `h_0 = x E` and no row of
`h_1 = x E + f(N_0(x E) W_read) W_write` is zero. -/
def residualZeroDomain (A : Arch T d 1) (θ : Params A dIn dOut) : Set (Matrix T dIn ℝ) :=
  {x | (∀ t, (x * θ.E) t ≠ 0) ∧
    ∀ t, (x * θ.E + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) t ≠ 0}

section HelpersRz0

open Filter
open scoped Topology

/-! ### RMSNorm with `ε = 0` at matrices without a zero row -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `N_0` forgets a positive scale, `N_0(s a) = N_0(a)` for `s > 0` (row by row, as the
private `rmsRow_zero_smul` of `Basic/RMSNorm.lean`). -/
private theorem rmsNorm_zero_smul_rz0 {s : ℝ} (hs : 0 < s) (a : Matrix T d ℝ) :
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
private theorem differentiableAt_rmsNorm_zero_rz0 {h : Matrix T d ℝ} (hh : ∀ t, h t ≠ 0) :
    DifferentiableAt ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h :=
  (analyticAt_rmsNorm_zero h hh).differentiableAt

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `𝐃N_0(s a)(s b) = 𝐃N_0(a)(b)` for `s > 0`, at `a` without a zero row (`N_0` is
invariant under `v ↦ s v`, so its derivative at `s a` composed with `s` is its derivative at
`a`). -/
private theorem fderiv_rmsNorm_zero_smul_rz0 {s : ℝ} (hs : 0 < s) {a : Matrix T d ℝ}
    (ha : ∀ t, a t ≠ 0) (b : Matrix T d ℝ) :
    fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (s • a) (s • b)
      = fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) a b := by
  have hsa : ∀ t, (s • a) t ≠ 0 := fun t => by
    show s • a t ≠ 0
    exact smul_ne_zero hs.ne' (ha t)
  have h1 := (differentiableAt_rmsNorm_zero_rz0 hsa).hasFDerivAt.comp a
    ((hasFDerivAt_id a).const_smul s)
  have e : (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) ∘ HSMul.hSMul s = rmsNorm 0 := by
    funext v
    exact rmsNorm_zero_smul_rz0 hs v
  rw [e] at h1
  have h2 : fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) a b
      = fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (s • a) (s • b) :=
    DFunLike.congr_fun h1.fderiv b
  exact h2.symm

/-! ### Step 0: the chain rule along a line of parameters, at an input of `U` -/

/-- Helper: the block `g(a) = f(N_0(a) W_read) W_write`, as a function of `a = x E`. -/
private noncomputable def gOne_rz0 (A : Arch T d 1) (θ : Params A dIn dOut) (a : Matrix T d ℝ) :
    Matrix T d ℝ :=
  A.f 0 (rmsNorm 0 a * θ.read 0) * θ.write 0

/-- Helper: the hidden state `h_1 = x E + g(x E)` of one residual block. -/
private noncomputable def hOne_rz0 (A : Arch T d 1) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    Matrix T d ℝ :=
  x * θ.E + gOne_rz0 A θ (x * θ.E)

/-- Helper: the derivative of the block along `η`, at `a = x E` and `b = x η_E`:
`𝐃f(N_0(a) W_read)(𝐃N_0(a)(b) W_read + N_0(a) η_read) W_write + f(N_0(a) W_read) η_write`. -/
private noncomputable def gam_rz0 (A : Arch T d 1) (θ η : Params A dIn dOut)
    (a b : Matrix T d ℝ) : Matrix T d ℝ :=
  fderiv ℝ (A.f 0) (rmsNorm 0 a * θ.read 0)
      (fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) a b * θ.read 0
        + rmsNorm 0 a * η.read 0) * θ.write 0
    + A.f 0 (rmsNorm 0 a * θ.read 0) * η.write 0

/-- Helper: the derivative `k(x) = x η_E + γ(x E, x η_E)` of `h_1` along `η` (Step 0). -/
private noncomputable def kOne_rz0 (A : Arch T d 1) (θ η : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T d ℝ :=
  x * η.E + gam_rz0 A θ η (x * θ.E) (x * η.E)

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the function of one residual block under pre-RMSNorm, `F_θ(x) = N_0(h_1) D`. -/
private theorem eval_eq_rz0 {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    eval A 1 θ x = rmsNorm 0 (hOne_rz0 A θ x) * θ.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]
  simp only [Pi.one_apply, Matrix.mul_one]
  rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product rule for matrices depending on one real variable. -/
private theorem hasDerivAt_mul_rz0 {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
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
private theorem hasDerivAt_affine_rz0 {m n : Type*} [Fintype m] [Fintype n]
    (M N : Matrix m n ℝ) : HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (Step 0): along the line `θ + τ η`, the hidden state `h_1` has the derivative `k(x)`
at `τ = 0`, if no row of `x E` vanishes. -/
private theorem hasDerivAt_hOne_line_rz0 {A : Arch T d 1} (hf : Differentiable ℝ (A.f 0))
    (θ η : Params A dIn dOut) (x : Matrix T dIn ℝ) (hx : ∀ t, (x * θ.E) t ≠ 0) :
    HasDerivAt (fun τ : ℝ => hOne_rz0 A (θ + τ • η) x) (kOne_rz0 A θ η x) 0 := by
  -- `x E(τ)`
  have hE : HasDerivAt (fun τ : ℝ => x * (θ + τ • η).E) (x * η.E) 0 := by
    have h := hasDerivAt_mul_rz0 (hasDerivAt_const (0 : ℝ) x) (hasDerivAt_affine_rz0 θ.E η.E)
      (P0 := x) (Q0 := θ.E) rfl (by simp)
    rw [Matrix.zero_mul, zero_add] at h
    exact h
  -- `N_0(x E(τ))`
  have hN : HasDerivAt (fun τ : ℝ => rmsNorm 0 (x * (θ + τ • η).E))
      (fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * η.E)) 0 :=
    (differentiableAt_rmsNorm_zero_rz0 hx).hasFDerivAt.comp_hasDerivAt_of_eq 0 hE (by simp)
  -- `N_0(x E(τ)) W_read(τ)`
  have hNR := hasDerivAt_mul_rz0 hN (hasDerivAt_affine_rz0 (θ.read 0) (η.read 0))
    (P0 := rmsNorm 0 (x * θ.E)) (Q0 := θ.read 0) (by simp) (by simp)
  -- `f(N_0(x E(τ)) W_read(τ))`
  have hF := (hf (rmsNorm 0 (x * θ.E) * θ.read 0)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hNR
    (by simp)
  -- `f(…) W_write(τ)`
  have hFW := hasDerivAt_mul_rz0 hF (hasDerivAt_affine_rz0 (θ.write 0) (η.write 0))
    (P0 := A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0)) (Q0 := θ.write 0) (by simp) (by simp)
  exact hE.add hFW

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two matrix-valued maps that are differentiable at a point is
differentiable there (matrix multiplication is a continuous bilinear map). -/
private theorem differentiableAt_matMul_rz0 {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
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

omit [Nonempty T] in
/-- Helper: at an input of `U`, the output is a differentiable function of the parameters at
`θ`. -/
private theorem differentiableAt_eval_rz0 {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (hf : Differentiable ℝ (A.f 0)) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ residualZeroDomain A θ) :
    DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' x) θ := by
  have e : (fun θ' : Params A dIn dOut => eval A 1 θ' x)
      = fun θ' => rmsNorm 0 (hOne_rz0 A θ' x) * θ'.D :=
    funext fun θ' => eval_eq_rz0 hA θ' x
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
  -- `x E`, `N_0(x E)` and `N_0(x E) W_read`
  have h1 : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => x * θ'.E) θ :=
    differentiableAt_matMul_rz0 (differentiableAt_const x) hE
  have h2 : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => rmsNorm 0 (x * θ'.E)) θ :=
    DifferentiableAt.comp (f := fun θ' : Params A dIn dOut => x * θ'.E) θ
      (differentiableAt_rmsNorm_zero_rz0 hx.1) h1
  have h3 : DifferentiableAt ℝ
      (fun θ' : Params A dIn dOut => rmsNorm 0 (x * θ'.E) * θ'.read 0) θ :=
    differentiableAt_matMul_rz0 h2 hR
  have h4 : DifferentiableAt ℝ
      (fun θ' : Params A dIn dOut => A.f 0 (rmsNorm 0 (x * θ'.E) * θ'.read 0)) θ :=
    DifferentiableAt.comp (f := fun θ' : Params A dIn dOut => rmsNorm 0 (x * θ'.E) * θ'.read 0)
      θ (hf _) h3
  -- `h_1`, `N_0(h_1)` and `N_0(h_1) D`
  have h5 : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => hOne_rz0 A θ' x) θ :=
    h1.add (differentiableAt_matMul_rz0 h4 hW)
  have h6 : DifferentiableAt ℝ
      (fun θ' : Params A dIn dOut => rmsNorm 0 (hOne_rz0 A θ' x)) θ :=
    DifferentiableAt.comp (f := fun θ' : Params A dIn dOut => hOne_rz0 A θ' x) θ
      (differentiableAt_rmsNorm_zero_rz0 hx.2) h5
  exact differentiableAt_matMul_rz0 h6 hD

omit [Fintype T] [Nonempty T] in
/-- Helper: a direction that is flat at the inputs of `U` has derivative `0` at an input of `U`. -/
private theorem fderiv_eq_zero_of_flatOn_rz0 {A : Arch T d 1} {θ η : Params A dIn dOut}
    {U : Set (Matrix T dIn ℝ)} (hη : η ∈ flatOn A 1 θ U) {x : Matrix T dIn ℝ} (hx : x ∈ U) :
    fderiv ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' x) θ η = 0 :=
  LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hη x) hx)

omit [Nonempty T] in
/-- Helper (Step 0): at an input of `U` along which `η` is flat,
`𝐃N_0(h_1) k(x) D + N_0(h_1) η_D = 0`. -/
private theorem flat_eq_rz0 {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (hf : Differentiable ℝ (A.f 0)) (θ η : Params A dIn dOut)
    (hη : η ∈ flatOn A 1 θ (residualZeroDomain A θ)) (x : Matrix T dIn ℝ)
    (hx : x ∈ residualZeroDomain A θ) :
    fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (hOne_rz0 A θ x) (kOne_rz0 A θ η x)
        * θ.D + rmsNorm 0 (hOne_rz0 A θ x) * η.D = 0 := by
  -- flatness: the derivative along the line is `0`
  have h1 := hasDerivAt_eval_line (A := A) 1 θ η x (differentiableAt_eval_rz0 hA hf θ x hx)
  rw [fderiv_eq_zero_of_flatOn_rz0 hη hx] at h1
  -- the same derivative by the chain rule
  have hh := hasDerivAt_hOne_line_rz0 hf θ η x hx.1
  have hN := (differentiableAt_rmsNorm_zero_rz0 (T := T) (d := d) hx.2).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hh (by rw [zero_smul, add_zero]; rfl)
  have h2 := hasDerivAt_mul_rz0 hN (hasDerivAt_affine_rz0 θ.D η.D)
    (P0 := rmsNorm 0 (hOne_rz0 A θ x)) (Q0 := θ.D) (by simp) (by simp)
  have e : (fun τ : ℝ => eval A 1 (θ + τ • η) x)
      = fun τ => rmsNorm 0 (hOne_rz0 A (θ + τ • η) x) * (θ.D + τ • η.D) := by
    funext τ
    rw [eval_eq_rz0 hA]
    rfl
  rw [e] at h1
  exact h2.unique h1

end HelpersRz0

/-- **Proof of Theorem B.1 (v) of the skips paper, "The residual network":** let `ε = 0`, `d ≥ 2`,
let the fixed map `f` of the block be analytic, let `E` and `D` have rank `d`, and let some input
`w` have, for every token, the rows of `w E` and of `g(w) = f(N_0(w E) W_read) W_write` linearly
independent. If `η` is flat at every input at which no normalized row vanishes, there are an
antisymmetric `Y` and a number `c` with `η_E = E (Y + c I)`, `η_D = −Y D`, and at every `n` with
all rows on the sphere of radius `√d` the derivative of `n ↦ f(n W_read) W_write` along
`η_read + Y W_read`, `η_write − W_write (Y + c I)` vanishes. -/
theorem exists_antisymm_scale_of_flatOn_residual_rmsNorm_zero {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t])
    (η : Params A dIn dOut) (hη : η ∈ flatOn A 1 θ (residualZeroDomain A θ)) :
    ∃ (Y : Matrix d d ℝ) (c : ℝ), Yᵀ = -Y ∧ η.E = θ.E * (Y + c • 1) ∧ η.D = -(Y * θ.D) ∧
      ∀ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = Fintype.card d) →
        fderiv ℝ (A.f 0) (n * θ.read 0) (n * (η.read 0 + Y * θ.read 0)) * θ.write 0
          + A.f 0 (n * θ.read 0) * (η.write 0 - θ.write 0 * (Y + c • 1)) = 0 := by
  sorry

end Skips
