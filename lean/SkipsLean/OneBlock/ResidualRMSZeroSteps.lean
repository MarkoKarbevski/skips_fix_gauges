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

/-! ### Step 1: the rows of `𝐃N_0(h) k = N_0(h) M` -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `⟨v, v⟩ > 0` and `⟨v, v⟩ / d > 0` for a row `v ≠ 0`. -/
private theorem dot_self_pos_rz0 {v : d → ℝ} (hv : v ≠ 0) :
    0 < v ⬝ᵥ v ∧ 0 < (v ⬝ᵥ v) / (Fintype.card d : ℝ) := by
  have h1 : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j))
      (fun h => hv (dotProduct_self_eq_zero.1 h.symm))
  obtain ⟨j, -⟩ := Function.ne_iff.1 hv
  have h2 : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩)
  exact ⟨h1, div_pos h1 h2⟩

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the real identity behind the rows of Step 1: from
`ρ⁻¹ a − (K/n) ρ⁻³ c = ρ⁻¹ b` with `ρ² = H/n` follows `a = b + (K/H) c`. -/
private theorem real_row_rz0 {a b c K H n ρ : ℝ} (hρ : 0 < ρ) (hH : 0 < H) (hn : 0 < n)
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
private theorem row_of_fderiv_rmsNorm_zero_rz0 {h k : Matrix T d ℝ} (hh : ∀ t, h t ≠ 0)
    {M : Matrix d d ℝ}
    (e : fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h k = rmsNorm 0 h * M) (t : T) :
    k t = h t ᵥ* M + ((h t ⬝ᵥ k t) / (h t ⬝ᵥ h t)) • h t := by
  rw [fderiv_rmsNorm_zero_apply h k hh] at e
  obtain ⟨hH, hq⟩ := dot_self_pos_rz0 (hh t)
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
  exact real_row_rz0 hs hH hn hs2 ei

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 1): if `k = h M + μ h` with `h ≠ 0`, then `⟨h M, h⟩ = 0`. -/
private theorem quad_of_row_rz0 {h k : d → ℝ} (hh : h ≠ 0) {M : Matrix d d ℝ}
    (e : k = h ᵥ* M + ((h ⬝ᵥ k) / (h ⬝ᵥ h)) • h) : h ᵥ* M ⬝ᵥ h = 0 := by
  have hH := (dot_self_pos_rz0 hh).1
  have e1 := congrArg (fun v => h ⬝ᵥ v) e
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at e1
  rw [div_mul_cancel₀ _ hH.ne'] at e1
  rw [dotProduct_comm]
  linarith

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `N_0(h) Z = 0` implies `h Z = 0` at `h` without a zero row (each row is rescaled by a
positive number). -/
private theorem mul_eq_zero_of_rmsNorm_zero_mul_rz0 {m : Type*} [Fintype m]
    {h : Matrix T d ℝ} (hh : ∀ t, h t ≠ 0) (Z : Matrix d m ℝ) (hZ : rmsNorm 0 h * Z = 0) :
    h * Z = 0 := by
  funext t
  have hq := (dot_self_pos_rz0 (hh t)).2
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

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: `h_1(s w) = s (w E) + g(w E)` for `s > 0` (`N_0(s w E) = N_0(w E)`). -/
private theorem hOne_smul_rz0 {A : Arch T d 1} (θ : Params A dIn dOut) (w : Matrix T dIn ℝ)
    {s : ℝ} (hs : 0 < s) : hOne_rz0 A θ (s • w) = s • (w * θ.E) + gOne_rz0 A θ (w * θ.E) := by
  unfold hOne_rz0 gOne_rz0
  rw [Matrix.smul_mul, rmsNorm_zero_smul_rz0 hs]

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: `k(s w) = s (w η_E) + γ(w E, w η_E)` for `s > 0`, if no row of `w E` vanishes. -/
private theorem kOne_smul_rz0 {A : Arch T d 1} (θ η : Params A dIn dOut) (w : Matrix T dIn ℝ)
    (hw : ∀ t, (w * θ.E) t ≠ 0) {s : ℝ} (hs : 0 < s) :
    kOne_rz0 A θ η (s • w) = s • (w * η.E) + gam_rz0 A θ η (w * θ.E) (w * η.E) := by
  unfold kOne_rz0 gam_rz0
  rw [Matrix.smul_mul, Matrix.smul_mul, rmsNorm_zero_smul_rz0 hs,
    fderiv_rmsNorm_zero_smul_rz0 hs hw]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: if, for every token, the rows of `w E` and of `g(w E)` are linearly independent, then
`s w ∈ U` for every `s > 0`. -/
private theorem smul_mem_domain_rz0 {A : Arch T d 1} {θ : Params A dIn dOut}
    {w : Matrix T dIn ℝ}
    (hw : ∀ t, LinearIndependent ℝ ![(w * θ.E) t, gOne_rz0 A θ (w * θ.E) t]) {s : ℝ}
    (hs : 0 < s) : s • w ∈ residualZeroDomain A θ := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rw [Matrix.smul_mul]
    exact smul_ne_zero hs.ne' ((hw t).ne_zero 0)
  · show hOne_rz0 A θ (s • w) t ≠ 0
    rw [hOne_smul_rz0 θ w hs]
    intro h0
    have := (LinearIndependent.pair_iff.1 (hw t)) s 1 (by rw [one_smul]; exact h0)
    exact hs.ne' this.1

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 1 on a ray): a quadratic polynomial `s ↦ ⟨(s a + b) Y, s a + b⟩` that vanishes
for `s > 0` has leading coefficient `⟨a Y, a⟩ = 0`. -/
private theorem quad_ray_rz0 {a b : d → ℝ} {Y : Matrix d d ℝ}
    (h : ∀ s : ℝ, 0 < s → (s • a + b) ᵥ* Y ⬝ᵥ (s • a + b) = 0) : a ᵥ* Y ⬝ᵥ a = 0 := by
  have h1 := h 1 one_pos
  have h2 := h 2 two_pos
  have h3 := h 3 three_pos
  simp only [Matrix.add_vecMul, Matrix.smul_vecMul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, one_smul] at h1 h2 h3
  linear_combination (h3 - 2 * h2 + h1) / 2

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 1 on a ray): `(s a + b) Z = 0` for `s > 0` gives `a Z = 0`. -/
private theorem lin_ray_rz0 {m : Type*} [Fintype m] {a b : d → ℝ} {Z : Matrix d m ℝ}
    (h : ∀ s : ℝ, 0 < s → (s • a + b) ᵥ* Z = 0) : a ᵥ* Z = 0 := by
  have h1 := h 1 one_pos
  have h2 := h 2 two_pos
  rw [Matrix.add_vecMul, Matrix.smul_vecMul] at h1 h2
  linear_combination (norm := module) h2 - h1

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 3 on a ray): if `a, b` are linearly independent and `s p + q` is a multiple of
`s a + b` for every `s > 0`, then `p = c a` and `q = c b` for one number `c`. -/
private theorem three_ray_rz0 {V : Type*} [AddCommGroup V] [Module ℝ V] {a b p q : V}
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

/-! ### Linear algebra on an open set of inputs -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: around a point `w₀` of an open set `G`, the points `w₀ ± δ v` lie in `G` for some
`δ > 0`. -/
private theorem exists_add_sub_mem_rz0 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
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
private theorem eq_zero_of_vecMul_rz0 {m n : Type*} [Fintype m] [DecidableEq m]
    {Z : Matrix m n ℝ} (h : ∀ u : m → ℝ, u ᵥ* Z = 0) : Z = 0 := by
  ext i j
  have := congrFun (h (Pi.single i 1)) j
  rwa [Matrix.single_one_vecMul, Matrix.row_apply] at this

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper (polarisation): if `⟨u Y, u⟩ = 0` for every `u`, then `Yᵀ = -Y`. -/
private theorem transpose_eq_neg_rz0 {Y : Matrix d d ℝ} (h : ∀ u : d → ℝ, u ᵥ* Y ⬝ᵥ u = 0) :
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
private theorem row_add_mul_rz0 {m n : Type*} [Fintype m] (w V : Matrix T m ℝ)
    (M : Matrix m n ℝ) (δ : ℝ) (t : T) :
    ((w + δ • V) * M) t = (w * M) t + δ • (V * M) t := by
  rw [Matrix.add_mul, Matrix.smul_mul]
  rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: row `t` of `(w - δ V) M` is `(w M)_t - δ (V M)_t`. -/
private theorem row_sub_mul_rz0 {m n : Type*} [Fintype m] (w V : Matrix T m ℝ)
    (M : Matrix m n ℝ) (δ : ℝ) (t : T) :
    ((w - δ • V) * M) t = (w * M) t - δ • (V * M) t := by
  rw [Matrix.sub_mul, Matrix.smul_mul]
  rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: row `t` of `V M`, for the matrix `V` whose rows all equal `u`, is `u M`. -/
private theorem constRows_mul_rz0 {m n : Type*} [Fintype m] (u : m → ℝ) (M : Matrix m n ℝ)
    (t : T) : ((Matrix.of fun _ : T => u) * M) t = u ᵥ* M := by
  rw [Matrix.mul_apply_eq_vecMul]
  rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 1): a matrix `K` with `w K = 0` for every `w` of a nonempty open set is `0`. -/
private theorem eq_zero_of_mul_on_rz0 {m n : Type*} [Fintype m] [DecidableEq m]
    {O : Set (Matrix T m ℝ)} (hO : IsOpen O) {w₀ : Matrix T m ℝ} (hw₀ : w₀ ∈ O)
    {K : Matrix m n ℝ} (h : ∀ w ∈ O, w * K = 0) : K = 0 := by
  refine eq_zero_of_vecMul_rz0 fun u => ?_
  obtain ⟨δ, hδ, hp, -⟩ := exists_add_sub_mem_rz0 hO hw₀ (Matrix.of fun _ : T => u)
  have e := congrFun (h _ hp) (Classical.arbitrary T)
  rw [row_add_mul_rz0, h w₀ hw₀, constRows_mul_rz0] at e
  have e2 : δ • (u ᵥ* K) = 0 := by
    rw [← zero_add (δ • (u ᵥ* K))]
    exact e
  exact (smul_eq_zero.1 e2).resolve_left hδ.ne'

omit [Nonempty T] [Fintype dOut] in
/-- Helper (Step 1): if `⟨(w E)_t Y, (w E)_t⟩ = 0` for every `w` of a nonempty open set and one
token `t`, and `E` has a left inverse, then `⟨u Y, u⟩ = 0` for every `u`
(`q(a + δ x) + q(a - δ x) = 2 q(a) + 2 δ² q(x)`). -/
private theorem quad_zero_on_rz0 {O : Set (Matrix T dIn ℝ)} (hO : IsOpen O)
    {w₀ : Matrix T dIn ℝ} (hw₀ : w₀ ∈ O) (t : T) {E : Matrix dIn d ℝ} {Ep : Matrix d dIn ℝ}
    (hEp : Ep * E = 1) {Y : Matrix d d ℝ} (h : ∀ w ∈ O, (w * E) t ᵥ* Y ⬝ᵥ (w * E) t = 0)
    (u : d → ℝ) : u ᵥ* Y ⬝ᵥ u = 0 := by
  obtain ⟨δ, hδ, hp, hm⟩ := exists_add_sub_mem_rz0 hO hw₀ (Matrix.of fun _ : T => u ᵥ* Ep)
  have e0 := h w₀ hw₀
  have ep := h _ hp
  have em := h _ hm
  rw [row_add_mul_rz0, constRows_mul_rz0, Matrix.vecMul_vecMul, hEp, Matrix.vecMul_one] at ep
  rw [row_sub_mul_rz0, constRows_mul_rz0, Matrix.vecMul_vecMul, hEp, Matrix.vecMul_one] at em
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
private theorem prop_aux_rz0 {V : Type*} [AddCommGroup V] [Module ℝ V] {a x p₀ y : V}
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
private theorem exists_not_mul_rz0 (hd : 2 ≤ Fintype.card d) {a : d → ℝ} (ha : a ≠ 0) :
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
private theorem exists_eq_smul_on_rz0 (hd : 2 ≤ Fintype.card d) {O : Set (Matrix T dIn ℝ)}
    (hO : IsOpen O) {w₀ : Matrix T dIn ℝ} (hw₀ : w₀ ∈ O) (t : T) {E M : Matrix dIn d ℝ}
    {Ep : Matrix d dIn ℝ} (hEp : Ep * E = 1) (ha : (w₀ * E) t ≠ 0)
    (h : ∀ w ∈ O, ∃ c : ℝ, (w * M) t = c • (w * E) t) : ∃ c : ℝ, M = c • E := by
  classical
  obtain ⟨c₀, h0⟩ := h w₀ hw₀
  -- at every `V` with `(V E)_t` independent of `a = (w₀ E)_t`: `(V M)_t = c₀ (V E)_t`
  have good : ∀ V : Matrix T dIn ℝ, (∀ μ : ℝ, μ • (w₀ * E) t ≠ (V * E) t) →
      (V * M) t = c₀ • (V * E) t := by
    intro V hV
    obtain ⟨δ, hδ, hp, hm⟩ := exists_add_sub_mem_rz0 hO hw₀ V
    obtain ⟨cp, ep⟩ := h _ hp
    obtain ⟨cm, em⟩ := h _ hm
    rw [row_add_mul_rz0, row_add_mul_rz0] at ep
    rw [row_sub_mul_rz0, row_sub_mul_rz0] at em
    refine prop_aux_rz0 hδ.ne' ?_ h0 ep em
    rw [linearIndependent_fin2]
    exact ⟨ha, hV⟩
  -- a row `b` that is not a multiple of `a`, and `V_b` with `(V_b E)_t = b`
  obtain ⟨b, hb⟩ := exists_not_mul_rz0 hd ha
  have hVb : ((Matrix.of fun _ : T => b ᵥ* Ep) * E) t = b := by
    rw [constRows_mul_rz0, Matrix.vecMul_vecMul, hEp, Matrix.vecMul_one]
  refine ⟨c₀, sub_eq_zero.1 (eq_zero_of_vecMul_rz0 fun u => ?_)⟩
  rw [Matrix.vecMul_sub, Matrix.vecMul_smul, sub_eq_zero]
  by_cases hu : ∀ μ : ℝ, μ • (w₀ * E) t ≠ u ᵥ* E
  · -- `u E` is not a multiple of `a`
    have e := good (Matrix.of fun _ : T => u) (by rw [constRows_mul_rz0]; exact hu)
    rwa [constRows_mul_rz0, constRows_mul_rz0] at e
  · -- `u E = μ a`: then `(u + b Ep) E = μ a + b` is not a multiple of `a`, nor is `b`
    push Not at hu
    obtain ⟨μ, hμ⟩ := hu
    have e1 := good (Matrix.of fun _ : T => u + b ᵥ* Ep) (by
      intro ν hν
      rw [constRows_mul_rz0, Matrix.add_vecMul, Matrix.vecMul_vecMul, hEp, Matrix.vecMul_one,
        ← hμ] at hν
      exact hb (ν - μ) (by rw [sub_smul, hν]; abel))
    have e2 := good (Matrix.of fun _ : T => b ᵥ* Ep) (by rw [hVb]; exact hb)
    rw [constRows_mul_rz0, constRows_mul_rz0, Matrix.add_vecMul, Matrix.add_vecMul] at e1
    rw [constRows_mul_rz0, constRows_mul_rz0] at e2
    rw [e2, smul_add] at e1
    exact add_right_cancel e1

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
