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

/-! ### The good inputs form an open set -/

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the inputs `w` at which, for every token, the rows of `w E` and of `g(w E)` are
linearly independent form an open set (`g` is continuous where no row of `w E` vanishes, and
linear independence is an open condition). -/
private theorem isOpen_good_rz0 {A : Arch T d 1} (hf : Continuous (A.f 0))
    (θ : Params A dIn dOut) :
    IsOpen {w : Matrix T dIn ℝ |
      ∀ t, LinearIndependent ℝ ![(w * θ.E) t, gOne_rz0 A θ (w * θ.E) t]} := by
  rw [isOpen_iff_mem_nhds]
  intro w₀ hw₀
  have hrows : ∀ t, (w₀ * θ.E) t ≠ 0 := fun t => (hw₀ t).ne_zero 0
  have hc1 : Continuous fun w : Matrix T dIn ℝ => w * θ.E :=
    continuous_id.matrix_mul continuous_const
  have hR : Continuous fun M : Matrix T d ℝ => M * θ.read 0 :=
    continuous_id.matrix_mul continuous_const
  have hW : Continuous fun M : Matrix T (A.w 0) ℝ => M * θ.write 0 :=
    continuous_id.matrix_mul continuous_const
  have hc2 : ContinuousAt (fun w : Matrix T dIn ℝ => gOne_rz0 A θ (w * θ.E)) w₀ := by
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
        (x := w₀) hf.continuousAt h2
    exact ContinuousAt.comp (f := fun w : Matrix T dIn ℝ => A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0))
      (x := w₀) hW.continuousAt h3
  have ht : ∀ t, ∀ᶠ w in 𝓝 w₀,
      LinearIndependent ℝ ![(w * θ.E) t, gOne_rz0 A θ (w * θ.E) t] := by
    intro t
    have hpair : ContinuousAt
        (fun w : Matrix T dIn ℝ => ![(w * θ.E) t, gOne_rz0 A θ (w * θ.E) t]) w₀ := by
      refine continuousAt_pi.2 fun i => ?_
      fin_cases i
      · exact ((continuous_apply t).comp hc1).continuousAt
      · exact ContinuousAt.comp (f := fun w : Matrix T dIn ℝ => gOne_rz0 A θ (w * θ.E))
          (x := w₀) (continuous_apply t).continuousAt hc2
    exact hpair.eventually_mem (isOpen_setOfPred_linearIndependent.mem_nhds (hw₀ t))
  exact Filter.eventually_all.2 ht

/-! ### Step 4: analyticity, the connected set of matrices without a zero row -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two matrix-valued maps analytic at a point is analytic there (as the
private `analyticAt_matMul_hz` of `Depth/HiddenZero.lean`). -/
private theorem analyticAt_matMul_rz0 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : X → Matrix m n ℝ} {g : X → Matrix n p ℝ} {y : X}
    (hf : AnalyticAt ℝ f y) (hg : AnalyticAt ℝ g y) :
    AnalyticAt ℝ (fun y => f y * g y) y := by
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.analyticAt_bilinear (f y, g y)).comp₂ hf hg

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: an analytic family of continuous linear maps, applied to an analytic family of
vectors, is analytic (as the private `analyticOnNhd_clm_apply'` of `Depth/StepTanhRMS.lean`). -/
private theorem analyticAt_clm_apply_rz0 {X E F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {J : X → E →L[ℝ] F} {v : X → E} {x : X} (hJ : AnalyticAt ℝ J x)
    (hv : AnalyticAt ℝ v x) : AnalyticAt ℝ (fun x => J x (v x)) x :=
  ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).analyticAt_bilinear (J x, v x)).comp₂ hJ hv

omit [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 4): for an analytic `f`, the derivative of `n ↦ f(n R) W` along `(R', W')` at
`n = N_0(v)`, `v ↦ 𝐃f(N_0(v) R)(N_0(v) R') W + f(N_0(v) R) W'`, is analytic at every `v` without
a zero row. -/
private theorem analyticAt_Psi_rz0 {r w : Type*} [Fintype r] [Fintype w]
    {f : Matrix T r ℝ → Matrix T w ℝ} (hf : AnalyticOnNhd ℝ f Set.univ) (R R' : Matrix d r ℝ)
    (W W' : Matrix w d ℝ) {v : Matrix T d ℝ} (hv : ∀ t, v t ≠ 0) :
    AnalyticAt ℝ (fun v : Matrix T d ℝ => fderiv ℝ f (rmsNorm 0 v * R) (rmsNorm 0 v * R') * W
      + f (rmsNorm 0 v * R) * W') v := by
  have hN := analyticAt_rmsNorm_zero v hv
  have h1 : AnalyticAt ℝ (fun v : Matrix T d ℝ => rmsNorm 0 v * R) v :=
    analyticAt_matMul_rz0 hN analyticAt_const
  have h1' : AnalyticAt ℝ (fun v : Matrix T d ℝ => rmsNorm 0 v * R') v :=
    analyticAt_matMul_rz0 hN analyticAt_const
  have hfd := hf.fderiv (rmsNorm 0 v * R) trivial
  have h2 := AnalyticAt.comp (f := fun v : Matrix T d ℝ => rmsNorm 0 v * R) (x := v) hfd h1
  have h3 := analyticAt_clm_apply_rz0 h2 h1'
  have h4 := AnalyticAt.comp (f := fun v : Matrix T d ℝ => rmsNorm 0 v * R) (x := v)
    (hf _ trivial) h1
  exact (analyticAt_matMul_rz0 h3 analyticAt_const).add (analyticAt_matMul_rz0 h4 analyticAt_const)

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (Step 4): for `d ≥ 2`, the matrices without a zero row form a connected set (a product
of copies of `ℝ^d ∖ {0}`). -/
private theorem isPreconnected_rows_rz0 (hd : 2 ≤ Fintype.card d) :
    IsPreconnected {v : Matrix T d ℝ | ∀ t, v t ≠ 0} := by
  have e : {v : Matrix T d ℝ | ∀ t, v t ≠ 0}
      = Set.univ.pi (fun _ : T => ({0}ᶜ : Set (d → ℝ))) := by
    ext v
    exact ⟨fun h i _ => h i, fun h i => h i (Set.mem_univ i)⟩
  rw [e]
  refine isPreconnected_univ_pi fun _ => ?_
  refine (isConnected_compl_singleton_of_one_lt_rank ?_ 0).isPreconnected
  rw [rank_fun']
  exact_mod_cast (by omega : 1 < Fintype.card d)

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
  classical
  have hfd : Differentiable ℝ (A.f 0) := fun z => (hf z trivial).differentiableAt
  -- a right inverse `D⁺` of `D` and a left inverse `E⁺` of `E` (both have rank `d`)
  obtain ⟨Dp, hDp⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1
    (Matrix.mulVec_surjective_iff_rank_eq_card.2 hD)
  obtain ⟨Ep, hEp⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.1
    (Matrix.vecMul_surjective_iff_rank_eq_card.2 hE)
  -- the good inputs `O`: for every token the rows of `w E` and `g(w E)` are independent; `O` is
  -- open and contains `w₀`, and `s w ∈ U` for `w ∈ O`, `s > 0`
  obtain ⟨O, hOdef⟩ : ∃ O : Set (Matrix T dIn ℝ), O = {w : Matrix T dIn ℝ |
      ∀ t, LinearIndependent ℝ ![(w * θ.E) t, gOne_rz0 A θ (w * θ.E) t]} := ⟨_, rfl⟩
  have hOo : IsOpen O := hOdef ▸ isOpen_good_rz0 hfd.continuous θ
  obtain ⟨w₀, hw₀⟩ := hw
  have hw₀O : w₀ ∈ O := by rw [hOdef]; exact hw₀
  have hind : ∀ w ∈ O, ∀ t, LinearIndependent ℝ ![(w * θ.E) t, gOne_rz0 A θ (w * θ.E) t] :=
    fun w hw => by rw [hOdef] at hw; exact hw
  have hrows : ∀ w ∈ O, ∀ t, (w * θ.E) t ≠ 0 := fun w hw t => (hind w hw t).ne_zero 0
  have hU : ∀ w ∈ O, ∀ s : ℝ, 0 < s → s • w ∈ residualZeroDomain A θ := fun w hw _ hs =>
    smul_mem_domain_rz0 (hind w hw) hs
  have t₀ : T := Classical.arbitrary T
  -- Step 1, for a flat direction `η'`, at an input `x` of `U`: with `Y' = -η'_D D⁺`,
  -- `𝐃N_0(h_1) k = N_0(h_1) Y'`, so `k_t = h_t Y' + μ_t h_t`, and `h_1 (Y' D + η'_D) = 0`
  have step1 : ∀ η' : Params A dIn dOut, η' ∈ flatOn A 1 θ (residualZeroDomain A θ) →
      ∀ x ∈ residualZeroDomain A θ,
        (∀ t, kOne_rz0 A θ η' x t = hOne_rz0 A θ x t ᵥ* (-(η'.D * Dp))
          + ((hOne_rz0 A θ x t ⬝ᵥ kOne_rz0 A θ η' x t)
            / (hOne_rz0 A θ x t ⬝ᵥ hOne_rz0 A θ x t)) • hOne_rz0 A θ x t) ∧
        hOne_rz0 A θ x * (-(η'.D * Dp) * θ.D + η'.D) = 0 := by
    intro η' hη' x hx
    have hx2 : ∀ t, hOne_rz0 A θ x t ≠ 0 := hx.2
    have h0 := flat_eq_rz0 hA hfd θ η' hη' x hx
    have hNY : fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (hOne_rz0 A θ x)
        (kOne_rz0 A θ η' x) = rmsNorm 0 (hOne_rz0 A θ x) * (-(η'.D * Dp)) := by
      have e := congrArg (· * Dp) h0
      simp only [Matrix.add_mul, Matrix.mul_assoc, hDp, Matrix.mul_one, Matrix.zero_mul] at e
      rw [Matrix.mul_neg]
      exact eq_neg_of_add_eq_zero_left e
    refine ⟨row_of_fderiv_rmsNorm_zero_rz0 hx2 hNY, ?_⟩
    refine mul_eq_zero_of_rmsNorm_zero_mul_rz0 hx2 _ ?_
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← hNY]
    exact h0
  -- Step 1 for `η` on the rays `s w`, `w ∈ O`: `⟨(w E)_t Y, (w E)_t⟩ = 0` and
  -- `(w E)(Y D + η_D) = 0`; hence `Y` is antisymmetric and `η_D = -Y D`
  obtain ⟨Y, hYdef⟩ : ∃ Y : Matrix d d ℝ, Y = -(η.D * Dp) := ⟨_, rfl⟩
  have hq : ∀ w ∈ O, (w * θ.E) t₀ ᵥ* Y ⬝ᵥ (w * θ.E) t₀ = 0 := by
    intro w hw
    refine quad_ray_rz0 (b := gOne_rz0 A θ (w * θ.E) t₀) fun s hs => ?_
    have hx := hU w hw s hs
    have hx2 : ∀ t, hOne_rz0 A θ (s • w) t ≠ 0 := hx.2
    have e := quad_of_row_rz0 (hx2 t₀) ((step1 η hη _ hx).1 t₀)
    rw [← hYdef, hOne_smul_rz0 θ w hs] at e
    exact e
  have hY : Yᵀ = -Y := transpose_eq_neg_rz0 (quad_zero_on_rz0 hOo hw₀O t₀ hEp hq)
  have hZ : ∀ w ∈ O, w * (θ.E * (Y * θ.D + η.D)) = 0 := by
    intro w hw
    funext t
    rw [← Matrix.mul_assoc, Matrix.mul_apply_eq_vecMul]
    refine lin_ray_rz0 (b := gOne_rz0 A θ (w * θ.E) t) fun s hs => ?_
    have e := congrFun (step1 η hη _ (hU w hw s hs)).2 t
    rw [← hYdef, hOne_smul_rz0 θ w hs, Matrix.mul_apply_eq_vecMul] at e
    exact e
  have hZ0 : Y * θ.D + η.D = 0 := by
    have e := congrArg (Ep * ·) (eq_zero_of_mul_on_rz0 hOo hw₀O hZ)
    simp only [← Matrix.mul_assoc, hEp, Matrix.one_mul, Matrix.mul_zero] at e
    exact e
  have hYD : η.D = -(Y * θ.D) := eq_neg_of_add_eq_zero_right hZ0
  -- Step 3, for a flat direction `ψ` with `ψ_D = 0`, on the rays `s w`, `w ∈ O`:
  -- `s (w ψ_E)_t + γ_t = μ (s (w E)_t + g_t)`, so `(w ψ_E)_t = c (w E)_t` and `γ_t = c g_t`
  have step3 : ∀ ψ : Params A dIn dOut, ψ ∈ flatOn A 1 θ (residualZeroDomain A θ) → ψ.D = 0 →
      ∀ w ∈ O, ∀ t, ∃ c : ℝ, (w * ψ.E) t = c • (w * θ.E) t ∧
        gam_rz0 A θ ψ (w * θ.E) (w * ψ.E) t = c • gOne_rz0 A θ (w * θ.E) t := by
    intro ψ hψ hψD w hw t
    refine three_ray_rz0 (hind w hw t) fun s hs => ?_
    have e := (step1 ψ hψ _ (hU w hw s hs)).1 t
    rw [hψD, Matrix.zero_mul, neg_zero, Matrix.vecMul_zero, zero_add,
      kOne_smul_rz0 θ ψ w (hrows w hw) hs, hOne_smul_rz0 θ w hs] at e
    exact ⟨_, e⟩
  -- Step 2: `η' = η - η^Y` is flat on `U`, with `η'_D = 0`
  obtain ⟨η', hη'def⟩ : ∃ η', η' = η - cobDir θ (fun _ => Y) := ⟨_, rfl⟩
  have hη' : η' ∈ flatOn A 1 θ (residualZeroDomain A θ) := hη'def ▸
    Submodule.sub_mem _ hη
      (flat_le_flatOn θ _ (cobDir_const_mem_flat_residual_rmsNorm_zero θ hA Y hY))
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
  -- Step 3 for `η'`: `(w η'_E)_t` is a multiple of `(w E)_t` on `O`, so `η'_E = c E`
  obtain ⟨c, hcE⟩ : ∃ c : ℝ, η'.E = c • θ.E := by
    refine exists_eq_smul_on_rz0 hd hOo hw₀O t₀ hEp (hrows w₀ hw₀O t₀) fun w hw => ?_
    obtain ⟨c, hc1, -⟩ := step3 η' hη' hη'D w hw t₀
    exact ⟨c, hc1⟩
  -- Step 4: `ψ = η' - c η^{scale}` is flat on `U`, moves only the weights of the block
  obtain ⟨ψ, hψdef⟩ : ∃ ψ, ψ = η' - scaleDir θ (fun _ => c) := ⟨_, rfl⟩
  have hψ : ψ ∈ flatOn A 1 θ (residualZeroDomain A θ) := hψdef ▸
    Submodule.sub_mem _ hη'
      (flat_le_flatOn θ _ (scaleDir_const_mem_flat_residual_rmsNorm_zero θ hA c))
  have hψE : ψ.E = 0 := by
    rw [hψdef]
    show η'.E - c • θ.E = 0
    rw [hcE, sub_self]
  have hψD : ψ.D = 0 := by
    rw [hψdef]
    show η'.D - 0 = 0
    rw [hη'D, sub_zero]
  have hψr : ψ.read 0 = η.read 0 + Y * θ.read 0 := by
    rw [hψdef]
    show η'.read 0 - 0 = _
    rw [sub_zero, hη'r]
  have hψw : ψ.write 0 = η.write 0 - θ.write 0 * (Y + c • 1) := by
    rw [hψdef]
    show η'.write 0 - c • θ.write 0 = _
    rw [hη'w, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
    abel
  -- Step 3 for `ψ` (`ψ_E = 0`): the derivative `γ` of the block vanishes at `w E`, `w ∈ O`
  have hgam : ∀ w ∈ O, gam_rz0 A θ ψ (w * θ.E) (w * ψ.E) = 0 := by
    intro w hw
    funext t
    obtain ⟨c', h1, h2⟩ := step3 ψ hψ hψD w hw t
    rw [hψE, Matrix.mul_zero] at h1
    have hc' : c' = 0 :=
      (smul_eq_zero.1 (show c' • (w * θ.E) t = 0 from h1.symm)).resolve_right (hrows w hw t)
    rw [h2, hc', zero_smul]
    rfl
  -- `Ψ(v) = 𝐃f(N_0(v) W_read)(N_0(v) ψ_read) W_write + f(N_0(v) W_read) ψ_write`
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Matrix T d ℝ → Matrix T d ℝ, Ψ = fun v =>
      fderiv ℝ (A.f 0) (rmsNorm 0 v * θ.read 0) (rmsNorm 0 v * ψ.read 0) * θ.write 0
        + A.f 0 (rmsNorm 0 v * θ.read 0) * ψ.write 0 := ⟨_, rfl⟩
  have hΨgam : ∀ w : Matrix T dIn ℝ, Ψ (w * θ.E) = gam_rz0 A θ ψ (w * θ.E) (w * ψ.E) := by
    intro w
    rw [hΨ]
    simp only [gam_rz0, hψE, Matrix.mul_zero, map_zero, Matrix.zero_mul, zero_add]
  -- `Ψ` vanishes near `w₀ E` (every `v` near `w₀ E` is `w E` with `w ∈ O`), is analytic on the
  -- connected set of the matrices without a zero row, hence vanishes there
  have hΩ : Set.EqOn Ψ 0 {v : Matrix T d ℝ | ∀ t, v t ≠ 0} := by
    refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero (𝕜 := ℝ) (fun v hv => ?_)
      (isPreconnected_rows_rz0 hd) (hrows w₀ hw₀O) ?_
    · rw [hΨ]
      exact analyticAt_Psi_rz0 hf _ _ _ _ hv
    · have hσ : Continuous fun v : Matrix T d ℝ => w₀ + (v - w₀ * θ.E) * Ep :=
        continuous_const.add ((continuous_id.sub continuous_const).matrix_mul continuous_const)
      have hσ0 : w₀ + (w₀ * θ.E - w₀ * θ.E) * Ep = w₀ := by
        rw [sub_self, Matrix.zero_mul, add_zero]
      have hev : ∀ᶠ v in nhds (w₀ * θ.E), w₀ + (v - w₀ * θ.E) * Ep ∈ O :=
        hσ.continuousAt.preimage_mem_nhds (by rw [hσ0]; exact hOo.mem_nhds hw₀O)
      filter_upwards [hev] with v hv
      have hvE : (w₀ + (v - w₀ * θ.E) * Ep) * θ.E = v := by
        rw [Matrix.add_mul, Matrix.mul_assoc, hEp, Matrix.mul_one, add_sub_cancel]
      rw [Pi.zero_apply, ← hvE, hΨgam, hgam _ hv]
  -- at `n` with rows on the sphere: `n` has no zero row and `N_0(n) = n`
  refine ⟨Y, c, hY, ?_, hYD, fun n hn => ?_⟩
  · rw [hη'E] at hcE
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, ← hcE]
    abel
  · have hdpos : (0 : ℝ) < Fintype.card d := by exact_mod_cast (by omega : 0 < Fintype.card d)
    have hn0 : ∀ t, n t ≠ 0 := fun t h0 => by
      have := hn t
      rw [h0, dotProduct_zero] at this
      exact hdpos.ne this
    have hNn : rmsNorm 0 n = n := by
      funext t
      show rmsRow 0 (n t) = n t
      rw [rmsRow, hn t, div_self hdpos.ne', add_zero, Real.sqrt_one, inv_one, one_smul]
    have e := hΩ hn0
    rw [hΨ, Pi.zero_apply] at e
    dsimp only at e
    rw [hNn, hψr, hψw] at e
    exact e

end Skips
