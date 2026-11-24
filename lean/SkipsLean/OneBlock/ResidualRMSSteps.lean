import SkipsLean.Depth.SuffixRMS
import SkipsLean.Residual.UpperBoundSymmetries

/-!
# One residual block under pre-RMSNorm: the final normalization, large inputs, the skip

Paper (skips paper): proof of Theorem B.1 (ii) (Theorem 4.6 (ii) of the main text), Steps 1 to 3,
for `ε > 0` and no biases. The network is

  `h_1 = x E + g(x)`, `g(x) = f(N_ε(x E) W_read) W_write`, `y = N_ε(h_1) D`,

with `N_ε` applied to every token. For a flat direction `η`:

* Step 1 (the final normalization): `η_D = -Y D` for a matrix `Y`, and
  `D_θ h_1 η = h_1 Y + (h_1 Y_s h_1^⊤ / (d ε)) h_1` at every token, `Y_s = (Y + Y^⊤)/2`;
* Step 2 (large inputs): at the inputs `x = t w`, `t → ∞`, the term of order `t³` gives `Y_s = 0`:
  `Y` is antisymmetric;
* Step 3 (the skip): with `η^Y` the direction of the orthogonal changes of basis `I + τ Y + O(τ²)`
  shared by `h_0` and `h_1` (`cobDir θ (fun _ => Y)`), the direction `η' = η - η^Y` is flat, has
  `η'_D = 0` and `D_θ h_1 η' = 0` at every input, and the inputs `t w` give `η'_E = 0`.

What is left of `D_θ h_1 η' = 0` is the last clause of the statement below: the derivative of
`n ↦ f(n W_read) W_write` along the entries of `η'` at the weights of the block vanishes at every
`n = N_ε(x E)`. Step 4 of the paper starts there (`OneBlock/ResidualRMSMlp.lean`,
`OneBlock/ResidualRMSGated.lean`).

The steps do not depend on the kind of block: they are stated for an arbitrary continuously
differentiable map `f`, and for hidden states with the rows `T`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

section Helpers

open Filter
open scoped Topology

/-! ### Step 0: the chain rule along a line of parameters -/

/-- Helper: the hidden state `h_1 = x E + f(N_ε(x E) W_read) W_write` of one residual block. -/
private noncomputable def hOneRS (A : Arch T d 1) (ε : ℝ) (θ : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T d ℝ :=
  x * θ.E + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * θ.write 0

/-- Helper: the derivative `k(x)` of `h_1` along `η` (Step 0). -/
private noncomputable def kOneRS (A : Arch T d 1) (ε : ℝ) (θ η : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T d ℝ :=
  x * η.E + fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
      (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * η.E) * θ.read 0
        + rmsNorm ε (x * θ.E) * η.read 0) * θ.write 0
    + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * η.write 0

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the function of one residual block under pre-RMSNorm, `F_θ(x) = N_ε(h_1) D`. -/
private theorem eval_eq_rs {A : Arch T d 1} {ε : ℝ} (hA : A.χ = rmsNorm ε)
    (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    eval A 1 θ x = rmsNorm ε (hOneRS A ε θ x) * θ.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]
  simp only [Pi.one_apply, Matrix.mul_one]
  rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product rule for matrices depending on one real variable. -/
private theorem hasDerivAt_mul_rs {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
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
private theorem hasDerivAt_affine_rs {m n : Type*} [Fintype m] [Fintype n] (M N : Matrix m n ℝ) :
    HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

omit [Nonempty T] [Fintype dOut] in
/-- Helper (Step 0): along the line `θ + τ η`, the hidden state `h_1` has the derivative `k(x)`
at `τ = 0`. -/
private theorem hasDerivAt_hOne_line {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hf : Differentiable ℝ (A.f 0)) (θ η : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    HasDerivAt (fun τ : ℝ => hOneRS A ε (θ + τ • η) x) (kOneRS A ε θ η x) 0 := by
  -- `x E(τ)`
  have hE : HasDerivAt (fun τ : ℝ => x * (θ + τ • η).E) (x * η.E) 0 := by
    have h := hasDerivAt_mul_rs (hasDerivAt_const (0 : ℝ) x) (hasDerivAt_affine_rs θ.E η.E)
      (P0 := x) (Q0 := θ.E) rfl (by simp)
    rw [Matrix.zero_mul, zero_add] at h
    exact h
  -- `N_ε(x E(τ))`
  have hN : HasDerivAt (fun τ : ℝ => rmsNorm ε (x * (θ + τ • η).E))
      (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * η.E)) 0 :=
    ((differentiable_rmsNorm hε) (x * θ.E)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hE
      (by simp)
  -- `N_ε(x E(τ)) W_read(τ)`
  have hNR := hasDerivAt_mul_rs hN (hasDerivAt_affine_rs (θ.read 0) (η.read 0))
    (P0 := rmsNorm ε (x * θ.E)) (Q0 := θ.read 0) (by simp) (by simp)
  -- `f(N_ε(x E(τ)) W_read(τ))`
  have hF := ((hf (rmsNorm ε (x * θ.E) * θ.read 0))).hasFDerivAt.comp_hasDerivAt_of_eq 0 hNR
    (by simp)
  -- `f(…) W_write(τ)`
  have hFW := hasDerivAt_mul_rs hF (hasDerivAt_affine_rs (θ.write 0) (η.write 0))
    (P0 := A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0)) (Q0 := θ.write 0) (by simp) (by simp)
  have h := hE.add hFW
  rw [← add_assoc] at h
  exact h

omit [Nonempty T] in
/-- Helper (Step 0): a flat direction `η` gives `𝐃N_ε(h_1) k(x) D + N_ε(h_1) η_D = 0` at every
input. -/
private theorem flat_eq_rs {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : Differentiable ℝ (A.f 0)) (θ η : Params A dIn dOut) (hη : η ∈ flat A 1 θ)
    (x : Matrix T dIn ℝ) :
    fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (hOneRS A ε θ x) (kOneRS A ε θ η x)
        * θ.D + rmsNorm ε (hOneRS A ε θ x) * η.D = 0 := by
  have hdiff : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' x) θ :=
    differentiable_eval (fun ℓ => by rw [Subsingleton.elim ℓ 0]; exact hf)
      (by rw [hA]; exact differentiable_rmsNorm hε) x θ
  -- flatness: the derivative along the line is `0`
  have h1 := hasDerivAt_eval_line (A := A) 1 θ η x hdiff
  have h0 : fderiv ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' x) θ η = 0 :=
    LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hη x)
  rw [h0] at h1
  -- the same derivative by the chain rule
  have hh := hasDerivAt_hOne_line hε hf θ η x
  have hN := ((differentiable_rmsNorm (T := T) (d := d) hε) (hOneRS A ε θ x)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hh (by simp)
  have h2 := hasDerivAt_mul_rs hN (hasDerivAt_affine_rs θ.D η.D)
    (P0 := rmsNorm ε (hOneRS A ε θ x)) (Q0 := θ.D) (by simp) (by simp)
  have e : (fun τ : ℝ => eval A 1 (θ + τ • η) x)
      = fun τ => rmsNorm ε (hOneRS A ε (θ + τ • η) x) * (θ.D + τ • η.D) := by
    funext τ
    rw [eval_eq_rs hA]
    rfl
  rw [e] at h1
  exact h2.unique h1

/-! ### Step 1: algebra of the final normalization -/

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `0 ≤ ⟨v, v⟩`. -/
private theorem dot_self_nonneg_rs (v : d → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- Helper: the coefficient `μ(v) = ⟨v Y, v⟩ / (d ε)` of Step 1. -/
private noncomputable def muRS (ε : ℝ) (Y : Matrix d d ℝ) (v : d → ℝ) : ℝ :=
  (v ᵥ* Y ⬝ᵥ v) / ((Fintype.card d : ℝ) * ε)

/-- Helper: the matrix whose row `t` is `μ(h_t) h_t`. -/
private noncomputable def muScaleRS (ε : ℝ) (Y : Matrix d d ℝ) (h : Matrix T d ℝ) :
    Matrix T d ℝ :=
  Matrix.of fun t => muRS ε Y (h t) • h t

omit [Nonempty T] in
/-- Helper (Step 1): `𝐃N_ε(h) (h Y + μ ⊙ h) = N_ε(h) Y`. -/
private theorem fderiv_rmsNorm_muScale {ε : ℝ} (hε : 0 < ε) (hd : (0 : ℝ) < Fintype.card d)
    (h : Matrix T d ℝ) (Y : Matrix d d ℝ) :
    fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) h (h * Y + muScaleRS ε Y h)
      = rmsNorm ε h * Y := by
  rw [fderiv_rmsNorm_apply hε]
  funext t i
  have hpos : 0 < (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε := by
    have := dot_self_nonneg_rs (h t)
    positivity
  have hR : (rmsNorm ε h * Y) t
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ • (h t ᵥ* Y) := by
    rw [Matrix.mul_apply_eq_vecMul]
    show rmsRow ε (h t) ᵥ* Y = _
    rw [rmsRow, Matrix.smul_vecMul]
  have hU : (h * Y + muScaleRS ε Y h) t = h t ᵥ* Y + muRS ε Y (h t) • h t := by
    rfl
  rw [hR]
  simp only [Matrix.of_apply, hU]
  have hs2 := Real.sq_sqrt hpos.le
  have hs := Real.sqrt_pos.2 hpos
  generalize Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε) = s at hs hs2
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct_add,
    dotProduct_smul, muRS]
  rw [dotProduct_comm (h t) (h t ᵥ* Y)]
  field_simp
  have hs2' : s ^ 2 * (Fintype.card d : ℝ) = h t ⬝ᵥ h t + ε * Fintype.card d := by
    rw [hs2]
    field_simp
  linear_combination ((h t ᵥ* Y ⬝ᵥ h t) * h t i) * hs2'

/-! ### Linear algebra -/

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix `Z` with `u Z = 0` for every row vector `u` is `0`. -/
private theorem eq_zero_of_vecMul_rs {m n : Type*} [Fintype m] [DecidableEq m]
    {Z : Matrix m n ℝ} (h : ∀ u : m → ℝ, u ᵥ* Z = 0) : Z = 0 := by
  ext i j
  have := congrFun (h (Pi.single i 1)) j
  rwa [Matrix.single_one_vecMul, Matrix.row_apply] at this

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper (polarisation): if `⟨u Y, u⟩ = 0` for every `u`, then `Yᵀ = -Y`. -/
private theorem transpose_eq_neg_rs {Y : Matrix d d ℝ} (h : ∀ u : d → ℝ, u ᵥ* Y ⬝ᵥ u = 0) :
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
private theorem mul_eq_zero_of_rmsNorm_mul_rs {ε : ℝ} (hε : 0 < ε) {m : Type*} [Fintype m]
    (h : Matrix T d ℝ) (Z : Matrix d m ℝ) (hZ : rmsNorm ε h * Z = 0) : h * Z = 0 := by
  funext t
  have hpos : 0 < (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε := by
    have := dot_self_nonneg_rs (h t)
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
private theorem constRows_mul_rs (w₀ : dIn → ℝ) (M : Matrix dIn d ℝ) (t : T) :
    ((Matrix.of fun _ : T => w₀) * M) t = w₀ ᵥ* M := by
  rw [Matrix.mul_apply_eq_vecMul]
  rfl

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: if `E` has rank `d`, a property of row vectors that holds at `0` and at the rows of
`w E` whenever all of them are nonzero holds for every row vector (every `u` is `w₀ E`). -/
private theorem forall_of_rows_rs {E : Matrix dIn d ℝ} (hE : E.rank = Fintype.card d)
    {P : (d → ℝ) → Prop} (h0 : P 0)
    (h : ∀ w : Matrix T dIn ℝ, (∀ t, (w * E) t ≠ 0) → ∀ t, P ((w * E) t)) (u : d → ℝ) : P u := by
  by_cases hu : u = 0
  · rw [hu]
    exact h0
  obtain ⟨w₀, hw₀⟩ := Matrix.vecMul_surjective_iff_rank_eq_card.2 hE u
  have hrow : ∀ t : T, ((Matrix.of fun _ : T => w₀) * E) t = u := fun t =>
    (constRows_mul_rs w₀ E t).trans hw₀
  have := h _ (fun t => by rw [hrow]; exact hu) (Classical.arbitrary T)
  rwa [hrow] at this

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `μ ⊙ h` is homogeneous of degree `3`. -/
private theorem muScale_smul_rs (ε : ℝ) (Y : Matrix d d ℝ) (c : ℝ) (h : Matrix T d ℝ) :
    muScaleRS ε Y (c • h) = c ^ 3 • muScaleRS ε Y h := by
  funext t i
  show muRS ε Y (c • h t) * (c * h t i) = c ^ 3 * (muRS ε Y (h t) * h t i)
  simp only [muRS, Matrix.smul_vecMul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `h ↦ μ ⊙ h` is continuous. -/
private theorem continuous_muScale_rs (ε : ℝ) (Y : Matrix d d ℝ) :
    Continuous (muScaleRS (T := T) ε Y) := by
  refine continuous_pi fun t => continuous_pi fun i => ?_
  show Continuous fun h : Matrix T d ℝ => muRS ε Y (h t) * h t i
  unfold muRS
  have h1 : Continuous fun h : Matrix T d ℝ => h t := continuous_apply t
  exact (((h1.matrix_vecMul continuous_const).dotProduct h1).div_const _).mul
    ((continuous_apply i).comp h1)

/-! ### Rays `x = s w`, `s → ∞` -/

/-- Helper: `c(v, y) = (‖v‖²/d + ε y²)^{-1/2}`; along the ray `s v`, `N_ε(s v) = c(v, 1/s) v`. -/
private noncomputable def cRS (ε : ℝ) (v : d → ℝ) (y : ℝ) : ℝ :=
  (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε * y ^ 2))⁻¹

/-- Helper: the matrix with rows `c(a_t, y) a_t`, which is `N_ε(s a)` at `y = 1/s`. -/
private noncomputable def nRS (ε : ℝ) (a : Matrix T d ℝ) (y : ℝ) : Matrix T d ℝ :=
  Matrix.of fun t => cRS ε (a t) y • a t

/-- Helper: the matrix that is `𝐃N_ε(s a)(s b)` at `y = 1/s`. -/
private noncomputable def dnRS (ε : ℝ) (a b : Matrix T d ℝ) (y : ℝ) : Matrix T d ℝ :=
  Matrix.of fun t => cRS ε (a t) y • b t
    - ((a t ⬝ᵥ b t) / (Fintype.card d : ℝ) * cRS ε (a t) y ^ 3) • a t

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `(‖s v‖²/d + ε)^{-1/2} = c(v, 1/s) / s` for `s > 0`. -/
private theorem inv_sqrt_smul_rs {ε s : ℝ} (hs : 0 < s) (v : d → ℝ) :
    (Real.sqrt ((s • v) ⬝ᵥ (s • v) / (Fintype.card d : ℝ) + ε))⁻¹ = cRS ε v s⁻¹ * s⁻¹ := by
  unfold cRS
  have e : (s • v) ⬝ᵥ (s • v) / (Fintype.card d : ℝ) + ε
      = s ^ 2 * ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε * s⁻¹ ^ 2) := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    field_simp
  rw [e, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le, mul_inv, mul_comm]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `N_ε(s a) = n(1/s)` for `s > 0`. -/
private theorem rmsNorm_smul_rs {ε s : ℝ} (hs : 0 < s) (a : Matrix T d ℝ) :
    rmsNorm ε (s • a) = nRS ε a s⁻¹ := by
  funext t i
  show (Real.sqrt ((s • a t) ⬝ᵥ (s • a t) / (Fintype.card d : ℝ) + ε))⁻¹ * (s * a t i)
    = cRS ε (a t) s⁻¹ * a t i
  rw [inv_sqrt_smul_rs hs, mul_assoc, inv_mul_cancel_left₀ hs.ne']

omit [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: `𝐃N_ε(s a)(s b) = dn(1/s)` for `s > 0`. -/
private theorem fderiv_rmsNorm_smul_rs {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) (a b : Matrix T d ℝ) :
    fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (s • a) (s • b) = dnRS ε a b s⁻¹ := by
  rw [fderiv_rmsNorm_apply hε]
  funext t i
  show (Real.sqrt ((s • a t) ⬝ᵥ (s • a t) / (Fintype.card d : ℝ) + ε))⁻¹ * (s * b t i)
      - ((s • a t) ⬝ᵥ (s • b t) / (Fintype.card d : ℝ)
        * (Real.sqrt ((s • a t) ⬝ᵥ (s • a t) / (Fintype.card d : ℝ) + ε))⁻¹ ^ 3) * (s * a t i)
    = cRS ε (a t) s⁻¹ * b t i
      - ((a t ⬝ᵥ b t) / (Fintype.card d : ℝ) * cRS ε (a t) s⁻¹ ^ 3) * a t i
  rw [inv_sqrt_smul_rs hs, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  field_simp

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `y ↦ c(v, y)` is continuous at `0` if `v ≠ 0`. -/
private theorem continuousAt_cRS {ε : ℝ} {v : d → ℝ} (hv : v ≠ 0) : ContinuousAt (cRS ε v) 0 := by
  have hpos : 0 < (v ⬝ᵥ v) / (Fintype.card d : ℝ) := by
    have h1 : 0 < v ⬝ᵥ v :=
      lt_of_le_of_ne (dot_self_nonneg_rs v) (Ne.symm (mt dotProduct_self_eq_zero.1 hv))
    have h2 : (0 : ℝ) < Fintype.card d := by
      obtain ⟨i, -⟩ := Function.ne_iff.1 hv
      exact_mod_cast Fintype.card_pos_iff.2 ⟨i⟩
    positivity
  have hc : Continuous fun y : ℝ => Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε * y ^ 2) := by
    fun_prop
  refine hc.continuousAt.inv₀ ?_
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
  exact (Real.sqrt_pos.2 hpos).ne'

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `n` and `dn` are continuous at `0` if every row of `a` is nonzero. -/
private theorem continuousAt_nRS_dnRS {ε : ℝ} {a : Matrix T d ℝ} (ha : ∀ t, a t ≠ 0)
    (b : Matrix T d ℝ) : ContinuousAt (nRS ε a) 0 ∧ ContinuousAt (dnRS ε a b) 0 := by
  constructor
  · refine continuousAt_pi.2 fun t => continuousAt_pi.2 fun i => ?_
    show ContinuousAt (fun y => cRS ε (a t) y * a t i) 0
    exact (continuousAt_cRS (ha t)).mul continuousAt_const
  · refine continuousAt_pi.2 fun t => continuousAt_pi.2 fun i => ?_
    show ContinuousAt (fun y => cRS ε (a t) y * b t i
      - ((a t ⬝ᵥ b t) / (Fintype.card d : ℝ) * cRS ε (a t) y ^ 3) * a t i) 0
    exact ((continuousAt_cRS (ha t)).mul continuousAt_const).sub
      ((continuousAt_const.mul ((continuousAt_cRS (ha t)).pow 3)).mul continuousAt_const)

omit [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper (Step 2, large inputs): if every row of `w E` is nonzero, `h_1(s w) / s → w E` as
`s → ∞` (`g` is bounded along the ray). -/
private theorem tendsto_hOne_ray {A : Arch T d 1} {ε : ℝ} (hf : ContDiff ℝ 1 (A.f 0))
    (θ : Params A dIn dOut) (w : Matrix T dIn ℝ) (hw : ∀ t, (w * θ.E) t ≠ 0) :
    Tendsto (fun s : ℝ => s⁻¹ • hOneRS A ε θ (s • w)) atTop (𝓝 (w * θ.E)) := by
  have hn := (continuousAt_nRS_dnRS (ε := ε) hw (w * θ.E)).1
  -- `Ψ(y) = f(n(y) W_read) W_write`, continuous at `0`
  have h1 : Continuous fun M : Matrix T d ℝ => A.f 0 (M * θ.read 0) * θ.write 0 :=
    (hf.continuous.comp (continuous_id.matrix_mul continuous_const)).matrix_mul continuous_const
  have hΨ : ContinuousAt (fun y => A.f 0 (nRS ε (w * θ.E) y * θ.read 0) * θ.write 0) 0 :=
    ContinuousAt.comp (f := nRS ε (w * θ.E)) (x := 0) h1.continuousAt hn
  have hlim := (tendsto_const_nhds (x := w * θ.E)).add
    (tendsto_inv_atTop_zero.smul (hΨ.tendsto.comp tendsto_inv_atTop_zero))
  rw [zero_smul, add_zero] at hlim
  refine hlim.congr' ((eventually_gt_atTop 0).mono fun s hs => ?_)
  -- `h_1(s w) = s (w E) + Ψ(1/s)`
  show w * θ.E + s⁻¹ • (A.f 0 (nRS ε (w * θ.E) s⁻¹ * θ.read 0) * θ.write 0)
    = s⁻¹ • hOneRS A ε θ (s • w)
  rw [hOneRS, Matrix.smul_mul, rmsNorm_smul_rs hs, smul_add, smul_smul, inv_mul_cancel₀ hs.ne',
    one_smul]

omit [Nonempty T] [Fintype dOut] in
/-- Helper (Steps 2 and 3, large inputs): if every row of `w E` is nonzero, `k(s w) / s → w η_E`
as `s → ∞` (the other terms of `k` are bounded along the ray). -/
private theorem tendsto_kOne_ray {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε) (hf : ContDiff ℝ 1 (A.f 0))
    (θ η : Params A dIn dOut) (w : Matrix T dIn ℝ) (hw : ∀ t, (w * θ.E) t ≠ 0) :
    Tendsto (fun s : ℝ => s⁻¹ • kOneRS A ε θ η (s • w)) atTop (𝓝 (w * η.E)) := by
  obtain ⟨hn, hdn⟩ := continuousAt_nRS_dnRS (ε := ε) hw (w * η.E)
  have hfd := hf.continuous_fderiv_apply one_ne_zero
  have hR : ∀ M : Matrix d (A.r 0) ℝ, Continuous fun N : Matrix T d ℝ => N * M := fun M =>
    continuous_id.matrix_mul continuous_const
  have h1 : ContinuousAt (fun y => nRS ε (w * θ.E) y * θ.read 0) 0 :=
    ContinuousAt.comp (f := nRS ε (w * θ.E)) (x := 0) (hR _).continuousAt hn
  have h2 : ContinuousAt (fun y => dnRS ε (w * θ.E) (w * η.E) y * θ.read 0
      + nRS ε (w * θ.E) y * η.read 0) 0 :=
    (ContinuousAt.comp (f := dnRS ε (w * θ.E) (w * η.E)) (x := 0) (hR _).continuousAt hdn).add
      (ContinuousAt.comp (f := nRS ε (w * θ.E)) (x := 0) (hR _).continuousAt hn)
  have h3 := ContinuousAt.comp (x := (0 : ℝ)) hfd.continuousAt (h1.prodMk h2)
  have hW : ∀ M : Matrix (A.w 0) d ℝ, Continuous fun N : Matrix T (A.w 0) ℝ => N * M := fun M =>
    continuous_id.matrix_mul continuous_const
  have h4 := ContinuousAt.comp (x := (0 : ℝ)) (hf.continuous.comp (hR (θ.read 0))).continuousAt hn
  have hΦ := (ContinuousAt.comp (x := (0 : ℝ)) (hW (θ.write 0)).continuousAt h3).add
    (ContinuousAt.comp (x := (0 : ℝ)) (hW (η.write 0)).continuousAt h4)
  have hlim := (tendsto_const_nhds (x := w * η.E)).add
    (tendsto_inv_atTop_zero.smul (hΦ.tendsto.comp tendsto_inv_atTop_zero))
  rw [zero_smul, add_zero] at hlim
  refine hlim.congr' ((eventually_gt_atTop 0).mono fun s hs => ?_)
  -- `k(s w) = s (w η_E) + Φ(1/s)`
  show w * η.E + s⁻¹ • (fderiv ℝ (A.f 0) (nRS ε (w * θ.E) s⁻¹ * θ.read 0)
      (dnRS ε (w * θ.E) (w * η.E) s⁻¹ * θ.read 0 + nRS ε (w * θ.E) s⁻¹ * η.read 0) * θ.write 0
      + A.f 0 (nRS ε (w * θ.E) s⁻¹ * θ.read 0) * η.write 0) = s⁻¹ • kOneRS A ε θ η (s • w)
  rw [kOneRS, Matrix.smul_mul, Matrix.smul_mul, rmsNorm_smul_rs hs, fderiv_rmsNorm_smul_rs hε hs,
    add_assoc, smul_add (s⁻¹) (s • (w * η.E)), smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

end Helpers

/-- **Proof of Theorem B.1 (ii) of the skips paper, Steps 1 to 3, for one residual block under
pre-RMSNorm with `ε > 0`:** let `E` and `D` have rank `d`, and let `η` be flat. Then there is an
antisymmetric `Y` with `η_E = E Y` and `η_D = -Y D`, and the direction `η' = η - η^Y`, whose
entries at the block are `η_read + Y W_read` and `η_write - W_write Y`, satisfies: the derivative
of `n ↦ f(n W_read) W_write` along these entries vanishes at every `n = N_ε(x E)`. -/
theorem exists_antisymm_of_flat_residual_rmsNorm {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ContDiff ℝ 1 (A.f 0)) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (η : Params A dIn dOut) (hη : η ∈ flat A 1 θ) :
    ∃ Y : Matrix d d ℝ, Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D) ∧
      ∀ x : Matrix T dIn ℝ,
        fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
            (rmsNorm ε (x * θ.E) * (η.read 0 + Y * θ.read 0)) * θ.write 0
          + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * (η.write 0 - θ.write 0 * Y) = 0 := by
  -- no coordinates: every matrix with a side indexed by `d` is `0`
  rcases isEmpty_or_nonempty d with hd0 | hd0
  · refine ⟨0, ?_, ?_, ?_, fun x => ?_⟩ <;> funext i j
    · exact isEmptyElim i
    · exact isEmptyElim j
    · exact isEmptyElim i
    · exact isEmptyElim j
  have hd : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos
  have hfd : Differentiable ℝ (A.f 0) := hf.differentiable one_ne_zero
  -- a right inverse `D⁺` of `D`, and `Y = -η_D D⁺`
  obtain ⟨Dp, hDp⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1
    (Matrix.mulVec_surjective_iff_rank_eq_card.2 hD)
  obtain ⟨Y, hYdef⟩ : ∃ Y : Matrix d d ℝ, Y = -(η.D * Dp) := ⟨_, rfl⟩
  -- Step 0 for `η`: `𝐃N_ε(h_1) k D + N_ε(h_1) η_D = 0`
  have h0 := flat_eq_rs hε hA hfd θ η hη
  -- Step 1: times `D⁺`, `𝐃N_ε(h_1) k = N_ε(h_1) Y`
  have hNY : ∀ x, fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (hOneRS A ε θ x)
      (kOneRS A ε θ η x) = rmsNorm ε (hOneRS A ε θ x) * Y := by
    intro x
    have e := congrArg (· * Dp) (h0 x)
    simp only [Matrix.add_mul, Matrix.mul_assoc, hDp, Matrix.mul_one, Matrix.zero_mul] at e
    rw [hYdef, Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left e
  -- hence `k = h_1 Y + μ ⊙ h_1`, since `𝐃N_ε(h_1)` is injective
  have hk : ∀ x, kOneRS A ε θ η x
      = hOneRS A ε θ x * Y + muScaleRS ε Y (hOneRS A ε θ x) := fun x =>
    injective_fderiv_rmsNorm hε _ (by rw [hNY x, fderiv_rmsNorm_muScale hε hd])
  -- and, substituting back, `N_ε(h_1) (Y D + η_D) = 0`, so `h_1 (Y D + η_D) = 0`
  have hZ : ∀ x, hOneRS A ε θ x * (Y * θ.D + η.D) = 0 := by
    intro x
    refine mul_eq_zero_of_rmsNorm_mul_rs hε _ _ ?_
    have e := h0 x
    rw [hNY x] at e
    rw [Matrix.mul_add, ← Matrix.mul_assoc]
    exact e
  -- at the inputs `s w`, `s → ∞`: `(w E)(Y D + η_D) = 0`; the rows `w E` span, so `η_D = -Y D`
  have hZ0 : Y * θ.D + η.D = 0 := by
    refine eq_zero_of_vecMul_rs (forall_of_rows_rs (T := T) hE
      (P := fun u => u ᵥ* (Y * θ.D + η.D) = 0) (Matrix.zero_vecMul _) ?_)
    intro w hw t
    have hc : Continuous fun M : Matrix T d ℝ => M * (Y * θ.D + η.D) :=
      continuous_id.matrix_mul continuous_const
    have hlim := (hc.tendsto (w * θ.E)).comp (tendsto_hOne_ray (ε := ε) hf θ w hw)
    have hlim0 : Filter.Tendsto (fun s : ℝ => (s⁻¹ • hOneRS A ε θ (s • w)) * (Y * θ.D + η.D))
        Filter.atTop (nhds 0) :=
      tendsto_const_nhds.congr fun s => by rw [Matrix.smul_mul, hZ, smul_zero]
    have e := tendsto_nhds_unique hlim hlim0
    show (w * θ.E) t ᵥ* (Y * θ.D + η.D) = 0
    rw [← Matrix.mul_apply_eq_vecMul, e]
    rfl
  have hYD : η.D = -(Y * θ.D) := eq_neg_of_add_eq_zero_right hZ0
  -- Step 2: the terms of order `s³` at the inputs `s w` give `⟨u Y, u⟩ = 0` for every `u`
  have hq : ∀ u : d → ℝ, u ᵥ* Y ⬝ᵥ u = 0 := by
    refine forall_of_rows_rs (T := T) hE (by simp) ?_
    intro w hw t
    have hu := tendsto_hOne_ray (ε := ε) hf θ w hw
    have hv := tendsto_kOne_ray hε hf θ η w hw
    have h1 := ((continuous_muScale_rs ε Y).tendsto _).comp hu
    have hc : Continuous fun M : Matrix T d ℝ => M * Y := continuous_id.matrix_mul continuous_const
    have h2 := (tendsto_inv_atTop_zero.pow 2).smul (hv.sub ((hc.tendsto _).comp hu))
    rw [zero_pow two_ne_zero, zero_smul] at h2
    -- the identity of Step 1 at `s w`, divided by `s³`
    have heq : ∀ s : ℝ, (s⁻¹) ^ 2 • (s⁻¹ • kOneRS A ε θ η (s • w)
        - (s⁻¹ • hOneRS A ε θ (s • w)) * Y) = muScaleRS ε Y (s⁻¹ • hOneRS A ε θ (s • w)) := by
      intro s
      rw [hk, muScale_smul_rs, Matrix.smul_mul, smul_add, add_sub_cancel_left, smul_smul,
        ← pow_succ]
    have h12 := tendsto_nhds_unique h1 (h2.congr heq)
    -- row `t`: `μ(a_t) a_t = 0` with `a_t ≠ 0`
    have hrow : muRS ε Y ((w * θ.E) t) • (w * θ.E) t = 0 := congrFun h12 t
    have hmu := (smul_eq_zero.1 hrow).resolve_right (hw t)
    unfold muRS at hmu
    exact (div_eq_zero_iff.1 hmu).resolve_right (mul_pos hd hε).ne'
  have hY : Yᵀ = -Y := transpose_eq_neg_rs hq
  -- Step 3: `η' = η - η^Y` is flat
  obtain ⟨η', hη'def⟩ : ∃ η', η' = η - cobDir θ (fun _ => Y) := ⟨_, rfl⟩
  have hη' : η' ∈ flat A 1 θ := hη'def ▸
    Submodule.sub_mem _ hη (cobDir_const_mem_flat_residual_rmsNorm' θ ε hA Y hY)
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
  -- `η'_D = 0`, so Step 0 gives `𝐃N_ε(h_1) k' D = 0`, hence `k' = 0` at every input
  have hk' : ∀ x, kOneRS A ε θ η' x = 0 := by
    intro x
    have e := flat_eq_rs hε hA hfd θ η' hη' x
    rw [hη'D, Matrix.mul_zero, add_zero] at e
    have e2 := congrArg (· * Dp) e
    simp only [Matrix.mul_assoc, hDp, Matrix.mul_one, Matrix.zero_mul] at e2
    exact injective_fderiv_rmsNorm hε _ (by rw [e2, map_zero])
  -- at the inputs `s w`: `w η'_E = 0`
  have hw' : ∀ w : Matrix T dIn ℝ, (∀ t, (w * θ.E) t ≠ 0) → w * η'.E = 0 := fun w hw =>
    tendsto_nhds_unique (tendsto_kOne_ray hε hf θ η' w hw)
      (tendsto_const_nhds.congr fun s => by rw [hk', smul_zero])
  -- hence `η'_E = 0`: first for the rows `w₀` with `w₀ E ≠ 0`, then for all by linearity
  have hE' : η'.E = 0 := by
    classical
    have h1 : ∀ w₀ : dIn → ℝ, w₀ ᵥ* θ.E ≠ 0 → w₀ ᵥ* η'.E = 0 := by
      intro w₀ hw₀
      have := congrFun (hw' (Matrix.of fun _ : T => w₀) fun t => by
        rw [constRows_mul_rs]; exact hw₀) (Classical.arbitrary T)
      rwa [constRows_mul_rs] at this
    obtain ⟨w₁, hw₁⟩ := Matrix.vecMul_surjective_iff_rank_eq_card.2 hE (fun _ => 1)
    have hw₁0 : w₁ ᵥ* θ.E ≠ 0 := by
      intro h
      have h2 : (fun _ : d => (1 : ℝ)) = 0 := hw₁.symm.trans h
      exact one_ne_zero (congrFun h2 (Classical.arbitrary d))
    refine eq_zero_of_vecMul_rs fun w₀ => ?_
    by_cases h : w₀ ᵥ* θ.E = 0
    · have e := h1 (w₀ + w₁) (by rw [Matrix.add_vecMul, h, zero_add]; exact hw₁0)
      rwa [Matrix.add_vecMul, h1 w₁ hw₁0, add_zero] at e
    · exact h1 w₀ h
  refine ⟨Y, hY, ?_, hYD, fun x => ?_⟩
  · rw [hη'E] at hE'
    exact sub_eq_zero.1 hE'
  · -- with `η'_E = 0`, `k'(x) = 0` is the last clause
    have e := hk' x
    unfold kOneRS at e
    rw [hE', Matrix.mul_zero, map_zero, Matrix.zero_mul, zero_add, zero_add, hη'r, hη'w] at e
    exact e

end Skips
