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
  sorry

end Skips
