import SkipsLean.OneBlock.LearnedSkipTriangularRescale
import SkipsLean.OneBlock.ResidualRMSZeroValue

/-!
# One block with a learned skip under pre-RMSNorm with `ε = 0`: "at most"

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. […] For `ε = 0` it exceeds that of the residual
network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and
ReGLU blocks."

Its proof, "The case `ε = 0`": "the scalings of `h_0` and `h_1` are symmetries too, since
`N_ε(c h) = N_ε(h)` for `c > 0`. […] For the residual network […] Its flat directions are the
rotation and the scaling of all hidden states, and the space `K_B` of directions of the block along
which `B` has derivative zero on the sphere. For the learned skip, `η^rot` and `K_B` are flat,
which gives at least `d_model (d_model − 1) + 2`, respectively `d_model (d_model − 1)/2 + 2`,
dimensions besides `K_B`, against `d_model (d_model − 1)/2 + 1` for the residual network. So the
difference is at most `d_model (d_model + 1)/2 − 1`."

Here, for a full learned skip and a block whose fixed map is analytic (tanh, GELU, SwiGLU, GeGLU,
attention), at one parameter:

* `learnedZeroDomain A θ R`: the inputs at which no normalized row vanishes, for the network with
  the learned skip `R 0`: no row of `h_0 = x E` and no row of `h_1 = x E A + g(x)` is zero (the
  paper's "every input" for `ε = 0`).
* The bound for the learned skip: the rotation and the scaling of `h_0`, the rotation and the
  scaling of `h_1` (`d(d−1) + 2` dimensions) and the space `V_θ` (`blockFlatSphere`, the paper's
  `K_B`) are flat and independent, so the functional dimension on these inputs is at most
  `P + d² − (d(d−1) + 2) − dim V_θ`.
* With the value for the residual network (`funDimOn_residual_rmsNorm_zero_eq`,
  `OneBlock/ResidualRMSZeroValue.lean`): the difference is at most `d(d+1)/2 − 1`, the two
  networks at the same weights.

The functional dimensions are those on the inputs at which no normalized row vanishes
(`funDimSkipsOn`, `funDimOn`): `V_θ` is flat only where the block reads rows on the sphere. Not
stated here: the upper triangular skip; ReLU, ReLU², ReGLU blocks and the equality for them; the
statements at almost every parameter.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The inputs at which no normalized row vanishes, for one block with the learned skip `R 0`
under pre-RMSNorm with `ε = 0`:** no row of `h_0 = x E` and no row of
`h_1 = x E A + f(N_0(x E) W_read) W_write` is zero (`A = R 0`). For `A = I` this is
`residualZeroDomain`. -/
def learnedZeroDomain (A : Arch T d 1) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ) :
    Set (Matrix T dIn ℝ) :=
  {x | (∀ t, (x * θ.E) t ≠ 0) ∧
    ∀ t, (x * θ.E * R 0 + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) t ≠ 0}


/-! ### Helpers: the product rule, the output of the network, and `V_θ`

Copies of private helpers of `OneBlock/ResidualRMSZeroValue.lean` and
`OneBlock/LearnedSkipGain.lean`. -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `hasDerivAt_mul_rzv`): the product rule for matrices depending
on one real variable. -/
private theorem hasDerivAt_mul_lzb {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
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

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `hasDerivAt_affine_rzv`): `τ ↦ M + τ N` has the derivative `N`
at `0`. -/
private theorem hasDerivAt_affine_lzb {m n : Type*} [Fintype m] [Fintype n]
    (M N : Matrix m n ℝ) : HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `hasDerivAt_block_rzv`): for a differentiable `f`, along the
line `(R + τ R', W + τ W')` of weights of the block, the output `f(n R) W` of the block at the
state `n` has, at `τ = 0`, the derivative `𝐃f(n R)(n R') W + f(n R) W'`. -/
private theorem hasDerivAt_block_lzb {r w : Type*} [Fintype r] [Fintype w]
    {f : Matrix T r ℝ → Matrix T w ℝ} (hf : Differentiable ℝ f) (n : Matrix T d ℝ)
    (R R' : Matrix d r ℝ) (W W' : Matrix w d ℝ) :
    HasDerivAt (fun τ : ℝ => f (n * (R + τ • R')) * (W + τ • W'))
      (fderiv ℝ f (n * R) (n * R') * W + f (n * R) * W') 0 := by
  have hR := hasDerivAt_mul_lzb (hasDerivAt_const (0 : ℝ) n) (hasDerivAt_affine_lzb R R')
    (P0 := n) (Q0 := R) rfl (by simp)
  have hF := (hf (n * R)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hR (by simp)
  have hFW := hasDerivAt_mul_lzb hF (hasDerivAt_affine_lzb W W') (P0 := f (n * R)) (Q0 := W)
    (by simp) (by simp)
  have e : (fun s : ℝ => (f ∘ fun s => n * (R + s • R')) s * (W + s • W'))
      = fun τ : ℝ => f (n * (R + τ • R')) * (W + τ • W') := rfl
  rw [e, Matrix.zero_mul, zero_add] at hFW
  exact hFW

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `mem_blockFlatSphere_rzv`): a direction of `V_θ` moves only the
read and the write, and the block has derivative zero along it at every `n` with rows on the
sphere. -/
private theorem mem_blockFlatSphere_lzb {A : Arch T d 1} {θ ψ : Params A dIn dOut}
    (hψ : ψ ∈ blockFlatSphere A θ) :
    ψ.E = 0 ∧ ψ.D = 0 ∧ ∀ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = Fintype.card d) →
      fderiv ℝ (A.f 0) (n * θ.read 0) (n * ψ.read 0) * θ.write 0
        + A.f 0 (n * θ.read 0) * ψ.write 0 = 0 := by
  induction hψ using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨rfl, rfl, fun n _ => ?_⟩
    rw [Params.zero_read, Params.zero_write, Matrix.mul_zero, map_zero, Matrix.zero_mul,
      Matrix.mul_zero, add_zero]
  | add x y _ _ hx hy =>
    refine ⟨by rw [Params.add_E, hx.1, hy.1, add_zero], by rw [Params.add_D, hx.2.1, hy.2.1,
      add_zero], fun n hn => ?_⟩
    rw [Params.add_read, Params.add_write, Matrix.mul_add, map_add, Matrix.add_mul,
      Matrix.mul_add, add_add_add_comm, hx.2.2 n hn, hy.2.2 n hn, add_zero]
  | smul c x _ hx =>
    refine ⟨by rw [Params.smul_E, hx.1, smul_zero], by rw [Params.smul_D, hx.2.1, smul_zero],
      fun n hn => ?_⟩
    rw [Params.smul_read, Params.smul_write, Matrix.mul_smul, map_smul, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hx.2.2 n hn, smul_zero]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `rmsRow_zero_dotProduct_self_rzv`): `N_0` puts a nonzero row on
the sphere of radius `√d`. -/
private theorem rmsRow_zero_dotProduct_self_lzb {v : d → ℝ} (hv : v ≠ 0) :
    rmsRow 0 v ⬝ᵥ rmsRow 0 v = Fintype.card d := by
  have hw2 : 0 < v ⬝ᵥ v := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i))
    (Ne.symm (dotProduct_self_eq_zero.not.mpr hv))
  have hn : (0 : ℝ) < Fintype.card d := by
    obtain ⟨i, -⟩ := Function.ne_iff.mp hv
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  unfold rmsRow
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_inv,
    Real.mul_self_sqrt (add_nonneg (div_nonneg hw2.le hn.le) le_rfl), add_zero, inv_div,
    div_mul_cancel₀ _ hw2.ne']

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper (the private `eval_eq_lsn` for `ε = 0`): the function of one block under pre-RMSNorm
with `ε = 0` and the skip `S 0`, `F(x) = N_0(x E S + f(N_0(x E) W_read) W_write) D`. -/
private theorem eval_eq_lzb {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (S : Fin 1 → Matrix d d ℝ) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    eval A S θ x = rmsNorm 0 (x * θ.E * S 0
      + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) * θ.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]

omit [DecidableEq d] in
/-- **Step 2, `V_θ` is flat on the inputs:** for `ψ ∈ V_θ`, the direction `(ψ, 0)` (the skip does
not move) is flat for the family with the learned skip at every input of
`learnedZeroDomain A θ R`: there the block reads `N_0(x E)`, whose rows are on the sphere, so the
block, and with it `h_1 = x E A + block`, does not move to first order, and `N_0` is
differentiable at `h_1`. As `blockFlatSphere_le_flatOn_residual_rzv` (the residual twin). -/
private theorem mem_flatSkipsOn_of_blockFlatSphere_lzb {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ)
    {ψ : Params A dIn dOut} (hψ : ψ ∈ blockFlatSphere A θ) :
    (ψ, 0) ∈ flatSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
      (learnedZeroDomain A θ R) := by
  obtain ⟨hψE, hψD, hψn⟩ := mem_blockFlatSphere_lzb hψ
  refine (Submodule.mem_iInf _).2 fun x => (Submodule.mem_iInf _).2 fun hx =>
    LinearMap.mem_ker.2 ?_
  show fderiv ℝ (fun p' : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
    evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p' x) (θ, R) (ψ, 0) = 0
  by_cases hdx : DifferentiableAt ℝ (fun p' : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
    evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p' x) (θ, R)
  swap
  · -- not differentiable: Mathlib's derivative is `0`
    rw [fderiv_zero_of_not_differentiableAt hdx]
    rfl
  -- the chain rule along the line `(θ + τ ψ, R)`
  have hline : HasDerivAt (fun τ : ℝ => ((θ, R) : Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
      + τ • (ψ, (0 : Fin 1 → Matrix d d ℝ))) (ψ, 0) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const (ψ, (0 : Fin 1 → Matrix d d ℝ))).const_add
      ((θ, R) : Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
    rw [one_smul] at h
    exact h
  have h1 := hdx.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by rw [zero_smul, add_zero])
  have e1 : ((fun p' : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p' x) ∘
      fun τ : ℝ => ((θ, R) : Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
        + τ • (ψ, (0 : Fin 1 → Matrix d d ℝ))) = fun τ => eval A R (θ + τ • ψ) x := by
    funext τ
    simp only [Function.comp_apply, evalSkips, Prod.smul_mk, Prod.mk_add_mk, smul_zero,
      add_zero]
    rfl
  rw [e1] at h1
  -- `n = N_0(x E)` has its rows on the sphere
  obtain ⟨n, hn⟩ : ∃ n, n = rmsNorm 0 (x * θ.E) := ⟨_, rfl⟩
  have hsph : ∀ t, n t ⬝ᵥ n t = Fintype.card d := by
    rw [hn]
    exact fun t => rmsRow_zero_dotProduct_self_lzb (hx.1 t)
  -- the block does not move to first order
  have hg : HasDerivAt (fun τ : ℝ => A.f 0 (n * (θ.read 0 + τ • ψ.read 0))
      * (θ.write 0 + τ • ψ.write 0)) 0 0 := by
    have h := hasDerivAt_block_lzb (fun z => (hf z trivial).differentiableAt) n (θ.read 0)
      (ψ.read 0) (θ.write 0) (ψ.write 0)
    rwa [hψn n hsph] at h
  -- neither does `h_1 = x E A + block`
  have hh : HasDerivAt (fun τ : ℝ => x * θ.E * R 0 + A.f 0 (n * (θ.read 0 + τ • ψ.read 0))
      * (θ.write 0 + τ • ψ.write 0)) 0 0 := by
    have h := hg.const_add (x * θ.E * R 0)
    exact h
  -- no row of `h_1` vanishes, so `N_0` is differentiable at `h_1`
  have hrows : ∀ t, (x * θ.E * R 0 + A.f 0 (n * θ.read 0) * θ.write 0) t ≠ 0 := by
    rw [hn]
    exact hx.2
  have hN := (analyticAt_rmsNorm_zero _ hrows).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq (0 : ℝ) hh (by simp)
  have h2 := hasDerivAt_mul_lzb hN (hasDerivAt_const (0 : ℝ) θ.D)
    (P0 := rmsNorm 0 (x * θ.E * R 0 + A.f 0 (n * θ.read 0) * θ.write 0)) (Q0 := θ.D)
    (by simp) rfl
  have e2 : (fun τ : ℝ => eval A R (θ + τ • ψ) x) = fun τ => rmsNorm 0
      (x * θ.E * R 0 + A.f 0 (n * (θ.read 0 + τ • ψ.read 0)) * (θ.write 0 + τ • ψ.write 0))
        * θ.D := by
    funext τ
    rw [eval_eq_lzb hA, hn]
    simp only [Params.add_E, Params.smul_E, hψE, smul_zero, add_zero, Params.add_D,
      Params.smul_D, hψD, Params.add_read, Params.smul_read, Params.add_write,
      Params.smul_write]
  rw [e2] at h1
  refine h1.unique (h2.congr_deriv ?_)
  rw [map_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero]

/-! ### Helpers: the changes of basis `G_i = c_i Q_i` are flat for the family with the learned
skip

Copies of the private helpers of `OneBlock/LearnedSkipOn.lean` (the rotations `Q_i = exp (τ X_i)`)
and of `Dimension/UpperBoundRMSNormZero.lean` (the scales `c_i = e^{τ β_i}`). -/

omit [DecidableEq d] in
/-- Helper (a copy of the private `mem_flatSkips_of_hasDerivAt_lso`): if a curve `γ` through `p`
with velocity `v` keeps the function near `τ = 0`, then `v` is flat. -/
private theorem mem_flatSkips_of_hasDerivAt_lzb {L : ℕ} {A : Arch T d L} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V)
    (γ : ℝ → Params A dIn dOut × V) (v : Params A dIn dOut × V) (hγ : HasDerivAt γ v 0)
    (hγ0 : γ 0 = p)
    (hconst : ∀ᶠ τ in nhds (0 : ℝ), ∀ x : Matrix T dIn ℝ,
      evalSkips A ι (γ τ) x = evalSkips A ι p x) :
    v ∈ flatSkips A ι p := by
  rw [flatSkips, Submodule.mem_iInf]
  intro x
  rw [LinearMap.mem_ker]
  show fderiv ℝ (fun p' => evalSkips A ι p' x) p v = 0
  by_cases hx : DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p
  · -- the chain rule: `τ ↦ F_{γ(τ)}(x)` has derivative `D_p F(x) v` at `0`
    have hl : HasFDerivAt (fun p' => evalSkips A ι p' x)
        (fderiv ℝ (fun p' => evalSkips A ι p' x) p) (γ 0) := by
      rw [hγ0]
      exact hx.hasFDerivAt
    have h1 := hl.comp_hasDerivAt (0 : ℝ) hγ
    -- the same map is constant near `0`, so its derivative there is `0`
    have h2 : HasDerivAt ((fun p' => evalSkips A ι p' x) ∘ γ) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (evalSkips A ι p x)).congr_of_eventuallyEq
        (hconst.mono fun τ hτ => hτ x)
    exact h1.unique h2
  · -- not differentiable at `p`: Mathlib's derivative is `0`
    rw [fderiv_zero_of_not_differentiableAt hx, _root_.zero_apply]

-- As in Mathlib's `MatrixExponential.lean`: without this option the instances of the operator
-- norm (e.g. `CompleteSpace`) are not found.
set_option backward.isDefEq.respectTransparency false in
/-- Helper (a copy of the private `hasDerivAt_exp_smul_apply_lso`): the derivative at `τ = 0` of
an entry of `exp (τ Y)` is the entry of `Y`. -/
private theorem hasDerivAt_exp_smul_apply_lzb (Y : Matrix d d ℝ) (i j : d) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) i j) (Y i j) 0 := by
  let _ : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℝ ℝ i j)).hasFDerivAt.comp_hasDerivAt 0 h

/-- Helper (a copy of the private `hasDerivAt_matrix_lso`): with the elementwise norm, the
derivative of a matrix-valued function is taken entry by entry. -/
private theorem hasDerivAt_matrix_lzb {m n : Type*} [Fintype m] [Fintype n]
    {f : ℝ → Matrix m n ℝ} {f' : Matrix m n ℝ} {x : ℝ}
    (h : ∀ i j, HasDerivAt (fun τ => f τ i j) (f' i j) x) : HasDerivAt f f' x :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 (h i)

/-- Helper (a copy of the private `hasDerivAt_mul_exp_lso`): the derivative of
`τ ↦ M exp (τ Y)` at `0` is `M Y`. -/
private theorem hasDerivAt_mul_exp_lzb {m : Type*} [Fintype m] (M : Matrix m d ℝ)
    (Y : Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => M * NormedSpace.exp (τ • Y)) (M * Y) 0 :=
  hasDerivAt_matrix_lzb fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_apply_lzb Y k j).const_mul (M i k)

/-- Helper (a copy of the private `hasDerivAt_exp_mul_lso`): the derivative of
`τ ↦ exp (τ Y) M` at `0` is `Y M`. -/
private theorem hasDerivAt_exp_mul_lzb {n : Type*} [Fintype n] (Y : Matrix d d ℝ)
    (M : Matrix d n ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) * M) (Y * M) 0 :=
  hasDerivAt_matrix_lzb fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_apply_lzb Y i k).mul_const (M k j)

-- See `hasDerivAt_exp_smul_apply_lzb` for this option.
set_option backward.isDefEq.respectTransparency false in
/-- Helper (a copy of the private `hasDerivAt_exp_mul_exp_lso`): the derivative of
`τ ↦ exp (-τ Y) S exp (τ Z)` at `0` is `−Y S + S Z`. -/
private theorem hasDerivAt_exp_mul_exp_lzb (Y Z S : Matrix d d ℝ) :
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

/-- Helper (a copy of the private `exp_smul_mul_exp_smul_neg_lso`): `exp (τ Y) exp (-τ Y) = 1`. -/
private theorem exp_smul_mul_exp_smul_neg_lzb (Y : Matrix d d ℝ) (τ : ℝ) :
    NormedSpace.exp (τ • Y) * NormedSpace.exp (τ • -Y) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).neg_right.smul_left τ).smul_right τ),
    smul_neg, add_neg_cancel, NormedSpace.exp_zero]

/-- Helper (a copy of the private `expGL_lso`): the invertible matrix `exp (τ Y)`, with inverse
`exp (-τ Y)`. -/
private noncomputable def expGL_lzb (Y : Matrix d d ℝ) (τ : ℝ) : GL d ℝ :=
  ⟨NormedSpace.exp (τ • Y), NormedSpace.exp (τ • -Y), exp_smul_mul_exp_smul_neg_lzb Y τ,
    by simpa only [neg_neg] using exp_smul_mul_exp_smul_neg_lzb (-Y) τ⟩

/-- Helper (a copy of the private `expGL_zero_lso`): `exp (0 Y) = 1`. -/
private theorem expGL_zero_lzb (Y : Matrix d d ℝ) : expGL_lzb Y 0 = 1 := by
  apply Units.ext
  change NormedSpace.exp ((0 : ℝ) • Y) = 1
  rw [zero_smul, NormedSpace.exp_zero]

/-- Helper (a copy of the private `expGL_mem_orthogonalGroup_lso`): for antisymmetric `Y`,
`exp (τ Y)` is orthogonal. -/
private theorem expGL_mem_orthogonalGroup_lzb {Y : Matrix d d ℝ} (hY : Yᵀ = -Y) (τ : ℝ) :
    (expGL_lzb Y τ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  change (NormedSpace.exp (τ • Y))ᵀ * NormedSpace.exp (τ • Y) = 1
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, hY]
  simpa only [neg_neg] using exp_smul_mul_exp_smul_neg_lzb (-Y) τ

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `cob_expGL_zero_lso`): the curve of the rotations passes through
`θ` at `τ = 0`. -/
private theorem cob_expGL_zero_lzb {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut)
    (X : Fin (L + 1) → Matrix d d ℝ) :
    θ.cob (fun ℓ => expGL_lzb (X ℓ) 0) (fun ℓ => expGL_lzb (X ℓ) 0) = θ := by
  simp only [expGL_zero_lzb]
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [Params.cob, inv_one, Units.val_one, Matrix.mul_one, Matrix.one_mul]

omit [Fintype T] in
/-- Helper (a copy of the private `hasDerivAt_cob_expGL_lso`): the curve of the rotations has
velocity `cobDir θ X` at `τ = 0`. -/
private theorem hasDerivAt_cob_expGL_lzb {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut)
    (X : Fin (L + 1) → Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => θ.cob (fun ℓ => expGL_lzb (X ℓ) τ) (fun ℓ => expGL_lzb (X ℓ) τ))
      (cobDir θ X) 0 := by
  -- the norm of the parameters is that of the tuple of their components
  let e : Params A dIn dOut ≃L[ℝ] Params.Prod A dIn dOut :=
    Params.linearEquivProd.toContinuousLinearEquiv
  have key : HasDerivAt
      (fun τ : ℝ => e (θ.cob (fun ℓ => expGL_lzb (X ℓ) τ) (fun ℓ => expGL_lzb (X ℓ) τ)))
      (e (cobDir θ X)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · exact hasDerivAt_mul_exp_lzb θ.E (X 0)
    · exact hasDerivAt_pi.2 fun ℓ =>
        (hasDerivAt_exp_mul_lzb (-X ℓ.castSucc) (θ.read ℓ)).congr_deriv (Matrix.neg_mul _ _)
    · exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_mul_exp_lzb (θ.write ℓ) (X ℓ.succ)
    · exact (hasDerivAt_exp_mul_lzb (-X (Fin.last L)) θ.D).congr_deriv (Matrix.neg_mul _ _)
  exact e.symm.hasFDerivAt.comp_hasDerivAt (0 : ℝ) key

/-- **Step 1, the rotations are flat** (a copy of the private `rot_mem_flatSkips_lso`): for
antisymmetric `X_ℓ`, the orthogonal changes of basis `exp (τ X_ℓ)` together with
`S_ℓ ↦ G_{ℓ-1}⁻¹ S_ℓ G_ℓ` keep the function, so their direction
`(cobDir θ X, −X_{ℓ-1} S_ℓ + S_ℓ X_ℓ)` is flat. -/
private theorem rot_mem_flatSkips_lzb {L : ℕ} {A : Arch T d L} {ε : ℝ} (hA : A.χ = rmsNorm ε)
    (θ : Params A dIn dOut) (S : Fin L → Matrix d d ℝ) (X : Fin (L + 1) → Matrix d d ℝ)
    (hX : ∀ ℓ, (X ℓ)ᵀ = -X ℓ) :
    (cobDir θ X, fun ℓ => -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ)
      ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S) := by
  -- the curve `τ ↦ (θ.cob G_τ G_τ, cobSkip S G_τ)` with `G_τ ℓ = exp (τ X_ℓ)` and its velocity
  have hγ : HasDerivAt (fun τ : ℝ => (θ.cob (fun ℓ => expGL_lzb (X ℓ) τ)
      (fun ℓ => expGL_lzb (X ℓ) τ), cobSkip S (fun ℓ => expGL_lzb (X ℓ) τ)))
      (cobDir θ X, fun ℓ => -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ) 0 :=
    (hasDerivAt_cob_expGL_lzb θ X).prodMk
      (hasDerivAt_pi.2 fun ℓ => hasDerivAt_exp_mul_exp_lzb (X ℓ.castSucc) (X ℓ.succ) (S ℓ))
  refine mem_flatSkips_of_hasDerivAt_lzb _ _ _ _ hγ ?_ ?_
  · -- at `τ = 0` the curve is at `(θ, S)`
    refine Prod.ext (cob_expGL_zero_lzb θ X) ?_
    show cobSkip S (fun ℓ => expGL_lzb (X ℓ) 0) = S
    funext ℓ
    simp only [cobSkip, expGL_zero_lzb, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  · -- along the curve the function is kept: pre-RMSNorm commutes with the orthogonal `G_τ ℓ`
    refine Filter.Eventually.of_forall fun τ x => ?_
    have hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (expGL_lzb (X ℓ) τ : Matrix d d ℝ))
        = A.χ h * (expGL_lzb (X ℓ) τ : Matrix d d ℝ) := by
      intro ℓ h
      rw [hA]
      exact rmsNorm_mul_orthogonal ε (expGL_mem_orthogonalGroup_lzb (hX ℓ) τ) h
    exact eval_cob (M := S) (θ := θ) (G := fun ℓ => expGL_lzb (X ℓ) τ)
      (K := fun ℓ => expGL_lzb (X ℓ) τ) (x := x) hχ

/-- Helper (a copy of the private `scalarGL_rz`): the invertible scalar matrix `c • 1`, for
`c ≠ 0`. -/
private noncomputable def scalarGL_lzb (c : ℝ) (hc : c ≠ 0) : GL d ℝ :=
  ⟨c • 1, c⁻¹ • 1, by simp [smul_smul, hc], by simp [smul_smul, hc]⟩

/-- Helper (a copy of the private `scaleCurve_rz`): the curve of the scales, `E ↦ e^{τ β_0} E`,
`W_write^ℓ ↦ e^{τ β_ℓ} W_write^ℓ`, the reads and `D` unchanged. -/
private noncomputable def scaleCurve_lzb {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut)
    (β : Fin (L + 1) → ℝ) (τ : ℝ) : Params A dIn dOut where
  E := Real.exp (τ * β 0) • θ.E
  read := θ.read
  write ℓ := Real.exp (τ * β ℓ.succ) • θ.write ℓ
  D := θ.D

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `scaleCurve_zero_rz`): the curve passes through `θ` at
`τ = 0`. -/
private theorem scaleCurve_zero_lzb {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut)
    (β : Fin (L + 1) → ℝ) : scaleCurve_lzb θ β 0 = θ := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [scaleCurve_lzb, zero_mul, Real.exp_zero, one_smul]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `scaleCurve_eq_cob_rz`): the curve is the change of basis
`G_ℓ = e^{τ β_ℓ} 1` at the writes and `K_ℓ = 1` at the reads. -/
private theorem scaleCurve_eq_cob_lzb {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut)
    (β : Fin (L + 1) → ℝ) (τ : ℝ) :
    scaleCurve_lzb θ β τ = θ.cob
      (fun ℓ => scalarGL_lzb (Real.exp (τ * β ℓ)) (Real.exp_ne_zero _)) (fun _ => 1) := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · show Real.exp (τ * β 0) • θ.E = θ.E * (Real.exp (τ * β 0) • (1 : Matrix d d ℝ))
    rw [Matrix.mul_smul, Matrix.mul_one]
  · show θ.read ℓ = (↑(1 : GL d ℝ)⁻¹ : Matrix d d ℝ) * θ.read ℓ
    rw [inv_one, Units.val_one, Matrix.one_mul]
  · show Real.exp (τ * β ℓ.succ) • θ.write ℓ
      = θ.write ℓ * (Real.exp (τ * β ℓ.succ) • (1 : Matrix d d ℝ))
    rw [Matrix.mul_smul, Matrix.mul_one]
  · show θ.D = (↑(1 : GL d ℝ)⁻¹ : Matrix d d ℝ) * θ.D
    rw [inv_one, Units.val_one, Matrix.one_mul]

/-- Helper: along the scales the skips become `G_{ℓ-1}⁻¹ S_ℓ G_ℓ = e^{τ (β_ℓ − β_{ℓ-1})} S_ℓ`. -/
private theorem cobSkip_scalarGL_lzb {L : ℕ} (S : Fin L → Matrix d d ℝ) (β : Fin (L + 1) → ℝ)
    (τ : ℝ) :
    cobSkip S (fun ℓ => scalarGL_lzb (Real.exp (τ * β ℓ)) (Real.exp_ne_zero _))
      = fun ℓ => Real.exp (τ * (β ℓ.succ - β ℓ.castSucc)) • S ℓ := by
  funext ℓ
  show ((Real.exp (τ * β ℓ.castSucc))⁻¹ • (1 : Matrix d d ℝ)) * S ℓ
      * (Real.exp (τ * β ℓ.succ) • (1 : Matrix d d ℝ)) = _
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_sub,
    Real.exp_sub, div_eq_mul_inv]

/-- Helper (a copy of the private `hasDerivAt_exp_mul_const_rz`): `τ ↦ e^{τ a} b` has derivative
`a b` at `τ = 0`. -/
private theorem hasDerivAt_exp_mul_const_lzb (a b : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.exp (τ * a) * b) (a * b) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const a).exp.mul_const b
  simpa using h

omit [Fintype T] [DecidableEq d] in
/-- Helper (a copy of the private `hasDerivAt_scaleCurve_rz`): the curve of the scales has
velocity `scaleDir θ β` at `τ = 0`. -/
private theorem hasDerivAt_scaleCurve_lzb {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut)
    (β : Fin (L + 1) → ℝ) : HasDerivAt (scaleCurve_lzb θ β) (scaleDir θ β) 0 := by
  have hprod : HasDerivAt (fun τ : ℝ => Params.linearEquivProd (scaleCurve_lzb θ β τ))
      (Params.linearEquivProd (scaleDir θ β)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · exact hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun k =>
        hasDerivAt_exp_mul_const_lzb (β 0) (θ.E i k)
    · exact hasDerivAt_const (0 : ℝ) θ.read
    · exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun k =>
        hasDerivAt_exp_mul_const_lzb (β ℓ.succ) (θ.write ℓ i k)
    · exact hasDerivAt_const (0 : ℝ) θ.D
  exact (LinearMap.toContinuousLinearMap
    (Params.linearEquivProd (A := A) (dIn := dIn)
      (dOut := dOut)).symm.toLinearMap).hasFDerivAt.comp_hasDerivAt 0 hprod

/-- **Step 1, the scales are flat** (Proposition 3.2 for `ε = 0` with the skips as parameters):
with `G_ℓ = e^{τ β_ℓ} I` and `K_ℓ = I`, `N_0` loses the scale, so the curve
`τ ↦ (θ.cob G_τ K, cobSkip S G_τ)` keeps the function, and its direction
`(scaleDir θ β, (β_ℓ − β_{ℓ-1}) S_ℓ)` is flat. -/
private theorem scale_mem_flatSkips_lzb {L : ℕ} {A : Arch T d L} (hA : A.χ = rmsNorm 0)
    (θ : Params A dIn dOut) (S : Fin L → Matrix d d ℝ) (β : Fin (L + 1) → ℝ) :
    (scaleDir θ β, fun ℓ => (β ℓ.succ - β ℓ.castSucc) • S ℓ)
      ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S) := by
  -- the curve, written out, and its velocity
  have hγ : HasDerivAt (fun τ : ℝ => (scaleCurve_lzb θ β τ,
      fun ℓ => Real.exp (τ * (β ℓ.succ - β ℓ.castSucc)) • S ℓ))
      (scaleDir θ β, fun ℓ => (β ℓ.succ - β ℓ.castSucc) • S ℓ) 0 :=
    (hasDerivAt_scaleCurve_lzb θ β).prodMk (hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun i =>
      hasDerivAt_pi.2 fun j => hasDerivAt_exp_mul_const_lzb (β ℓ.succ - β ℓ.castSucc) (S ℓ i j))
  refine mem_flatSkips_of_hasDerivAt_lzb _ _ _ _ hγ ?_ ?_
  · -- at `τ = 0` the curve is at `(θ, S)`
    refine Prod.ext (scaleCurve_zero_lzb θ β) ?_
    funext ℓ
    show Real.exp (0 * (β ℓ.succ - β ℓ.castSucc)) • S ℓ = S ℓ
    rw [zero_mul, Real.exp_zero, one_smul]
  · -- along the curve the function is kept: `N_0(h c I) = N_0(h)` for `c > 0`
    refine Filter.Eventually.of_forall fun τ x => ?_
    have hχ : ∀ ℓ (h : Matrix T d ℝ),
        A.χ (h * ((scalarGL_lzb (Real.exp (τ * β ℓ)) (Real.exp_ne_zero _) : GL d ℝ) :
          Matrix d d ℝ))
          = A.χ h * ((1 : GL d ℝ) : Matrix d d ℝ) := by
      intro ℓ h
      rw [hA, Units.val_one]
      exact rmsNorm_zero_mul_smul_orthogonal (Real.exp_pos _) (one_mem _) h
    have h := eval_cob (M := S) (θ := θ)
      (G := fun ℓ => scalarGL_lzb (Real.exp (τ * β ℓ)) (Real.exp_ne_zero _))
      (K := fun _ => 1) (x := x) hχ
    rw [cobSkip_scalarGL_lzb S β τ, ← scaleCurve_eq_cob_lzb θ β τ] at h
    exact h

/-! ### Helpers: the linear maps of the directions, independence, and the count -/

/-- Helper (a copy of the private `skipDirLin_lso`): the direction of the skips under the
rotations, `X ↦ −X_{ℓ-1} S_ℓ + S_ℓ X_ℓ`, is linear. -/
private noncomputable def skipDirLin_lzb {L : ℕ} (S : Fin L → Matrix d d ℝ) :
    (Fin (L + 1) → Matrix d d ℝ) →ₗ[ℝ] (Fin L → Matrix d d ℝ) where
  toFun X ℓ := -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ
  map_add' X Y := by
    funext ℓ
    simp only [Pi.add_apply, Matrix.add_mul, Matrix.mul_add, neg_add]
    abel
  map_smul' c X := by
    funext ℓ
    simp only [Pi.smul_apply, Matrix.smul_mul, Matrix.mul_smul, smul_neg, smul_add,
      RingHom.id_apply]

/-- Helper (a copy of the private `scaleDirLin_rzv`): `β ↦ scaleDir θ β` is linear. -/
private noncomputable def scaleDirLin_lzb {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut) :
    (Fin (L + 1) → ℝ) →ₗ[ℝ] Params A dIn dOut where
  toFun := scaleDir θ
  map_add' β β' := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.add_E, Params.add_read, Params.add_write, Params.add_D,
        Pi.add_apply, add_smul, add_zero]
  map_smul' c β := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [scaleDir, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        Pi.smul_apply, smul_eq_mul, mul_smul, smul_zero, RingHom.id_apply]

/-- Helper: the direction of the skips under the scales, `β ↦ (β_ℓ − β_{ℓ-1}) S_ℓ`, is
linear. -/
private noncomputable def skipScaleLin_lzb {L : ℕ} (S : Fin L → Matrix d d ℝ) :
    (Fin (L + 1) → ℝ) →ₗ[ℝ] (Fin L → Matrix d d ℝ) where
  toFun β ℓ := (β ℓ.succ - β ℓ.castSucc) • S ℓ
  map_add' β β' := by
    funext ℓ
    simp only [Pi.add_apply, add_sub_add_comm, add_smul]
  map_smul' c β := by
    funext ℓ
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, mul_smul, RingHom.id_apply]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `eq_zero_of_mul_eq_zero_rzv`): a matrix `M` of rank equal to
its number of columns has no left zero divisor, `M X = 0 → X = 0`. -/
private theorem eq_zero_of_mul_eq_zero_lzb {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
    (hM : M.rank = Fintype.card n) {X : Matrix n k ℝ} (h : M * X = 0) : X = 0 := by
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [Matrix.rank] at hM
    omega
  ext i j
  have hcol : M.mulVecLin (fun l => X l j) = M.mulVecLin 0 := by
    funext p
    have := congrFun (congrFun h p) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  exact congrFun (hinj hcol) i

omit [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper (a copy of the private `antisymm_add_smul_one_eq_zero_rzv`): if `Y + b I = 0` with `Y`
antisymmetric and `d ≥ 1`, then `Y = 0` and `b = 0` (the diagonal of `Y` vanishes). -/
private theorem antisymm_add_smul_one_eq_zero_lzb [Nonempty d] {Y : Matrix d d ℝ}
    (hY : Yᵀ = -Y) {b : ℝ} (h : Y + b • (1 : Matrix d d ℝ) = 0) : Y = 0 ∧ b = 0 := by
  obtain ⟨k⟩ := ‹Nonempty d›
  have hYk : Y k k = 0 := by
    have := congrFun (congrFun hY k) k
    rw [transpose_apply, Matrix.neg_apply] at this
    linarith
  have hk := congrFun (congrFun h k) k
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, hYk,
    zero_add, Matrix.zero_apply] at hk
  subst hk
  rw [zero_smul, add_zero] at h
  exact ⟨h, rfl⟩

omit [Fintype T] [DecidableEq d] in
/-- Helper (a copy of the private `finrank_paramsSkip_lsn`): the weights and the skip have
`P + d²` entries. -/
private theorem finrank_paramsSkip_lzb {A : Arch T d 1} :
    Module.finrank ℝ (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))
      = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_matrix]
  simp [sq]

omit [DecidableEq d] in
/-- **Step 4, the count:** the functional dimension on a set `U` of inputs and the dimension of
the directions flat on `U` add up to at most the number of parameters. The functional dimension
on `U` is the rank on some batch of inputs of `U` (the ranks are bounded), and the kernel of the
Jacobian on that batch contains the directions flat on `U` (where the output is not
differentiable, the derivative is `0` and the kernel is everything). -/
private theorem funDimSkipsOn_add_finrank_flatSkipsOn_le_lzb {L : ℕ} {A : Arch T d L}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V) (U : Set (Matrix T dIn ℝ)) :
    funDimSkipsOn A ι p U + Module.finrank ℝ (flatSkipsOn A ι p U)
      ≤ Module.finrank ℝ (Params A dIn dOut × V) := by
  -- the functional dimension on `U` is the rank on some batch `X` of inputs of `U`
  have hbd : BddAbove {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      r = jacobianRankSkips A ι X p} := by
    refine ⟨Module.finrank ℝ (Params A dIn dOut × V), ?_⟩
    rintro _ ⟨m, Y, -, rfl⟩
    exact LinearMap.finrank_range_le _
  have hne : ({r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      r = jacobianRankSkips A ι X p}).Nonempty := ⟨_, 0, Fin.elim0, fun i => i.elim0, rfl⟩
  obtain ⟨n, X, hX, hEq⟩ : ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧
      funDimSkipsOn A ι p U = jacobianRankSkips A ι X p := Nat.sSup_mem hne hbd
  -- the directions flat on `U` are in the kernel of the Jacobian on `X`
  have hker : flatSkipsOn A ι p U ≤ LinearMap.ker (fderiv ℝ
      (fun p' : Params A dIn dOut × V => fun i : Fin n =>
        evalSkips A ι p' (X i)) p).toLinearMap := by
    intro η hη
    rw [LinearMap.mem_ker]
    by_cases hd : ∀ i, DifferentiableAt ℝ
        (fun p' : Params A dIn dOut × V => evalSkips A ι p' (X i)) p
    · have h : fderiv ℝ (fun p' : Params A dIn dOut × V =>
            fun i : Fin n => evalSkips A ι p' (X i)) p =
          ContinuousLinearMap.pi fun i => fderiv ℝ (fun p' => evalSkips A ι p' (X i)) p :=
        fderiv_pi hd
      show fderiv ℝ (fun p' : Params A dIn dOut × V =>
        fun i : Fin n => evalSkips A ι p' (X i)) p η = 0
      rw [h]
      funext i
      exact LinearMap.mem_ker.1
        ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hη (X i)) (hX i))
    · have hnd : ¬DifferentiableAt ℝ (fun p' : Params A dIn dOut × V =>
          fun i : Fin n => evalSkips A ι p' (X i)) p := fun h => hd (differentiableAt_pi.1 h)
      show fderiv ℝ (fun p' : Params A dIn dOut × V =>
        fun i : Fin n => evalSkips A ι p' (X i)) p η = 0
      rw [fderiv_zero_of_not_differentiableAt hnd]
      rfl
  -- rank–nullity on `X`
  have hrn : jacobianRankSkips A ι X p + Module.finrank ℝ (LinearMap.ker (fderiv ℝ
      (fun p' : Params A dIn dOut × V => fun i : Fin n => evalSkips A ι p' (X i)) p).toLinearMap)
      = Module.finrank ℝ (Params A dIn dOut × V) :=
    LinearMap.finrank_range_add_finrank_ker _
  have hmono := Submodule.finrank_mono hker
  rw [hEq]
  omega

/-- **Proof of Theorem B.1 (iii) of the skips paper, "The case `ε = 0`", the bound for the learned
skip:** for one block with an analytic fixed map and a full learned skip `A` that is invertible,
under pre-RMSNorm with `ε = 0`, if `E` has rank `d ≥ 1`, the functional dimension on the inputs
at which no normalized row vanishes is at most `P + d² − (d(d−1) + 2) − dim V_θ`. -/
theorem funDimSkipsOn_add_le_learned_rmsNorm_zero {A : Arch T d 1} [Nonempty d]
    (hA : A.χ = rmsNorm 0) (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (R : Fin 1 → Matrix d d ℝ) (hE : θ.E.rank = Fintype.card d) (hR : IsUnit (R 0).det) :
    funDimSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
        (learnedZeroDomain A θ R)
        + ((Fintype.card d * (Fintype.card d - 1) + 2)
          + Module.finrank ℝ (blockFlatSphere A θ))
      ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
  -- the families `X = (X_0, X_1)` of antisymmetric matrices, as matrices
  let Ψ : (Fin (1 + 1) → antisymmetric d) →ₗ[ℝ] (Fin (1 + 1) → Matrix d d ℝ) :=
    LinearMap.compLeft (antisymmetric d).subtype (Fin (1 + 1))
  -- the linear map `((X, β), ψ) ↦ (rotation by X) + (scaling by β) + (ψ, 0)`
  let Φ : ((Fin (1 + 1) → antisymmetric d) × (Fin (1 + 1) → ℝ)) × blockFlatSphere A θ →ₗ[ℝ]
      Params A dIn dOut × (Fin 1 → Matrix d d ℝ) :=
    ((((cobDirLin θ).comp Ψ).prod ((skipDirLin_lzb R).comp Ψ)).coprod
      ((scaleDirLin_lzb θ).prod (skipScaleLin_lzb R))).coprod
      ((LinearMap.inl ℝ (Params A dIn dOut) (Fin 1 → Matrix d d ℝ)).comp
        (blockFlatSphere A θ).subtype)
  -- Steps 1 and 2: its directions are flat on the inputs of `learnedZeroDomain A θ R`
  have hflat : LinearMap.range Φ ≤ flatSkipsOn A
      (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R) (learnedZeroDomain A θ R) := by
    rintro _ ⟨⟨⟨X, β⟩, ψ⟩, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact flatSkips_le_flatSkipsOn A _ (θ, R) _
        (rot_mem_flatSkips_lzb hA θ R (fun ℓ => (X ℓ : Matrix d d ℝ)) fun ℓ => (X ℓ).2)
    · exact flatSkips_le_flatSkipsOn A _ (θ, R) _ (scale_mem_flatSkips_lzb hA θ R β)
    · exact mem_flatSkipsOn_of_blockFlatSphere_lzb hA hf θ R ψ.2
  -- Step 3: it is injective
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨X, β⟩, ψ⟩ hp
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply] at hp
    obtain ⟨hψE, hψD, -⟩ := mem_blockFlatSphere_lzb ψ.2
    have h1 : cobDir θ (fun ℓ => (X ℓ : Matrix d d ℝ)) + scaleDir θ β
        + (ψ : Params A dIn dOut) = 0 := congrArg Prod.fst hp
    have h2 : (fun ℓ : Fin 1 => -((X ℓ.castSucc : Matrix d d ℝ) * R ℓ)
        + R ℓ * (X ℓ.succ : Matrix d d ℝ)) + (fun ℓ : Fin 1 => (β ℓ.succ - β ℓ.castSucc) • R ℓ)
        + 0 = 0 := congrArg Prod.snd hp
    -- the `E` component: `E (X_0 + β_0 I) = 0`, so `X_0 = 0` and `β_0 = 0`
    have hE0 : θ.E * (X 0 : Matrix d d ℝ) + β 0 • θ.E + (ψ : Params A dIn dOut).E = 0 :=
      congrArg Params.E h1
    rw [hψE, add_zero] at hE0
    have hE1 : θ.E * ((X 0 : Matrix d d ℝ) + β 0 • 1) = 0 := by
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
      exact hE0
    obtain ⟨hX0, hβ0⟩ :=
      antisymm_add_smul_one_eq_zero_lzb (X 0).2 (eq_zero_of_mul_eq_zero_lzb θ.E hE hE1)
    -- the skip component: `A (X_1 + β_1 I) = 0`, so `X_1 = 0` and `β_1 = 0` (`A` invertible)
    have hS0 : -((X 0 : Matrix d d ℝ) * R 0) + R 0 * (X 1 : Matrix d d ℝ) + (β 1 - β 0) • R 0
        + 0 = 0 := congrFun h2 0
    rw [hX0, hβ0, Matrix.zero_mul, neg_zero, zero_add, sub_zero, add_zero] at hS0
    have hS1 : R 0 * ((X 1 : Matrix d d ℝ) + β 1 • 1) = 0 := by
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
      exact hS0
    obtain ⟨hX1, hβ1⟩ := antisymm_add_smul_one_eq_zero_lzb (X 1).2
      (eq_zero_of_mul_eq_zero_lzb (R 0)
        (Matrix.rank_of_isUnit (R 0) ((Matrix.isUnit_iff_isUnit_det _).2 hR)) hS1)
    -- then `ψ` has read and write `0`
    have hR0 : -((X 0 : Matrix d d ℝ) * θ.read 0) + 0 + (ψ : Params A dIn dOut).read 0 = 0 :=
      congrArg (fun η => η.read 0) h1
    have hW0 : θ.write 0 * (X 1 : Matrix d d ℝ) + β 1 • θ.write 0
        + (ψ : Params A dIn dOut).write 0 = 0 :=
      congrArg (fun η => η.write 0) h1
    rw [hX0, Matrix.zero_mul, neg_zero, zero_add, zero_add] at hR0
    rw [hX1, hβ1, Matrix.mul_zero, zero_smul, zero_add, zero_add] at hW0
    have hψ0 : ψ = 0 := by
      refine Subtype.ext (Params.ext' hψE (fun ℓ => ?_) (fun ℓ => ?_) hψD)
      · rw [Fin.fin_one_eq_zero ℓ, hR0]
        rfl
      · rw [Fin.fin_one_eq_zero ℓ, hW0]
        rfl
    have hX : X = 0 := by
      funext ℓ
      refine Subtype.ext ?_
      fin_cases ℓ
      exacts [hX0, hX1]
    have hβ : β = 0 := by
      funext ℓ
      fin_cases ℓ
      exacts [hβ0, hβ1]
    subst hX hβ hψ0
    rfl
  -- its source has dimension `2 (d(d−1)/2) + 2 + dim V_θ = d(d−1) + 2 + dim V_θ`
  have hdim : Module.finrank ℝ
      (((Fin (1 + 1) → antisymmetric d) × (Fin (1 + 1) → ℝ)) × blockFlatSphere A θ)
      = (Fintype.card d * (Fintype.card d - 1) + 2)
        + Module.finrank ℝ (blockFlatSphere A θ) := by
    rw [Module.finrank_prod, Module.finrank_prod,
      Module.finrank_pi_fintype (R := ℝ) (ι := Fin (1 + 1)) (M := fun _ => antisymmetric d),
      finrank_antisymmetric, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Module.finrank_fin_fun]
    have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
    generalize Fintype.card d * (Fintype.card d - 1) = n at h2 ⊢
    omega
  -- so the directions flat on these inputs have dimension at least `d(d−1) + 2 + dim V_θ`
  have hrange := Submodule.finrank_mono hflat
  rw [LinearMap.finrank_range_of_inj hinj, hdim] at hrange
  -- Step 4: the count
  have hcount : funDimSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
        (learnedZeroDomain A θ R)
      + Module.finrank ℝ (flatSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ))
        (θ, R) (learnedZeroDomain A θ R))
      ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 :=
    (funDimSkipsOn_add_finrank_flatSkipsOn_le_lzb _ _ _).trans_eq finrank_paramsSkip_lzb
  generalize Fintype.card d * (Fintype.card d - 1) = q at hrange ⊢
  generalize Fintype.card d ^ 2 = s at hcount ⊢
  omega

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", at one parameter:** under the
conditions of the value for the residual network (`d ≥ 2`, `E`, `D` of rank `d`, one input `w`
with the rows of `w E` and `g(w)` independent for every token) and for an invertible full learned
skip, the functional dimension of the network with the learned skip exceeds that of the residual
network with the same weights by at most `d(d+1)/2 − 1`; both on the inputs at which no
normalized row vanishes. -/
theorem funDimSkipsOn_learned_le_funDimOn_residual_add_rmsNorm_zero {A : Arch T d 1}
    [Nonempty T] (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (R : Fin 1 → Matrix d d ℝ) (hE : θ.E.rank = Fintype.card d)
    (hD : θ.D.rank = Fintype.card d) (hR : IsUnit (R 0).det)
    (hw : ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t]) :
    funDimSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
        (learnedZeroDomain A θ R)
      ≤ funDimOn A 1 θ (residualZeroDomain A θ)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have h1 := funDimSkipsOn_add_le_learned_rmsNorm_zero hA hf θ R hE hR
  have h2 := funDimOn_residual_rmsNorm_zero_eq hA hd hf θ hE hD hw
  -- `d(d−1)` is even, and `d(d+1)/2 + d(d−1)/2 = d²`
  have e1 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  have e2 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (Fintype.card d))
  have e3 : Fintype.card d * (Fintype.card d + 1) + Fintype.card d * (Fintype.card d - 1)
      = 2 * Fintype.card d ^ 2 := by
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card d = m + 1 := ⟨Fintype.card d - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    ring
  generalize Fintype.card d * (Fintype.card d + 1) = y at e2 e3 ⊢
  generalize Fintype.card d * (Fintype.card d - 1) = x at h1 h2 e1 e3
  generalize Fintype.card d ^ 2 = q at h1 e3
  omega

end Skips
