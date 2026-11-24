import SkipsLean.OneBlock.ResidualRMSZeroSteps
import SkipsLean.Depth.SuffixZero

/-!
# One block under pre-RMSNorm with `ε = 0`: the gain of the skip is at least `dim CO(d)`

Paper (skips paper), Theorem B.1 (v): "Let the network be pre-RMSNorm with `ε = 0`, without biases,
with a tanh, GELU, SwiGLU, GeGLU or attention block. For generic parameters the skip raises the
functional dimension by at least `d_model (d_model − 1)/2 + 1`, the dimension of `CO(d_model)`."

Its proof: "Let `V_θ` be the space of directions that move only the weights of the block and leave
its output unchanged to first order at every input whose rows lie on this sphere; it contains the
symmetries inside the block. We show that the flat directions of the residual network are those of
`CO(d_model)` and those of `V_θ`, while the skipless network has at least two copies of
`CO(d_model)` and `V_θ`. The bound then holds whatever `V_θ` is. […] So `K(θ)` is the direct sum
of these directions and `V_θ`, and the residual network has functional dimension
`P − dim CO(d_model) − dim V_θ`."

"Notation and flat directions" (Appendix B): with `ε = 0`, "every input" excludes the inputs at
which a row of a hidden state that is normalized vanishes. Lean's `funDim` uses every input, also
an input with a zero row, at which Lean's `rmsNorm 0` is `0`. So the functional dimension of
Theorem B.1 (v) is stated here as the largest rank of the Jacobian over the finite batches of
inputs of a set (`funDimOn`): for the residual network the inputs at which no row of `h_0` and of
`h_1` vanishes (`residualZeroDomain`), for the skipless network the inputs at which no row of
`h_0` and of the output `h_1` of the block vanishes (`skiplessZeroDomain`).

Here, at one parameter `θ`, for a fixed map `f` of the block that is analytic, under the
conditions of the proof: `V_θ` (`blockFlatSphere`); the residual network has functional dimension
at least `P − (d(d−1)/2 + 1) − dim V_θ`; the skipless network at most
`P − 2 (d(d−1)/2 + 1) − dim V_θ`; so the skip raises it by at least `d(d−1)/2 + 1`. The
conditions: `d ≥ 2`; `E` and `D` of rank `d`; one input `w` at which for every token the rows of
`w E` and of `g(w)` are linearly independent (residual side); the block is not zero at some point
of the sphere (skipless side: the scale at `h_1` then does not lie in `V_θ`). The second condition
follows from the first, so the gain is stated under the first alone. That these conditions hold at
generic parameters for the five kinds of block is in `OneBlock/ResidualRMSZeroKinds.lean`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The functional dimension on a set of inputs:** the largest rank of the Jacobian in the
weights over the finite batches of inputs of `U`. (For `U` the set of all inputs it is `funDim`.) -/
noncomputable def funDimOn {L : ℕ} (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (θ : Params A dIn dOut) (U : Set (Matrix T dIn ℝ)) : ℕ :=
  sSup {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) ∧ r = jacobianRank A S X θ}

/-- **The inputs of a skipless network of one block under pre-RMSNorm with `ε = 0` at which no
normalized row vanishes:** no row of `h_0 = x E` and no row of `h_1 = f(N_0(x E) W_read) W_write`
is zero. -/
def skiplessZeroDomain (A : Arch T d 1) (θ : Params A dIn dOut) : Set (Matrix T dIn ℝ) :=
  {x | (∀ t, (x * θ.E) t ≠ 0) ∧
    ∀ t, (A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) t ≠ 0}

/-- **The space `V_θ` of the proof of Theorem B.1 (v):** the directions that move only the weights
of the block and leave its output unchanged to first order at every input `n` whose rows lie on
the sphere of radius `√d`. (The set of these directions is a subspace; it is written as its
span.) -/
noncomputable def blockFlatSphere (A : Arch T d 1) (θ : Params A dIn dOut) :
    Submodule ℝ (Params A dIn dOut) :=
  Submodule.span ℝ {ψ | ψ.E = 0 ∧ ψ.D = 0 ∧
    ∀ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = Fintype.card d) →
      fderiv ℝ (A.f 0) (n * θ.read 0) (n * ψ.read 0) * θ.write 0
        + A.f 0 (n * θ.read 0) * ψ.write 0 = 0}

/-! ### Helpers: the supremum in `funDimOn` -/

omit [Nonempty T] [DecidableEq d] in
/-- Helper: the rank of the Jacobian on a batch of inputs of `U` is at most `funDimOn` (the ranks
are bounded by `P`). -/
private theorem jacobianRank_le_funDimOn_rzg {L : ℕ} (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (θ : Params A dIn dOut) (U : Set (Matrix T dIn ℝ)) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i, X i ∈ U) : jacobianRank A S X θ ≤ funDimOn A S θ U := by
  -- a member of a set of naturals bounded above (by `P`) is at most its supremum
  refine le_csSup ⟨Module.finrank ℝ (Params A dIn dOut), ?_⟩ ⟨n, X, hX, rfl⟩
  rintro _ ⟨m, Y, -, rfl⟩
  exact jacobianRank_le_finrank θ Y

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: if every batch of inputs of `U` has `rank + k ≤ N`, then `funDimOn + k ≤ N`. -/
private theorem funDimOn_add_le_rzg {L : ℕ} (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (θ : Params A dIn dOut) (U : Set (Matrix T dIn ℝ)) {k N : ℕ}
    (h : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ U) →
      jacobianRank A S X θ + k ≤ N) :
    funDimOn A S θ U + k ≤ N := by
  -- the empty batch gives `k ≤ N`
  have h0 := h 0 (fun i => i.elim0) (fun i => i.elim0)
  -- every rank is at most `N - k`, hence so is the supremum
  have hle : funDimOn A S θ U ≤ N - k := by
    refine csSup_le ⟨_, 0, fun i => i.elim0, fun i => i.elim0, rfl⟩ ?_
    rintro _ ⟨m, Y, hY, rfl⟩
    have := h m Y hY
    omega
  omega

omit [Nonempty T] [DecidableEq d] in
/-- Helper: the directions flat at every input of `U` lie in the kernel of the Jacobian on a batch
of inputs of `U` (if some output of the batch is not differentiable, the Jacobian is `0`). -/
private theorem flatOn_le_ker_rzg {L : ℕ} {A : Arch T d L} {S : Fin L → Matrix d d ℝ}
    (θ : Params A dIn dOut) {U : Set (Matrix T dIn ℝ)} {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i, X i ∈ U) :
    flatOn A S θ U ≤ LinearMap.ker (fderiv ℝ (evalBatch A S X) θ).toLinearMap := by
  intro η hη
  rw [LinearMap.mem_ker]
  by_cases hd : ∀ i, DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A S θ' (X i)) θ
  · -- the Jacobian on the batch is the tuple of the derivatives at its inputs
    have h : fderiv ℝ (evalBatch A S X) θ =
        ContinuousLinearMap.pi fun i => fderiv ℝ (fun θ' => eval A S θ' (X i)) θ :=
      fderiv_pi hd
    show fderiv ℝ (evalBatch A S X) θ η = 0
    rw [h]
    funext i
    exact LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hη (X i)) (hX i))
  · -- not differentiable: Mathlib's derivative is `0`
    have hnd : ¬DifferentiableAt ℝ (evalBatch A S X) θ := fun h => hd (differentiableAt_pi.1 h)
    show fderiv ℝ (evalBatch A S X) θ η = 0
    rw [fderiv_zero_of_not_differentiableAt hnd]
    rfl

omit [Nonempty T] [DecidableEq d] in
/-- Helper (rank–nullity on a batch of inputs of `U`): `rank + dim K_U(θ) ≤ P`. -/
private theorem jacobianRank_add_finrank_flatOn_le_rzg {L : ℕ} {A : Arch T d L}
    {S : Fin L → Matrix d d ℝ} (θ : Params A dIn dOut) {U : Set (Matrix T dIn ℝ)} {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) (hX : ∀ i, X i ∈ U) :
    jacobianRank A S X θ + Module.finrank ℝ (flatOn A S θ U)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ (evalBatch A S X) θ).toLinearMap
  have hmono := Submodule.finrank_mono (flatOn_le_ker_rzg (S := S) θ X hX)
  unfold jacobianRank
  omega

/-! ### Helpers: the sphere, and the space `V_θ` -/

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper (the private `rmsRow_zero_dotProduct_self` of `Basic/RMSNormConverse.lean`): for
`ε = 0` every nonzero row is normalized to squared norm `d`. -/
private theorem rmsRow_zero_dotProduct_self_rzg {v : d → ℝ} (hv : v ≠ 0) :
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

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `N_0(h)` has all rows on the sphere of radius `√d` if no row of `h` vanishes. -/
private theorem rmsNorm_zero_sphere_rzg {h : Matrix T d ℝ} (hh : ∀ t, h t ≠ 0) (t : T) :
    rmsNorm 0 h t ⬝ᵥ rmsNorm 0 h t = Fintype.card d :=
  rmsRow_zero_dotProduct_self_rzg (hh t)

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: every direction of `V_θ` moves only the weights of the block, and its derivative
vanishes at every `n` on the sphere: the conditions are linear in `ψ`, so they pass from the
spanning set to its span. -/
private theorem mem_blockFlatSphere_rzg {A : Arch T d 1} {θ ψ : Params A dIn dOut}
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

/-! ### Helpers: the function of one block, and derivatives along a line -/

omit [Fintype T] [Nonempty T] [Fintype dOut] in
/-- Helper: the function of the residual network of one block under pre-RMSNorm with `ε = 0`. -/
private theorem eval_residual_rzg {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    eval A 1 θ x
      = rmsNorm 0 (x * θ.E + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) * θ.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]
  simp only [Pi.one_apply, Matrix.mul_one]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the function of the skipless network of one block under pre-RMSNorm with `ε = 0`
(the stream matrix is `0`). -/
private theorem eval_skipless_rzg {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    eval A 0 θ x
      = rmsNorm 0 (A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) * θ.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]
  simp only [Pi.zero_apply, Matrix.mul_zero, zero_add]

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `hasDerivAt_mul_son`): the product rule for matrices depending on one
real variable. -/
private theorem hasDerivAt_mul_rzg {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
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
/-- Helper (the private `hasDerivAt_affine_son`): `τ ↦ M + τ N` has the derivative `N` at `0`. -/
private theorem hasDerivAt_affine_rzg {m n : Type*} [Fintype m] [Fintype n]
    (M N : Matrix m n ℝ) : HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `differentiableAt_matMul_son`): the product of two matrix-valued maps
that are differentiable at a point is differentiable there. -/
private theorem differentiableAt_matMul_rzg {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
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

/-! ### Helpers for the residual network -/

omit [Nonempty T] in
/-- Helper: at an input of `residualZeroDomain`, the output of the residual network is a
differentiable function of the parameters at `θ`: the rows of `x E` and of `h_1` are nonzero, so
`N_0` is differentiable at both, and `f` is analytic. -/
private theorem differentiableAt_eval_residual_rzg {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ residualZeroDomain A θ) :
    DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 1 θ' x) θ := by
  have e : (fun θ' : Params A dIn dOut => eval A 1 θ' x) = fun θ' => rmsNorm 0
      (x * θ'.E + A.f 0 (rmsNorm 0 (x * θ'.E) * θ'.read 0) * θ'.write 0) * θ'.D :=
    funext fun θ' => eval_residual_rzg hA θ' x
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
  -- `x E`, `N_0(x E)` (no row of `x E` vanishes) and `N_0(x E) W_read`
  have h1 : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => x * θ'.E) θ :=
    differentiableAt_matMul_rzg (differentiableAt_const x) hE
  have h2 : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => rmsNorm 0 (x * θ'.E)) θ :=
    DifferentiableAt.comp (f := fun θ' : Params A dIn dOut => x * θ'.E) θ
      (analyticAt_rmsNorm_zero _ hx.1).differentiableAt h1
  have h3 : DifferentiableAt ℝ
      (fun θ' : Params A dIn dOut => rmsNorm 0 (x * θ'.E) * θ'.read 0) θ :=
    differentiableAt_matMul_rzg h2 hR
  -- `f` is analytic
  have h4 : DifferentiableAt ℝ
      (fun θ' : Params A dIn dOut => A.f 0 (rmsNorm 0 (x * θ'.E) * θ'.read 0)) θ :=
    DifferentiableAt.comp (f := fun θ' : Params A dIn dOut => rmsNorm 0 (x * θ'.E) * θ'.read 0)
      θ (hf _ (Set.mem_univ _)).differentiableAt h3
  -- `h_1`, `N_0(h_1)` (no row of `h_1` vanishes) and `N_0(h_1) D`
  have h5 : DifferentiableAt ℝ (fun θ' : Params A dIn dOut =>
      x * θ'.E + A.f 0 (rmsNorm 0 (x * θ'.E) * θ'.read 0) * θ'.write 0) θ :=
    h1.add (differentiableAt_matMul_rzg h4 hW)
  have h6 : DifferentiableAt ℝ (fun θ' : Params A dIn dOut =>
      rmsNorm 0 (x * θ'.E + A.f 0 (rmsNorm 0 (x * θ'.E) * θ'.read 0) * θ'.write 0)) θ :=
    DifferentiableAt.comp (f := fun θ' : Params A dIn dOut =>
      x * θ'.E + A.f 0 (rmsNorm 0 (x * θ'.E) * θ'.read 0) * θ'.write 0) θ
      (analyticAt_rmsNorm_zero _ hx.2).differentiableAt h5
  exact differentiableAt_matMul_rzg h6 hD

/-- Helper (the private `scaleDirLin_rz`): `β ↦ scaleDir θ β` is linear. -/
private noncomputable def scaleDirLin_rzg {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut) :
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

/-- **Theorem B.1 (v) of the skips paper, the residual network:** under the conditions of
`exists_antisymm_scale_of_flatOn_residual_rmsNorm_zero`, the functional dimension of the residual
network with `ε = 0`, on the inputs at which no normalized row vanishes, is at least
`P − (d(d−1)/2 + 1) − dim V_θ`. -/
theorem finrank_le_funDimOn_residual_rmsNorm_zero {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t]) :
    Module.finrank ℝ (Params A dIn dOut)
      ≤ funDimOn A 1 θ (residualZeroDomain A θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        + Module.finrank ℝ (blockFlatSphere A θ) := by
  -- (a) at every input of `U` the output is differentiable at `θ`, so some batch of inputs of `U`
  -- has `rank + dim K_U(θ) = P`, and its rank is at most `funDimOn`
  obtain ⟨n, X, hXU, hrank⟩ := exists_jacobianRank_add_finrank_flatOn (S := 1) θ
    (residualZeroDomain A θ) fun x hx => differentiableAt_eval_residual_rzg hA hf θ x hx
  have hfd := jacobianRank_le_funDimOn_rzg A 1 θ (residualZeroDomain A θ) X hXU
  -- (b) the directions of `CO(d)`: `(Y, c) ↦ cobDir θ (fun _ => Y) + scaleDir θ (fun _ => c)`
  let Ψ : antisymmetric d × ℝ →ₗ[ℝ] Params A dIn dOut :=
    ((cobDirLin θ).comp (LinearMap.pi fun _ => (antisymmetric d).subtype)).coprod
      ((scaleDirLin_rzg θ).comp (LinearMap.pi fun _ => LinearMap.id))
  -- a direction flat on `U` is one of `CO(d)` plus one of `V_θ`
  have hle : flatOn A 1 θ (residualZeroDomain A θ) ≤ LinearMap.range Ψ ⊔ blockFlatSphere A θ := by
    intro η hη
    obtain ⟨Y, c, hY, hηE, hηD, hn⟩ :=
      exists_antisymm_scale_of_flatOn_residual_rmsNorm_zero hA hd hf θ hE hD hw η hη
    have hsplit : η = Ψ (⟨Y, hY⟩, c) + (η - Ψ (⟨Y, hY⟩, c)) := (add_sub_cancel _ _).symm
    rw [hsplit]
    refine Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (Submodule.subset_span ?_)
    -- `ψ = η − η^Y − c η^scale` moves only the weights of the block, and is flat on the sphere
    show _ ∧ _ ∧ _
    refine ⟨?_, ?_, fun m hm => ?_⟩
    · show η.E - (θ.E * Y + c • θ.E) = 0
      rw [hηE, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, sub_self]
    · show η.D - (-(Y * θ.D) + 0) = 0
      rw [hηD, add_zero, sub_self]
    · have hR : (η - Ψ (⟨Y, hY⟩, c)).read 0 = η.read 0 + Y * θ.read 0 := by
        show η.read 0 - (-(Y * θ.read 0) + 0) = _
        rw [add_zero, sub_neg_eq_add]
      have hW : (η - Ψ (⟨Y, hY⟩, c)).write 0 = η.write 0 - θ.write 0 * (Y + c • 1) := by
        show η.write 0 - (θ.write 0 * Y + c • θ.write 0) = _
        rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
      rw [hR, hW]
      exact hn m hm
  -- (c) `dim (range Ψ ⊔ V_θ) ≤ dim CO(d) + dim V_θ`
  have h1 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range Ψ) (blockFlatSphere A θ)
  have h2 := LinearMap.finrank_range_le Ψ
  have h3 : Module.finrank ℝ (antisymmetric d × ℝ)
      = Fintype.card d * (Fintype.card d - 1) / 2 + 1 := by
    rw [Module.finrank_prod, finrank_antisymmetric, Module.finrank_self]
  have h4 := Submodule.finrank_mono hle
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = q at h3 ⊢
  omega

/-! ### Helpers for the skipless network -/

omit [Nonempty T] [DecidableEq d] in
/-- Helper: a direction of `V_θ` is flat at every input of the skipless network at which no
normalized row vanishes. Along it only the weights of the block move; `n = N_0(x E)` has its rows
on the sphere, so the block's output `h_1 = f(n W_read) W_write` does not move to first order, and
neither does `N_0(h_1) D` (`N_0` is differentiable at `h_1`, whose rows are nonzero). -/
private theorem blockFlatSphere_le_flatOn_rzg {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut) :
    blockFlatSphere A θ ≤ flatOn A 0 θ (skiplessZeroDomain A θ) := by
  intro ψ hψ
  obtain ⟨hψE, hψD, hψn⟩ := mem_blockFlatSphere_rzg hψ
  rw [flatOn, Submodule.mem_iInf]
  intro x
  rw [Submodule.mem_iInf]
  intro hx
  rw [LinearMap.mem_ker]
  show fderiv ℝ (fun θ' : Params A dIn dOut => eval A 0 θ' x) θ ψ = 0
  by_cases hdx : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A 0 θ' x) θ
  swap
  · rw [fderiv_zero_of_not_differentiableAt hdx]
    rfl
  -- the derivative along the line `θ + τ ψ`
  have h1 := hasDerivAt_eval_line (0 : Fin 1 → Matrix d d ℝ) θ ψ x hdx
  -- `n = N_0(x E)` does not move along the line; its rows lie on the sphere
  obtain ⟨n, hn⟩ : ∃ n, n = rmsNorm 0 (x * θ.E) := ⟨_, rfl⟩
  have hsph : ∀ t, n t ⬝ᵥ n t = Fintype.card d := by
    rw [hn]
    exact rmsNorm_zero_sphere_rzg hx.1
  -- the block `f(n W_read(τ)) W_write(τ)` has the derivative `0` at `τ = 0`
  have hR := hasDerivAt_mul_rzg (hasDerivAt_const (0 : ℝ) n)
    (hasDerivAt_affine_rzg (θ.read 0) (ψ.read 0)) (P0 := n) (Q0 := θ.read 0) rfl (by simp)
  have hF := ((hf (n * θ.read 0) (Set.mem_univ _)).differentiableAt).hasFDerivAt
    |>.comp_hasDerivAt_of_eq (0 : ℝ) hR (by simp)
  have hFW := hasDerivAt_mul_rzg hF (hasDerivAt_affine_rzg (θ.write 0) (ψ.write 0))
    (P0 := A.f 0 (n * θ.read 0)) (Q0 := θ.write 0) (by simp) (by simp)
  have hg : HasDerivAt (fun τ : ℝ => A.f 0 (n * (θ.read 0 + τ • ψ.read 0))
      * (θ.write 0 + τ • ψ.write 0)) 0 0 := by
    refine hFW.congr_deriv ?_
    rw [Matrix.zero_mul, zero_add]
    exact hψn n hsph
  -- `N_0` is differentiable at `h_1 = f(n W_read) W_write`, whose rows are nonzero
  have hrows : ∀ t, (A.f 0 (n * θ.read 0) * θ.write 0) t ≠ 0 := by
    rw [hn]
    exact hx.2
  have hN := (analyticAt_rmsNorm_zero _ hrows).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq (0 : ℝ) hg (by simp)
  have h2 := hasDerivAt_mul_rzg hN (hasDerivAt_const (0 : ℝ) θ.D)
    (P0 := rmsNorm 0 (A.f 0 (n * θ.read 0) * θ.write 0)) (Q0 := θ.D) (by simp) rfl
  -- the output along the line, written with `n`
  have e : (fun τ : ℝ => eval A 0 (θ + τ • ψ) x) = fun τ => rmsNorm 0
      (A.f 0 (n * (θ.read 0 + τ • ψ.read 0)) * (θ.write 0 + τ • ψ.write 0)) * θ.D := by
    funext τ
    rw [eval_skipless_rzg hA, hn]
    simp only [Params.add_E, Params.smul_E, hψE, smul_zero, add_zero, Params.add_D,
      Params.smul_D, hψD, Params.add_read, Params.smul_read, Params.add_write,
      Params.smul_write]
  rw [e] at h1
  refine h1.unique (h2.congr_deriv ?_)
  rw [map_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero]

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix `M` of rank equal to its number of columns has no left zero divisor:
`M X = 0 → X = 0` (its kernel is `0` by rank–nullity). -/
private theorem eq_zero_of_mul_eq_zero_rzg {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
    (hM : M.rank = Fintype.card n) {X : Matrix n k ℝ} (h : M * X = 0) : X = 0 := by
  -- `v ↦ M v` is injective: `rank M + dim ker M = card n`
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [Matrix.rank] at hM
    omega
  -- column by column
  ext i j
  have hcol : M.mulVecLin (fun l => X l j) = M.mulVecLin 0 := by
    funext p
    have := congrFun (congrFun h p) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  exact congrFun (hinj hcol) i

omit [Fintype T] [Nonempty T] [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if `Y + b I = 0` with `Y` antisymmetric, then `Y = 0` and `b = 0`: the diagonal of an
antisymmetric matrix vanishes, so a diagonal entry gives `b = 0`. -/
private theorem antisymm_add_smul_one_eq_zero_rzg [Nonempty d] {Y : Matrix d d ℝ}
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

/-- **Theorem B.1 (v) of the skips paper, the skipless network:** if `E` and `D` have rank `d` and
the block is not zero at some `n` with rows on the sphere of radius `√d`, the functional dimension
of the skipless network with `ε = 0`, on the inputs at which no normalized row vanishes, is at
most `P − 2 (d(d−1)/2 + 1) − dim V_θ`: the directions of `CO(d)` at `h_0`, of `CO(d)` at `h_1` and
of `V_θ` are flat and independent. -/
theorem funDimOn_add_le_skipless_rmsNorm_zero {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hB : ∃ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = Fintype.card d) ∧
      A.f 0 (n * θ.read 0) * θ.write 0 ≠ 0) :
    funDimOn A 0 θ (skiplessZeroDomain A θ)
        + 2 * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        + Module.finrank ℝ (blockFlatSphere A θ)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- `d` is not empty: the block is not zero at the `n₀` of `hB`
  obtain ⟨n₀, hn₀, hB₀⟩ := hB
  have hne : Nonempty d := by
    obtain ⟨t, ht⟩ := Function.ne_iff.1 hB₀
    obtain ⟨j, -⟩ := Function.ne_iff.1 ht
    exact ⟨j⟩
  -- the linear map `((Y, β), ψ) ↦ cobDir θ Y + scaleDir θ β + ψ`, with antisymmetric `Y_0, Y_1`
  let Φ : ((Fin (1 + 1) → antisymmetric d) × (Fin (1 + 1) → ℝ)) × blockFlatSphere A θ →ₗ[ℝ]
      Params A dIn dOut :=
    (((cobDirLin θ).comp (LinearMap.compLeft (antisymmetric d).subtype (Fin (1 + 1)))).coprod
      (scaleDirLin_rzg θ)).coprod (blockFlatSphere A θ).subtype
  -- its directions are flat at every input of `U`: `CO(d)` at `h_0` and at `h_1`, and `V_θ`
  have hflat : LinearMap.range Φ ≤ flatOn A 0 θ (skiplessZeroDomain A θ) := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact flat_le_flatOn θ _ (cobDir_mem_flat_skipless_rmsNorm' θ 0 hA
        (fun ℓ => (p.1.1 ℓ : Matrix d d ℝ)) fun ℓ => (p.1.1 ℓ).2)
    · exact flat_le_flatOn θ _ (scaleDir_mem_flat_skipless_rmsNorm_zero θ hA p.1.2)
    · exact blockFlatSphere_le_flatOn_rzg hA hf θ p.2.2
  -- it is injective
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨Y, β⟩, ψ⟩ hp
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply] at hp
    have h : cobDir θ (fun ℓ => (Y ℓ : Matrix d d ℝ)) + scaleDir θ β
        + (ψ : Params A dIn dOut) = 0 := hp
    obtain ⟨hψE, hψD, hψn⟩ := mem_blockFlatSphere_rzg ψ.2
    -- the four components
    have hE0 : θ.E * (Y 0 : Matrix d d ℝ) + β 0 • θ.E + (ψ : Params A dIn dOut).E = 0 :=
      congrArg Params.E h
    have hD0 : -((Y 1 : Matrix d d ℝ) * θ.D) + 0 + (ψ : Params A dIn dOut).D = 0 :=
      congrArg Params.D h
    have hR0 : -((Y 0 : Matrix d d ℝ) * θ.read 0) + 0 + (ψ : Params A dIn dOut).read 0 = 0 :=
      congrArg (fun η => η.read 0) h
    have hW0 : θ.write 0 * (Y 1 : Matrix d d ℝ) + β 1 • θ.write 0
        + (ψ : Params A dIn dOut).write 0 = 0 :=
      congrArg (fun η => η.write 0) h
    -- `E (Y_0 + β_0 I) = 0`, and `E` has rank `d`: `Y_0 = 0`, `β_0 = 0`
    rw [hψE, add_zero] at hE0
    have hE1 : θ.E * ((Y 0 : Matrix d d ℝ) + β 0 • 1) = 0 := by
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
      exact hE0
    obtain ⟨hY0, hβ0⟩ :=
      antisymm_add_smul_one_eq_zero_rzg (Y 0).2 (eq_zero_of_mul_eq_zero_rzg θ.E hE hE1)
    -- `Y_1 D = 0`, and `D` has rank `d`: `Y_1 = 0`
    rw [hψD, add_zero, add_zero, neg_eq_zero] at hD0
    have hY1 : (Y 1 : Matrix d d ℝ) = 0 := by
      have h' : θ.Dᵀ * (Y 1 : Matrix d d ℝ)ᵀ = 0 := by
        rw [← Matrix.transpose_mul, hD0, Matrix.transpose_zero]
      have h'' := eq_zero_of_mul_eq_zero_rzg θ.Dᵀ (by rw [Matrix.rank_transpose]; exact hD) h'
      rwa [Matrix.transpose_eq_zero] at h''
    -- the read of `ψ` is `0`, its write `−β_1 W_write`
    rw [hY0, Matrix.zero_mul, neg_zero, zero_add, zero_add] at hR0
    rw [hY1, Matrix.mul_zero, zero_add] at hW0
    have hW1 : (ψ : Params A dIn dOut).write 0 = -(β 1 • θ.write 0) :=
      eq_neg_of_add_eq_zero_right hW0
    -- at `n₀`: `β_1 f(n₀ W_read) W_write = 0`, so `β_1 = 0`
    have h1 := hψn n₀ hn₀
    rw [hR0, Matrix.mul_zero, map_zero, Matrix.zero_mul, zero_add, hW1, Matrix.mul_neg,
      Matrix.mul_smul, neg_eq_zero] at h1
    have hβ1 : β 1 = 0 := (smul_eq_zero.1 h1).resolve_right hB₀
    -- so every component vanishes
    have hψ0 : ψ = 0 := by
      refine Subtype.ext (Params.ext' hψE (fun ℓ => ?_) (fun ℓ => ?_) hψD)
      · rw [Fin.fin_one_eq_zero ℓ, hR0]
        rfl
      · rw [Fin.fin_one_eq_zero ℓ, hW1, hβ1, zero_smul, neg_zero]
        rfl
    have hY : ∀ ℓ, (Y ℓ : Matrix d d ℝ) = 0 := Fin.forall_fin_two.2 ⟨hY0, hY1⟩
    have hβ : ∀ ℓ, β ℓ = 0 := Fin.forall_fin_two.2 ⟨hβ0, hβ1⟩
    exact Prod.ext (Prod.ext (funext fun ℓ => Subtype.ext (hY ℓ)) (funext hβ)) hψ0
  -- the domain has dimension `2 (d(d−1)/2 + 1) + dim V_θ`
  have hdim : Module.finrank ℝ
      (((Fin (1 + 1) → antisymmetric d) × (Fin (1 + 1) → ℝ)) × blockFlatSphere A θ)
      = 2 * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        + Module.finrank ℝ (blockFlatSphere A θ) := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_pi_fintype,
      finrank_antisymmetric, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Module.finrank_fin_fun]
    ring
  have hrange := Submodule.finrank_mono hflat
  rw [LinearMap.finrank_range_of_inj hinj, hdim] at hrange
  -- every batch of inputs of `U` has `rank + dim K_U(θ) ≤ P`
  have hfd := funDimOn_add_le_rzg A 0 θ (skiplessZeroDomain A θ)
    (k := Module.finrank ℝ (flatOn A 0 θ (skiplessZeroDomain A θ)))
    (fun _ X hX => jacobianRank_add_finrank_flatOn_le_rzg θ X hX)
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = q at hrange ⊢
  omega

/-! ### Helper: the condition `hB` follows from `hw` -/

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the hypothesis `hB` of the skipless count follows from the hypothesis `hw` of the
residual count. At the input `w` of `hw` every row of `w E` is nonzero (it is part of an
independent pair), so the rows of `n = N_0(w E)` lie on the sphere; and every row of
`f(n W_read) W_write` is nonzero too (independence again), while `T` is nonempty. -/
private theorem exists_sphere_ne_zero_of_linearIndependent_rzg {A : Arch T d 1}
    (θ : Params A dIn dOut)
    (hw : ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t]) :
    ∃ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = Fintype.card d) ∧
      A.f 0 (n * θ.read 0) * θ.write 0 ≠ 0 := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨t₀⟩ := ‹Nonempty T›
  refine ⟨rmsNorm 0 (w * θ.E), rmsNorm_zero_sphere_rzg fun t => ?_, fun h0 => ?_⟩
  · exact (hw t).ne_zero 0
  · apply (hw t₀).ne_zero 1
    show (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t₀ = 0
    rw [h0]
    rfl

/-- **Theorem B.1 (v) of the skips paper, at one parameter, under the conditions of its proof:**
with `ε = 0`, if `d ≥ 2`, `E` and `D` have rank `d` and some input `w` has, for every token, the
rows of `w E` and of `g(w)` linearly independent, the skip raises the functional dimension by at
least `d(d−1)/2 + 1`, the dimension of `CO(d)`. -/
theorem funDimOn_skipless_add_le_funDimOn_residual_rmsNorm_zero {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t]) :
    funDimOn A 0 θ (skiplessZeroDomain A θ) + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn A 1 θ (residualZeroDomain A θ) := by
  -- the residual count, and the skipless count with `hB` obtained from `hw`
  have h1 := finrank_le_funDimOn_residual_rmsNorm_zero hA hd hf θ hE hD hw
  have h2 := funDimOn_add_le_skipless_rmsNorm_zero hA hf θ hE hD
    (exists_sphere_ne_zero_of_linearIndependent_rzg θ hw)
  -- `P ≤ fd_res + co + dim V_θ` and `fd_skipless + 2 co + dim V_θ ≤ P`
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = q at h1 h2 ⊢
  omega

end Skips
