import SkipsLean.OneBlock.SkiplessRMSZeroReadout
import SkipsLean.OneBlock.UnitsParallel
import SkipsLean.OneBlock.SkiplessHomogeneousRMSZero
import SkipsLean.OneBlock.ResidualRMSZeroRescaleGeneric
import SkipsLean.OneBlock.Factorization
import SkipsLean.OneBlock.ResidualRMSZeroGain

/-!
# One skipless ReLU or ReLU² block of width `d` under pre-RMSNorm with `ε = 0`: the equality

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`, and the skipless
network at most `P − d_model² − d_model (d_model − 1)/2 − 1 − s`, with equality for ReLU and ReLU²
blocks. So the skip raises the functional dimension by at least `d_model²`, and by exactly
`d_model²` for ReLU and ReLU² blocks."

Here "with equality for ReLU and ReLU² blocks" and "by exactly `d_model²`", **for a block of width
exactly `d_model`**. The bound is `OneBlock/SkiplessHomogeneousRMSZero.lean`. The proof of the
equality ("The skipless network: equality") in the steps of the paper:

* the normalization before the block drops out, so the network is `x ↦ N_0(h_1(x)) D` with
  `h_1(x) = σ(x E W_read) W_write` (`eval_skipless_rmsNorm_zero_of_rowHomogeneous`);
* the final normalization (equation (18)): `OneBlock/SkiplessRMSZeroReadout.lean`;
* "The kinks stay" and "One scale": `UnitsParallel` (`OneBlock/UnitsParallel.lean`), which is
  stated for linearly independent columns `c_i` of `E W_read` and rows `a_i` of `W_write`; this
  is where the width `d_model` is used;
* "Counting": Lemma B.2 (`keeps_products_iff_mem_range_cobDir`) gives the change of basis at
  `h_0`.

Blocks wider than `d_model`, for which the paper's proof uses a resultant and two entries of
`h_1` without a common factor at generic parameters: `OneBlock/SkiplessReluWideRMSZero.lean`
(ReLU) and `OneBlock/SkiplessReluSqWideRMSZero.lean` (ReLU²).

The functional dimension: the value of Lean's `funDim`, and a finite batch of the paper's inputs
(no normalized row vanishes, no hidden unit at its kink) with this rank; the two together are the
paper's statement.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-! ### Helpers: `N_0` scales the rows by positive numbers -/

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `N_0` scales every row: `(N_0(h) W)_{t i} = (‖h_t‖²/d)^{-1/2} (h W)_{t i}` (a copy of
the private `rmsNorm_mul_apply_rzr` of `OneBlock/ResidualRMSZeroRescale.lean`). -/
private theorem rmsNorm_mul_apply_she {n : Type*} [Fintype n] (h : Matrix T d ℝ)
    (W : Matrix d n ℝ) (t : T) (i : n) :
    (rmsNorm 0 h * W) t i
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + 0))⁻¹ * (h * W) t i := by
  simp only [Matrix.mul_apply, Finset.mul_sum, rmsNorm, rmsRow, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul, mul_assoc]

omit [DecidableEq d] in
/-- Helper: the factor of `N_0` at a row `v ≠ 0` is positive (a copy of `inv_sqrt_pos_rzr`). -/
private theorem inv_sqrt_pos_she {v : d → ℝ} (hv : v ≠ 0) :
    0 < (Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + 0))⁻¹ := by
  have h1 : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j))
      (fun h => hv (dotProduct_self_eq_zero.1 h.symm))
  obtain ⟨j, -⟩ := Function.ne_iff.1 hv
  have h2 : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩)
  rw [add_zero]
  exact inv_pos.2 (Real.sqrt_pos.2 (div_pos h1 h2))

omit [DecidableEq d] in
/-- Helper: `N_0(s v) = N_0(v)` for `s > 0` (the row version of `rmsNorm_zero_smul_rzo`). -/
private theorem rmsRow_zero_smul_she {s : ℝ} (hs : 0 < s) (v : d → ℝ) :
    rmsRow 0 (s • v) = rmsRow 0 v := by
  unfold rmsRow
  have e : Real.sqrt ((s • v ⬝ᵥ s • v) / (Fintype.card d : ℝ) + 0)
      = s * Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + 0) := by
    have e1 : (s • v ⬝ᵥ s • v) / (Fintype.card d : ℝ) + 0
        = s ^ 2 * ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + 0) := by
      rw [smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul, add_zero]
      ring
    rw [e1, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]
  rw [e, mul_inv, smul_smul, mul_comm s⁻¹, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `N_0` does not see a positive factor of a row. -/
private theorem rmsNorm_zero_rowScale_she {c : T → ℝ} (hc : ∀ t, 0 < c t) (M : Matrix T d ℝ) :
    rmsNorm 0 (Matrix.of fun t j => c t * M t j) = rmsNorm 0 M := by
  funext t
  show rmsRow 0 (c t • M t) = rmsRow 0 (M t)
  exact rmsRow_zero_smul_she (hc t) (M t)

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: for a block that is homogeneous row by row, at an input with no zero row of `x E`, the
output of the block on `N_0(x E)` has the rows of `f(x E W_read) W_write` times numbers `c_t > 0`:
`N_0` scales row `t` of `x E` by `s_t > 0`, and the block scales it by `s_t^k`. -/
private theorem block_rowScale_she {A : Arch T d 1} {k : ℕ} (hf : RowHomogeneous A k)
    (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) (hx : ∀ t, (x * θ.E) t ≠ 0) :
    ∃ c : T → ℝ, (∀ t, 0 < c t) ∧
      A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0
        = Matrix.of fun t j => c t * (A.f 0 (x * θ.E * θ.read 0) * θ.write 0) t j := by
  obtain ⟨s, hs, hN⟩ : ∃ s : T → ℝ, (∀ t, 0 < s t) ∧
      rmsNorm 0 (x * θ.E) * θ.read 0 = Matrix.of fun t i => s t * (x * θ.E * θ.read 0) t i :=
    ⟨fun t => (Real.sqrt (((x * θ.E) t ⬝ᵥ (x * θ.E) t) / (Fintype.card d : ℝ) + 0))⁻¹,
      fun t => inv_sqrt_pos_she (hx t), by ext t i; exact rmsNorm_mul_apply_she _ _ t i⟩
  refine ⟨fun t => s t ^ k, fun t => pow_pos (hs t) k, ?_⟩
  rw [hN, hf 0 s hs]
  ext t j
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, mul_assoc]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- **Proof of Theorem B.1 (iv) of the skips paper, "Its normalization before the block drops
out":** for one skipless block that is positively homogeneous row by row, under pre-RMSNorm with
`ε = 0`, at an input `x` with no zero row of `x E`, the network is `N_0(f(x E W_read) W_write) D`,
without the normalization before the block. -/
theorem eval_skipless_rmsNorm_zero_of_rowHomogeneous {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    {k : ℕ} (hf : RowHomogeneous A k) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (hx : ∀ t, (x * θ.E) t ≠ 0) :
    eval A 0 θ x = rmsNorm 0 (A.f 0 (x * θ.E * θ.read 0) * θ.write 0) * θ.D := by
  -- the block's output on `N_0(x E)` is that on `x E` with its rows scaled by `c_t > 0`
  obtain ⟨c, hc, he⟩ := block_rowScale_she hf θ x hx
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]
  simp only [Pi.zero_apply, Matrix.mul_zero, zero_add]
  -- `N_0` does not see a positive factor of a row
  rw [he, rmsNorm_zero_rowScale_she hc]

variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

section HelpersShe

open Filter
open scoped Topology

/-! ### Helpers: linear algebra -/

/-- Helper: a matrix whose rank is its number of columns has an injective `mulVec` (rank–nullity,
as in `cancel_left_of_rank_shz`). -/
private theorem mulVec_injective_she {m n : Type*} [Fintype n] (M : Matrix m n ℝ)
    (hM : M.rank = Fintype.card n) : Function.Injective M.mulVec := by
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [Matrix.rank] at hM
    omega
  exact hinj

/-- Helper: a matrix of rank equal to its number of columns cancels on the left. -/
private theorem cancel_left_she {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
    (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ} (h : M * X = M * Y) : X = Y := by
  ext i j
  have hcol : M *ᵥ (fun l => X l j) = M *ᵥ (fun l => Y l j) := by
    funext p
    have := congrFun (congrFun h p) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  exact congrFun (mulVec_injective_she M hM hcol) i

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] in
/-- Helper: row `t` of `of F * W` is `∑_i F_{t i} W_i`. -/
private theorem row_of_mul_she {q : Type*} [Fintype q] (F : T → q → ℝ) (W : Matrix q d ℝ)
    (t : T) : (Matrix.of F * W) t = ∑ i, F t i • W i := by
  funext j
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

omit [DecidableEq d] in
/-- Helper: the row identity of the step "the kinks stay": if `g = ∑ s_i a_i`,
`k = ∑ s'_i ψ_i a_i + ∑ s_i ψa_i` and `k = g Y + μ g`, then
`∑ [s_i (ψa_i − a_i Y) + s'_i ψ_i a_i] = μ g`. -/
private theorem row_identity_she {q : Type*} [Fintype q] (s s' ψ : q → ℝ) (W ηW : Matrix q d ℝ)
    (Y : Matrix d d ℝ) (g kk : d → ℝ) (μ : ℝ) (hg : g = ∑ i, s i • W i)
    (hk : kk = ∑ i, (s' i * ψ i) • W i + ∑ i, s i • ηW i) (h : kk = g ᵥ* Y + μ • g) :
    ∑ i, (s i • (ηW i - (W * Y) i) + (s' i * ψ i) • W i) = μ • ∑ i, s i • W i := by
  have hgY : g ᵥ* Y = ∑ i, s i • (W * Y) i := by
    rw [hg, Matrix.sum_vecMul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_vecMul]
    rfl
  have e1 : ∑ i, (s i • (ηW i - (W * Y) i) + (s' i * ψ i) • W i)
      = (∑ i, s i • ηW i - g ᵥ* Y) + ∑ i, (s' i * ψ i) • W i := by
    rw [hgY, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_sub]
  have e2 : μ • g = kk - g ᵥ* Y := by
    rw [h]
    abel
  rw [e1, ← hg, e2, hk]
  abel

/-! ### Helpers: derivatives along a line (copies of the `_rzo` helpers) -/

/-- Helper: the product rule for matrices depending on one real variable. -/
private theorem hasDerivAt_mul_she {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
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

/-- Helper: `τ ↦ M + τ N` has the derivative `N` at `0`. -/
private theorem hasDerivAt_affine_she {m n : Type*} [Fintype m] [Fintype n]
    (M N : Matrix m n ℝ) : HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

/-! ### Helpers: differentiability (copies of the `_rzr` helpers) -/

/-- Helper: the product of two matrix-valued maps differentiable at `y` is differentiable at `y`. -/
private theorem differentiableAt_matMul_she {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] {f : E → Matrix m n ℝ}
    {g : E → Matrix n p ℝ} {y : E} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) : DifferentiableAt ℝ (fun y => f y * g y) y := by
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

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: a linear map of the parameters is differentiable. -/
private theorem differentiable_lin_she {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut →ₗ[ℝ] F) :
    Differentiable ℝ l := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).differentiable

/-- Helper: `M ↦ σ(M)` (entrywise) is differentiable at a matrix with no zero entry. -/
private theorem differentiableAt_map_she (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    {m n : Type*} [Fintype m] [Fintype n] {P : Matrix m n ℝ} (hP : ∀ t i, P t i ≠ 0) :
    DifferentiableAt ℝ (fun M : Matrix m n ℝ => M.map σ) P := by
  refine differentiableAt_pi.2 fun t => differentiableAt_pi.2 fun i => ?_
  have hent : Differentiable ℝ (fun M : Matrix m n ℝ => M t i) :=
    differentiable_pi.1 (differentiable_pi.1 differentiable_id t) i
  have h := (hσ _ (hP t i)).differentiableAt.comp P (hent P)
  exact h

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the function of one skipless block under pre-RMSNorm with `ε = 0`,
`F_θ(x) = N_0(σ(N_0(x E) W_read) W_write) D`. -/
private theorem eval_eq_she
    (θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ) :
    eval (Arch.mlp σ (rmsNorm 0) hid) 0 θ' x
      = rmsNorm 0 ((rmsNorm 0 (x * θ'.E) * θ'.read 0).map σ * θ'.write 0) * θ'.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero]
  simp only [Pi.zero_apply, Matrix.mul_zero, zero_add]

omit [Nonempty T] [DecidableEq d] in
/-- Helper: at an input of `skiplessZeroDomain ∩ noKinkRMS θ` the output is differentiable in the
parameters: no row of `x E` and of `h_1` vanishes, so `N_0` is differentiable at both, and the
pre-activations `N_0(x E) W_read` have no zero entry. -/
private theorem differentiableAt_eval_she (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ skiplessZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ) :
    DifferentiableAt ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        eval (Arch.mlp σ (rmsNorm 0) hid) 0 θ' x) θ := by
  obtain ⟨⟨hx0, hx1⟩, hxk⟩ := hx
  have e : (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
      eval (Arch.mlp σ (rmsNorm 0) hid) 0 θ' x) = fun θ' =>
        rmsNorm 0 ((rmsNorm 0 (x * θ'.E) * θ'.read 0).map σ * θ'.write 0) * θ'.D :=
    funext fun θ' => eval_eq_she θ' x
  rw [e]
  -- the components of the parameters are linear, hence differentiable
  have hE : Differentiable ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut => θ'.E) := by
    have h := differentiable_lin_she (Params.linE
      (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) (dIn := dIn) (dOut := dOut))
    exact h
  have hR : Differentiable ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut => θ'.read 0) := by
    have h := differentiable_lin_she (Params.linRead
      (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) (dIn := dIn) (dOut := dOut) 0)
    exact h
  have hW : Differentiable ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        θ'.write 0) := by
    have h := differentiable_lin_she (Params.linWrite
      (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) (dIn := dIn) (dOut := dOut) 0)
    exact h
  have hD : Differentiable ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut => θ'.D) := by
    have h := differentiable_lin_she (Params.linD
      (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) (dIn := dIn) (dOut := dOut))
    exact h
  -- `x E`, `N_0(x E)` and the pre-activations `N_0(x E) W_read`
  have hxE : DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut => x * θ'.E) θ :=
    differentiableAt_matMul_she (differentiableAt_const x) (hE θ)
  have hN0 : DifferentiableAt ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) :=
    (analyticAt_rmsNorm_zero _ hx0).differentiableAt
  have hn : DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        rmsNorm 0 (x * θ'.E)) θ :=
    DifferentiableAt.comp (f := fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid)
      dIn dOut => x * θ'.E) θ hN0 hxE
  have hpre : DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        rmsNorm 0 (x * θ'.E) * θ'.read 0) θ :=
    differentiableAt_matMul_she hn (hR θ)
  -- at `θ` they have no zero entry, so `σ` is differentiable there
  have hP : ∀ t i, (rmsNorm 0 (x * θ.E) * θ.read 0) t i ≠ 0 := by
    intro t i
    rw [rmsNorm_mul_apply_she]
    exact mul_ne_zero (inv_sqrt_pos_she (hx0 t)).ne' (hxk t i)
  have hact : DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        (rmsNorm 0 (x * θ'.E) * θ'.read 0).map σ) θ := by
    have h := (differentiableAt_map_she hσ hP).comp θ hpre
    exact h
  -- `h_1 = σ(N_0(x E) W_read) W_write`, no row of which vanishes, and the output `N_0(h_1) D`
  have hh : DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        (rmsNorm 0 (x * θ'.E) * θ'.read 0).map σ * θ'.write 0) θ :=
    differentiableAt_matMul_she hact (hW θ)
  have hN1 : DifferentiableAt ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ)
      ((rmsNorm 0 (x * θ.E) * θ.read 0).map σ * θ.write 0) :=
    (analyticAt_rmsNorm_zero _ hx1).differentiableAt
  have hout : DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        rmsNorm 0 ((rmsNorm 0 (x * θ'.E) * θ'.read 0).map σ * θ'.write 0)) θ :=
    DifferentiableAt.comp (f := fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid)
      dIn dOut => (rmsNorm 0 (x * θ'.E) * θ'.read 0).map σ * θ'.write 0) θ hN1 hh
  exact differentiableAt_matMul_she hout (hD θ)

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: a direction that is flat at the inputs of `U` has derivative `0` at an input of `U`. -/
private theorem fderiv_eq_zero_of_flatOn_she {A : Arch T d 1} {θ η : Params A dIn dOut}
    {U : Set (Matrix T dIn ℝ)} (hη : η ∈ flatOn A 0 θ U) {x : Matrix T dIn ℝ} (hx : x ∈ U) :
    fderiv ℝ (fun θ' : Params A dIn dOut => eval A 0 θ' x) θ η = 0 :=
  LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hη x) hx)

/-! ### Helpers: the block without the normalization before it, and its derivative -/

/-- Helper: the block without the normalization before it, `g_θ(x) = σ(x E W_read) W_write`. -/
private noncomputable def gS_she
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ) :
    Matrix T d ℝ :=
  (x * θ.E * θ.read 0).map σ * θ.write 0

/-- Helper: the derivative of `θ ↦ g_θ(x)` along `η`, with `dσ` the derivative of `σ`:
`(dσ(x E W_read) ⊙ x (η_E W_read + E η_read)) W_write + σ(x E W_read) η_write`. -/
private noncomputable def kS_she (dσ : ℝ → ℝ)
    (θ η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T d ℝ :=
  (Matrix.of fun t i => dσ ((x * θ.E * θ.read 0) t i)
      * (x * η.E * θ.read 0 + x * θ.E * η.read 0) t i) * θ.write 0
    + (x * θ.E * θ.read 0).map σ * η.write 0

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: row `t` of `g_θ(x)` is `∑_i σ((x E W_read)_{t i}) a_i`. -/
private theorem gS_row_she (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) :
    gS_she θ x t = ∑ i, σ ((x * θ.E * θ.read 0) t i) • θ.write 0 i := by
  funext j
  simp only [gS_she, Matrix.mul_apply, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: row `t` of `k(x)`. -/
private theorem kS_row_she (dσ : ℝ → ℝ)
    (θ η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) :
    kS_she dσ θ η x t = ∑ i, (dσ ((x * θ.E * θ.read 0) t i)
        * (x * η.E * θ.read 0 + x * θ.E * η.read 0) t i) • θ.write 0 i
      + ∑ i, σ ((x * θ.E * θ.read 0) t i) • η.write 0 i := by
  funext j
  simp only [kS_she, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: at an input with no zero row of `x E`, no row of `g_θ(x)` vanishes if no row of the
block's output on `N_0(x E)` does (they differ by positive factors). -/
private theorem gS_ne_zero_she {k : ℕ}
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) {x : Matrix T dIn ℝ}
    (hx : x ∈ skiplessZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ) (t : T) :
    gS_she θ x t ≠ 0 := by
  obtain ⟨c, hc, he⟩ := block_rowScale_she (rowHomogeneous_mlp hhom (rmsNorm 0) hid) θ x hx.1
  intro h0
  apply hx.2 t
  funext j
  have e2 : gS_she θ x t j = 0 := by rw [h0]; rfl
  rw [he]
  show c t * gS_she θ x t j = 0
  rw [e2, mul_zero]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: an input with no hidden unit at its kink and no zero row of `g_θ(x)` lies in
`skiplessZeroDomain ∩ noKinkRMS θ`. -/
private theorem mem_U_she {k : ℕ} (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) [Nonempty (hid 0)]
    {x : Matrix T dIn ℝ} (h1 : ∀ t i, (x * θ.E * θ.read 0) t i ≠ 0)
    (h2 : ∀ t, gS_she θ x t ≠ 0) :
    x ∈ skiplessZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ := by
  -- no row of `x E` vanishes, since the rows of `x E W_read` do not
  have hx : ∀ t, (x * θ.E) t ≠ 0 := by
    intro t h
    obtain ⟨i⟩ := ‹Nonempty (hid 0)›
    apply h1 t i
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun a _ => by rw [show (x * θ.E) t a = 0 from congrFun h a, zero_mul]
  -- the block's output on `N_0(x E)` has the rows of `g_θ(x)` times positive numbers
  obtain ⟨c, hc, he⟩ := block_rowScale_she (rowHomogeneous_mlp hhom (rmsNorm 0) hid) θ x hx
  refine ⟨⟨hx, fun t h => h2 t ?_⟩, h1⟩
  funext j
  have e := congrFun (congrFun he t) j
  rw [congrFun h j] at e
  have e2 : c t * gS_she θ x t j = 0 := e.symm
  exact (mul_eq_zero.1 e2).resolve_left (hc t).ne'

omit [Fintype T] [Fintype dOut] in
/-- Helper (the open set of values): for `k ≠ 0`, `σ(1) ≠ 0`, `E`, `W_read` and `W_write` of rank
`d` and `d` hidden units, the rows of `g_θ(x)`, for inputs `x` of `U`, fill a nonempty open set:
for a row `x` with all `x c_i > 0`, `g = σ(1) ((x c_i)^k)_i W_write`. -/
private theorem exists_open_she {k : ℕ}
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (hk : k ≠ 0) (hσ1 : σ 1 ≠ 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) [Nonempty (hid 0)]
    (hcard : Fintype.card (hid 0) = Fintype.card d) (hE : θ.E.rank = Fintype.card d)
    (hR : (θ.read 0).rank = Fintype.card d) (hW : (θ.write 0).rank = Fintype.card d) :
    ∃ O : Set (d → ℝ), IsOpen O ∧ O.Nonempty ∧ ∀ v ∈ O, ∃ x : Matrix T dIn ℝ,
      x ∈ skiplessZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ ∧
        ∃ t, gS_she θ x t = v := by
  classical
  -- `x ↦ x E W_read` is onto
  have hsurj : ∀ u : hid 0 → ℝ, ∃ x : dIn → ℝ, x ᵥ* (θ.E * θ.read 0) = u := by
    intro u
    obtain ⟨z, hz⟩ := Matrix.vecMul_surjective_iff_rank_eq_card.mpr (hR.trans hcard.symm) u
    obtain ⟨x, hx⟩ := Matrix.vecMul_surjective_iff_rank_eq_card.mpr hE z
    exact ⟨x, by
      rw [← Matrix.vecMul_vecMul]
      exact (congrArg (fun w => w ᵥ* θ.read 0) hx).trans hz⟩
  -- the square write is invertible: `B W_write = 1` and `W_write B = 1`
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hW)
  have hB' : θ.write 0 * B = 1 := (Matrix.mul_eq_one_comm_of_card_eq d (hid 0) ℝ hcard.symm).mp hB
  refine ⟨{v | ∀ i, 0 < (σ 1)⁻¹ * (v ᵥ* B) i}, ?_, ?_, ?_⟩
  · -- the set is open
    refine isOpen_iff_mem_nhds.2 fun v hv => Filter.eventually_all.2 fun i => ?_
    have hc : Continuous fun w : d → ℝ => (σ 1)⁻¹ * (w ⬝ᵥ fun j => B j i) :=
      continuous_const.mul (continuous_id.dotProduct continuous_const)
    exact continuousAt_const.eventually_lt hc.continuousAt (hv i)
  · -- and not empty: it contains `(σ(1), …, σ(1)) W_write`
    refine ⟨(fun _ : hid 0 => σ 1) ᵥ* θ.write 0, fun i => ?_⟩
    rw [Matrix.vecMul_vecMul, hB', Matrix.vecMul_one]
    show 0 < (σ 1)⁻¹ * σ 1
    rw [inv_mul_cancel₀ hσ1]
    exact one_pos
  · intro v hv
    -- `u_i = (w_i / σ(1))^{1/k} > 0` with `w = v B`, so that `σ(u_i) = u_i^k σ(1) = w_i`
    obtain ⟨u, hu, huk⟩ : ∃ u : hid 0 → ℝ, (∀ i, 0 < u i) ∧ ∀ i, σ (u i) = (v ᵥ* B) i := by
      refine ⟨fun i => ((σ 1)⁻¹ * (v ᵥ* B) i) ^ ((k : ℝ)⁻¹),
        fun i => Real.rpow_pos_of_pos (hv i) _, fun i => ?_⟩
      have h1 := hhom (((σ 1)⁻¹ * (v ᵥ* B) i) ^ ((k : ℝ)⁻¹)) 1 (Real.rpow_pos_of_pos (hv i) _)
      rw [mul_one] at h1
      rw [h1, Real.rpow_inv_natCast_pow (hv i).le hk, mul_comm ((σ 1)⁻¹),
        inv_mul_cancel_right₀ hσ1]
    -- an input whose rows `x` have `x E W_read = u`
    obtain ⟨x, hx⟩ := hsurj u
    have hXP : ∀ t i, ((Matrix.of fun _ : T => x) * θ.E * θ.read 0) t i = u i := fun t i => by
      rw [Matrix.mul_assoc]
      exact congrFun hx i
    have hrow : ∀ t, gS_she θ (Matrix.of fun _ : T => x) t = v := by
      intro t
      rw [gS_row_she]
      simp only [hXP, huk]
      rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, hB, Matrix.vecMul_one]
    have hv0 : v ≠ 0 := by
      rintro rfl
      obtain ⟨i⟩ := ‹Nonempty (hid 0)›
      have := hv i
      simp only [Matrix.zero_vecMul, Pi.zero_apply, mul_zero, lt_self_iff_false] at this
    refine ⟨Matrix.of fun _ : T => x, mem_U_she hhom θ (fun t i => ?_) (fun t => ?_),
      Classical.arbitrary T, hrow _⟩
    · rw [hXP]
      exact (hu i).ne'
    · rw [hrow]
      exact hv0

omit [Nonempty T] [DecidableEq d] in
/-- Helper (the derivative at an input of `U`): `𝐃N_0(g(x))[k(x)] D + N_0(g(x)) η_D = 0` for a
direction `η` with derivative `0` at `x`. Near `θ` the output is `N_0(g_θ(x)) D` by
`eval_skipless_rmsNorm_zero_of_rowHomogeneous`. -/
private theorem flat_eq_she {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (x : Matrix T dIn ℝ)
    (hx : x ∈ skiplessZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ)
    (h0 : fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
      eval (Arch.mlp σ (rmsNorm 0) hid) 0 θ' x) θ η = 0) :
    fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (gS_she θ x) (kS_she σ' θ η x) * θ.D
      + rmsNorm 0 (gS_she θ x) * η.D = 0 := by
  -- along the line `θ + τ η` the output has the derivative `0` at `τ = 0`
  have h1 := hasDerivAt_eval_line (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) 0 θ η x
    (differentiableAt_eval_she hσ θ x hx)
  rw [h0] at h1
  -- near `τ = 0` no row of `x E(τ)` vanishes, so the output is `N_0(g_{θ + τ η}(x)) D(τ)`
  have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ t, (x * (θ + τ • η).E) t ≠ 0 := by
    refine Filter.eventually_all.2 fun t => ?_
    have hc : Continuous fun τ : ℝ => (x * θ.E) t + τ • (x * η.E) t := by fun_prop
    have h00 : (x * θ.E) t + (0 : ℝ) • (x * η.E) t ≠ 0 := by
      rw [zero_smul, add_zero]
      exact hx.1.1 t
    filter_upwards [hc.continuousAt.eventually_ne h00] with τ hτ
    have e : (x * (θ + τ • η).E) t = (x * θ.E) t + τ • (x * η.E) t := by
      rw [Params.add_E, Params.smul_E, Matrix.mul_add, Matrix.mul_smul]
      rfl
    rw [e]
    exact hτ
  have heq : (fun τ : ℝ => rmsNorm 0 (gS_she (θ + τ • η) x) * (θ.D + τ • η.D)) =ᶠ[𝓝 0]
      fun τ => eval (Arch.mlp σ (rmsNorm 0) hid) 0 (θ + τ • η) x := by
    filter_upwards [hev] with τ hτ
    exact (eval_skipless_rmsNorm_zero_of_rowHomogeneous rfl
      (rowHomogeneous_mlp hhom (rmsNorm 0) hid) (θ + τ • η) x hτ).symm
  have h2 := h1.congr_of_eventuallyEq heq
  -- the same derivative by the chain rule: `x E(τ) W_read(τ)`, then `σ`, then `W_write(τ)`
  have hE : HasDerivAt (fun τ : ℝ => x * (θ + τ • η).E) (x * η.E) 0 := by
    have h := hasDerivAt_mul_she (hasDerivAt_const (0 : ℝ) x) (hasDerivAt_affine_she θ.E η.E)
      (P0 := x) (Q0 := θ.E) rfl (by simp)
    rw [Matrix.zero_mul, zero_add] at h
    exact h
  have hP := hasDerivAt_mul_she hE (hasDerivAt_affine_she (θ.read 0) (η.read 0))
    (P0 := x * θ.E) (Q0 := θ.read 0) (by simp) (by simp)
  have hM : HasDerivAt (fun τ : ℝ => (x * (θ + τ • η).E * (θ + τ • η).read 0).map σ)
      (Matrix.of fun t i => σ' ((x * θ.E * θ.read 0) t i)
        * (x * η.E * θ.read 0 + x * θ.E * η.read 0) t i) 0 := by
    refine hasDerivAt_pi.2 fun t => hasDerivAt_pi.2 fun i => ?_
    have hent := hasDerivAt_pi.1 (hasDerivAt_pi.1 hP t) i
    have h := (hσ _ (hx.2 t i)).comp_of_eq (0 : ℝ) hent (by simp)
    exact h
  have hG0 := hasDerivAt_mul_she hM (hasDerivAt_affine_she (θ.write 0) (η.write 0))
    (P0 := (x * θ.E * θ.read 0).map σ) (Q0 := θ.write 0) (by simp) (by simp)
  have hG : HasDerivAt (fun τ : ℝ => gS_she (θ + τ • η) x) (kS_she σ' θ η x) 0 := hG0
  -- then `N_0`, at `g_θ(x)`, which has no zero row, and `D(τ)`
  have hN := (analyticAt_rmsNorm_zero _ (gS_ne_zero_she hhom θ hx.1)).differentiableAt
    |>.hasFDerivAt.comp_hasDerivAt_of_eq 0 hG (by simp [gS_she])
  have h3 := hasDerivAt_mul_she hN (hasDerivAt_affine_she θ.D η.D)
    (P0 := rmsNorm 0 (gS_she θ x)) (Q0 := θ.D) (by simp [gS_she]) (by simp)
  exact h3.unique h2

end HelpersShe

/-- **Proof of Theorem B.1 (iv) of the skips paper, "The skipless network: equality", for MLP
blocks of width `d` with a positively homogeneous activation:** let `ε = 0`, `d ≥ 2`, let `σ` be
differentiable off `0`, positively homogeneous of degree `k ≥ 1` with `σ(1) ≠ 0`, with the steps
"The kinks stay" and "One scale" in the form `UnitsParallel`; let the block have exactly `d`
hidden units and let `E`, `D`, `W_read`, `W_write` have rank `d`. Then a direction that is flat
at every input at which no normalized row vanishes and no hidden unit sits at its kink is the
direction of a change of basis `I + τ X` at `h_0`, of a rotation and a scaling at `h_1`, plus a
rescaling of the hidden units. -/
theorem flatOn_le_mlp_rescale_skipless_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (hk : k ≠ 0) (hσ1 : σ 1 ≠ 0)
    (hP : UnitsParallel σ σ' k dIn d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hd : 2 ≤ Fintype.card d) (hcard : Fintype.card (hid 0) = Fintype.card d)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hR : (θ.read 0).rank = Fintype.card d) (hW : (θ.write 0).rank = Fintype.card d)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.mlp σ (rmsNorm 0) hid) 0 θ
      (skiplessZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ)) :
    ∃ (X Y : Matrix d d ℝ) (c : ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
      η = cobDir θ ![X, Y] + c • scaleDir θ ![0, 1] + rescaleDirMlp k θ α := by
  have : Nonempty (hid 0) := Fintype.card_pos_iff.1 (by omega)
  -- the final normalization (equation (18)): the rows of `g(x)`, `x ∈ U`, fill an open set, so
  -- `η_D = -Y D` with `Y` antisymmetric and `k(x)_t = g(x)_t Y + μ g(x)_t`
  obtain ⟨O, hOo, hOn, hOv⟩ := exists_open_she hhom hk hσ1 θ hcard hE hR hW
  obtain ⟨Y, hYa, hDY, hrow⟩ := exists_antisymm_of_fderiv_rmsNorm_zero_mul
    (fun p : {x // x ∈ skiplessZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ} =>
      gS_she θ p.1) (fun p => kS_she σ' θ η p.1) θ.D η.D hD
    (fun p t => gS_ne_zero_she hhom θ p.2.1 t)
    ⟨O, hOo, hOn, fun v hv => by
      obtain ⟨x, hx, t, hxt⟩ := hOv v hv
      exact ⟨⟨x, hx⟩, t, hxt⟩⟩
    (fun p => flat_eq_she hσ hhom θ η p.1 p.2 (fderiv_eq_zero_of_flatOn_she hη p.2))
  -- the columns `c_i` of `E W_read` and the rows `a_i` of `W_write` are linearly independent
  have hlinC : LinearIndependent ℝ (fun i => (θ.E * θ.read 0)ᵀ i) := by
    have h : Function.Injective (θ.E * θ.read 0).mulVec := by
      intro u v huv
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at huv
      exact mulVec_injective_she _ (hR.trans hcard.symm) (mulVec_injective_she _ hE huv)
    exact Matrix.mulVec_injective_iff.mp h
  have hlinW : LinearIndependent ℝ (fun i => θ.write 0 i) := by
    have h : Function.Injective (θ.write 0).vecMul := by
      intro u v huv
      have h' : (θ.write 0)ᵀ *ᵥ u = (θ.write 0)ᵀ *ᵥ v := by
        rw [Matrix.mulVec_transpose, Matrix.mulVec_transpose]
        exact huv
      exact mulVec_injective_she _ (by rw [Matrix.rank_transpose, hW, hcard]) h'
    exact Matrix.vecMul_injective_iff.mp h
  -- equation (18) at the inputs with all rows `x`: `J(x) = μ h_1(x)` with `β_i = ψa_i − a_i Y`
  have hpar : ∀ x : dIn → ℝ, (∀ i, x ⬝ᵥ (θ.E * θ.read 0)ᵀ i ≠ 0) →
      ∑ i, σ (x ⬝ᵥ (θ.E * θ.read 0)ᵀ i) • θ.write 0 i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (σ (x ⬝ᵥ (θ.E * θ.read 0)ᵀ i) • (η.write 0 i - (θ.write 0 * Y) i)
        + (σ' (x ⬝ᵥ (θ.E * θ.read 0)ᵀ i) * (x ⬝ᵥ (η.E * θ.read 0 + θ.E * η.read 0)ᵀ i))
          • θ.write 0 i) = μ • ∑ i, σ (x ⬝ᵥ (θ.E * θ.read 0)ᵀ i) • θ.write 0 i := by
    intro x hx hne
    have hP' : ∀ t i, ((Matrix.of fun _ : T => x) * θ.E * θ.read 0) t i
        = x ⬝ᵥ (θ.E * θ.read 0)ᵀ i := fun t i => by
      rw [Matrix.mul_assoc]
      rfl
    have hQ' : ∀ t i, ((Matrix.of fun _ : T => x) * η.E * θ.read 0
        + (Matrix.of fun _ : T => x) * θ.E * η.read 0) t i
          = x ⬝ᵥ (η.E * θ.read 0 + θ.E * η.read 0)ᵀ i := fun t i => by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add]
      rfl
    have hg : ∀ t, gS_she θ (Matrix.of fun _ : T => x) t
        = ∑ i, σ (x ⬝ᵥ (θ.E * θ.read 0)ᵀ i) • θ.write 0 i := fun t => by
      rw [gS_row_she]
      simp only [hP']
    have hk' : ∀ t, kS_she σ' θ η (Matrix.of fun _ : T => x) t
        = ∑ i, (σ' (x ⬝ᵥ (θ.E * θ.read 0)ᵀ i) * (x ⬝ᵥ (η.E * θ.read 0 + θ.E * η.read 0)ᵀ i))
          • θ.write 0 i + ∑ i, σ (x ⬝ᵥ (θ.E * θ.read 0)ᵀ i) • η.write 0 i := fun t => by
      rw [kS_row_she]
      simp only [hP', hQ']
    have hXU := mem_U_she (x := Matrix.of fun _ : T => x) hhom θ
      (fun t i => by rw [hP']; exact hx i) (fun t => by rw [hg]; exact hne)
    exact ⟨_, row_identity_she _ _ _ (θ.write 0) (η.write 0) Y _ _ _
      (hg (Classical.arbitrary T)) (hk' (Classical.arbitrary T))
      (hrow ⟨_, hXU⟩ (Classical.arbitrary T))⟩
  -- the kinks stay and one scale: `ψc_i = λ_i c_i` and `ψa_i − a_i Y = (c₀ − k λ_i) a_i`
  obtain ⟨c₀, lam, hlam⟩ := hP (fun i => (θ.E * θ.read 0)ᵀ i) (fun i => θ.write 0 i)
    (fun i => (η.E * θ.read 0 + θ.E * η.read 0)ᵀ i) (fun i => η.write 0 i - (θ.write 0 * Y) i)
    hlinC hlinW (by omega) hpar
  -- counting: the rescaling with these `λ_i`
  obtain ⟨α, hα⟩ : ∃ α : ∀ ℓ : Fin 1, hid ℓ → ℝ, α 0 = lam :=
    ⟨fun ℓ => Fin.cases lam (fun l => l.elim0) ℓ, rfl⟩
  -- the rest `η''` keeps `E W_read` and `W_write D` to first order
  obtain ⟨η'', hη''⟩ : ∃ η'' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut,
      η'' = η - (c₀ • scaleDir θ ![0, 1] + rescaleDirMlp k θ α) := ⟨_, rfl⟩
  have hW2 : η''.write 0 = θ.write 0 * Y := by
    rw [hη'']
    show η.write 0 - (c₀ • ((1 : ℝ) • θ.write 0)
      + Matrix.of fun i a => -((k : ℝ) * α 0 i) * θ.write 0 i a) = θ.write 0 * Y
    ext i a
    have h1 := congrFun (hlam i).2 a
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
      smul_eq_mul, one_mul, hα]
    linear_combination h1
  have hD2 : η''.D = -(Y * θ.D) := by
    rw [hη'']
    show η.D - (c₀ • (0 : Matrix d dOut ℝ) + 0) = -(Y * θ.D)
    rw [smul_zero, add_zero, sub_zero, hDY]
  have hc1 : η''.E * θ.read 0 + θ.E * η''.read 0 = 0 := by
    rw [hη'']
    show (η.E - (c₀ • ((0 : ℝ) • θ.E) + 0)) * θ.read 0 + θ.E * (η.read 0
      - (c₀ • (0 : Matrix d (hid 0) ℝ) + Matrix.of fun a i => α 0 i * θ.read 0 a i)) = 0
    simp only [zero_smul, smul_zero, add_zero, sub_zero, zero_add, Matrix.mul_sub]
    ext a i
    have h1 := congrFun (hlam i).1 a
    simp only [Matrix.transpose_apply, Matrix.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    have h2 : (θ.E * Matrix.of fun a i => α 0 i * θ.read 0 a i) a i
        = α 0 i * (θ.E * θ.read 0) a i := by
      simp only [Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Matrix.add_apply, Matrix.sub_apply, h2, hα, Matrix.zero_apply]
    linear_combination h1
  have hc2 : η''.write 0 * θ.D + θ.write 0 * η''.D = 0 := by
    rw [hW2, hD2, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel]
  -- Lemma B.2: `η''` is the direction of a change of basis `X''`, with `X''_1 = Y`
  obtain ⟨X'', hX''⟩ := (keeps_products_iff_mem_range_cobDir θ η'' hE hD hR hW).1 ⟨hc1, hc2⟩
  have hX1 : X'' 1 = Y := by
    apply cancel_left_she (θ.write 0) hW
    rw [← hW2, hX'']
    rfl
  have hXeq : X'' = ![X'' 0, Y] := by
    funext i
    fin_cases i
    · rfl
    · exact hX1
  refine ⟨X'' 0, Y, c₀, α, hYa, ?_⟩
  rw [← hXeq, ← hX'', add_assoc, hη'', sub_add_cancel]

/-! ### Helpers: the directions of the symmetries, as a linear map -/

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: a matrix and an antisymmetric matrix `(X, Y)`, as the family `![X, Y]` (a copy of
`pairLin_shz`). -/
private noncomputable def pairLin_she :
    (Matrix d d ℝ × antisymmetric d) →ₗ[ℝ] (Fin (1 + 1) → Matrix d d ℝ) where
  toFun p := ![p.1, (p.2 : Matrix d d ℝ)]
  map_add' p q := by
    funext i
    fin_cases i <;> rfl
  map_smul' c p := by
    funext i
    fin_cases i <;> rfl

/-- Helper: `α ↦ rescaleDirMlp k θ α` is linear (a copy of `rescaleDirMlpLin_shz`). -/
private noncomputable def rescaleDirMlpLin_she (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut where
  toFun := rescaleDirMlp k θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDirMlp]
    · intro ℓ
      ext a i
      simp only [rescaleDirMlp, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply]
      ring
    · intro ℓ
      ext i a
      simp only [rescaleDirMlp, Pi.add_apply, Params.add_write, Matrix.add_apply, Matrix.of_apply]
      ring
    · simp [rescaleDirMlp]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDirMlp]
    · intro ℓ
      ext a i
      simp only [rescaleDirMlp, Pi.smul_apply, Params.smul_read, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · intro ℓ
      ext i a
      simp only [rescaleDirMlp, Pi.smul_apply, Params.smul_write, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [rescaleDirMlp]

/-- Helper: `(((X, Y), c), α) ↦ cobDir θ ![X, Y] + c scaleDir θ ![0, 1] + rescaleDirMlp k θ α`
with `Y` antisymmetric (the map of the proof of
`funDim_add_le_skipless_mlp_homogeneous_rmsNorm_zero`). -/
private noncomputable def dirLin_she (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    ((Matrix d d ℝ × antisymmetric d) × ℝ) × (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ]
      Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut :=
  (((cobDirLin θ).comp pairLin_she).coprod
    (LinearMap.toSpanSingleton ℝ _ (scaleDir θ ![0, 1]))).coprod (rescaleDirMlpLin_she k θ)

omit [Fintype T] [Nonempty T] [Fintype dIn] [Fintype dOut] in
/-- Helper: these directions span a space of dimension at most `d² + (d(d−1)/2 + 1) + s`. -/
private theorem finrank_range_dirLin_le_she (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    Module.finrank ℝ (LinearMap.range (dirLin_she k θ))
      ≤ Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        + Fintype.card (hid 0) := by
  refine (LinearMap.finrank_range_le _).trans (le_of_eq ?_)
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, Module.finrank_matrix,
    finrank_antisymmetric, Module.finrank_self, Module.finrank_pi_fintype, Fin.sum_univ_one]
  simp only [Module.finrank_fintype_fun_eq_card]
  ring

/-- Helper: the directions that are flat at every input of `skiplessZeroDomain ∩ noKinkRMS θ` are
among them. -/
private theorem flatOn_le_range_she {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (hk : k ≠ 0) (hσ1 : σ 1 ≠ 0)
    (hP : UnitsParallel σ σ' k dIn d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hd : 2 ≤ Fintype.card d) (hcard : Fintype.card (hid 0) = Fintype.card d)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hR : (θ.read 0).rank = Fintype.card d) (hW : (θ.write 0).rank = Fintype.card d) :
    flatOn (Arch.mlp σ (rmsNorm 0) hid) 0 θ
        (skiplessZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ)
      ≤ LinearMap.range (dirLin_she k θ) := by
  intro η hη
  obtain ⟨X, Y, c, α, hY, rfl⟩ := flatOn_le_mlp_rescale_skipless_rmsNorm_zero hσ hhom hk hσ1 hP θ
    hd hcard hE hD hR hW η hη
  exact ⟨(((X, ⟨Y, hY⟩), c), α), rfl⟩

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, "with equality", for MLP blocks
of width `d` with a positively homogeneous activation, at one parameter:** under the conditions of
`flatOn_le_mlp_rescale_skipless_rmsNorm_zero`, `funDim = P − d² − (d(d−1)/2 + 1) − s`, with `s`
the number of hidden units. -/
theorem funDim_mlp_oneBlock_rescale_skipless_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (hk : k ≠ 0) (hσ1 : σ 1 ≠ 0)
    (hP : UnitsParallel σ σ' k dIn d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hd : 2 ≤ Fintype.card d) (hcard : Fintype.card (hid 0) = Fintype.card d)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hR : (θ.read 0).rank = Fintype.card d) (hW : (θ.write 0).rank = Fintype.card d) :
    funDim (Arch.mlp σ (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- `≤`: the changes of basis `GL(d)` at `h_0`, `CO(d)` at `h_1` and the rescalings (no read
  -- column is zero: `W_read` has rank `d` and `d` columns)
  have hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0 := by
    intro ℓ i
    obtain rfl := Subsingleton.elim ℓ 0
    exact (Matrix.mulVec_injective_iff.mp
      (mulVec_injective_she (θ.read 0) (hR.trans hcard.symm))).ne_zero i
  have hle := funDim_add_le_skipless_mlp_homogeneous_rmsNorm_zero hhom θ hE
    (fun ℓ => by obtain rfl := Subsingleton.elim ℓ 0; exact hW) hc
  -- `≥`: `K(θ) ≤ K_U(θ)`, which lies in the range of these directions
  have hflat : flat (Arch.mlp σ (rmsNorm 0) hid) 0 θ ≤ LinearMap.range (dirLin_she k θ) :=
    (flat_le_flatOn θ _).trans (flatOn_le_range_she hσ hhom hk hσ1 hP θ hd hcard hE hD hR hW)
  have h := funDim_add_finrank_flat' (S := 0) θ
  have hmono := Submodule.finrank_mono hflat
  have hdim := finrank_range_dirLin_le_she k θ
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at hle hdim ⊢
  generalize Fintype.card d ^ 2 = M at hle hdim ⊢
  omega

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, "with equality", in the paper's
own sense, at one parameter:** under the same conditions, a finite batch of inputs at which no
normalized row vanishes and no hidden unit sits at its kink, on which the Jacobian has the rank
`P − d² − (d(d−1)/2 + 1) − s`. -/
theorem exists_jacobianRank_mlp_oneBlock_rescale_skipless_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (hk : k ≠ 0) (hσ1 : σ 1 ≠ 0)
    (hP : UnitsParallel σ σ' k dIn d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hd : 2 ≤ Fintype.card d) (hcard : Fintype.card (hid 0) = Fintype.card d)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hR : (θ.read 0).rank = Fintype.card d) (hW : (θ.write 0).rank = Fintype.card d) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ skiplessZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp σ (rmsNorm 0) hid) 0 X θ
          + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
            + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  -- a batch of inputs of `U`, where the network is differentiable in `θ`, with the rank
  -- `P - dim K_U(θ)`
  obtain ⟨n, X, hX, h⟩ := exists_jacobianRank_add_finrank_flatOn (S := 0) θ
    (skiplessZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ)
    (fun x hx => differentiableAt_eval_she hσ θ x hx)
  -- the sandwich: `dim K(θ) ≤ dim K_U(θ) ≤ d² + d(d-1)/2 + 1 + s = dim K(θ)`
  have hfd := funDim_mlp_oneBlock_rescale_skipless_rmsNorm_zero hσ hhom hk hσ1 hP θ hd hcard hE
    hD hR hW
  have h' := funDim_add_finrank_flat' (S := 0) θ
  have h1 := Submodule.finrank_mono (flat_le_flatOn (S := 0) θ
    (skiplessZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ))
  have h2 := Submodule.finrank_mono (flatOn_le_range_she hσ hhom hk hσ1 hP θ hd hcard hE hD hR hW)
  have h3 := finrank_range_dirLin_le_she k θ
  refine ⟨n, X, hX, ?_⟩
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at hfd h3 ⊢
  generalize Fintype.card d ^ 2 = M at hfd h3 ⊢
  omega

omit [Nonempty T] in
/-- **The conditions of the proof at generic parameters:** for `d_in, d_out ≥ d` and a block of
exactly `d` hidden units, at almost every parameter `E`, `D`, `W_read` and `W_write` have rank
`d`. -/
theorem ae_rank_E_D_read_write_of_card_eq
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card (hid 0) = Fintype.card d) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d ∧ θ.D.rank = Fintype.card d ∧
      (θ.read 0).rank = Fintype.card d ∧ (θ.write 0).rank = Fintype.card d := by
  -- `d` columns of `D` and `d` columns of the read, invertible at generic parameters
  obtain ⟨ρD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  obtain ⟨ρR⟩ := Function.Embedding.nonempty_of_card_le hcard.ge
  filter_upwards [ae_rank_E_write μ hdIn
      (fun ℓ => by obtain rfl := Subsingleton.elim ℓ 0; exact hcard.ge),
    ae_isUnit_det_submatrix μ] with θ h1 h2
  exact ⟨h1.1, rank_eq_card_of_isUnit_det θ.D ρD (h2.2.1 ρD),
    rank_eq_card_of_isUnit_det (θ.read 0) ρR (h2.1 0 ρR), h1.2 0⟩

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, "with equality", for one ReLU
block of width `d`:** for `ε = 0`, `d_in, d_out ≥ d ≥ 2` and a block of exactly `d` hidden units,
at almost every parameter `funDim = P − d² − d(d−1)/2 − 1 − s`. -/
theorem ae_funDim_relu_oneBlock_skipless_rmsNorm_zero
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card (hid 0) = Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_D_read_write_of_card_eq μ hdIn hdOut hcard] with θ hθ
  exact funDim_mlp_oneBlock_rescale_skipless_rmsNorm_zero (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous one_ne_zero (by simp [relu]) (relu_unitsParallel dIn d (hid 0)) θ hd hcard
    hθ.1 hθ.2.1 hθ.2.2.1 hθ.2.2.2

/-- **The same in the paper's own sense, for one ReLU block of width `d`:** at almost every
parameter there is a finite batch of inputs at which no normalized row vanishes and no hidden
unit sits at its kink, on which the Jacobian has the rank `P − d² − d(d−1)/2 − 1 − s`. -/
theorem ae_exists_jacobianRank_relu_oneBlock_skipless_rmsNorm_zero
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card (hid 0) = Fintype.card d) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ skiplessZeroDomain (Arch.mlp relu (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp relu (rmsNorm 0) hid) 0 X θ
          + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
            + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_D_read_write_of_card_eq μ hdIn hdOut hcard] with θ hθ
  exact exists_jacobianRank_mlp_oneBlock_rescale_skipless_rmsNorm_zero
    (fun _ hz => hasDerivAt_relu hz) relu_homogeneous one_ne_zero (by simp [relu])
    (relu_unitsParallel dIn d (hid 0)) θ hd hcard hθ.1 hθ.2.1 hθ.2.2.1 hθ.2.2.2

/-- **Theorem B.1 (iv), the skipless network, "with equality", for one ReLU² block of width
`d`.** -/
theorem ae_funDim_reluSq_oneBlock_skipless_rmsNorm_zero
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card (hid 0) = Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_D_read_write_of_card_eq μ hdIn hdOut hcard] with θ hθ
  exact funDim_mlp_oneBlock_rescale_skipless_rmsNorm_zero (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous two_ne_zero (by simp [reluSq]) (reluSq_unitsParallel dIn d (hid 0)) θ hd
    hcard hθ.1 hθ.2.1 hθ.2.2.1 hθ.2.2.2

/-- **The same in the paper's own sense, for one ReLU² block of width `d`.** -/
theorem ae_exists_jacobianRank_reluSq_oneBlock_skipless_rmsNorm_zero
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card (hid 0) = Fintype.card d) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ skiplessZeroDomain (Arch.mlp reluSq (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp reluSq (rmsNorm 0) hid) 0 X θ
          + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
            + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_D_read_write_of_card_eq μ hdIn hdOut hcard] with θ hθ
  exact exists_jacobianRank_mlp_oneBlock_rescale_skipless_rmsNorm_zero
    (fun z _ => hasDerivAt_reluSq z) reluSq_homogeneous two_ne_zero (by simp [reluSq])
    (reluSq_unitsParallel dIn d (hid 0)) θ hd hcard hθ.1 hθ.2.1 hθ.2.2.1 hθ.2.2.2

/-- **Theorem B.1 (iv) of the skips paper, "by exactly `d_model²` for ReLU and ReLU² blocks", for
one ReLU block of width `d`:** at almost every parameter `funDim` of the residual network is
`funDim` of the skipless network plus `d²`. -/
theorem ae_funDim_relu_oneBlock_residual_rmsNorm_zero_eq_add
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card (hid 0) = Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 1 θ
      = funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ + Fintype.card d ^ 2 := by
  have : Nonempty (hid 0) := Fintype.card_pos_iff.1 (by omega)
  filter_upwards [ae_funDim_relu_oneBlock_residual_rmsNorm_zero μ hd hdIn hdOut,
    ae_funDim_relu_oneBlock_skipless_rmsNorm_zero μ hd hdIn hdOut hcard] with θ h1 h0
  omega

/-- **The same for one ReLU² block of width `d`.** -/
theorem ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero_eq_add
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card (hid 0) = Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 1 θ
      = funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ + Fintype.card d ^ 2 := by
  have : Nonempty (hid 0) := Fintype.card_pos_iff.1 (by omega)
  filter_upwards [ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero μ hd hdIn hdOut,
    ae_funDim_reluSq_oneBlock_skipless_rmsNorm_zero μ hd hdIn hdOut hcard] with θ h1 h0
  omega

end Skips
