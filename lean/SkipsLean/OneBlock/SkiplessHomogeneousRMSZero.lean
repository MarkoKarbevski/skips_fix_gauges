import SkipsLean.Dimension.UpperBoundRMSNormZero
import SkipsLean.Dimension.RescalingMlp
import SkipsLean.OneBlock.Common
import SkipsLean.Dimension.ExpOrbit

/-!
# One skipless block under pre-RMSNorm with `ε = 0`, ReLU and ReLU²: the bound

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`, and the skipless
network at most `P − d_model² − d_model (d_model − 1)/2 − 1 − s`, with equality for ReLU and ReLU²
blocks."

Its proof, "Part (iv)": "With `ε = 0`, `N_ε(h) = √d_model h/‖h‖` depends only on the direction of
`h`, and `B(λ n) = λ^k B(n)` for `λ > 0`, so `N_ε(B(N_ε(h))) = N_ε(B(h))`: the skipless network
computes `x ↦ N_ε(B(x E)) D`. Its normalization before the block drops out, which leaves the
changes of basis `GL(d_model)` at `h_0` and `CO(d_model)` at `h_1`, of dimension
`d_model² + d_model (d_model − 1)/2 + 1`". And "The skipless network: the bound. The changes of
basis in `GL(d_model)` at `h_0` and in `CO(d_model)` at `h_1` and the symmetries inside the block
preserve the function. They move the parameters along the directions with the entries `E X` at
`E` and `−X W_read` at `W_read`, with the entries `W_write (Y + c I)` at `W_write` and `−Y D` at
`D` for an antisymmetric `Y` and a number `c`, and along the rescalings of the units. For generic
parameters these directions are independent, as in Step 3 of part (i). So
`dim K(θ) ≥ d_model² + d_model (d_model − 1)/2 + 1 + s`, which is the bound."

Here, for one MLP block whose activation is positively homogeneous of degree `k` (ReLU: `k = 1`;
ReLU²: `k = 2`), `s` is the number of hidden units: the direction of a change of basis `I + τ X`
at `h_0`, for every matrix `X`, is flat under pre-RMSNorm with `ε = 0`; the bound at one parameter
under the conditions of the proof (`E` and the write of rank `d`, no read column zero); the bound
at almost every parameter for ReLU and ReLU² blocks of width at least `d`.

The functional dimension is Lean's `funDim`, over all inputs, with the derivative in the weights
taken to be `0` where the output is not differentiable, and with Lean's `rmsNorm 0`, which maps a
zero row to `0`. It is at least the paper's, which uses fewer inputs, so the bound holds for the
paper's. Not stated here: the bound for ReGLU blocks; the value for the residual network; the
equality for ReLU and ReLU² blocks.
-/

namespace Skips

open Matrix MeasureTheory

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the function of the skipless network of one block under pre-RMSNorm with `ε = 0`
(the stream matrix is `0`): `x ↦ N_0(f(N_0(x E) W_read) W_write) D`. -/
private theorem eval_skipless_shz {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (θ : Params A dIn dOut) (x : Matrix T dIn ℝ) :
    eval A 0 θ x
      = rmsNorm 0 (A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) * θ.D := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hA]
  simp only [Pi.zero_apply, Matrix.mul_zero, zero_add]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `N_0(c w) = N_0(w)` for `c > 0` (a copy of the private `rmsRow_zero_smul` of
`Basic/RMSNorm.lean`). -/
private theorem rmsRow_zero_smul_shz {c : ℝ} (hc : 0 < c) (w : d → ℝ) :
    rmsRow 0 (c • w) = rmsRow 0 w := by
  unfold rmsRow
  -- `‖cw‖² / d = c² (‖w‖² / d)`, hence `sqrt (‖cw‖² / d) = c * sqrt (‖w‖² / d)`
  have hs : Real.sqrt ((c • w ⬝ᵥ c • w) / (Fintype.card d : ℝ) + 0)
      = c * Real.sqrt ((w ⬝ᵥ w) / (Fintype.card d : ℝ) + 0) := by
    have : (c • w ⬝ᵥ c • w) / (Fintype.card d : ℝ) + 0
        = c ^ 2 * ((w ⬝ᵥ w) / (Fintype.card d : ℝ) + 0) := by
      rw [smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul, add_zero]
      ring
    rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  -- the factor `c` cancels
  rw [hs, mul_inv, smul_smul]
  congr 1
  rw [mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `√(‖v‖²/d) > 0` for a nonzero row `v`. -/
private theorem sqrt_meanSq_pos_shz {v : d → ℝ} (hv : v ≠ 0) :
    0 < Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + 0) := by
  obtain ⟨i, -⟩ := Function.ne_iff.mp hv
  have h1 : v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_self_eq_zero.mp h)
  have h2 : 0 < (Fintype.card d : ℝ) := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨i⟩)
  rw [add_zero]
  exact Real.sqrt_pos.2
    (div_pos (lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)) h1.symm) h2)

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: for an invertible `G`, `N_0(v G) G⁻¹ = c N_0(v)` with `c > 0`:
`c = √(‖v‖²/d) / √(‖v G‖²/d)` if `v ≠ 0`, and `c = 1` if `v = 0` (both sides are `0`). -/
private theorem exists_rmsRow_vecMul_inv_shz (G : GL d ℝ) (v : d → ℝ) :
    ∃ c : ℝ, 0 < c ∧
      rmsRow 0 (v ᵥ* (G : Matrix d d ℝ)) ᵥ* (↑G⁻¹ : Matrix d d ℝ) = c • rmsRow 0 v := by
  by_cases hv : v = 0
  · -- a zero row stays zero
    refine ⟨1, one_pos, ?_⟩
    simp only [hv, Matrix.zero_vecMul, rmsRow, smul_zero]
  · -- `v ≠ 0` and `v G ≠ 0`, so both norms are positive
    have hvG : v ᵥ* (G : Matrix d d ℝ) ≠ 0 := by
      intro h
      apply hv
      have h' := congrArg (· ᵥ* (↑G⁻¹ : Matrix d d ℝ)) h
      simpa only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one,
        Matrix.zero_vecMul] using h'
    have ha := sqrt_meanSq_pos_shz hv
    have hb := sqrt_meanSq_pos_shz hvG
    refine ⟨_, div_pos ha hb, ?_⟩
    -- `N_0(v G) G⁻¹ = (√(‖vG‖²/d))⁻¹ v`
    unfold rmsRow
    rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, smul_smul]
    congr 1
    field_simp

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: scaling the rows commutes with a product on the right. -/
private theorem rowScale_mul_shz {n p : Type*} [Fintype n] (c : T → ℝ) (M : Matrix T n ℝ)
    (N : Matrix n p ℝ) :
    (Matrix.of fun t => c t • M t) * N = Matrix.of fun t => c t • (M * N) t := by
  ext t j
  simp only [Matrix.mul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_assoc]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `N_0` forgets a positive scaling of the rows. -/
private theorem rmsNorm_zero_rowScale_shz (μ : T → ℝ) (hμ : ∀ t, 0 < μ t) (h : Matrix T d ℝ) :
    rmsNorm 0 (Matrix.of fun t => μ t • h t) = rmsNorm 0 h := by
  ext t j
  show rmsRow 0 (μ t • h t) j = rmsRow 0 (h t) j
  rw [rmsRow_zero_smul_shz (hμ t)]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Helper: for an invertible `G`, `N_0(h G) G⁻¹` is `N_0(h)` with row `t` scaled by
`c t > 0`. -/
private theorem exists_rmsNorm_mul_inv_shz (G : GL d ℝ) (h : Matrix T d ℝ) :
    ∃ c : T → ℝ, (∀ t, 0 < c t) ∧
      rmsNorm 0 (h * (G : Matrix d d ℝ)) * (↑G⁻¹ : Matrix d d ℝ)
        = Matrix.of fun t => c t • rmsNorm 0 h t := by
  choose c hc heq using fun t => exists_rmsRow_vecMul_inv_shz G (h t)
  refine ⟨c, hc, ?_⟩
  ext t j
  have hrow : (rmsNorm 0 (h * (G : Matrix d d ℝ)) * (↑G⁻¹ : Matrix d d ℝ)) t
      = rmsRow 0 (h t ᵥ* (G : Matrix d d ℝ)) ᵥ* (↑G⁻¹ : Matrix d d ℝ) := rfl
  exact congrFun (hrow.trans (heq t)) j

omit [Fintype T] [Fintype dOut] in
/-- Helper: the change of basis `G` at `h_0` of a skipless network of one block under
pre-RMSNorm with `ε = 0` (`E ↦ E G`, `W_read ↦ G⁻¹ W_read`) preserves the function if `f`
sends a positive scaling of the rows of its input to a positive scaling of the rows of its
output. -/
private theorem eval_eq_of_rowScaling_shz {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    (hf : ∀ c : T → ℝ, (∀ t, 0 < c t) → ∀ z : Matrix T (A.r 0) ℝ, ∃ μ : T → ℝ, (∀ t, 0 < μ t) ∧
      A.f 0 (Matrix.of fun t => c t • z t) = Matrix.of fun t => μ t • A.f 0 z t)
    (θ θ' : Params A dIn dOut) (G : GL d ℝ) (hE : θ'.E = θ.E * (G : Matrix d d ℝ))
    (hr : θ'.read 0 = (↑G⁻¹ : Matrix d d ℝ) * θ.read 0) (hw : θ'.write 0 = θ.write 0)
    (hD : θ'.D = θ.D) (x : Matrix T dIn ℝ) :
    eval A 0 θ' x = eval A 0 θ x := by
  rw [eval_skipless_shz hA, eval_skipless_shz hA, hE, hr, hw, hD]
  -- the input of the block: row `t` is multiplied by `c t > 0`
  obtain ⟨c, hc, hn⟩ := exists_rmsNorm_mul_inv_shz G (x * θ.E)
  have hin : rmsNorm 0 (x * (θ.E * (G : Matrix d d ℝ))) * ((↑G⁻¹ : Matrix d d ℝ) * θ.read 0)
      = Matrix.of fun t => c t • (rmsNorm 0 (x * θ.E) * θ.read 0) t := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hn, rowScale_mul_shz]
  -- the output of the block: row `t` is multiplied by `μ t > 0`, which `N_0` forgets
  obtain ⟨μ, hμ, hfμ⟩ := hf c hc (rmsNorm 0 (x * θ.E) * θ.read 0)
  rw [hin, hfμ, rowScale_mul_shz, rmsNorm_zero_rowScale_shz μ hμ]

open scoped Matrix.Norms.Elementwise in
omit [Fintype T] in
/-- Helper: the curve `τ ↦ θ.cob (exp (τ m)) (exp (τ m))` has velocity `cobDir θ m` at
`τ = 0`. -/
private theorem hasDerivAt_cobExp_smul_shz {L : ℕ} {A : Arch T d L} (θ : Params A dIn dOut)
    (m : Fin (L + 1) → Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => cobExp θ (τ • m)) (cobDir θ m) 0 := by
  obtain ⟨Φ', hΦ, hΦm⟩ := hasStrictFDerivAt_cobExp θ
  -- the line `τ ↦ τ m` has velocity `1 • m`; the chain rule
  have hl := (hasDerivAt_id (0 : ℝ)).smul_const m
  have h := hΦ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact h.congr_deriv ((congrArg Φ' (one_smul ℝ m)).trans (hΦm m))

/-- **The normalization before the block drops out** (proof of Theorem B.1 (iv) of the skips
paper): for a skipless network of one block under pre-RMSNorm with `ε = 0` whose map `f` sends a
positive scaling of the rows of its input to a positive scaling of the rows of its output, the
direction of the change of basis `I + τ X` at `h_0` (`E X` at `E`, `−X W_read` at `W_read`) is
flat, for every matrix `X`. -/
private theorem cobDir_zero_mem_flat_of_rowScaling_shz {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0)
    (hf : ∀ c : T → ℝ, (∀ t, 0 < c t) → ∀ z : Matrix T (A.r 0) ℝ, ∃ μ : T → ℝ, (∀ t, 0 < μ t) ∧
      A.f 0 (Matrix.of fun t => c t • z t) = Matrix.of fun t => μ t • A.f 0 z t)
    (θ : Params A dIn dOut) (X : Matrix d d ℝ) :
    cobDir θ ![X, 0] ∈ flat A 0 θ := by
  -- the curve `τ ↦ θ.cob (exp (τ ![X, 0]))`: `exp (τ X)` at `h_0`, the identity at `h_1`; it
  -- passes through `θ` with velocity `cobDir θ ![X, 0]`, and keeps the function at every `τ`
  refine mem_flat_of_hasDerivAt' θ (fun τ => cobExp θ (τ • ![X, 0])) (cobDir θ ![X, 0])
    (hasDerivAt_cobExp_smul_shz θ ![X, 0]) (by rw [zero_smul]; exact cobExp_zero θ)
    (Filter.Eventually.of_forall fun τ x => ?_)
  refine eval_eq_of_rowScaling_shz hA hf θ _ (expGL (τ • X)) rfl rfl ?_ ?_ x
  · -- the write is `W_write exp (τ 0) = W_write`
    show θ.write 0 * NormedSpace.exp (τ • (0 : Matrix d d ℝ)) = θ.write 0
    rw [smul_zero, NormedSpace.exp_zero, Matrix.mul_one]
  · -- the readout is `exp (-τ 0) D = D`
    show NormedSpace.exp (-(τ • (0 : Matrix d d ℝ))) * θ.D = θ.D
    rw [smul_zero, neg_zero, NormedSpace.exp_zero, Matrix.one_mul]

/-- **Proof of Theorem B.1 (iv) of the skips paper, "Its normalization before the block drops
out":** for one skipless MLP block with `σ(λ z) = λ^k σ(z)` for `λ > 0`, under pre-RMSNorm with
`ε = 0`, the direction of the change of basis `I + τ X` at `h_0` (`E X` at `E`, `−X W_read` at
`W_read`) is flat, for every matrix `X`. -/
theorem cobDir_zero_mem_flat_skipless_mlp_homogeneous_rmsNorm_zero {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (X : Matrix d d ℝ) :
    cobDir θ ![X, 0] ∈ flat (Arch.mlp σ (rmsNorm 0) hid) 0 θ := by
  -- the MLP block multiplies row `t` of its output by `c t ^ k` when row `t` of its input is
  -- multiplied by `c t > 0`
  refine cobDir_zero_mem_flat_of_rowScaling_shz rfl
    (fun c hc z => ⟨fun t => c t ^ k, fun t => pow_pos (hc t) k, ?_⟩) θ X
  ext t i
  show σ (c t * z t i) = c t ^ k * σ (z t i)
  exact hσ _ _ (hc t)

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, the bound, under the conditions
of the proof:** for one skipless MLP block with a positively homogeneous activation under
pre-RMSNorm with `ε = 0`, if `E` and the write have rank `d ≥ 1` and no read column is zero, the
functional dimension is at most `P − d² − (d(d−1)/2 + 1) − s`, where `s` is the number of hidden
units. -/
theorem funDim_add_le_skipless_mlp_homogeneous_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, for a ReLU block of width at
least `d` at generic parameters:** under pre-RMSNorm with `ε = 0`, with `d_in ≥ d ≥ 1`, the
functional dimension is at most `P − d² − d(d−1)/2 − 1 − s`. -/
theorem ae_funDim_add_le_skipless_relu_oneBlock_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, for a ReLU² block of width at
least `d` at generic parameters:** under pre-RMSNorm with `ε = 0`, with `d_in ≥ d ≥ 1`, the
functional dimension is at most `P − d² − d(d−1)/2 − 1 − s`. -/
theorem ae_funDim_add_le_skipless_reluSq_oneBlock_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      ≤ Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  sorry

end Skips
