import SkipsLean.Depth.SuffixZeroClaim
import SkipsLean.Depth.StepZeroValues

/-!
# The converse of the claim `(D_k)` in the case `ε = 0`

Paper (dimension paper): Appendix D.3, after the forms (17) to (19): "Conversely, every
`Z = Z_k ∈ 𝔤` and `η` of the form (17), or (19) for gated blocks, satisfy (16): it is the
derivative at `τ = 0` of the identity `𝓑_{>k}(h exp(τ Z_k)) = 𝓑_{>k}(h)`, in which the left side
is taken at the weights moved by the symmetries with `G_ℓ = exp(τ Z_ℓ)`"; in the case (0) the form
is (18): `Z = Y_k + β_k I`, reads `−Y_{ℓ−1} W_read^ℓ`, writes `W_write^ℓ (Y_ℓ + β_ℓ I)`, `−Y_L D`,
with antisymmetric `Y_ℓ` (the symmetries are `G_ℓ = c_ℓ Q_ℓ`, and `N(hG) = N(h)Q`).

The proof of Lemma D.19 uses it in "Step 3: subtracting a symmetry": "The pair `Y_k + β_k I` and
`(−Y_k W, V (Y_{k+1} + β_{k+1} I), η')` is of the form (18), so it satisfies (16) for `k`."

Stated here for real-analytic blocks of any kind under pre-RMSNorm with `ε = 0` and regular `θ`:
the direction `cobDir θ Y + scaleDir θ β` is of the form (18) for every `k` (its entries at `E`
and at the blocks before `h_k` play no role in (16)), and it satisfies (16) for `k` with
`Z = Y_k + β_k I`, when `Y_ℓ` is antisymmetric for `ℓ ≥ k`. (`Depth/SuffixFlatConverse.lean` has
the case of gated blocks without normalization.)
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L) (θ : Params A dIn dOut)

omit [DecidableEq d] in
/-- Helper: `⟨v Y, v⟩ = 0` for an antisymmetric `Y`. -/
private theorem vecMul_dotProduct_self_conv {Y : Matrix d d ℝ} (hY : Y ∈ antisymmetric d)
    (v : d → ℝ) : (v ᵥ* Y) ⬝ᵥ v = 0 := by
  have hT : Yᵀ = -Y := hY
  -- `v Y = Yᵀ v = −Y v`, and `⟨Y v, v⟩ = ⟨v, Y v⟩ = ⟨v Y, v⟩`
  have e : (v ᵥ* Y) ⬝ᵥ v = -((v ᵥ* Y) ⬝ᵥ v) := by
    calc (v ᵥ* Y) ⬝ᵥ v = (Yᵀ *ᵥ v) ⬝ᵥ v := by rw [Matrix.mulVec_transpose]
      _ = -((Y *ᵥ v) ⬝ᵥ v) := by rw [hT, Matrix.neg_mulVec, neg_dotProduct]
      _ = -((v ᵥ* Y) ⬝ᵥ v) := by rw [dotProduct_comm, Matrix.dotProduct_mulVec]
  linarith

/-- Helper: `𝐃N(h)(h(Y + β I)) = N(h) Y` for an antisymmetric `Y`, at `h` without a zero row. -/
private theorem fderiv_rmsNorm_zero_antisymm_conv {Y : Matrix d d ℝ} (hY : Y ∈ antisymmetric d)
    (β : ℝ) (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) :
    fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h (h * (Y + β • (1 : Matrix d d ℝ)))
      = rmsNorm 0 h * Y := by
  -- linearity, `𝐃N(h) h = 0` (15), and (14) with `⟨n Y, n⟩ = 0`
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, map_add, map_smul,
    fderiv_rmsNorm_zero_self h hh, smul_zero, add_zero, fderiv_rmsNorm_zero_mul Y h hh]
  ext t i
  show (rmsNorm 0 h * Y) t i
      - (((rmsNorm 0 h * Y) t ⬝ᵥ rmsNorm 0 h t) / (Fintype.card d : ℝ)) * rmsNorm 0 h t i
    = (rmsNorm 0 h * Y) t i
  rw [Matrix.mul_apply_eq_vecMul, vecMul_dotProduct_self_conv hY, zero_div, zero_mul, sub_zero]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the line `τ ↦ a + τ b` has the velocity `b` (as in `Depth/StepZeroValues.lean`). -/
private theorem hasDerivAt_line_conv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) : HasDerivAt (fun τ : ℝ => a + τ • b) b 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a
  rw [one_smul] at h
  exact h

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product rule for matrix-valued functions of one real variable (as in
`Depth/StepZeroValues.lean`). -/
private theorem hasDerivAt_matMul_conv {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {A : ℝ → Matrix m n ℝ} {B : ℝ → Matrix n p ℝ} {A' : Matrix m n ℝ} {B' : Matrix n p ℝ}
    {τ : ℝ} (hA : HasDerivAt A A' τ) (hB : HasDerivAt B B' τ) :
    HasDerivAt (fun s => A s * B s) (A' * B τ + A τ * B') τ := by
  refine hasDerivAt_pi.2 fun t => hasDerivAt_pi.2 fun i => ?_
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA t) j).mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB j) i)
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact h

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: for `Φ` differentiable at `(x, y)`, the derivatives of its two partial maps add up to
its derivative along `(a, b)` (as in `Depth/StepZeroValues.lean`). -/
private theorem fderiv_partial_add_conv {E₁ E₂ F : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Φ : E₁ → E₂ → F} {x : E₁} {y : E₂}
    (hΦ : DifferentiableAt ℝ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y)) (a : E₁) (b : E₂) :
    fderiv ℝ (fun y' => Φ x y') y b + fderiv ℝ (fun x' => Φ x' y) x a
      = fderiv ℝ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y) (a, b) := by
  have h1 : HasFDerivAt (fun x' => Φ x' y)
      ((fderiv ℝ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y)).comp
        (ContinuousLinearMap.inl ℝ E₁ E₂)) x := by
    have hc := hΦ.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
    exact hc
  have h2 : HasFDerivAt (fun y' => Φ x y')
      ((fderiv ℝ (fun p : E₁ × E₂ => Φ p.1 p.2) (x, y)).comp
        (ContinuousLinearMap.inr ℝ E₁ E₂)) y := by
    have hc := hΦ.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
    exact hc
  rw [h1.fderiv, h2.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ← map_add, Prod.mk_add_mk,
    zero_add, add_zero]

/-- Helper: `y ↦ y M`, as a continuous linear map. -/
private noncomputable def mulRightCLM_conv {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (M : Matrix n p ℝ) : Matrix m n ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => y * M
      map_add' := fun a b => Matrix.add_mul a b M
      map_smul' := fun c a => Matrix.smul_mul c a M }

/-- Helper (as in `Depth/SuffixZero.lean`): for `χ = N`, the derivative of `h ↦ 𝓑_{>L}(h) = N(h) D`
at `h` without a zero row, along `v`, is `(𝐃N(h) v) D`. -/
private theorem fderiv_suffix_last_zero_conv (hχ : A.χ = rmsNorm 0) (h v : Matrix T d ℝ)
    (hh : ∀ t, h t ≠ 0) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ (Fin.last L) h') h v
      = fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h v * θ.D := by
  simp only [suffix_last, hχ]
  have hc := (mulRightCLM_conv (m := T) θ.D).hasFDerivAt.comp h
    (analyticAt_rmsNorm_zero h hh).differentiableAt.hasFDerivAt
  exact DFunLike.congr_fun hc.fderiv v

/-- **"Conversely, every `Z = Z_k ∈ 𝔤` and `η` of the form (18) satisfy (16)", the case (0):** for
real-analytic blocks under pre-RMSNorm with `ε = 0` and regular `θ`, if `Y_ℓ` is antisymmetric for
every `ℓ ≥ k`, then `Z = Y_k + β_k I` and `η = cobDir θ Y + scaleDir θ β` satisfy (16) for `k`. -/
theorem suffixFlatZero_cobDir_add_scaleDir (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ) (k : Fin (L + 1))
    (Y : Fin (L + 1) → Matrix d d ℝ) (hY : ∀ ℓ, k ≤ ℓ → Y ℓ ∈ antisymmetric d)
    (β : Fin (L + 1) → ℝ) :
    SuffixFlatZero A θ k (Y k + β k • (1 : Matrix d d ℝ)) (cobDir θ Y + scaleDir θ β) := by
  sorry

end Skips
