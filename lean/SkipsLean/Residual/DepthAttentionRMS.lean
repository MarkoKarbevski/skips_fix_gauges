import SkipsLean.OneBlock.AttentionFamily
import SkipsLean.Residual.SmallWritesRMSSteps
import SkipsLean.Dimension.UpperBoundAttention
import SkipsLean.Network.AttentionAnalytic

/-!
# Residual networks of attention blocks at any depth under pre-RMSNorm: small writes

Paper (skips paper): Lemma A.27 (Small writes), its second value, for attention blocks: "For all
small `τ ≠ 0`, the residual network has […] `fd(θ_τ) = P − d_model (d_model − 1)/2 − s`
(pre-RMSNorm with `ε > 0`, no biases)". Its proof, "Under pre-RMSNorm": with `h = x E`,
`n = N_ε(h)` and the limit `(J_0 η)(x) = 𝐃N_ε(h) (x η_E + D_θ g(n) η) D + N_ε(h) η_D`, "this is
the equation of the proof of Theorem B.1 (ii) with `h_1 = x E` and
`D_θ h_1 η = x η_E + D_θ g(n) η`, and its Steps 1 to 5 go through"; Steps 1 to 3
(`Residual/SmallWritesRMSSteps.lean`, for any continuously differentiable blocks) give an
antisymmetric `Y` with `η_E = E Y`, `η_D = −Y D`, and `D_θ g(n) η = 0` at every `n = N_ε(x E)`.
For attention blocks `g` is the sum of the heads of all blocks with the matrices
`Γ_j = W_Q W_K^⊤/√d_h` and `W_V W_O` ("with `E` and `D` replaced by the identity"), the identity
`D_θ g(n) η = 0` extends from the rows of norm less than `√d` to all rows because its left side is
real-analytic in `n`, and Step 2 for a family of heads (`OneBlock/AttentionFamily.lean`) gives
that the derivatives of every `Γ_j` and every `W_V W_O` along `η` vanish.

Here, for `Arch.attention sees (rmsNorm ε) H dh` with `L` blocks, `ε > 0`, and a token `t₂` that
sees itself and another token `t₁`:

* `headScoreModel θ ℓ i`, `headValueModel θ ℓ i`: the matrices `W_Q W_K^⊤/√d_h` and `W_V W_O` of
  head `i` of block `ℓ`, on the model space.
* `SmallWritesGenericAttentionRMS θ`: the conditions on `θ` that the proof uses.
* `smallWritesLimitNorm_eq_zero_attention_rmsNorm`: a direction that is flat for `J_0` has
  `η_E = E Y`, `η_D = −Y D` with `Y` antisymmetric, and in every block the reads and writes of
  the directions of the changes of basis inside the heads.
* `eventually_funDim_smallWrites_attention_rmsNorm`:
  `fd(θ_τ) = P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²` for all small `τ ≠ 0`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees] {χ : Matrix T d ℝ → Matrix T d ℝ}
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)] {ε : ℝ}

/-- **The matrix `W_Q W_K^⊤ / √d_h`** of head `i` of block `ℓ`, on the model space. -/
noncomputable def headScoreModel (θ : Params (Arch.attention sees χ H dh) dIn dOut) (ℓ : Fin L)
    (i : H ℓ) : Matrix d d ℝ :=
  (Real.sqrt (Fintype.card (dh ℓ)))⁻¹ •
    (((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k))
      * ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))ᵀ)

/-- **The matrix `W_V W_O`** of head `i` of block `ℓ`, on the model space. -/
def headValueModel (θ : Params (Arch.attention sees χ H dh) dIn dOut) (ℓ : Fin L) (i : H ℓ) :
    Matrix d d ℝ :=
  ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
    * ((θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id)

/-- **The conditions on `θ` in Lemma A.27 under pre-RMSNorm, for attention blocks:** `E` and `D`
have rank `d`; the query, key, value and output matrices of every head of every block have rank
`d_h`; and, "with `E` and `D` replaced by the identity", some `v` has the columns
`W_Q W_K^⊤ v^⊤` of the heads of all blocks together nonzero and pairwise non-collinear, and every
row `v W_V W_O` nonzero. -/
structure SmallWritesGenericAttentionRMS
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_Q : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
    = Fintype.card (dh ℓ)
  rank_K : ∀ ℓ (i : H ℓ),
    ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k))).rank
      = Fintype.card (dh ℓ)
  rank_V : ∀ ℓ (i : H ℓ),
    ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
      = Fintype.card (dh ℓ)
  rank_O : ∀ ℓ (i : H ℓ), ((θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id).rank
    = Fintype.card (dh ℓ)
  /-- some `v` has the `W_Q W_K^⊤ v^⊤` of all heads nonzero and pairwise non-collinear and every
  `v W_V W_O` nonzero -/
  exists_v : ∃ v : d → ℝ, (∀ p : (Σ ℓ, H ℓ), headScoreModel θ p.1 p.2 *ᵥ v ≠ 0)
    ∧ (∀ p q : (Σ ℓ, H ℓ), p ≠ q → ∀ r : ℝ,
        headScoreModel θ p.1 p.2 *ᵥ v ≠ r • (headScoreModel θ q.1 q.2 *ᵥ v))
    ∧ (∀ p : (Σ ℓ, H ℓ), v ᵥ* headValueModel θ p.1 p.2 ≠ 0)


/-! ### Helpers: derivatives of matrix curves at `0` -/

/-- Helper (as `hasDerivAt_line_dpa` of `Residual/DepthAttention.lean`): a line `τ ↦ M + τ N` of
matrices has the derivative `N`. -/
private theorem hasDerivAt_line_rma {m n : Type*} [Fintype m] [Fintype n] (M N : Matrix m n ℝ) :
    HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

/-- Helper (as `hasDerivAt_mul_dpa`): the product rule for two matrix curves, entry by entry. -/
private theorem hasDerivAt_mul_rma {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {A : ℝ → Matrix m n ℝ} {B : ℝ → Matrix n p ℝ} {A' : Matrix m n ℝ} {B' : Matrix n p ℝ}
    (hA : HasDerivAt A A' 0) (hB : HasDerivAt B B' 0) :
    HasDerivAt (fun τ => A τ * B τ) (A' * B 0 + A 0 * B') 0 := by
  refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun c => ?_
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun b _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA a) b).fun_mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB b) c)
  simp only [Matrix.add_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  exact h

/-- Helper (as `hasDerivAt_transpose_dpa`): the transpose of a matrix curve has the transposed
derivative. -/
private theorem hasDerivAt_transpose_rma {m n : Type*} [Fintype m] [Fintype n]
    {A : ℝ → Matrix m n ℝ} {A' : Matrix m n ℝ} (hA : HasDerivAt A A' 0) :
    HasDerivAt (fun τ => (A τ)ᵀ) A'ᵀ 0 :=
  hasDerivAt_pi.2 fun b => hasDerivAt_pi.2 fun a => hasDerivAt_pi.1 (hasDerivAt_pi.1 hA a) b

/-! ### Helpers: the curves of the heads along a direction of the reads and the writes -/

/-- Helper (as `moveRW_dpa`): the parameters `θ` with the reads and the writes moved by `τ η`;
`E` and `D` stay. -/
private def moveRW_rma {A : Arch T d L} (θ η : Params A dIn dOut) (τ : ℝ) :
    Params A dIn dOut where
  E := θ.E
  read ℓ := θ.read ℓ + τ • η.read ℓ
  write ℓ := θ.write ℓ + τ • η.write ℓ
  D := θ.D

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: at `τ = 0` the moved parameters are `θ`. -/
private theorem moveRW_rma_zero {A : Arch T d L} (θ η : Params A dIn dOut) :
    moveRW_rma θ η 0 = θ := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · show θ.read ℓ + (0 : ℝ) • η.read ℓ = θ.read ℓ
    rw [zero_smul, add_zero]
  · show θ.write ℓ + (0 : ℝ) • η.write ℓ = θ.write ℓ
    rw [zero_smul, add_zero]

/-- Helper: the query matrix `W_{Q,i}` of head `i` of block `ℓ`. -/
private abbrev wQ_rma (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (ℓ : Fin L) (i : H ℓ) : Matrix d (dh ℓ) ℝ :=
  (θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)

/-- Helper: the key matrix `W_{K,i}` of head `i` of block `ℓ`. -/
private abbrev wK_rma (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (ℓ : Fin L) (i : H ℓ) : Matrix d (dh ℓ) ℝ :=
  (θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k))

/-- Helper: the value matrix `W_{V,i}` of head `i` of block `ℓ`. -/
private abbrev wV_rma (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (ℓ : Fin L) (i : H ℓ) : Matrix d (dh ℓ) ℝ :=
  (θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))

/-- Helper: the output matrix `W_{O,i}` of head `i` of block `ℓ`. -/
private abbrev wO_rma (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (ℓ : Fin L) (i : H ℓ) : Matrix (dh ℓ) d ℝ :=
  (θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the moved reads, the matrix `W_Q W_K^⊤ / √d_h` of head `i` of block `ℓ` has at
`τ = 0` the derivative `(η_Q W_K^⊤ + W_Q η_K^⊤) / √d_h`. -/
private theorem hasDerivAt_headScoreModel_rma
    (θ η : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) (ℓ : Fin L)
    (i : H ℓ) :
    HasDerivAt (fun τ => headScoreModel (moveRW_rma θ η τ) ℓ i)
      ((Real.sqrt (Fintype.card (dh ℓ)))⁻¹ • (wQ_rma η ℓ i * (wK_rma θ ℓ i)ᵀ
        + wQ_rma θ ℓ i * (wK_rma η ℓ i)ᵀ)) 0 := by
  -- `(W_Q + τ η_Q) (W_K + τ η_K)^⊤ / √d_h`
  have h := (hasDerivAt_mul_rma (hasDerivAt_line_rma (wQ_rma θ ℓ i) (wQ_rma η ℓ i))
    (hasDerivAt_transpose_rma (hasDerivAt_line_rma (wK_rma θ ℓ i) (wK_rma η ℓ i)))).const_smul
      (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
  exact h.congr_deriv (by simp only [zero_smul, add_zero])

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the moved reads and writes, the matrix `W_V W_O` of head `i` of block `ℓ` has
at `τ = 0` the derivative `η_V W_O + W_V η_O`. -/
private theorem hasDerivAt_headValueModel_rma
    (θ η : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) (ℓ : Fin L)
    (i : H ℓ) :
    HasDerivAt (fun τ => headValueModel (moveRW_rma θ η τ) ℓ i)
      (wV_rma η ℓ i * wO_rma θ ℓ i + wV_rma θ ℓ i * wO_rma η ℓ i) 0 := by
  -- `(W_V + τ η_V) (W_O + τ η_O)`
  have h := hasDerivAt_mul_rma (hasDerivAt_line_rma (wV_rma θ ℓ i) (wV_rma η ℓ i))
    (hasDerivAt_line_rma (wO_rma θ ℓ i) (wO_rma η ℓ i))
  exact h.congr_deriv (by simp only [zero_smul, add_zero])

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper ("let the heads of all attention blocks form one attention block", with `E` and `D`
replaced by the identity): `∑_{(ℓ,i)} P(n Γ_{ℓ,i} n^⊤) n W_{V,ℓ,i} W_{O,ℓ,i}
= ∑_ℓ f_ℓ(n W_read^ℓ) W_write^ℓ`. -/
private theorem sum_heads_eq_rma
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) (n : Matrix T d ℝ) :
    ∑ p : (Σ ℓ, H ℓ), attnWeights sees (n * headScoreModel θ p.1 p.2 * nᵀ) * n
        * headValueModel θ p.1 p.2
      = ∑ ℓ, (Arch.attention (T := T) (d := d) sees χ H dh).f ℓ (n * θ.read ℓ) * θ.write ℓ := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  -- block `ℓ` is equation (4) on the input `n`
  rw [f_attention_mul]
  rfl

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the term of block `ℓ` along the moved reads and writes,
`τ ↦ f_ℓ(n (W_read + τ η_read)) (W_write + τ η_write)`, has at `τ = 0` the derivative
`D f_ℓ(n W_read)(n η_read) W_write + f_ℓ(n W_read) η_write` (chain rule). -/
private theorem hasDerivAt_block_rma
    (θ η : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (n : Matrix T d ℝ) (ℓ : Fin L) :
    HasDerivAt (fun τ => (Arch.attention (T := T) (d := d) sees χ H dh).f ℓ
        (n * (moveRW_rma θ η τ).read ℓ) * (moveRW_rma θ η τ).write ℓ)
      (fderiv ℝ ((Arch.attention (T := T) (d := d) sees χ H dh).f ℓ) (n * θ.read ℓ)
          (n * η.read ℓ) * θ.write ℓ
        + (Arch.attention (T := T) (d := d) sees χ H dh).f ℓ (n * θ.read ℓ) * η.write ℓ) 0 := by
  -- the line `τ ↦ n (W_read + τ η_read)` has the derivative `n η_read`
  have hl : HasDerivAt (fun τ : ℝ => n * (θ.read ℓ + τ • η.read ℓ)) (n * η.read ℓ) 0 :=
    (hasDerivAt_mul_rma (hasDerivAt_const (0 : ℝ) n)
      (hasDerivAt_line_rma (θ.read ℓ) (η.read ℓ))).congr_deriv
      (by simp only [Matrix.zero_mul, zero_add])
  -- the chain rule through `f_ℓ`
  have hf := (differentiable_f_attention (d := d) sees χ H dh ℓ (n * θ.read ℓ)).hasFDerivAt
  have hc := hf.comp_hasDerivAt_of_eq (0 : ℝ) hl (by rw [zero_smul, add_zero])
  have hc' : HasDerivAt (fun τ : ℝ => (Arch.attention (T := T) (d := d) sees χ H dh).f ℓ
      (n * (θ.read ℓ + τ • η.read ℓ)))
      (fderiv ℝ ((Arch.attention (T := T) (d := d) sees χ H dh).f ℓ) (n * θ.read ℓ)
        (n * η.read ℓ)) 0 := hc
  -- the product rule with the write
  have h := hasDerivAt_mul_rma hc' (hasDerivAt_line_rma (θ.write ℓ) (η.write ℓ))
  exact h.congr_deriv (by simp only [zero_smul, add_zero])

/-! ### Helpers: the derivative of the wide block, and its analyticity -/

/-- Helper: the derivative of the wide block `n ↦ ∑_ℓ f_ℓ(n W_read^ℓ) W_write^ℓ` along the reads
and the writes of `η`, at the input `n`: `D_θ g(n) η`. -/
private noncomputable def blockDir_rma
    (θ η : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) (n : Matrix T d ℝ) :
    Matrix T d ℝ :=
  ∑ ℓ, (fderiv ℝ ((Arch.attention (T := T) (d := d) sees χ H dh).f ℓ) (n * θ.read ℓ)
      (n * η.read ℓ) * θ.write ℓ
    + (Arch.attention (T := T) (d := d) sees χ H dh).f ℓ (n * θ.read ℓ) * η.write ℓ)

/-- Helper (as `analyticOnNhd_clm_apply'` of `Depth/StepTanhRMS.lean`): an analytic family of
continuous linear maps, applied to an analytic family of vectors, is analytic. -/
private theorem analyticOnNhd_clm_apply_rma {X E F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {J : X → E →L[ℝ] F} {v : X → E} {s : Set X} (hJ : AnalyticOnNhd ℝ J s)
    (hv : AnalyticOnNhd ℝ v s) : AnalyticOnNhd ℝ (fun x => J x (v x)) s :=
  fun x hx => ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).analyticAt_bilinear (J x, v x)).comp₂
    (hJ x hx) (hv x hx)

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `n ↦ D_θ g(n) η` is real-analytic (the blocks are analytic, so is their derivative). -/
private theorem analyticOnNhd_blockDir_rma
    (θ η : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    AnalyticOnNhd ℝ (blockDir_rma θ η) Set.univ := by
  unfold blockDir_rma
  refine Finset.analyticOnNhd_fun_sum _ fun ℓ _ => ?_
  have hfa := analyticOnNhd_f_attention (d := d) sees χ H dh ℓ
  have hr : AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => n * θ.read ℓ) Set.univ :=
    analyticOnNhd_matrix_mul analyticOnNhd_id analyticOnNhd_const
  have he : AnalyticOnNhd ℝ (fun n : Matrix T d ℝ => n * η.read ℓ) Set.univ :=
    analyticOnNhd_matrix_mul analyticOnNhd_id analyticOnNhd_const
  -- `n ↦ D f_ℓ(n W_read)(n η_read)`
  have h1 := analyticOnNhd_clm_apply_rma (hfa.fderiv.comp hr (Set.mapsTo_univ _ _)) he
  -- `n ↦ f_ℓ(n W_read)`
  have h2 := hfa.comp hr (Set.mapsTo_univ _ _)
  exact (analyticOnNhd_matrix_mul h1 analyticOnNhd_const).add
    (analyticOnNhd_matrix_mul h2 analyticOnNhd_const)

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `N_ε(0) = 0`. -/
private theorem rmsNorm_zero_rma : rmsNorm ε (0 : Matrix T d ℝ) = 0 := by
  ext t k
  simp [rmsNorm, rmsRow]

/-! ### Helpers: linear algebra -/

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `head_QK_dpa` of `Residual/DepthAttention.lean`, with `E` the identity): if
`(η_Q W_K^⊤ + W_Q η_K^⊤) / √d_h = 0`, then `η_Q = W_Q Γ` and `η_K = −W_K Γ^⊤` for a square
matrix `Γ`. -/
private theorem head_QK_rma {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (Q K ηQ ηK : Matrix n k ℝ) (hQ : Q.rank = Fintype.card k) (hK : K.rank = Fintype.card k)
    (hB : (Real.sqrt (Fintype.card k))⁻¹ • (ηQ * Kᵀ + Q * ηKᵀ) = 0) :
    ∃ Γ : Matrix k k ℝ, ηQ = Q * Γ ∧ ηK = -(K * Γᵀ) := by
  -- `d_h = 0`: the matrices of the head are empty
  by_cases h0 : Fintype.card k = 0
  · have : IsEmpty k := Fintype.card_eq_zero_iff.mp h0
    exact ⟨0, Matrix.ext fun _ b => isEmptyElim b, Matrix.ext fun _ b => isEmptyElim b⟩
  -- otherwise `1 / √d_h ≠ 0`, so `η_Q W_K^⊤ + W_Q η_K^⊤ = 0`
  have hc : (Real.sqrt (Fintype.card k))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)))
  have hM := (smul_eq_zero.mp hB).resolve_left hc
  -- one-sided inverses from the ranks
  obtain ⟨Q', hQ'⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hQ)
  obtain ⟨K', hK'⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hK)
  have hKt : Kᵀ * K'ᵀ = 1 := by rw [← Matrix.transpose_mul, hK', Matrix.transpose_one]
  -- multiplying on the right by `(W_K^+)^⊤`: `η_Q = W_Q Γ`
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Matrix k k ℝ, Γ = -(ηKᵀ * K'ᵀ) := ⟨_, rfl⟩
  have hZ1 : ηQ = Q * Γ := by
    calc ηQ = ηQ * (Kᵀ * K'ᵀ) := by rw [hKt, Matrix.mul_one]
      _ = (ηQ * Kᵀ + Q * ηKᵀ) * K'ᵀ - Q * (ηKᵀ * K'ᵀ) := by
          simp only [Matrix.add_mul, Matrix.mul_assoc, add_sub_cancel_right]
      _ = Q * Γ := by rw [hM, Matrix.zero_mul, zero_sub, hΓ, Matrix.mul_neg]
  -- then `W_Q (Γ W_K^⊤ + η_K^⊤) = 0`, and cancelling `W_Q`: `η_K = −W_K Γ^⊤`
  have h3 : Γ * Kᵀ + ηKᵀ = 0 := by
    calc Γ * Kᵀ + ηKᵀ = Q' * Q * (Γ * Kᵀ + ηKᵀ) := by rw [hQ', Matrix.one_mul]
      _ = Q' * (Q * Γ * Kᵀ + Q * ηKᵀ) := by simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = 0 := by rw [← hZ1, hM, Matrix.mul_zero]
  refine ⟨Γ, hZ1, ?_⟩
  rw [← Matrix.transpose_transpose ηK, eq_neg_of_add_eq_zero_right h3, Matrix.transpose_neg,
    Matrix.transpose_mul, Matrix.transpose_transpose]

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `head_VO_dpa`, with `E` and `D` the identity): if `η_V W_O + W_V η_O = 0`, then
`η_V = W_V Γ'` and `η_O = −Γ' W_O` for a square matrix `Γ'`. -/
private theorem head_VO_rma {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (V ηV : Matrix n k ℝ) (O ηO : Matrix k n ℝ) (hV : V.rank = Fintype.card k)
    (hO : O.rank = Fintype.card k) (hM : ηV * O + V * ηO = 0) :
    ∃ Γ : Matrix k k ℝ, ηV = V * Γ ∧ ηO = -(Γ * O) := by
  -- one-sided inverses from the ranks
  obtain ⟨V', hV'⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hV)
  obtain ⟨O', hO'⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hO)
  -- multiplying on the right by `W_O^+`: `η_V = W_V Γ'`
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Matrix k k ℝ, Γ = -(ηO * O') := ⟨_, rfl⟩
  have hZ1 : ηV = V * Γ := by
    calc ηV = ηV * (O * O') := by rw [hO', Matrix.mul_one]
      _ = (ηV * O + V * ηO) * O' - V * (ηO * O') := by
          simp only [Matrix.add_mul, Matrix.mul_assoc, add_sub_cancel_right]
      _ = V * Γ := by rw [hM, Matrix.zero_mul, zero_sub, hΓ, Matrix.mul_neg]
  -- then `W_V (Γ' W_O + η_O) = 0`, and cancelling `W_V`: `η_O = −Γ' W_O`
  have h3 : Γ * O + ηO = 0 := by
    calc Γ * O + ηO = V' * V * (Γ * O + ηO) := by rw [hV', Matrix.one_mul]
      _ = V' * (V * Γ * O + V * ηO) := by simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = 0 := by rw [← hZ1, hM, Matrix.mul_zero]
  exact ⟨Γ, hZ1, eq_neg_of_add_eq_zero_right h3⟩

/-- **Proof of Lemma A.27 under pre-RMSNorm, attention blocks, the flat directions of `J_0`:**
let `ε > 0` and let token `t₂` see itself and another token `t₁`. Under the conditions of the
lemma, a direction `η` with `(J_0 η)(x) = 0` at every input `x` has `η_E = E Y` and
`η_D = −Y D` for one antisymmetric matrix `Y`, and in every block its reads and its writes are
those of the directions of the changes of basis inside the heads. -/
theorem smallWritesLimitNorm_eq_zero_attention_rmsNorm (hε : 0 < ε) (t₁ t₂ : T) (h12 : t₁ ≠ t₂)
    (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hθ : SmallWritesGenericAttentionRMS θ)
    (η : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hη : ∀ x, smallWritesLimitNorm (Arch.attention sees (rmsNorm ε) H dh) θ η x = 0) :
    ∃ (Y : Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D)
        ∧ (∀ ℓ, η.read ℓ = (headDirQK θ Γ + headDirVO θ Γ').read ℓ)
        ∧ (∀ ℓ, η.write ℓ = (headDirQK θ Γ + headDirVO θ Γ').write ℓ) := by
  classical
  have : Nonempty T := ⟨t₁⟩
  -- the blocks are analytic, hence `C¹`
  have hf : ∀ ℓ, ContDiff ℝ 1 ((Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).f ℓ) :=
    fun ℓ => (analyticOnNhd_f_attention (d := d) sees (rmsNorm ε) H dh ℓ).contDiff
  -- Steps 1 to 3: `Y` antisymmetric, `η_E = E Y`, `η_D = −Y D`, and `D_θ g(n) η = 0` at every
  -- `n = N_ε(x E)`
  obtain ⟨Y, hYa, hEY, hDY, hF⟩ :=
    exists_antisymm_of_smallWritesLimitNorm_rmsNorm hε rfl hf θ hθ.rank_E hθ.rank_D η hη
  -- the continuation: `x ↦ x E` is onto (a left inverse `B` of `E`), so `D_θ g(n) η = 0` on the
  -- range of `N_ε`, an open set around `N_ε(0) = 0`; `n ↦ D_θ g(n) η` is analytic, so it
  -- vanishes everywhere
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hθ.rank_E)
  have hev : blockDir_rma θ η =ᶠ[𝓝 0] 0 :=
    Filter.eventually_of_mem ((isOpenMap_rmsNorm (T := T) (d := d) hε).isOpen_range.mem_nhds
      ⟨0, rmsNorm_zero_rma⟩) fun n hn => by
        obtain ⟨h, hh⟩ := hn
        have e := hF (h * B)
        rw [Matrix.mul_assoc h B θ.E, hB, Matrix.mul_one, hh] at e
        exact e
  have hall : ∀ n, blockDir_rma θ η n = 0 := fun n =>
    (analyticOnNhd_blockDir_rma θ η).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ 0) hev (Set.mem_univ n)
  -- the family of all heads, with `E` and `D` replaced by the identity: along `τ η` the curves
  -- `Γ_p(τ)`, `C_p(τ)` of the heads `p = (ℓ, i)`, and the output
  -- `∑_p P(n Γ_p(τ) n^⊤) n C_p(τ) = ∑_ℓ f_ℓ(n W_read^ℓ(τ)) W_write^ℓ(τ)` has the derivative
  -- `D_θ g(n) η = 0` at `τ = 0`
  have hM : HasDerivAt (fun _ : ℝ => (0 : Matrix d d ℝ)) 0 0 := hasDerivAt_const 0 0
  have hBd : ∀ p : (Σ ℓ, H ℓ), HasDerivAt (fun τ => headScoreModel (moveRW_rma θ η τ) p.1 p.2)
      ((Real.sqrt (Fintype.card (dh p.1)))⁻¹
        • (wQ_rma η p.1 p.2 * (wK_rma θ p.1 p.2)ᵀ + wQ_rma θ p.1 p.2 * (wK_rma η p.1 p.2)ᵀ)) 0 :=
    fun p => hasDerivAt_headScoreModel_rma θ η p.1 p.2
  have hCd : ∀ p : (Σ ℓ, H ℓ), HasDerivAt (fun τ => headValueModel (moveRW_rma θ η τ) p.1 p.2)
      (wV_rma η p.1 p.2 * wO_rma θ p.1 p.2 + wV_rma θ p.1 p.2 * wO_rma η p.1 p.2) 0 :=
    fun p => hasDerivAt_headValueModel_rma θ η p.1 p.2
  have hv : ∃ v : d → ℝ,
      (∀ p : (Σ ℓ, H ℓ), headScoreModel (moveRW_rma θ η 0) p.1 p.2 *ᵥ v ≠ 0)
      ∧ (∀ p q : (Σ ℓ, H ℓ), p ≠ q → ∀ r : ℝ, headScoreModel (moveRW_rma θ η 0) p.1 p.2 *ᵥ v
          ≠ r • (headScoreModel (moveRW_rma θ η 0) q.1 q.2 *ᵥ v))
      ∧ (∀ p : (Σ ℓ, H ℓ), v ᵥ* headValueModel (moveRW_rma θ η 0) p.1 p.2 ≠ 0) := by
    rw [moveRW_rma_zero]
    exact hθ.exists_v
  have hflat : ∀ x : Matrix T d ℝ, HasDerivAt (fun τ : ℝ => x * (0 : Matrix d d ℝ)
      + ∑ p : (Σ ℓ, H ℓ), attnWeights sees (x * headScoreModel (moveRW_rma θ η τ) p.1 p.2 * xᵀ)
        * x * headValueModel (moveRW_rma θ η τ) p.1 p.2) 0 0 := by
    intro x
    simp only [Matrix.mul_zero, zero_add, sum_heads_eq_rma]
    exact (HasDerivAt.fun_sum (u := Finset.univ) fun ℓ _ =>
      hasDerivAt_block_rma θ η x ℓ).congr_deriv (hall x)
  -- Step 2 for the family of all heads: the derivatives of every `Γ_p` and every `C_p` vanish
  obtain ⟨-, hBC⟩ := attnFamily_rigid (J := Σ ℓ, H ℓ) t₁ t₂ h12 hs2 hs1 _ _ _ _ _ _ hM hBd hCd
    hv hflat
  -- every head: `η_Q = W_Q Γ`, `η_K = −W_K Γ^⊤`, `η_V = W_V Γ'`, `η_O = −Γ' W_O`
  choose Γ hΓQ hΓK using fun ℓ (i : H ℓ) => head_QK_rma (wQ_rma θ ℓ i) (wK_rma θ ℓ i)
    (wQ_rma η ℓ i) (wK_rma η ℓ i) (hθ.rank_Q ℓ i) (hθ.rank_K ℓ i) (hBC ⟨ℓ, i⟩).1
  choose Γ' hΓV hΓO using fun ℓ (i : H ℓ) => head_VO_rma (wV_rma θ ℓ i) (wV_rma η ℓ i)
    (wO_rma θ ℓ i) (wO_rma η ℓ i) (hθ.rank_V ℓ i) (hθ.rank_O ℓ i) (hBC ⟨ℓ, i⟩).2
  refine ⟨Y, Γ, Γ', hYa, hEY, hDY, fun ℓ => ?_, fun ℓ => ?_⟩
  -- assemble the reads entry by entry: query, key and value columns of head `i`
  · ext a ⟨i, k | k | k⟩
    · change η.read ℓ a (i, Sum.inl k) = (wQ_rma θ ℓ i * Γ ℓ i) a k + 0
      rw [add_zero]
      exact congrFun (congrFun (hΓQ ℓ i) a) k
    · change η.read ℓ a (i, Sum.inr (Sum.inl k)) = -((wK_rma θ ℓ i * (Γ ℓ i)ᵀ) a k) + 0
      rw [add_zero]
      exact congrFun (congrFun (hΓK ℓ i) a) k
    · change η.read ℓ a (i, Sum.inr (Sum.inr k)) = 0 + (wV_rma θ ℓ i * Γ' ℓ i) a k
      rw [zero_add]
      exact congrFun (congrFun (hΓV ℓ i) a) k
  -- the writes: the output rows of head `i`
  · ext ⟨i, k⟩ b
    change η.write ℓ (i, k) b = 0 + -((Γ' ℓ i * wO_rma θ ℓ i) k b)
    rw [zero_add]
    exact congrFun (congrFun (hΓO ℓ i) k) b


/-! ### Helpers: the space of the flat directions of `J_0` -/

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- Helper (as `flatEDLin_dpa` of `Residual/DepthAttention.lean`): the directions
`Y ↦ (E Y, 0, 0, −Y D)` of one change of basis at all hidden states, as a linear map. -/
private def flatEDLin_rma {A : Arch T d L} (θ : Params A dIn dOut) :
    Matrix d d ℝ →ₗ[ℝ] Params A dIn dOut where
  toFun X := ⟨θ.E * X, 0, 0, -(X * θ.D)⟩
  map_add' X Y := by
    apply Params.ext'
    · exact Matrix.mul_add _ _ _
    · intro ℓ
      exact (add_zero 0).symm
    · intro ℓ
      exact (add_zero 0).symm
    · show -((X + Y) * θ.D) = -(X * θ.D) + -(Y * θ.D)
      rw [Matrix.add_mul, neg_add]
  map_smul' c X := by
    apply Params.ext'
    · exact Matrix.mul_smul _ _ _
    · intro ℓ
      exact (smul_zero c).symm
    · intro ℓ
      exact (smul_zero c).symm
    · show -((c • X) * θ.D) = c • -(X * θ.D)
      rw [Matrix.smul_mul, smul_neg]

/-- Helper (as `headDirQKLin_dpa`): `Γ ↦ headDirQK θ Γ` is linear. -/
private noncomputable def headDirQKLin_rma
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  toFun := headDirQK θ
  map_add' Γ Δ := by
    apply Params.ext'
    · simp [headDirQK]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp only [headDirQK, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib]
      · simp only [headDirQK, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib, neg_add]
      · simp [headDirQK]
    · intro ℓ
      simp [headDirQK]
    · simp [headDirQK]
  map_smul' c Γ := by
    apply Params.ext'
    · simp [headDirQK]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp only [headDirQK, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      · simp only [headDirQK, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_neg]
        exact congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => by ring)
      · simp [headDirQK]
    · intro ℓ
      simp [headDirQK]
    · simp [headDirQK]

/-- Helper (as `headDirVOLin_dpa`): `Γ' ↦ headDirVO θ Γ'` is linear. -/
private noncomputable def headDirVOLin_rma
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  toFun := headDirVO θ
  map_add' Γ Δ := by
    apply Params.ext'
    · simp [headDirVO]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp [headDirVO]
      · simp [headDirVO]
      · simp only [headDirVO, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib]
    · intro ℓ
      ext p b
      simp only [headDirVO, Params.add_write, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
        add_mul, Finset.sum_add_distrib, neg_add]
    · simp [headDirVO]
  map_smul' c Γ := by
    apply Params.ext'
    · simp [headDirVO]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp [headDirVO]
      · simp [headDirVO]
      · simp only [headDirVO, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    · intro ℓ
      ext p b
      simp only [headDirVO, Params.smul_write, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
        smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_neg]
      exact congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => by ring)
    · simp [headDirVO]

/-- Helper (as `finrank_headFun_dpa`): the families `Γ` of `d_h × d_h` matrices, one for each
head of each block, form a space of dimension `∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_rma :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

/-- **Lemma A.27 (Small writes), second value, for attention blocks, under the conditions of its
proof:** under pre-RMSNorm with `ε > 0`, with a token that sees itself and another token, for all
small `τ ≠ 0` the residual network has `fd(θ_τ) = P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem eventually_funDim_smallWrites_attention_rmsNorm (hε : 0 < ε) (t₁ t₂ : T)
    (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hθ : SmallWritesGenericAttentionRMS θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.attention sees (rmsNorm ε) H dh) 1 (θ.smallWrites τ)
          + (Fintype.card d * (Fintype.card d - 1) / 2
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ
            (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  classical
  -- the flat directions of `J_0` lie in the range `V` of the linear map
  -- `(Y, Γ, Γ') ↦ (E Y, 0, 0, −Y D) + headDirQK θ Γ + headDirVO θ Γ'` on antisymmetric `Y`
  -- (the first theorem)
  let Φ := ((flatEDLin_rma θ).comp (antisymmetric d).subtype).coprod
    ((headDirQKLin_rma θ).coprod (headDirVOLin_rma θ))
  have hV : ∀ η, (∀ x, smallWritesLimitNorm (Arch.attention sees (rmsNorm ε) H dh) θ η x = 0) →
      η ∈ LinearMap.range Φ := by
    intro η hη
    obtain ⟨Y, Γ, Γ', hYa, hE, hD, hr, hw⟩ :=
      smallWritesLimitNorm_eq_zero_attention_rmsNorm hε t₁ t₂ h12 hs2 hs1 θ hθ η hη
    refine ⟨(⟨Y, hYa⟩, Γ, Γ'), ?_⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply]
    apply Params.ext'
    · show θ.E * Y + ((0 : Matrix dIn d ℝ) + 0) = η.E
      rw [add_zero, add_zero, hE]
    · intro ℓ
      show 0 + (headDirQK θ Γ + headDirVO θ Γ').read ℓ = η.read ℓ
      rw [zero_add, hr ℓ]
    · intro ℓ
      show 0 + (headDirQK θ Γ + headDirVO θ Γ').write ℓ = η.write ℓ
      rw [zero_add, hw ℓ]
    · show -(Y * θ.D) + ((0 : Matrix d dOut ℝ) + 0) = η.D
      rw [add_zero, add_zero, hD]
  -- `dim V ≤ d(d−1)/2 + 2 ∑_ℓ H_ℓ d_{h,ℓ}²`, the dimension of the domain of the map
  have hdim : Module.finrank ℝ (LinearMap.range Φ)
      ≤ Fintype.card d * (Fintype.card d - 1) / 2
        + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
    have h := LinearMap.finrank_range_le Φ
    rwa [Module.finrank_prod, Module.finrank_prod, finrank_antisymmetric, finrank_headFun_rma,
      ← two_mul] at h
  -- `≥`: "The rank" of the proof of Lemma A.27 (`N_ε` and the blocks are analytic); `≤`: the
  -- upper bound for residual networks under pre-RMSNorm, as `θ ↦ θ_τ` changes neither `E` nor
  -- the reads
  filter_upwards [eventually_funDim_smallWrites_ge_norm
    (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) θ (analyticOnNhd_rmsNorm hε)
    (fun ℓ => analyticOnNhd_f_attention (d := d) sees (rmsNorm ε) H dh ℓ) _ hV] with τ hτ
  have hle := funDim_add_le_residual_attention_rmsNorm ε (θ.smallWrites τ) hθ.rank_E hθ.rank_Q
    hθ.rank_V
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at hle hdim ⊢
  omega

end Skips
