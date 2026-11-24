import SkipsLean.OneBlock.AttentionFamily
import SkipsLean.Residual.SmallWrites
import SkipsLean.Dimension.UpperBoundAttention
import SkipsLean.Network.AttentionAnalytic

/-!
# Residual networks of attention blocks at any depth: small writes

Paper (skips paper): Lemma A.27 (Small writes), its first value, for attention blocks: "Let
`d_model ≥ 2`, let `E` and `D` have rank `d_model`, and let each block, in any order and of any
width, be an attention block with heads of width at most `d_model`, causal or not, on sequences
of at least two tokens […]. For generic parameters `θ` and a number `τ`, let
`θ_τ = (E, (W_read^ℓ, τ W_write^ℓ)_ℓ, D)`. […] For all small `τ ≠ 0`, the residual network has
`fd(θ_τ) = P − d_model² − s` (no normalization, no biases)." Its proof: "let the heads of all
attention blocks form one attention block", and for a direction that is flat for the limit `J_0`
the argument of "Part (i) for attention blocks" of Theorem B.1 gives `D_θ B_j η = 0` and
`D_θ C_j η = 0` for the heads `j` of all blocks, where `E` and `D` do not vary inside the blocks,
and `η_E D + E η_D = 0`.

Here, for `Arch.attention sees id H dh` with `L` blocks (heads `H ℓ` of width `dh ℓ` in block
`ℓ`), without normalization, with a token `t₂` that sees itself and another token `t₁`:

* `headScore θ ℓ i`, `headValue θ ℓ i`: the matrices `B = E W_Q W_K^⊤ E^⊤/√d_h` and
  `C = E W_V W_O D` of head `i` of block `ℓ`.
* `SmallWritesGenericAttention θ`: the conditions on `θ` that the proof uses.
* `smallWritesLimit_eq_zero_attention`: a direction that is flat for `J_0`
  (`smallWritesLimit`, `Residual/SmallWrites.lean`) has `η_E = E X`, `η_D = −X D`, and in every
  block the reads and the writes of the directions of the changes of basis inside the heads.
* `eventually_funDim_smallWrites_attention`: `fd(θ_τ) = P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²` for all
  small `τ ≠ 0`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees] {χ : Matrix T d ℝ → Matrix T d ℝ}
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-- **The matrix `B = E W_Q W_K^⊤ E^⊤ / √d_h`** of head `i` of block `ℓ`. -/
noncomputable def headScore (θ : Params (Arch.attention sees χ H dh) dIn dOut) (ℓ : Fin L)
    (i : H ℓ) : Matrix dIn dIn ℝ :=
  (Real.sqrt (Fintype.card (dh ℓ)))⁻¹ •
    (θ.E * ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k))
      * ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))ᵀ * θ.Eᵀ)

/-- **The matrix `C = E W_V W_O D`** of head `i` of block `ℓ`. -/
def headValue (θ : Params (Arch.attention sees χ H dh) dIn dOut) (ℓ : Fin L) (i : H ℓ) :
    Matrix dIn dOut ℝ :=
  θ.E * ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
    * ((θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id) * θ.D

/-- **The conditions on `θ` in Lemma A.27, for attention blocks without normalization:** `E` and
`D` have rank `d`; the query, key, value and output matrices of every head of every block have
rank `d_h`; and some `v` has the columns `B_j v^⊤` of the heads of all blocks together nonzero
and pairwise non-collinear, and every row `v C_j` nonzero. -/
structure SmallWritesGenericAttention
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) : Prop where
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
  /-- some `v` has the `B_j v^⊤` of all heads nonzero and pairwise non-collinear and every
  `v C_j` nonzero -/
  exists_v : ∃ v : dIn → ℝ, (∀ p : (Σ ℓ, H ℓ), headScore θ p.1 p.2 *ᵥ v ≠ 0)
    ∧ (∀ p q : (Σ ℓ, H ℓ), p ≠ q → ∀ r : ℝ,
        headScore θ p.1 p.2 *ᵥ v ≠ r • (headScore θ q.1 q.2 *ᵥ v))
    ∧ (∀ p : (Σ ℓ, H ℓ), v ᵥ* headValue θ p.1 p.2 ≠ 0)

/-! ### Helpers: derivatives of matrix curves at `0` -/

/-- Helper (as `hasDerivAt_line_ob2` of `OneBlock/Attention.lean`): a line `τ ↦ M + τ N` of
matrices has the derivative `N`. -/
private theorem hasDerivAt_line_dpa {m n : Type*} [Fintype m] [Fintype n] (M N : Matrix m n ℝ) :
    HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

/-- Helper (as `hasDerivAt_mul_ob2`): the product rule for two matrix curves, entry by entry. -/
private theorem hasDerivAt_mul_dpa {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {A : ℝ → Matrix m n ℝ} {B : ℝ → Matrix n p ℝ} {A' : Matrix m n ℝ} {B' : Matrix n p ℝ}
    (hA : HasDerivAt A A' 0) (hB : HasDerivAt B B' 0) :
    HasDerivAt (fun τ => A τ * B τ) (A' * B 0 + A 0 * B') 0 := by
  refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun c => ?_
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun b _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA a) b).fun_mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB b) c)
  simp only [Matrix.add_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  exact h

/-- Helper (as `hasDerivAt_transpose_ob2`): the transpose of a matrix curve has the transposed
derivative. -/
private theorem hasDerivAt_transpose_dpa {m n : Type*} [Fintype m] [Fintype n]
    {A : ℝ → Matrix m n ℝ} {A' : Matrix m n ℝ} (hA : HasDerivAt A A' 0) :
    HasDerivAt (fun τ => (A τ)ᵀ) A'ᵀ 0 :=
  hasDerivAt_pi.2 fun b => hasDerivAt_pi.2 fun a => hasDerivAt_pi.1 (hasDerivAt_pi.1 hA a) b

/-! ### Helpers: the curves of the heads along a direction of the reads and the writes -/

/-- Helper: the parameters `θ` with the reads and the writes moved by `τ η`; `E` and `D` stay. -/
private def moveRW_dpa {A : Arch T d L} (θ η : Params A dIn dOut) (τ : ℝ) :
    Params A dIn dOut where
  E := θ.E
  read ℓ := θ.read ℓ + τ • η.read ℓ
  write ℓ := θ.write ℓ + τ • η.write ℓ
  D := θ.D

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: at `τ = 0` the moved parameters are `θ`. -/
private theorem moveRW_dpa_zero {A : Arch T d L} (θ η : Params A dIn dOut) :
    moveRW_dpa θ η 0 = θ := by
  refine Params.ext' rfl (fun ℓ => ?_) (fun ℓ => ?_) rfl
  · show θ.read ℓ + (0 : ℝ) • η.read ℓ = θ.read ℓ
    rw [zero_smul, add_zero]
  · show θ.write ℓ + (0 : ℝ) • η.write ℓ = θ.write ℓ
    rw [zero_smul, add_zero]

/-- Helper: the query matrix `W_{Q,i}` of head `i` of block `ℓ`. -/
private abbrev wQ_dpa (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (ℓ : Fin L) (i : H ℓ) : Matrix d (dh ℓ) ℝ :=
  (θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)

/-- Helper: the key matrix `W_{K,i}` of head `i` of block `ℓ`. -/
private abbrev wK_dpa (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (ℓ : Fin L) (i : H ℓ) : Matrix d (dh ℓ) ℝ :=
  (θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k))

/-- Helper: the value matrix `W_{V,i}` of head `i` of block `ℓ`. -/
private abbrev wV_dpa (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (ℓ : Fin L) (i : H ℓ) : Matrix d (dh ℓ) ℝ :=
  (θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))

/-- Helper: the output matrix `W_{O,i}` of head `i` of block `ℓ`. -/
private abbrev wO_dpa (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (ℓ : Fin L) (i : H ℓ) : Matrix (dh ℓ) d ℝ :=
  (θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id

omit [DecidableEq d] [Fintype dOut] in
/-- Helper: along the moved reads, the matrix `B` of head `i` of block `ℓ` has at `τ = 0` the
derivative `(E η_Q W_K^⊤ E^⊤ + E W_Q η_K^⊤ E^⊤) / √d_h` (`E` does not move). -/
private theorem hasDerivAt_headScore_dpa
    (θ η : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) (ℓ : Fin L)
    (i : H ℓ) :
    HasDerivAt (fun τ => headScore (moveRW_dpa θ η τ) ℓ i)
      ((Real.sqrt (Fintype.card (dh ℓ)))⁻¹ • (θ.E * wQ_dpa η ℓ i * (wK_dpa θ ℓ i)ᵀ * θ.Eᵀ
        + θ.E * wQ_dpa θ ℓ i * (wK_dpa η ℓ i)ᵀ * θ.Eᵀ)) 0 := by
  -- `B(τ) = E (W_Q + τ η_Q) (W_K + τ η_K)^⊤ E^⊤ / √d_h`
  have h := (hasDerivAt_mul_dpa (hasDerivAt_mul_dpa (hasDerivAt_mul_dpa
    (hasDerivAt_const (0 : ℝ) θ.E) (hasDerivAt_line_dpa (wQ_dpa θ ℓ i) (wQ_dpa η ℓ i)))
    (hasDerivAt_transpose_dpa (hasDerivAt_line_dpa (wK_dpa θ ℓ i) (wK_dpa η ℓ i))))
    (hasDerivAt_const (0 : ℝ) θ.Eᵀ)).const_smul (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
  exact h.congr_deriv (by simp only [zero_smul, add_zero, Matrix.zero_mul, zero_add,
    Matrix.mul_zero, Matrix.add_mul])

omit [DecidableEq d] in
/-- Helper: along the moved reads and writes, the matrix `C` of head `i` of block `ℓ` has at
`τ = 0` the derivative `E η_V W_O D + E W_V η_O D` (`E` and `D` do not move). -/
private theorem hasDerivAt_headValue_dpa
    (θ η : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) (ℓ : Fin L)
    (i : H ℓ) :
    HasDerivAt (fun τ => headValue (moveRW_dpa θ η τ) ℓ i)
      (θ.E * wV_dpa η ℓ i * wO_dpa θ ℓ i * θ.D + θ.E * wV_dpa θ ℓ i * wO_dpa η ℓ i * θ.D) 0 := by
  -- `C(τ) = E (W_V + τ η_V) (W_O + τ η_O) D`
  have h := hasDerivAt_mul_dpa (hasDerivAt_mul_dpa (hasDerivAt_mul_dpa
    (hasDerivAt_const (0 : ℝ) θ.E) (hasDerivAt_line_dpa (wV_dpa θ ℓ i) (wV_dpa η ℓ i)))
    (hasDerivAt_line_dpa (wO_dpa θ ℓ i) (wO_dpa η ℓ i))) (hasDerivAt_const (0 : ℝ) θ.D)
  exact h.congr_deriv (by simp only [zero_smul, add_zero, Matrix.zero_mul, zero_add,
    Matrix.mul_zero, Matrix.add_mul])

omit [DecidableEq d] [Fintype dOut] in
/-- Helper ("let the heads of all attention blocks form one attention block"): the heads of all
blocks give the sum of the blocks, `∑_{(ℓ,i)} P(x B_{ℓ,i} x^⊤) x C_{ℓ,i}
= ∑_ℓ f_ℓ(x E W_read^ℓ) W_write^ℓ D`. -/
private theorem sum_heads_eq_dpa
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) (x : Matrix T dIn ℝ) :
    ∑ p : (Σ ℓ, H ℓ), attnWeights sees (x * headScore θ p.1 p.2 * xᵀ) * x * headValue θ p.1 p.2
      = ∑ ℓ, (Arch.attention (T := T) (d := d) sees id H dh).f ℓ (x * θ.E * θ.read ℓ)
          * θ.write ℓ * θ.D := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  -- block `ℓ` is equation (4) on the hidden state `x E`, and `(x E) Γ (x E)^⊤ = x (E Γ E^⊤) x^⊤`
  rw [f_attention_mul]
  simp only [attentionBlock, attnHeads, headScore, headValue, Matrix.sum_mul,
    Matrix.transpose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

omit [DecidableEq d] in
/-- Helper: the term of block `ℓ` along the moved reads and writes,
`τ ↦ f_ℓ(x E (W_read + τ η_read)) (W_write + τ η_write) D`, has at `τ = 0` the derivative
`(D f_ℓ(x E W_read)(x E η_read) W_write + f_ℓ(x E W_read) η_write) D` (chain rule). -/
private theorem hasDerivAt_block_dpa
    (θ η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (x : Matrix T dIn ℝ) (ℓ : Fin L) :
    HasDerivAt (fun τ => (Arch.attention (T := T) (d := d) sees id H dh).f ℓ
        (x * θ.E * (moveRW_dpa θ η τ).read ℓ) * (moveRW_dpa θ η τ).write ℓ * θ.D)
      ((fderiv ℝ ((Arch.attention (T := T) (d := d) sees id H dh).f ℓ) (x * θ.E * θ.read ℓ)
          (x * θ.E * η.read ℓ) * θ.write ℓ
        + (Arch.attention (T := T) (d := d) sees id H dh).f ℓ (x * θ.E * θ.read ℓ)
          * η.write ℓ) * θ.D) 0 := by
  -- the line `τ ↦ x E (W_read + τ η_read)` has the derivative `x E η_read`
  have hl : HasDerivAt (fun τ : ℝ => x * θ.E * (θ.read ℓ + τ • η.read ℓ))
      (x * θ.E * η.read ℓ) 0 :=
    (hasDerivAt_mul_dpa (hasDerivAt_const (0 : ℝ) (x * θ.E))
      (hasDerivAt_line_dpa (θ.read ℓ) (η.read ℓ))).congr_deriv
      (by simp only [Matrix.zero_mul, zero_add])
  -- the chain rule through `f_ℓ`
  have hf := (differentiable_f_attention (d := d) sees id H dh ℓ
    (x * θ.E * θ.read ℓ)).hasFDerivAt
  have hc := hf.comp_hasDerivAt_of_eq (0 : ℝ) hl (by rw [zero_smul, add_zero])
  have hc' : HasDerivAt (fun τ : ℝ => (Arch.attention (T := T) (d := d) sees id H dh).f ℓ
      (x * θ.E * (θ.read ℓ + τ • η.read ℓ)))
      (fderiv ℝ ((Arch.attention (T := T) (d := d) sees id H dh).f ℓ) (x * θ.E * θ.read ℓ)
        (x * θ.E * η.read ℓ)) 0 := hc
  -- the product rule with the write and with `D`
  have h := hasDerivAt_mul_dpa (hasDerivAt_mul_dpa hc'
    (hasDerivAt_line_dpa (θ.write ℓ) (η.write ℓ))) (hasDerivAt_const (0 : ℝ) θ.D)
  exact h.congr_deriv (by simp only [zero_smul, add_zero, Matrix.mul_zero])

/-! ### Helpers: linear algebra -/

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `cancel_left_of_rank_dm` of `Residual/DepthMlp.lean`): a matrix whose rank is its
number of columns cancels on the left, via a left inverse. -/
private theorem cancel_left_of_rank_dpa {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as `head_QK_ob1` of `OneBlock/AttentionStepOne.lean`, with `X = 0`): if
`(E η_Q W_K^⊤ E^⊤ + E W_Q η_K^⊤ E^⊤) / √d_h = 0`, then `η_Q = W_Q Γ` and `η_K = −W_K Γ^⊤` for a
square matrix `Γ`. -/
private theorem head_QK_dpa {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq n]
    [DecidableEq k] (E : Matrix m n ℝ) (hE : E.rank = Fintype.card n) (Q K ηQ ηK : Matrix n k ℝ)
    (hQ : Q.rank = Fintype.card k) (hK : K.rank = Fintype.card k)
    (hB : (Real.sqrt (Fintype.card k))⁻¹ • (E * ηQ * Kᵀ * Eᵀ + E * Q * ηKᵀ * Eᵀ) = 0) :
    ∃ Γ : Matrix k k ℝ, ηQ = Q * Γ ∧ ηK = -(K * Γᵀ) := by
  -- `d_h = 0`: the matrices of the head are empty
  by_cases h0 : Fintype.card k = 0
  · have : IsEmpty k := Fintype.card_eq_zero_iff.mp h0
    exact ⟨0, Matrix.ext fun _ b => isEmptyElim b, Matrix.ext fun _ b => isEmptyElim b⟩
  -- otherwise `1 / √d_h ≠ 0`
  have hc : (Real.sqrt (Fintype.card k))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)))
  have hB' := (smul_eq_zero.mp hB).resolve_left hc
  -- one-sided inverses from the ranks
  obtain ⟨E', hE'⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hE)
  obtain ⟨Q', hQ'⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hQ)
  obtain ⟨K', hK'⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hK)
  have hEt : Eᵀ * E'ᵀ = 1 := by rw [← Matrix.transpose_mul, hE', Matrix.transpose_one]
  have hKt : Kᵀ * K'ᵀ = 1 := by rw [← Matrix.transpose_mul, hK', Matrix.transpose_one]
  -- cancelling `E` on the left and `E^⊤` on the right: `η_Q W_K^⊤ + W_Q η_K^⊤ = 0`
  have hM : ηQ * Kᵀ + Q * ηKᵀ = 0 := by
    calc ηQ * Kᵀ + Q * ηKᵀ = E' * E * (ηQ * Kᵀ + Q * ηKᵀ) * (Eᵀ * E'ᵀ) := by
          rw [hE', hEt, Matrix.one_mul, Matrix.mul_one]
      _ = E' * (E * ηQ * Kᵀ * Eᵀ + E * Q * ηKᵀ * Eᵀ) * E'ᵀ := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hB', Matrix.mul_zero, Matrix.zero_mul]
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
/-- Helper (as `head_VO_ob1` of `OneBlock/AttentionStepOne.lean`, with `X = Y = 0`): if
`E η_V W_O D + E W_V η_O D = 0`, then `η_V = W_V Γ'` and `η_O = −Γ' W_O` for a square matrix
`Γ'`. -/
private theorem head_VO_dpa {m n k p : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype p]
    [DecidableEq n] [DecidableEq k] (E : Matrix m n ℝ) (hE : E.rank = Fintype.card n)
    (D : Matrix n p ℝ) (hD : D.rank = Fintype.card n) (V ηV : Matrix n k ℝ)
    (O ηO : Matrix k n ℝ) (hV : V.rank = Fintype.card k) (hO : O.rank = Fintype.card k)
    (hC : E * ηV * O * D + E * V * ηO * D = 0) :
    ∃ Γ : Matrix k k ℝ, ηV = V * Γ ∧ ηO = -(Γ * O) := by
  -- one-sided inverses from the ranks
  obtain ⟨E', hE'⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hE)
  obtain ⟨D', hD'⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hD)
  obtain ⟨V', hV'⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hV)
  obtain ⟨O', hO'⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hO)
  -- cancelling `E` on the left and `D` on the right: `η_V W_O + W_V η_O = 0`
  have hM : ηV * O + V * ηO = 0 := by
    calc ηV * O + V * ηO = E' * E * (ηV * O + V * ηO) * (D * D') := by
          rw [hE', hD', Matrix.one_mul, Matrix.mul_one]
      _ = E' * (E * ηV * O * D + E * V * ηO * D) * D' := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hC, Matrix.mul_zero, Matrix.zero_mul]
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

/-- **Proof of Lemma A.27, attention blocks without normalization, the flat directions of
`J_0`:** let token `t₂` see itself and another token `t₁`. Under the conditions of the lemma, a
direction `η` with `(J_0 η)(x) = 0` at every input `x` has `η_E = E X` and `η_D = −X D` for one
matrix `X`, and in every block its reads and its writes are those of the directions of the
changes of basis inside the heads. -/
theorem smallWritesLimit_eq_zero_attention (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂)
    (hs1 : sees t₂ t₁) (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hθ : SmallWritesGenericAttention θ)
    (η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hη : ∀ x, smallWritesLimit (Arch.attention sees id H dh) θ η x = 0) :
    ∃ (X : Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      η.E = θ.E * X ∧ η.D = -(X * θ.D)
        ∧ (∀ ℓ, η.read ℓ = (headDirQK θ Γ + headDirVO θ Γ').read ℓ)
        ∧ (∀ ℓ, η.write ℓ = (headDirQK θ Γ + headDirVO θ Γ').write ℓ) := by
  classical
  -- the heads of all blocks form one family; along `τ η` the curves are `M(τ) = E D + τ ψ_M`
  -- with `ψ_M = η_E D + E η_D`, and the `B_p(τ)`, `C_p(τ)` of the heads `p = (ℓ, i)` with the
  -- reads and the writes moved by `τ η` (`E` and `D` do not move inside the blocks). The output
  -- `x M(τ) + ∑_p P(x B_p(τ) x^⊤) x C_p(τ)` is `x M(τ) + ∑_ℓ f_ℓ(x E W_read^ℓ(τ)) W_write^ℓ(τ) D`,
  -- whose derivative at `τ = 0` is `(J_0 η)(x) = 0`
  have hflat : ∀ x : Matrix T dIn ℝ, HasDerivAt (fun τ : ℝ =>
      x * (θ.E * θ.D + τ • (η.E * θ.D + θ.E * η.D))
        + ∑ p : (Σ ℓ, H ℓ), attnWeights sees (x * headScore (moveRW_dpa θ η τ) p.1 p.2 * xᵀ)
          * x * headValue (moveRW_dpa θ η τ) p.1 p.2) 0 0 := by
    intro x
    simp only [sum_heads_eq_dpa]
    have hd := (hasDerivAt_mul_dpa (hasDerivAt_const (0 : ℝ) x)
      (hasDerivAt_line_dpa (θ.E * θ.D) (η.E * θ.D + θ.E * η.D))).add
      (HasDerivAt.fun_sum (u := Finset.univ) fun ℓ _ => hasDerivAt_block_dpa θ η x ℓ)
    refine hd.congr_deriv ?_
    rw [Matrix.zero_mul, zero_add]
    exact hη x
  -- Step 2 for the family of all heads: `ψ_M = 0`, and `D B_p = 0`, `D C_p = 0` for every head
  have hB : ∀ p : (Σ ℓ, H ℓ), HasDerivAt (fun τ => headScore (moveRW_dpa θ η τ) p.1 p.2)
      ((Real.sqrt (Fintype.card (dh p.1)))⁻¹
        • (θ.E * wQ_dpa η p.1 p.2 * (wK_dpa θ p.1 p.2)ᵀ * θ.Eᵀ
          + θ.E * wQ_dpa θ p.1 p.2 * (wK_dpa η p.1 p.2)ᵀ * θ.Eᵀ)) 0 :=
    fun p => hasDerivAt_headScore_dpa θ η p.1 p.2
  have hC : ∀ p : (Σ ℓ, H ℓ), HasDerivAt (fun τ => headValue (moveRW_dpa θ η τ) p.1 p.2)
      (θ.E * wV_dpa η p.1 p.2 * wO_dpa θ p.1 p.2 * θ.D
        + θ.E * wV_dpa θ p.1 p.2 * wO_dpa η p.1 p.2 * θ.D) 0 :=
    fun p => hasDerivAt_headValue_dpa θ η p.1 p.2
  have hv : ∃ v : dIn → ℝ,
      (∀ p : (Σ ℓ, H ℓ), headScore (moveRW_dpa θ η 0) p.1 p.2 *ᵥ v ≠ 0)
      ∧ (∀ p q : (Σ ℓ, H ℓ), p ≠ q → ∀ r : ℝ, headScore (moveRW_dpa θ η 0) p.1 p.2 *ᵥ v
          ≠ r • (headScore (moveRW_dpa θ η 0) q.1 q.2 *ᵥ v))
      ∧ (∀ p : (Σ ℓ, H ℓ), v ᵥ* headValue (moveRW_dpa θ η 0) p.1 p.2 ≠ 0) := by
    rw [moveRW_dpa_zero]
    exact hθ.exists_v
  obtain ⟨hM, hBC⟩ := attnFamily_rigid (J := Σ ℓ, H ℓ) t₁ t₂ h12 hs2 hs1 _ _ _ _ _ _
    (hasDerivAt_line_dpa (θ.E * θ.D) (η.E * θ.D + θ.E * η.D)) hB hC hv hflat
  -- `η_E D + E η_D = 0`: with a right inverse `R` of `D`, `X = -(η_D R)`
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hθ.rank_D)
  have h1 : η.E + θ.E * (η.D * R) = 0 := by
    have h := congrArg (· * R) hM
    simpa only [Matrix.add_mul, Matrix.mul_assoc, hR, Matrix.mul_one, Matrix.zero_mul] using h
  have hE : η.E = θ.E * -(η.D * R) := by
    rw [Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left h1
  -- then `E η_D = -η_E D = E (-(X D))`
  have hD : θ.E * η.D = θ.E * -(-(η.D * R) * θ.D) := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← hE]
    exact eq_neg_of_add_eq_zero_right hM
  -- every head: `η_Q = W_Q Γ`, `η_K = −W_K Γ^⊤`, `η_V = W_V Γ'`, `η_O = −Γ' W_O`
  choose Γ hΓQ hΓK using fun ℓ (i : H ℓ) => head_QK_dpa θ.E hθ.rank_E (wQ_dpa θ ℓ i)
    (wK_dpa θ ℓ i) (wQ_dpa η ℓ i) (wK_dpa η ℓ i) (hθ.rank_Q ℓ i) (hθ.rank_K ℓ i) (hBC ⟨ℓ, i⟩).1
  choose Γ' hΓV hΓO using fun ℓ (i : H ℓ) => head_VO_dpa θ.E hθ.rank_E θ.D hθ.rank_D
    (wV_dpa θ ℓ i) (wV_dpa η ℓ i) (wO_dpa θ ℓ i) (wO_dpa η ℓ i) (hθ.rank_V ℓ i)
    (hθ.rank_O ℓ i) (hBC ⟨ℓ, i⟩).2
  refine ⟨-(η.D * R), Γ, Γ', hE, cancel_left_of_rank_dpa θ.E hθ.rank_E hD, fun ℓ => ?_,
    fun ℓ => ?_⟩
  -- assemble the reads entry by entry: query, key and value columns of head `i`
  · ext a ⟨i, k | k | k⟩
    · change η.read ℓ a (i, Sum.inl k) = (wQ_dpa θ ℓ i * Γ ℓ i) a k + 0
      rw [add_zero]
      exact congrFun (congrFun (hΓQ ℓ i) a) k
    · change η.read ℓ a (i, Sum.inr (Sum.inl k)) = -((wK_dpa θ ℓ i * (Γ ℓ i)ᵀ) a k) + 0
      rw [add_zero]
      exact congrFun (congrFun (hΓK ℓ i) a) k
    · change η.read ℓ a (i, Sum.inr (Sum.inr k)) = 0 + (wV_dpa θ ℓ i * Γ' ℓ i) a k
      rw [zero_add]
      exact congrFun (congrFun (hΓV ℓ i) a) k
  -- the writes: the output rows of head `i`
  · ext ⟨i, k⟩ b
    change η.write ℓ (i, k) b = 0 + -((Γ' ℓ i * wO_dpa θ ℓ i) k b)
    rw [zero_add]
    exact congrFun (congrFun (hΓO ℓ i) k) b

/-- **Lemma A.27 (Small writes), first value, for attention blocks, under the conditions of its
proof:** with a token that sees itself and another token, for all small `τ ≠ 0` the residual
network has `fd(θ_τ) = P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem eventually_funDim_smallWrites_attention (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂)
    (hs1 : sees t₂ t₁) (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hθ : SmallWritesGenericAttention θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.attention sees id H dh) 1 (θ.smallWrites τ)
          + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ
            (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

end Skips
