import SkipsLean.Network.AttentionAnalytic
import SkipsLean.Symmetry.AttentionHeads
import SkipsLean.OneBlock.Tanh
import SkipsLean.Generic.Params

/-!
# The one-block theorem for an attention block: the reduction and Step 2

Paper (dimension paper): Theorem 5.1 (Theorem C.1 in the appendix) for an attention block:
"Let `d_model ≥ 2` and `d_in, d_out ≥ d_model`, let inputs range over all of `ℝ^{T × d_in}`, and
consider networks with one block, without normalization and without biases. The block is […] an
attention block of `H` heads of width `d_h ≤ d_model` with `H d_h ≥ d_model`, causal or not, on
sequences of at least two tokens. At generic parameters the functional dimension is
`P − 2 d_model² − s`", with `s = 2 H d_h²` for an attention block. The skips paper, Theorem B.1
(i), has the same block with a skip ("Part (i) for attention blocks", with `M = E D` "only in the
residual network"); the statements here are for any stream matrix `S 0`, so they serve both.

The proof, "Attention blocks". Reduction: with `B_i = E W_{Q,i} W_{K,i}^⊤ E^⊤ / √d_h`,
`C_i = E W_{V,i} W_{O,i} D`, `S = ∑_i C_i`: "Head `i` gives token `t` the scores `x_t B_i x_s^⊤`
and the weights `a_ts^{(i)}`, their softmax over the tokens `s` that token `t` sees, and the
output at token `t` is `∑_i ∑_s a_ts^{(i)} x_s C_i`. So the parameters enter only through these
matrices. We use inputs of two kinds: with a causal mask, any sequence, whose second token sees
only the first two; without a mask, sequences whose tokens other than the second all equal the
first. Let `k` be the number of tokens other than the second that the second token sees […].
With `u = x_2` and `v = x_2 − x_1`, head `i` puts the weight `1/(1 + k e^{−u B_i v^⊤})` on the
second token and the rest on the copies of the first, and `1/(1 + e^{−z}) = ½ + ½ tanh(z/2)`
gives the output at the second token
`y_2 = u S − ½ v S + ½ ∑_i tanh(½ (u B_i v^⊤ − log k)) v C_i`  (8)."
Step 2: "For generic parameters and generic `v` the columns `B_i v^⊤` are nonzero and pairwise
non-collinear, since `d_model ≥ 2`, and every row `v C_i` is nonzero. For such a `v`, (8) is, as
a function of `u`, the function `G` of Lemma C.3 with one tanh hidden unit per head: unit `i` has
the read column `½ B_i v^⊤`, the bias `−½ log k` and the write row `½ v C_i`, the linear term is
`u S`, and the constant is `−½ v S`. […] Lemma C.3 for tanh shows that all of these vanish. This
holds for all `v` in an open set, so `D_θ B_i η = 0` and `D_θ C_i η = 0` for every head."

Stated here for `Arch.attention sees id H dh` with one block (`Network/Attention.lean`). The
mask enters through one token `t₂` that sees itself and another token `t₁` (the paper's second
and first token: `t₂ = 1`, `t₁ = 0` under the causal mask; any two tokens without a mask). The
inputs of the proof have the row `u` at `t₂` and the row `u − v` at every other token, and the
paper's `k` is the number of tokens other than `t₂` that `t₂` sees.

* `attnQ`, `attnK`, `attnV`, `attnO`: the four matrices of head `i` of the one block.
* `attnScore θ i`, `attnValue θ i`: the matrices `B_i`, `C_i`; `dAttnScore θ η i`,
  `dAttnValue θ η i`: their derivatives along a direction `η` of the parameters.
* `eval_attention_oneBlock`: the reduction, for any stream matrix; `eval_attention_two_tokens`:
  equation (8).
* `OneBlockGenericAttention θ`: the conditions on `θ` that the proof uses.
* `flat_attention_oneBlock_keeps`: Step 2, a flat direction keeps `E S_0 D`, every `B_i` and
  every `C_i` to first order.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees] {χ : Matrix T d ℝ → Matrix T d ℝ}
variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-- The query matrix `W_{Q,i}` of head `i` of the one block. -/
abbrev attnQ (θ : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) : Matrix d (dh 0) ℝ :=
  (θ.read 0).submatrix id fun k : dh 0 => (i, Sum.inl k)

/-- The key matrix `W_{K,i}` of head `i` of the one block. -/
abbrev attnK (θ : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) : Matrix d (dh 0) ℝ :=
  (θ.read 0).submatrix id fun k : dh 0 => (i, Sum.inr (Sum.inl k))

/-- The value matrix `W_{V,i}` of head `i` of the one block. -/
abbrev attnV (θ : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) : Matrix d (dh 0) ℝ :=
  (θ.read 0).submatrix id fun k : dh 0 => (i, Sum.inr (Sum.inr k))

/-- The output matrix `W_{O,i}` of head `i` of the one block. -/
abbrev attnO (θ : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) : Matrix (dh 0) d ℝ :=
  (θ.write 0).submatrix (fun k : dh 0 => (i, k)) id

/-- **The matrix `B_i = E W_{Q,i} W_{K,i}^⊤ E^⊤ / √d_h`** of head `i` of the one block. -/
noncomputable def attnScore (θ : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) :
    Matrix dIn dIn ℝ :=
  (Real.sqrt (Fintype.card (dh 0)))⁻¹ • (θ.E * attnQ θ i * (attnK θ i)ᵀ * θ.Eᵀ)

/-- **The matrix `C_i = E W_{V,i} W_{O,i} D`** of head `i` of the one block. -/
def attnValue (θ : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) :
    Matrix dIn dOut ℝ :=
  θ.E * attnV θ i * attnO θ i * θ.D

/-- **`D_θ B_i η`:** the derivative of `B_i` at `θ` along the direction `η`. -/
noncomputable def dAttnScore (θ η : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) :
    Matrix dIn dIn ℝ :=
  (Real.sqrt (Fintype.card (dh 0)))⁻¹ •
    (η.E * attnQ θ i * (attnK θ i)ᵀ * θ.Eᵀ + θ.E * attnQ η i * (attnK θ i)ᵀ * θ.Eᵀ
      + θ.E * attnQ θ i * (attnK η i)ᵀ * θ.Eᵀ + θ.E * attnQ θ i * (attnK θ i)ᵀ * η.Eᵀ)

/-- **`D_θ C_i η`:** the derivative of `C_i` at `θ` along the direction `η`. -/
def dAttnValue (θ η : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) :
    Matrix dIn dOut ℝ :=
  η.E * attnV θ i * attnO θ i * θ.D + θ.E * attnV η i * attnO θ i * θ.D
    + θ.E * attnV θ i * attnO η i * θ.D + θ.E * attnV θ i * attnO θ i * η.D


/-! ### Helpers: derivatives of matrix curves at `0` -/

/-- Helper: a line `τ ↦ M + τ N` of matrices has the derivative `N`. -/
private theorem hasDerivAt_line_ob2 {m n : Type*} [Fintype m] [Fintype n] (M N : Matrix m n ℝ) :
    HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

/-- Helper: the product rule for two matrix curves, entry by entry. -/
private theorem hasDerivAt_mul_ob2 {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {A : ℝ → Matrix m n ℝ} {B : ℝ → Matrix n p ℝ} {A' : Matrix m n ℝ} {B' : Matrix n p ℝ}
    (hA : HasDerivAt A A' 0) (hB : HasDerivAt B B' 0) :
    HasDerivAt (fun τ => A τ * B τ) (A' * B 0 + A 0 * B') 0 := by
  refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun c => ?_
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun b _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA a) b).fun_mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB b) c)
  simp only [Matrix.add_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  exact h

/-- Helper: the transpose of a matrix curve has the transposed derivative. -/
private theorem hasDerivAt_transpose_ob2 {m n : Type*} [Fintype m] [Fintype n]
    {A : ℝ → Matrix m n ℝ} {A' : Matrix m n ℝ} (hA : HasDerivAt A A' 0) :
    HasDerivAt (fun τ => (A τ)ᵀ) A'ᵀ 0 :=
  hasDerivAt_pi.2 fun b => hasDerivAt_pi.2 fun a => hasDerivAt_pi.1 (hasDerivAt_pi.1 hA a) b

omit [DecidableEq d] [Fintype dOut] in
/-- `dAttnScore θ η i` is the derivative of `B_i` along the line `θ + τ η`. -/
theorem hasDerivAt_attnScore (θ η : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) :
    HasDerivAt (fun τ : ℝ => attnScore (θ + τ • η) i) (dAttnScore θ η i) 0 := by
  -- `B_i(τ)` is a product of four affine curves: `E(τ) Q_i(τ) K_i(τ)ᵀ E(τ)ᵀ / √d_h`
  have hE := hasDerivAt_line_ob2 θ.E η.E
  have hQ := hasDerivAt_line_ob2 (attnQ θ i) (attnQ η i)
  have hK := hasDerivAt_transpose_ob2 (hasDerivAt_line_ob2 (attnK θ i) (attnK η i))
  have h := (hasDerivAt_mul_ob2 (hasDerivAt_mul_ob2 (hasDerivAt_mul_ob2 hE hQ) hK)
    (hasDerivAt_transpose_ob2 hE)).const_smul (Real.sqrt (Fintype.card (dh 0)))⁻¹
  exact h.congr_deriv (by simp only [zero_smul, add_zero, Matrix.add_mul, dAttnScore])

omit [DecidableEq d] in
/-- `dAttnValue θ η i` is the derivative of `C_i` along the line `θ + τ η`. -/
theorem hasDerivAt_attnValue (θ η : Params (Arch.attention sees χ H dh) dIn dOut) (i : H 0) :
    HasDerivAt (fun τ : ℝ => attnValue (θ + τ • η) i) (dAttnValue θ η i) 0 := by
  -- `C_i(τ)` is a product of four affine curves: `E(τ) V_i(τ) O_i(τ) D(τ)`
  have h := hasDerivAt_mul_ob2 (hasDerivAt_mul_ob2 (hasDerivAt_mul_ob2
    (hasDerivAt_line_ob2 θ.E η.E) (hasDerivAt_line_ob2 (attnV θ i) (attnV η i)))
    (hasDerivAt_line_ob2 (attnO θ i) (attnO η i))) (hasDerivAt_line_ob2 θ.D η.D)
  exact h.congr_deriv (by simp only [zero_smul, add_zero, Matrix.add_mul, dAttnValue])

omit [DecidableEq d] [Fintype dOut] in
/-- **Proof of Theorem C.1 for attention blocks, the reduction:** without normalization, the
network of one attention block with the stream matrix `S 0` gives the output
`x E S_0 D + ∑_i P_i(x) x C_i`, where `P_i(x)` holds the weights of the scores `x B_i x^⊤`: "the
parameters enter only through these matrices". -/
theorem eval_attention_oneBlock (S : Fin 1 → Matrix d d ℝ)
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) (x : Matrix T dIn ℝ) :
    eval (Arch.attention sees id H dh) S θ x
      = x * (θ.E * S 0 * θ.D)
        + ∑ i, attnWeights sees (x * attnScore θ i * xᵀ) * x * attnValue θ i := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.attention (T := T) (d := d) sees id H dh).χ = id := rfl
  -- `h_1 = h_0 S_0 + f(h_0 W_read) W_write` with `h_0 = x E`, and the block is equation (4)
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hχ, id_eq, id_eq, f_attention_mul]
  -- `h_0 Γ_i h_0ᵀ = x B_i xᵀ` and `P h_0 W_{V,i} W_{O,i} D = P x C_i`
  simp only [attentionBlock, attnHeads, attnScore, attnValue, attnQ, attnK, attnV, attnO,
    Matrix.add_mul, Matrix.sum_mul, Matrix.transpose_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc]

/-! ### Helpers: the row of the second token -/

/-- Helper: `1 - e^z / (e^z + k e^{z - w}) = ½ - ½ tanh(½ (w - log k))` for `k > 0`. -/
private theorem one_sub_weight_ob2 (z w k : ℝ) (hk : 0 < k) :
    1 - Real.exp z / (Real.exp z + k * Real.exp (z - w))
      = 1 / 2 - 1 / 2 * Real.tanh (1 / 2 * (w - Real.log k)) := by
  obtain ⟨y, hy⟩ : ∃ y, y = 1 / 2 * (w - Real.log k) := ⟨_, rfl⟩
  rw [← hy]
  have hw : w = y + y + Real.log k := by rw [hy]; ring
  have he : Real.exp w = Real.exp y * Real.exp y * k := by
    rw [hw, Real.exp_add, Real.exp_add, Real.exp_log hk]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_sub, he, Real.exp_neg]
  have h1 := Real.exp_pos z
  have h2 := Real.exp_pos y
  field_simp
  ring

/-- Helper: a probability vector `p` against the rows `u` at `t₂` and `u - v` elsewhere gives
`u - (1 - p_{t₂}) v`. -/
private theorem vecMul_rows_ob2 {m n : Type*} [Fintype m] [DecidableEq m] (t₂ : m)
    (p : m → ℝ) (hp : ∑ s, p s = 1) (X : Matrix m n ℝ) (u v : n → ℝ) (hX2 : X t₂ = u)
    (hXs : ∀ s, s ≠ t₂ → X s = u - v) :
    p ᵥ* X = u - (1 - p t₂) • v := by
  have h1 : ∑ s ∈ Finset.univ.erase t₂, p s = 1 - p t₂ := by
    rw [← hp, ← Finset.add_sum_erase _ _ (Finset.mem_univ t₂)]
    ring
  have h2 : ∑ s ∈ Finset.univ.erase t₂, p s • X s = ∑ s ∈ Finset.univ.erase t₂, p s • (u - v) :=
    Finset.sum_congr rfl fun s hs => by rw [hXs s (Finset.ne_of_mem_erase hs)]
  rw [Matrix.vecMul_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ t₂), hX2, h2,
    ← Finset.sum_smul, h1]
  module

/-- Helper: the weights of row `t₂` when `t₂` sees itself with the score `z` and every other
token with the score `z - w`: they sum to `1`, and the weight at `t₂` is `e^z / (e^z + k e^{z-w})`,
`k` the number of tokens other than `t₂` that `t₂` sees. -/
private theorem attnWeights_row_ob2 [DecidableEq T] (t₂ : T) (hs2 : sees t₂ t₂)
    (Z : Matrix T T ℝ) (z w : ℝ) (hz : Z t₂ t₂ = z) (hzw : ∀ s, s ≠ t₂ → Z t₂ s = z - w) :
    (∑ s, attnWeights sees Z t₂ s = 1) ∧ attnWeights sees Z t₂ t₂
      = Real.exp z / (Real.exp z
        + ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ) * Real.exp (z - w)) := by
  obtain ⟨den, hden⟩ : ∃ den, den = ∑ s', if sees t₂ s' then Real.exp (Z t₂ s') else 0 :=
    ⟨_, rfl⟩
  have hpos : 0 < den := by
    rw [hden]
    refine Finset.sum_pos' (fun s _ => ?_) ⟨t₂, Finset.mem_univ _, ?_⟩
    · split_ifs <;> positivity
    · rw [ite_eq_left hs2]
      exact Real.exp_pos _
  -- the denominator is `e^z + k e^{z - w}`
  have hden' : den = Real.exp z
      + ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ) * Real.exp (z - w) := by
    have hs : ∀ s, (if sees t₂ s then Real.exp (Z t₂ s) else 0)
        = (if s = t₂ then Real.exp z else 0)
          + (if sees t₂ s ∧ s ≠ t₂ then Real.exp (z - w) else 0) := by
      intro s
      by_cases h : s = t₂
      · subst h
        simp [hs2, hz]
      · by_cases hst : sees t₂ s <;> simp [h, hst, hzw s h]
    rw [hden, Finset.sum_congr rfl fun s _ => hs s, Finset.sum_add_distrib, Finset.sum_ite_eq',
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ite_eq_left (Finset.mem_univ t₂)]
  have hP : ∀ s, attnWeights sees Z t₂ s
      = (if sees t₂ s then Real.exp (Z t₂ s) else 0) / den := by
    intro s
    simp only [attnWeights, Matrix.of_apply, ← hden]
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_congr rfl fun s _ => hP s, ← Finset.sum_div, ← hden, div_self hpos.ne']
  · rw [hP, ite_eq_left hs2, hz, hden']

/-- Helper: row `t₂` of `P_i(x) x` at the input with the row `u` at `t₂` and `u - v` elsewhere is
`u - (½ - ½ tanh(½ (u B v^⊤ - log k))) v`. -/
private theorem row_two_tokens_ob2 [DecidableEq T] (t₁ t₂ : T) (h12 : t₁ ≠ t₂)
    (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) (B : Matrix dIn dIn ℝ) (u v : dIn → ℝ) :
    (attnWeights sees ((Matrix.of fun t => if t = t₂ then u else u - v : Matrix T dIn ℝ) * B
        * (Matrix.of fun t => if t = t₂ then u else u - v : Matrix T dIn ℝ)ᵀ)
      * (Matrix.of fun t => if t = t₂ then u else u - v : Matrix T dIn ℝ)) t₂
      = u - ((1 / 2 : ℝ) - (1 / 2 : ℝ) * Real.tanh ((1 / 2) * (u ⬝ᵥ (B *ᵥ v)
          - Real.log ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ)))) • v := by
  obtain ⟨X, hX⟩ : ∃ X : Matrix T dIn ℝ, X = Matrix.of fun t => if t = t₂ then u else u - v :=
    ⟨_, rfl⟩
  rw [← hX]
  have hX2 : X t₂ = u := by
    rw [hX]
    exact ite_eq_left rfl
  have hXs : ∀ s, s ≠ t₂ → X s = u - v := fun s hs => by
    rw [hX]
    exact ite_eq_right hs
  -- the scores of row `t₂`: `u B uᵀ` at `t₂`, `u B (u - v)ᵀ` elsewhere
  have hZ : ∀ s, (X * B * Xᵀ) t₂ s = u ⬝ᵥ (B *ᵥ X s) := by
    intro s
    rw [Matrix.mul_mul_apply, Matrix.transpose_transpose, hX2]
  have hk : 0 < ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ) :=
    Nat.cast_pos.2 (Finset.card_pos.2 ⟨t₁, Finset.mem_filter.2 ⟨Finset.mem_univ _, hs1, h12⟩⟩)
  obtain ⟨h1, h2⟩ := attnWeights_row_ob2 t₂ hs2 (X * B * Xᵀ) (u ⬝ᵥ (B *ᵥ u)) (u ⬝ᵥ (B *ᵥ v))
    (by rw [hZ, hX2])
    (fun s hs => by rw [hZ, hXs s hs, Matrix.mulVec_sub, dotProduct_sub])
  rw [Matrix.mul_apply_eq_vecMul, vecMul_rows_ob2 t₂ _ h1 X u v hX2 hXs, h2,
    one_sub_weight_ob2 _ _ _ hk]

/-- Helper: row `t` of `A + ∑_i F_i`. -/
private theorem row_add_sum_ob2 {ι m n : Type*} [Fintype ι] (A : Matrix m n ℝ)
    (F : ι → Matrix m n ℝ) (t : m) :
    (A + ∑ i, F i) t = A t + ∑ i, F i t := by
  ext o
  rw [Matrix.add_apply, Matrix.sum_apply, Pi.add_apply, Finset.sum_apply]

omit [DecidableEq d] [Fintype dOut] in
/-- **Equation (8):** let token `t₂` see itself and another token `t₁`, and let `k` be the number
of tokens other than `t₂` that `t₂` sees. At the input with the row `u` at `t₂` and the row
`u − v` at every other token, the output at `t₂` is
`u (E S_0 D + ∑_i C_i) − ½ v ∑_i C_i + ½ ∑_i tanh(½ (u B_i v^⊤ − log k)) v C_i`. -/
theorem eval_attention_two_tokens [DecidableEq T] (S : Fin 1 → Matrix d d ℝ) (t₁ t₂ : T)
    (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) (u v : dIn → ℝ) :
    eval (Arch.attention sees id H dh) S θ (Matrix.of fun t => if t = t₂ then u else u - v) t₂
      = u ᵥ* (θ.E * S 0 * θ.D + ∑ i, attnValue θ i) - (1 / 2 : ℝ) • (v ᵥ* ∑ i, attnValue θ i)
        + ∑ i, ((1 / 2 : ℝ) * Real.tanh ((1 / 2) * (u ⬝ᵥ (attnScore θ i *ᵥ v)
            - Real.log ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ))))
          • (v ᵥ* attnValue θ i) := by
  -- the reduction, at row `t₂`: head `i` gives `(u - (½ - ½ tanh(…)) v) C_i`
  have hi : ∀ i, (attnWeights sees ((Matrix.of fun t => if t = t₂ then u else u - v
        : Matrix T dIn ℝ) * attnScore θ i
        * (Matrix.of fun t => if t = t₂ then u else u - v : Matrix T dIn ℝ)ᵀ)
      * (Matrix.of fun t => if t = t₂ then u else u - v : Matrix T dIn ℝ) * attnValue θ i) t₂
      = (u - ((1 / 2 : ℝ) - (1 / 2 : ℝ) * Real.tanh ((1 / 2) * (u ⬝ᵥ (attnScore θ i *ᵥ v)
          - Real.log ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ)))) • v)
        ᵥ* attnValue θ i := fun i => by
    rw [← row_two_tokens_ob2 t₁ t₂ h12 hs2 hs1 (attnScore θ i) u v]
    rfl
  have hu : (Matrix.of fun t => if t = t₂ then u else u - v : Matrix T dIn ℝ) t₂ = u :=
    ite_eq_left rfl
  rw [eval_attention_oneBlock, row_add_sum_ob2, Matrix.mul_apply_eq_vecMul, hu,
    Finset.sum_congr rfl fun i _ => hi i]
  -- collect the terms
  simp only [Matrix.vecMul_add, Matrix.vecMul_sum, Matrix.sub_vecMul, Matrix.smul_vecMul,
    sub_smul, Finset.sum_sub_distrib, Finset.smul_sum]
  abel

/-- **The conditions on `θ` in the proof of Theorem C.1 for an attention block:** `E` and `D`
have rank `d`; the query, key, value and output matrices of every head have rank `d_h`; the
queries of all heads and the write (the output matrices of all heads) have rank `d`; and some `v`
has the columns `B_i v^⊤` nonzero and pairwise non-collinear and every row `v C_i` nonzero. -/
structure OneBlockGenericAttention
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_Q : ∀ i : H 0, (attnQ θ i).rank = Fintype.card (dh 0)
  rank_K : ∀ i : H 0, (attnK θ i).rank = Fintype.card (dh 0)
  rank_V : ∀ i : H 0, (attnV θ i).rank = Fintype.card (dh 0)
  rank_O : ∀ i : H 0, (attnO θ i).rank = Fintype.card (dh 0)
  /-- the queries of all heads have rank `d` -/
  rank_queries : ((θ.read 0).submatrix id fun p : H 0 × dh 0 => (p.1, Sum.inl p.2)).rank
    = Fintype.card d
  /-- the write, which stacks the output matrices of all heads, has rank `d` -/
  rank_write : (θ.write 0).rank = Fintype.card d
  /-- some `v` has the `B_i v^⊤` nonzero and pairwise non-collinear and every `v C_i` nonzero -/
  exists_v : ∃ v : dIn → ℝ, (∀ i, attnScore θ i *ᵥ v ≠ 0)
    ∧ (∀ i j, i ≠ j → ∀ r : ℝ, attnScore θ i *ᵥ v ≠ r • (attnScore θ j *ᵥ v))
    ∧ (∀ i, v ᵥ* attnValue θ i ≠ 0)

/-! ### Helpers: Step 2 -/

/-- Helper: `τ ↦ x N(τ)` has the derivative `x N'`. -/
private theorem hasDerivAt_vecMul_ob2 {m n : Type*} [Fintype m] [Fintype n] (x : m → ℝ)
    {N : ℝ → Matrix m n ℝ} {N' : Matrix m n ℝ} (hN : HasDerivAt N N' 0) :
    HasDerivAt (fun τ => x ᵥ* N τ) (x ᵥ* N') 0 :=
  hasDerivAt_pi.2 fun b => HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hN a) b).const_mul (x a)

/-- Helper: `τ ↦ N(τ) y` has the derivative `N' y`. -/
private theorem hasDerivAt_mulVec_ob2 {m n : Type*} [Fintype m] [Fintype n] (y : n → ℝ)
    {N : ℝ → Matrix m n ℝ} {N' : Matrix m n ℝ} (hN : HasDerivAt N N' 0) :
    HasDerivAt (fun τ => N τ *ᵥ y) (N' *ᵥ y) 0 :=
  hasDerivAt_pi.2 fun a => HasDerivAt.fun_sum (u := Finset.univ) fun b _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hN a) b).mul_const (y b)

/-- Helper: the derivative at `0` of `τ ↦ x M(τ) + γ(τ) + ∑_i tanh(x c_i(τ) + β_i) a_i(τ)`, in the
form of `UnitsRigid`. -/
private theorem hasDerivAt_units_ob2 {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (x : n → ℝ) {Mf : ℝ → Matrix n k ℝ} {γf : ℝ → k → ℝ} {cf : q → ℝ → n → ℝ} (β : q → ℝ)
    {af : q → ℝ → k → ℝ} {M' : Matrix n k ℝ} {γ' : k → ℝ} {c' c0 : q → n → ℝ}
    {a' a0 : q → k → ℝ} (hM : HasDerivAt Mf M' 0) (hγ : HasDerivAt γf γ' 0)
    (hc : ∀ i, HasDerivAt (cf i) (c' i) 0) (ha : ∀ i, HasDerivAt (af i) (a' i) 0)
    (hc0 : ∀ i, cf i 0 = c0 i) (ha0 : ∀ i, af i 0 = a0 i) :
    HasDerivAt (fun τ => x ᵥ* Mf τ + γf τ + ∑ i, Real.tanh (x ⬝ᵥ cf i τ + β i) • af i τ)
      (x ᵥ* M' + γ' + ∑ i, (Real.tanh (x ⬝ᵥ c0 i + β i) • a' i
        + ((1 - Real.tanh (x ⬝ᵥ c0 i + β i) ^ 2) * (x ⬝ᵥ c' i + 0)) • a0 i)) 0 := by
  -- the chain rule through `tanh` for every unit
  have hth : ∀ i, HasDerivAt (fun τ => Real.tanh (x ⬝ᵥ cf i τ + β i))
      ((1 - Real.tanh (x ⬝ᵥ c0 i + β i) ^ 2) * (x ⬝ᵥ c' i + 0)) 0 := by
    intro i
    have hdot : HasDerivAt (fun τ => x ⬝ᵥ cf i τ + β i) (x ⬝ᵥ c' i + 0) 0 :=
      (HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
        (hasDerivAt_pi.1 (hc i) j).const_mul (x j)).add (hasDerivAt_const (0 : ℝ) (β i))
    exact (hasDerivAt_tanh _).comp_of_eq (0 : ℝ) hdot (by simp only [hc0])
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hth i).smul (ha i)
  exact (((hasDerivAt_vecMul_ob2 x hM).add hγ).add hsum).congr_deriv (by simp only [hc0, ha0])

/-- Helper: a matrix `N` with `N v = 0` for all `v` near `v₀` is `0`. -/
private theorem eq_zero_of_mulVec_ob2 {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {P : (n → ℝ) → Prop} {v₀ : n → ℝ} (hP : ∀ᶠ v in nhds v₀, P v) (N : Matrix m n ℝ)
    (h : ∀ v, P v → N *ᵥ v = 0) : N = 0 := by
  -- the kernel of `v ↦ N v` has nonempty interior, so it is everything
  have hK : LinearMap.ker (Matrix.mulVecLin N) = ⊤ := by
    refine Submodule.eq_top_of_nonempty_interior' _ ⟨v₀, ?_⟩
    exact interior_mono (fun v hv => LinearMap.mem_ker.2 (h v hv))
      (mem_interior_iff_mem_nhds.2 hP)
  ext a b
  have h1 : Pi.single b 1 ∈ LinearMap.ker (Matrix.mulVecLin N) := hK ▸ Submodule.mem_top
  have h2 := congrFun (LinearMap.mem_ker.1 h1) a
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h2
  exact h2

/-- Helper: a matrix `N` with `v N = 0` for all `v` near `v₀` is `0`. -/
private theorem eq_zero_of_vecMul_ob2 {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    {P : (m → ℝ) → Prop} {v₀ : m → ℝ} (hP : ∀ᶠ v in nhds v₀, P v) (N : Matrix m n ℝ)
    (h : ∀ v, P v → v ᵥ* N = 0) : N = 0 :=
  Matrix.transpose_eq_zero.1 (eq_zero_of_mulVec_ob2 hP Nᵀ fun v hv => by
    rw [Matrix.mulVec_transpose]
    exact h v hv)

omit [DecidableEq d] in
/-- **Proof of Theorem C.1 for attention blocks, Step 2, for any stream matrix:** let token `t₂`
see itself and another token `t₁`, and let some `v` have the columns `B_i v^⊤` nonzero and
pairwise non-collinear and every row `v C_i` nonzero. Then a flat direction `η` of the network
with the stream matrix `S 0` keeps `E S_0 D`, every `B_i` and every `C_i` to first order. -/
theorem flat_attention_oneBlock_keeps (S : Fin 1 → Matrix d d ℝ) (t₁ t₂ : T) (h12 : t₁ ≠ t₂)
    (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hv : ∃ v : dIn → ℝ, (∀ i, attnScore θ i *ᵥ v ≠ 0)
      ∧ (∀ i j, i ≠ j → ∀ r : ℝ, attnScore θ i *ᵥ v ≠ r • (attnScore θ j *ᵥ v))
      ∧ (∀ i, v ᵥ* attnValue θ i ≠ 0))
    (η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hη : η ∈ flat (Arch.attention sees id H dh) S θ) :
    η.E * S 0 * θ.D + θ.E * S 0 * η.D = 0
      ∧ ∀ i, dAttnScore θ η i = 0 ∧ dAttnValue θ η i = 0 := by
  classical
  -- along a flat direction the output at every input has the derivative `0`
  have hflat : ∀ x : Matrix T dIn ℝ, HasDerivAt
      (fun τ : ℝ => eval (Arch.attention sees id H dh) S (θ + τ • η) x) 0 0 := by
    intro x
    have hdiff := differentiable_eval (A := Arch.attention (T := T) (d := d) sees id H dh)
      (S := S) (dIn := dIn) (dOut := dOut)
      (fun ℓ => differentiable_f_attention sees id H dh ℓ) differentiable_id x
    have h0 : fderiv ℝ (fun θ' => eval (Arch.attention sees id H dh) S θ' x) θ η = 0 :=
      LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hη x)
    exact (hasDerivAt_eval_line S θ η x (hdiff θ)).congr_deriv h0
  -- the derivative of `E(τ) S_0 D(τ)`
  have hEMD : HasDerivAt (fun τ : ℝ => (θ + τ • η).E * S 0 * (θ + τ • η).D)
      (η.E * S 0 * θ.D + θ.E * S 0 * η.D) 0 :=
    (hasDerivAt_mul_ob2 (hasDerivAt_mul_ob2 (hasDerivAt_line_ob2 θ.E η.E)
      (hasDerivAt_const (0 : ℝ) (S 0))) (hasDerivAt_line_ob2 θ.D η.D)).congr_deriv
      (by simp only [zero_smul, add_zero, Matrix.mul_zero])
  -- equation (8) along the line `θ + τ η`, differentiated at `τ = 0`, for all `u` and `v`
  have hzero : ∀ u v : dIn → ℝ,
      u ᵥ* (η.E * S 0 * θ.D + θ.E * S 0 * η.D + ∑ i, dAttnValue θ η i)
        + -(1 / 2 : ℝ) • (v ᵥ* ∑ i, dAttnValue θ η i)
        + ∑ i, (Real.tanh (u ⬝ᵥ ((1 / 2 : ℝ) • (attnScore θ i *ᵥ v))
              + -(1 / 2) * Real.log ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ))
            • ((1 / 2 : ℝ) • (v ᵥ* dAttnValue θ η i))
          + ((1 - Real.tanh (u ⬝ᵥ ((1 / 2 : ℝ) • (attnScore θ i *ᵥ v))
              + -(1 / 2) * Real.log ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ))
                ^ 2)
              * (u ⬝ᵥ ((1 / 2 : ℝ) • (dAttnScore θ η i *ᵥ v)) + 0))
            • ((1 / 2 : ℝ) • (v ᵥ* attnValue θ i))) = 0 := by
    intro u v
    have hG := hasDerivAt_units_ob2 u
      (Mf := fun τ => (θ + τ • η).E * S 0 * (θ + τ • η).D + ∑ i, attnValue (θ + τ • η) i)
      (γf := fun τ => -(1 / 2 : ℝ) • (v ᵥ* ∑ i, attnValue (θ + τ • η) i))
      (cf := fun i τ => (1 / 2 : ℝ) • (attnScore (θ + τ • η) i *ᵥ v))
      (fun _ => -(1 / 2) * Real.log ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ))
      (af := fun i τ => (1 / 2 : ℝ) • (v ᵥ* attnValue (θ + τ • η) i))
      (c0 := fun i => (1 / 2 : ℝ) • (attnScore θ i *ᵥ v))
      (a0 := fun i => (1 / 2 : ℝ) • (v ᵥ* attnValue θ i))
      (hEMD.add (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hasDerivAt_attnValue θ η i))
      ((hasDerivAt_vecMul_ob2 v (HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
        hasDerivAt_attnValue θ η i)).const_smul (-(1 / 2 : ℝ)))
      (fun i => (hasDerivAt_mulVec_ob2 v (hasDerivAt_attnScore θ η i)).const_smul (1 / 2 : ℝ))
      (fun i => (hasDerivAt_vecMul_ob2 v (hasDerivAt_attnValue θ η i)).const_smul (1 / 2 : ℝ))
      (fun i => by simp only [zero_smul, add_zero]) (fun i => by simp only [zero_smul, add_zero])
    have hF := hasDerivAt_pi.1 (hflat (Matrix.of fun t => if t = t₂ then u else u - v)) t₂
    refine hG.unique (hF.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_))
    dsimp only
    -- equation (8) at `θ + τ η`
    rw [eval_attention_two_tokens S t₁ t₂ h12 hs2 hs1, neg_smul, ← sub_eq_add_neg]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have harg : u ⬝ᵥ ((1 / 2 : ℝ) • (attnScore (θ + τ • η) i *ᵥ v))
        + -(1 / 2) * Real.log ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ)
        = (1 / 2) * (u ⬝ᵥ (attnScore (θ + τ • η) i *ᵥ v)
          - Real.log ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ)) := by
      rw [dotProduct_smul, smul_eq_mul]
      ring
    rw [harg, smul_smul, mul_comm]
  -- Step 2, Lemma C.3 for tanh, at every `v` with the three properties
  have hstep : ∀ v : dIn → ℝ, (∀ i, attnScore θ i *ᵥ v ≠ 0)
      → (∀ i j, i ≠ j → ∀ r : ℝ, attnScore θ i *ᵥ v ≠ r • (attnScore θ j *ᵥ v))
      → (∀ i, v ᵥ* attnValue θ i ≠ 0)
      → η.E * S 0 * θ.D + θ.E * S 0 * η.D + ∑ i, dAttnValue θ η i = 0
        ∧ (∀ i, dAttnScore θ η i *ᵥ v = 0) ∧ (∀ i, v ᵥ* dAttnValue θ η i = 0) := by
    intro v h1 h2 h3
    have hhalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
    obtain ⟨hψM, -, hψc, -, hψa⟩ := tanh_unitsRigid dIn dOut (H 0)
      (fun i => (1 / 2 : ℝ) • (attnScore θ i *ᵥ v))
      (fun _ => -(1 / 2) * Real.log ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ))
      (fun i => (1 / 2 : ℝ) • (v ᵥ* attnValue θ i))
      (η.E * S 0 * θ.D + θ.E * S 0 * η.D + ∑ i, dAttnValue θ η i)
      (-(1 / 2 : ℝ) • (v ᵥ* ∑ i, dAttnValue θ η i))
      (fun i => (1 / 2 : ℝ) • (dAttnScore θ η i *ᵥ v)) 0
      (fun i => (1 / 2 : ℝ) • (v ᵥ* dAttnValue θ η i))
      (fun i => smul_ne_zero hhalf (h3 i)) (fun i => smul_ne_zero hhalf (h1 i))
      (fun i j hij r hr => h2 i j hij r (by
        rw [smul_comm r] at hr
        exact smul_right_injective _ hhalf hr))
      (fun x => hzero x v)
    refine ⟨hψM, fun i => ?_, fun i => ?_⟩
    · have h := congrFun hψc i
      simpa [hhalf] using h
    · have h := congrFun hψa i
      simpa [hhalf] using h
  -- the `v` with the three properties form a neighbourhood of the given one
  obtain ⟨v₀, hv1, hv2, hv3⟩ := hv
  have hB : ∀ i, Continuous fun v : dIn → ℝ => attnScore θ i *ᵥ v :=
    fun i => continuous_const.matrix_mulVec continuous_id
  have hC : ∀ i, Continuous fun v : dIn → ℝ => v ᵥ* attnValue θ i :=
    fun i => continuous_id.matrix_vecMul continuous_const
  have hnhds : ∀ᶠ v in nhds v₀, (∀ i, attnScore θ i *ᵥ v ≠ 0)
      ∧ (∀ i j, i ≠ j → ∀ r : ℝ, attnScore θ i *ᵥ v ≠ r • (attnScore θ j *ᵥ v))
      ∧ (∀ i, v ᵥ* attnValue θ i ≠ 0) := by
    refine (Filter.eventually_all.2 fun i => (hB i).continuousAt.eventually_ne (hv1 i)).and
      ((Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_).and
        (Filter.eventually_all.2 fun i => (hC i).continuousAt.eventually_ne (hv3 i)))
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hij h
    · -- non-collinearity of a pair is linear independence, an open condition
      have hli : LinearIndependent ℝ ![attnScore θ i *ᵥ v₀, attnScore θ j *ᵥ v₀] := by
        rw [linearIndependent_fin2]
        exact ⟨hv1 j, fun r h => hv2 i j hij r h.symm⟩
      have hcont : Continuous fun v : dIn → ℝ => ![attnScore θ i *ᵥ v, attnScore θ j *ᵥ v] :=
        continuous_pi (Fin.forall_fin_two.2 ⟨hB i, hB j⟩)
      refine ((hcont.tendsto v₀).eventually hli.eventually).mono fun v hv _ r h => ?_
      rw [linearIndependent_fin2] at hv
      exact hv.2 r h.symm
  -- a matrix that kills every `v` of a neighbourhood is `0`
  have hdB : ∀ i, dAttnScore θ η i = 0 := fun i =>
    eq_zero_of_mulVec_ob2 hnhds _ fun v hv => (hstep v hv.1 hv.2.1 hv.2.2).2.1 i
  have hdC : ∀ i, dAttnValue θ η i = 0 := fun i =>
    eq_zero_of_vecMul_ob2 hnhds _ fun v hv => (hstep v hv.1 hv.2.1 hv.2.2).2.2 i
  have hM := (hstep v₀ hv1 hv2 hv3).1
  simp only [hdC, Finset.sum_const_zero, add_zero] at hM
  exact ⟨hM, fun i => ⟨hdB i, hdC i⟩⟩

end Skips
