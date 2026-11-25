import SkipsLean.OneBlock.Attention
import SkipsLean.Dimension.FunctionalBiases

/-!
# The one-block theorem for an attention block with biases: the reduction and Step 2

Paper (skips paper), Theorem B.1 (i): "with biases on the embedding, the block and the readout,
counted in `P`, both values are `2 d_model` lower, and `2 d_model + 2 H d_h` lower for
attention." Its proof, "Part (i) for attention blocks", Reduction, after equation (16): "With
biases `b_E` on the embedding, `b_{Q,i}`, `b_{K,i}`, `b_{V,i}` on the queries, keys and values,
`b_O` on the output projection and `b_D` on the readout, `u B_i v^⊤` becomes
`(u B_i + β_i) v^⊤` with `β_i = (b_E W_{Q,i} + b_{Q,i}) W_{K,i}^⊤ E^⊤ / √d_h`, and the constant
`γ = ∑_i (b_E W_{V,i} + b_{V,i}) W_{O,i} D + b_O D + b_D` is added, plus `b_E D` in the residual
network. The key biases drop out, since they shift all scores of a token equally, and the value
biases enter only through `γ`, since the weights of a token sum to one." Step 2: "For such a `v`,
(16) is, as a function of `u`, a residual network with one hidden layer of tanh units, one per
head, with input weights `½ B_i v^⊤`, biases `½ (β_i v^⊤ − log k)`, output weights `½ v C_i`,
linear part `K` and constant term `γ − ½ v S`. Along a flat direction `η` these have the
derivatives `½ (D_θ B_i η) v^⊤`, `½ (D_θ β_i η) v^⊤`, `½ v (D_θ C_i η)`, `D_θ K η` and
`D_θ γ η − ½ v (D_θ S η)`, and Lemma B.3 for tanh shows that all of these vanish. This holds for
all `v` in an open set, so `D_θ B_i η = 0`, `D_θ β_i η = 0` and `D_θ C_i η = 0`; hence
`D_θ S η = 0`, `D_θ M η = D_θ K η − D_θ S η = 0` and `D_θ γ η = 0`."

Stated here for `Arch.attention sees id H dh` with one block and the biases of
`Network/Biases.lean` (the read bias is `[b_Q | b_K | b_V]`, the write bias is `b_O`), for any
stream matrix `S 0` (`0` for the skipless network, `1` for the residual one), as the twin of
`OneBlock/Attention.lean`:

* `attnBQ b i`, `attnBK b i`, `attnBV b i`: the biases of the queries, keys and values of head
  `i`; `attnScoreBias p i`: the row `β_i`; `attnConst S p`: the constant `γ`, with `b_E S_0 D`
  for the stream; `dAttnScoreBias p η i`, `dAttnConst S p η`: their derivatives along a direction
  `η` of weights and biases.
* `evalB_attention_oneBlock_row`: the reduction, at a token that sees at least one token (its
  weights then sum to one; a token that sees no token has all weights `0`).
* `evalB_attention_two_tokens`: equation (16) with biases.
* `flatB_attention_oneBlock_keeps`: Step 2, a flat direction keeps `E S_0 D`, every `B_i`, every
  `C_i`, every `β_i` and `γ` to first order.

Numeric check of the reduction and of (16) with biases: `attention_biases_check_2026-11-25.py`,
parts (a) and (a2).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees] {χ : Matrix T d ℝ → Matrix T d ℝ}
variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-- The bias `b_{Q,i}` of the queries of head `i` of the one block. -/
abbrev attnBQ (b : Biases (Arch.attention sees χ H dh) dOut) (i : H 0) : dh 0 → ℝ :=
  fun k => b.read 0 (i, Sum.inl k)

/-- The bias `b_{K,i}` of the keys of head `i` of the one block. -/
abbrev attnBK (b : Biases (Arch.attention sees χ H dh) dOut) (i : H 0) : dh 0 → ℝ :=
  fun k => b.read 0 (i, Sum.inr (Sum.inl k))

/-- The bias `b_{V,i}` of the values of head `i` of the one block. -/
abbrev attnBV (b : Biases (Arch.attention sees χ H dh) dOut) (i : H 0) : dh 0 → ℝ :=
  fun k => b.read 0 (i, Sum.inr (Sum.inr k))

/-- **The row `β_i = (b_E W_{Q,i} + b_{Q,i}) W_{K,i}^⊤ E^⊤ / √d_h`** of head `i` of the one
block with biases. -/
noncomputable def attnScoreBias (p : ParamsB (Arch.attention sees χ H dh) dIn dOut) (i : H 0) :
    dIn → ℝ :=
  (Real.sqrt (Fintype.card (dh 0)))⁻¹ •
    ((p.2.E ᵥ* attnQ p.1 i + attnBQ p.2 i) ᵥ* ((attnK p.1 i)ᵀ * p.1.Eᵀ))

/-- **The constant `γ`** of the network of one attention block with biases and the stream matrix
`S 0`: `b_E S_0 D + ∑_i (b_E W_{V,i} + b_{V,i}) W_{O,i} D + b_O D + b_D` (the paper's `γ` for
`S 0 = 0`, and "plus `b_E D` in the residual network" for `S 0 = 1`). -/
noncomputable def attnConst (S : Fin 1 → Matrix d d ℝ)
    (p : ParamsB (Arch.attention sees χ H dh) dIn dOut) : dOut → ℝ :=
  p.2.E ᵥ* (S 0 * p.1.D)
    + ∑ i, (p.2.E ᵥ* attnV p.1 i + attnBV p.2 i) ᵥ* (attnO p.1 i * p.1.D)
    + p.2.write 0 ᵥ* p.1.D + p.2.D

/-- **`D_θ β_i η`:** the derivative of `β_i` at `p = (θ, b)` along the direction `η` of weights
and biases. -/
noncomputable def dAttnScoreBias (p η : ParamsB (Arch.attention sees χ H dh) dIn dOut)
    (i : H 0) : dIn → ℝ :=
  (Real.sqrt (Fintype.card (dh 0)))⁻¹ •
    ((η.2.E ᵥ* attnQ p.1 i + p.2.E ᵥ* attnQ η.1 i + attnBQ η.2 i)
        ᵥ* ((attnK p.1 i)ᵀ * p.1.Eᵀ)
      + (p.2.E ᵥ* attnQ p.1 i + attnBQ p.2 i)
        ᵥ* ((attnK η.1 i)ᵀ * p.1.Eᵀ + (attnK p.1 i)ᵀ * η.1.Eᵀ))

/-- **`D_θ γ η`:** the derivative of the constant `γ` at `p = (θ, b)` along the direction `η` of
weights and biases, for the stream matrix `S 0`. -/
noncomputable def dAttnConst (S : Fin 1 → Matrix d d ℝ)
    (p η : ParamsB (Arch.attention sees χ H dh) dIn dOut) : dOut → ℝ :=
  η.2.E ᵥ* (S 0 * p.1.D) + p.2.E ᵥ* (S 0 * η.1.D)
    + ∑ i, ((η.2.E ᵥ* attnV p.1 i + p.2.E ᵥ* attnV η.1 i + attnBV η.2 i)
          ᵥ* (attnO p.1 i * p.1.D)
        + (p.2.E ᵥ* attnV p.1 i + attnBV p.2 i)
          ᵥ* (attnO η.1 i * p.1.D + attnO p.1 i * η.1.D))
    + (η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D) + η.2.D


/-! ### Helpers: derivatives of matrix and vector curves at `0` -/

/-- Helper: a line `τ ↦ M + τ N` of matrices has the derivative `N`. -/
private theorem hasDerivAt_line_abi {m n : Type*} [Fintype m] [Fintype n] (M N : Matrix m n ℝ) :
    HasDerivAt (fun τ : ℝ => M + τ • N) N 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  rw [one_smul] at h
  exact h

/-- Helper: a line `τ ↦ u + τ w` of vectors has the derivative `w`. -/
private theorem hasDerivAt_vline_abi {n : Type*} [Fintype n] (u w : n → ℝ) :
    HasDerivAt (fun τ : ℝ => u + τ • w) w 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add u
  rw [one_smul] at h
  exact h

/-- Helper: the product rule for two matrix curves, entry by entry. -/
private theorem hasDerivAt_mul_abi {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {A : ℝ → Matrix m n ℝ} {B : ℝ → Matrix n p ℝ} {A' : Matrix m n ℝ} {B' : Matrix n p ℝ}
    (hA : HasDerivAt A A' 0) (hB : HasDerivAt B B' 0) :
    HasDerivAt (fun τ => A τ * B τ) (A' * B 0 + A 0 * B') 0 := by
  refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun c => ?_
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun b _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA a) b).fun_mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB b) c)
  simp only [Matrix.add_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  exact h

/-- Helper: the transpose of a matrix curve has the transposed derivative. -/
private theorem hasDerivAt_transpose_abi {m n : Type*} [Fintype m] [Fintype n]
    {A : ℝ → Matrix m n ℝ} {A' : Matrix m n ℝ} (hA : HasDerivAt A A' 0) :
    HasDerivAt (fun τ => (A τ)ᵀ) A'ᵀ 0 :=
  hasDerivAt_pi.2 fun b => hasDerivAt_pi.2 fun a => hasDerivAt_pi.1 (hasDerivAt_pi.1 hA a) b

/-- Helper: the product rule for a vector curve times a matrix curve. -/
private theorem hasDerivAt_vecMul2_abi {m n : Type*} [Fintype m] [Fintype n]
    {a : ℝ → m → ℝ} {N : ℝ → Matrix m n ℝ} {a' : m → ℝ} {N' : Matrix m n ℝ}
    (ha : HasDerivAt a a' 0) (hN : HasDerivAt N N' 0) :
    HasDerivAt (fun τ => a τ ᵥ* N τ) (a' ᵥ* N 0 + a 0 ᵥ* N') 0 := by
  refine hasDerivAt_pi.2 fun b => ?_
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (hasDerivAt_pi.1 ha j).fun_mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hN j) b)
  have e : (a' ᵥ* N 0 + a 0 ᵥ* N') b = ∑ j, (a' j * N 0 j b + a 0 j * N' j b) := by
    rw [Finset.sum_add_distrib]
    rfl
  rw [e]
  exact h

/-- Helper: `τ ↦ f(τ) ⬝ v` has the derivative `f' ⬝ v`. -/
private theorem hasDerivAt_dotProduct_abi {n : Type*} [Fintype n] (v : n → ℝ) {f : ℝ → n → ℝ}
    {f' : n → ℝ} (hf : HasDerivAt f f' 0) : HasDerivAt (fun τ => f τ ⬝ᵥ v) (f' ⬝ᵥ v) 0 :=
  HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (hasDerivAt_pi.1 hf j).mul_const (v j)

/-- `dAttnScoreBias p η i` is the derivative of `β_i` along the line `p + τ η`. -/
theorem hasDerivAt_attnScoreBias (p η : ParamsB (Arch.attention sees χ H dh) dIn dOut)
    (i : H 0) :
    HasDerivAt (fun τ : ℝ => attnScoreBias (p + τ • η) i) (dAttnScoreBias p η i) 0 := by
  -- `β_i(τ) = (b_E(τ) W_{Q,i}(τ) + b_{Q,i}(τ)) W_{K,i}(τ)ᵀ E(τ)ᵀ / √d_h`: affine curves
  have hq := (hasDerivAt_vecMul2_abi (hasDerivAt_vline_abi p.2.E η.2.E)
    (hasDerivAt_line_abi (attnQ p.1 i) (attnQ η.1 i))).fun_add
    (hasDerivAt_vline_abi (attnBQ p.2 i) (attnBQ η.2 i))
  have hk := hasDerivAt_mul_abi
    (hasDerivAt_transpose_abi (hasDerivAt_line_abi (attnK p.1 i) (attnK η.1 i)))
    (hasDerivAt_transpose_abi (hasDerivAt_line_abi p.1.E η.1.E))
  have h := (hasDerivAt_vecMul2_abi hq hk).fun_const_smul (Real.sqrt (Fintype.card (dh 0)))⁻¹
  exact h.congr_deriv (by simp only [zero_smul, add_zero, dAttnScoreBias])

/-- `dAttnConst S p η` is the derivative of the constant `γ` along the line `p + τ η`. -/
theorem hasDerivAt_attnConst (S : Fin 1 → Matrix d d ℝ)
    (p η : ParamsB (Arch.attention sees χ H dh) dIn dOut) :
    HasDerivAt (fun τ : ℝ => attnConst S (p + τ • η)) (dAttnConst S p η) 0 := by
  -- `γ(τ)` is a sum of products of affine curves
  have hE := hasDerivAt_vline_abi p.2.E η.2.E
  have hD := hasDerivAt_line_abi p.1.D η.1.D
  have h1 := hasDerivAt_vecMul2_abi hE (hasDerivAt_mul_abi (hasDerivAt_const (0 : ℝ) (S 0)) hD)
  have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hasDerivAt_vecMul2_abi
    ((hasDerivAt_vecMul2_abi hE (hasDerivAt_line_abi (attnV p.1 i) (attnV η.1 i))).fun_add
      (hasDerivAt_vline_abi (attnBV p.2 i) (attnBV η.2 i)))
    (hasDerivAt_mul_abi (hasDerivAt_line_abi (attnO p.1 i) (attnO η.1 i)) hD)
  have h3 := hasDerivAt_vecMul2_abi (hasDerivAt_vline_abi (p.2.write 0) (η.2.write 0)) hD
  have h := ((h1.fun_add h2).fun_add h3).fun_add (hasDerivAt_vline_abi p.2.D η.2.D)
  exact h.congr_deriv (by simp only [zero_smul, add_zero, Matrix.zero_mul, zero_add, dAttnConst])

/-! ### Helpers: the reduction with biases -/

/-- Helper: adding to the scores a function of the row index alone does not change the
weights. -/
private theorem attnWeights_add_row_abi (Z : Matrix T T ℝ) (r : T → ℝ) :
    attnWeights sees (Z + Matrix.of fun t _ => r t) = attnWeights sees Z := by
  ext t s
  simp only [attnWeights, Matrix.of_apply, Matrix.add_apply]
  split_ifs with h
  · have e : (∑ s', if sees t s' then Real.exp (Z t s' + r t) else 0)
        = (∑ s', if sees t s' then Real.exp (Z t s') else 0) * Real.exp (r t) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s' _ => ?_
      split_ifs
      · rw [Real.exp_add]
      · rw [zero_mul]
    rw [e, Real.exp_add, mul_div_mul_right _ _ (Real.exp_pos _).ne']
  · rfl

/-- Helper (copy of `attnWeights_den_pos_ba`): the denominator of row `t` of the weights is
positive when token `t` sees some token. -/
private theorem attnWeights_den_pos_abi (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
    0 < ∑ s', if sees t s' then Real.exp (Z t s') else 0 := by
  obtain ⟨s, hs⟩ := ht
  refine Finset.sum_pos' (fun s' _ => ?_) ⟨s, Finset.mem_univ _, ?_⟩
  · split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  · simp only [hs, ite_true]
    exact Real.exp_pos _

/-- Helper (copy of `attnWeights_sum_ba`): row `t` of the weights sums to `1` when token `t` sees
some token. -/
private theorem attnWeights_sum_abi (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
    ∑ s, attnWeights sees Z t s = 1 := by
  have hS := attnWeights_den_pos_abi Z t ht
  have h1 : ∀ s, attnWeights sees Z t s = (if sees t s then Real.exp (Z t s) else 0)
      / ∑ s', if sees t s' then Real.exp (Z t s') else 0 := by
    intro s
    simp only [attnWeights, Matrix.of_apply]
    split_ifs
    · rfl
    · rw [zero_div]
  simp only [h1, ← Finset.sum_div]
  exact div_self hS.ne'

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the block of `Arch.attention` on `h W_read + b_read`, times the write: head `i` has
the queries `h W_{Q,i} + b_{Q,i}`, the keys `h W_{K,i} + b_{K,i}` and the values
`h W_{V,i} + b_{V,i}`. -/
private theorem f_attention_bias_abi
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (b : Biases (Arch.attention (T := T) (d := d) sees χ H dh) dOut) (h : Matrix T d ℝ) :
    (Arch.attention sees χ H dh).f 0 (h * θ.read 0 + Matrix.of fun _ => b.read 0) * θ.write 0
      = ∑ i, attnWeights sees ((Real.sqrt (Fintype.card (dh 0)))⁻¹ •
          ((h * attnQ θ i + Matrix.of fun _ => attnBQ b i)
            * (h * attnK θ i + Matrix.of fun _ => attnBK b i)ᵀ))
        * (h * attnV θ i + Matrix.of fun _ => attnBV b i) * attnO θ i := by
  ext t a
  simp only [Matrix.sum_apply]
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  rfl

/-- Helper: `(a P) · (b N) = a (P Nᵀ) bᵀ`. -/
private theorem dot_vecMul_abi {m n : Type*} [Fintype m] [Fintype n] (a b : m → ℝ)
    (P N : Matrix m n ℝ) : (a ᵥ* P) ⬝ᵥ (b ᵥ* N) = a ⬝ᵥ ((P * Nᵀ) *ᵥ b) := by
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

/-- Helper: an entry of `c A Bᵀ`. -/
private theorem smul_mul_transpose_apply_abi {m n : Type*} [Fintype n] (c : ℝ)
    (A B : Matrix m n ℝ) (t s : m) : (c • (A * Bᵀ)) t s = c * (A t ⬝ᵥ B s) := rfl

omit [DecidableEq d] [Fintype dOut] in
/-- Helper: the scores of head `i` with biases at `h_0 = x E + b_E` are
`x B_i xᵀ + 1 (x β_iᵀ)ᵀ` plus a function of the row index alone. -/
private theorem scores_abi (p : ParamsB (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (x : Matrix T dIn ℝ) (i : H 0) :
    (Real.sqrt (Fintype.card (dh 0)))⁻¹ •
        (((x * p.1.E + Matrix.of fun _ => p.2.E) * attnQ p.1 i
            + Matrix.of fun _ => attnBQ p.2 i)
          * ((x * p.1.E + Matrix.of fun _ => p.2.E) * attnK p.1 i
            + Matrix.of fun _ => attnBK p.2 i)ᵀ)
      = x * attnScore p.1 i * xᵀ + (Matrix.of fun _ s => (x *ᵥ attnScoreBias p i) s)
        + Matrix.of fun t _ => (Real.sqrt (Fintype.card (dh 0)))⁻¹ *
          ((x t ᵥ* (p.1.E * attnQ p.1 i) + (p.2.E ᵥ* attnQ p.1 i + attnBQ p.2 i))
            ⬝ᵥ (p.2.E ᵥ* attnK p.1 i + attnBK p.2 i)) := by
  -- the rows `q_t = x_t E W_Q + (b_E W_Q + b_Q)` and `k_s = x_s E W_K + (b_E W_K + b_K)`
  have hq : ∀ t, ((x * p.1.E + Matrix.of fun _ => p.2.E) * attnQ p.1 i
      + Matrix.of fun _ => attnBQ p.2 i : Matrix T (dh 0) ℝ) t
      = x t ᵥ* (p.1.E * attnQ p.1 i) + (p.2.E ᵥ* attnQ p.1 i + attnBQ p.2 i) := by
    intro t
    show (x t ᵥ* p.1.E + p.2.E) ᵥ* attnQ p.1 i + attnBQ p.2 i = _
    rw [Matrix.add_vecMul, Matrix.vecMul_vecMul, add_assoc]
  have hk : ∀ s, ((x * p.1.E + Matrix.of fun _ => p.2.E) * attnK p.1 i
      + Matrix.of fun _ => attnBK p.2 i : Matrix T (dh 0) ℝ) s
      = x s ᵥ* (p.1.E * attnK p.1 i) + (p.2.E ᵥ* attnK p.1 i + attnBK p.2 i) := by
    intro s
    show (x s ᵥ* p.1.E + p.2.E) ᵥ* attnK p.1 i + attnBK p.2 i = _
    rw [Matrix.add_vecMul, Matrix.vecMul_vecMul, add_assoc]
  -- `x_t B_i x_sᵀ = (x_t E W_Q) · (x_s E W_K) / √d_h`
  have hB : ∀ t s, (x * attnScore p.1 i * xᵀ) t s = (Real.sqrt (Fintype.card (dh 0)))⁻¹
      * ((x t ᵥ* (p.1.E * attnQ p.1 i)) ⬝ᵥ (x s ᵥ* (p.1.E * attnK p.1 i))) := by
    intro t s
    rw [Matrix.mul_mul_apply, Matrix.transpose_transpose, attnScore, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, dot_vecMul_abi, Matrix.transpose_mul, ← Matrix.mul_assoc]
  -- `x_s β_iᵀ = (b_E W_Q + b_Q) · (x_s E W_K) / √d_h`
  have hβ : ∀ s, (x *ᵥ attnScoreBias p i) s = (Real.sqrt (Fintype.card (dh 0)))⁻¹
      * ((p.2.E ᵥ* attnQ p.1 i + attnBQ p.2 i) ⬝ᵥ (x s ᵥ* (p.1.E * attnK p.1 i))) := by
    intro s
    show x s ⬝ᵥ attnScoreBias p i = _
    rw [attnScoreBias, dotProduct_smul, smul_eq_mul, ← Matrix.transpose_mul,
      Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, dotProduct_comm]
  ext t s
  rw [smul_mul_transpose_apply_abi, hq, hk, Matrix.add_apply, Matrix.add_apply, Matrix.of_apply,
    Matrix.of_apply, hB, hβ]
  simp only [add_dotProduct, dotProduct_add]
  ring

/-- Helper: a probability vector `a` against rows `Y_s = X_s P + w` gives `(a X) P + w`. -/
private theorem vecMul_rows_abi {m n k : Type*} [Fintype m] [Fintype n] (a : m → ℝ)
    (ha : ∑ s, a s = 1) (X : Matrix m n ℝ) (Y : Matrix m k ℝ) (P : Matrix n k ℝ) (w : k → ℝ)
    (hY : ∀ s, Y s = X s ᵥ* P + w) : a ᵥ* Y = (a ᵥ* X) ᵥ* P + w := by
  rw [Matrix.vecMul_eq_sum, Matrix.vecMul_eq_sum a X]
  simp only [hY, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, ha, one_smul,
    Matrix.sum_vecMul, Matrix.smul_vecMul]

/-- Helper: row `t` of `A + B`. -/
private theorem row_add_abi {m n : Type*} (A B : Matrix m n ℝ) (t : m) :
    (A + B) t = A t + B t := rfl

/-- Helper: row `t` of the matrix whose rows are all `v`. -/
private theorem row_of_abi {m n : Type*} (v : n → ℝ) (t : m) :
    (Matrix.of fun _ : m => v) t = v := rfl

/-- Helper: row `t` of a sum of matrices. -/
private theorem row_sum_abi {ι m n : Type*} [Fintype ι] (F : ι → Matrix m n ℝ) (t : m) :
    (∑ i, F i) t = ∑ i, F i t :=
  Finset.sum_apply t _ _

/-- **The reduction with biases:** without normalization, at a token `t` that sees at least one
token, the network of one attention block with biases and the stream matrix `S 0` gives the row
`x_t E S_0 D + ∑_i ∑_s a_ts^{(i)} x_s C_i + γ`, where the weights `a_ts^{(i)}` are those of the
scores `x_t B_i x_s^⊤ + β_i x_s^⊤`: "The key biases drop out […] and the value biases enter only
through `γ`". -/
theorem evalB_attention_oneBlock_row (S : Fin 1 → Matrix d d ℝ)
    (p : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) (x : Matrix T dIn ℝ)
    (t : T) (ht : ∃ s, sees t s) :
    evalB (Arch.attention sees id H dh) S p.1 p.2 x t
      = (x * (p.1.E * S 0 * p.1.D)
          + ∑ i, attnWeights sees (x * attnScore p.1 i * xᵀ
              + Matrix.of fun _ s => (x *ᵥ attnScoreBias p i) s) * x * attnValue p.1 i) t
        + attnConst S p := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.attention (T := T) (d := d) sees id H dh).χ = id := rfl
  -- `h_1 = h_0 S_0 + f(h_0 W_read + b_read) W_write + b_write` with `h_0 = x E + b_E`
  rw [evalB, h1, hiddenB_succ, Fin.castSucc_zero, hiddenB_zero, hχ, id_eq, id_eq,
    f_attention_bias_abi]
  -- the scores: the key biases drop out
  simp only [scores_abi, attnWeights_add_row_abi]
  -- row `t` of head `i`: `(∑_s a_ts x_s) C_i + (b_E W_V + b_V) W_O`, as the weights sum to `1`
  have hi : ∀ i, (attnWeights sees (x * attnScore p.1 i * xᵀ
        + Matrix.of fun _ s => (x *ᵥ attnScoreBias p i) s)
      * ((x * p.1.E + Matrix.of fun _ => p.2.E) * attnV p.1 i
        + Matrix.of fun _ => attnBV p.2 i) * attnO p.1 i : Matrix T d ℝ) t
      = (attnWeights sees (x * attnScore p.1 i * xᵀ
          + Matrix.of fun _ s => (x *ᵥ attnScoreBias p i) s) t ᵥ* x)
          ᵥ* (p.1.E * attnV p.1 i * attnO p.1 i)
        + (p.2.E ᵥ* attnV p.1 i + attnBV p.2 i) ᵥ* attnO p.1 i := by
    intro i
    rw [Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul,
      vecMul_rows_abi _ (attnWeights_sum_abi _ t ht) x _ (p.1.E * attnV p.1 i) _ fun s => by
        show (x s ᵥ* p.1.E + p.2.E) ᵥ* attnV p.1 i + attnBV p.2 i = _
        rw [Matrix.add_vecMul, Matrix.vecMul_vecMul, add_assoc],
      Matrix.add_vecMul, Matrix.vecMul_vecMul]
  rw [row_add_abi, Matrix.mul_apply_eq_vecMul, row_add_abi, row_add_abi, row_sum_abi,
    Finset.sum_congr rfl fun i _ => hi i]
  simp only [row_add_abi, row_of_abi, row_sum_abi, Matrix.mul_apply_eq_vecMul]
  -- collect the terms
  simp only [attnValue, attnConst, Matrix.add_vecMul, Matrix.sum_vecMul, Matrix.vecMul_vecMul,
    Finset.sum_add_distrib, Matrix.mul_assoc]
  abel

/-- **Equation (16) with biases:** let token `t₂` see itself and another token `t₁`, and let `k`
be the number of tokens other than `t₂` that `t₂` sees. At the input with the row `u` at `t₂`
and the row `u − v` at every other token, the output at `t₂` is
`u (E S_0 D + ∑_i C_i) − ½ v ∑_i C_i + ½ ∑_i tanh(½ ((u B_i + β_i) v^⊤ − log k)) v C_i + γ`. -/
theorem evalB_attention_two_tokens [DecidableEq T] (S : Fin 1 → Matrix d d ℝ) (t₁ t₂ : T)
    (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (p : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) (u v : dIn → ℝ) :
    evalB (Arch.attention sees id H dh) S p.1 p.2
        (Matrix.of fun t => if t = t₂ then u else u - v) t₂
      = u ᵥ* (p.1.E * S 0 * p.1.D + ∑ i, attnValue p.1 i)
        - (1 / 2 : ℝ) • (v ᵥ* ∑ i, attnValue p.1 i)
        + ∑ i, ((1 / 2 : ℝ) * Real.tanh ((1 / 2) * (u ⬝ᵥ (attnScore p.1 i *ᵥ v)
            + attnScoreBias p i ⬝ᵥ v
            - Real.log ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ))))
          • (v ᵥ* attnValue p.1 i)
        + attnConst S p := by
  sorry

/-- **Proof of Theorem B.1 (i) for attention blocks with biases, Step 2, for any stream matrix:**
let token `t₂` see itself and another token `t₁`, and let some `v` have the columns `B_i v^⊤`
nonzero and pairwise non-collinear and every row `v C_i` nonzero. Then a flat direction `η` of
the network with biases and the stream matrix `S 0` keeps `E S_0 D`, every `B_i`, every `C_i`,
every `β_i` and the constant `γ` to first order. -/
theorem flatB_attention_oneBlock_keeps (S : Fin 1 → Matrix d d ℝ) (t₁ t₂ : T) (h12 : t₁ ≠ t₂)
    (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (p : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hv : ∃ v : dIn → ℝ, (∀ i, attnScore p.1 i *ᵥ v ≠ 0)
      ∧ (∀ i j, i ≠ j → ∀ r : ℝ, attnScore p.1 i *ᵥ v ≠ r • (attnScore p.1 j *ᵥ v))
      ∧ (∀ i, v ᵥ* attnValue p.1 i ≠ 0))
    (η : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hη : η ∈ flatB (Arch.attention sees id H dh) S p) :
    (η.1.E * S 0 * p.1.D + p.1.E * S 0 * η.1.D = 0
        ∧ ∀ i, dAttnScore p.1 η.1 i = 0 ∧ dAttnValue p.1 η.1 i = 0)
      ∧ (∀ i, dAttnScoreBias p η i = 0) ∧ dAttnConst S p η = 0 := by
  sorry

end Skips
