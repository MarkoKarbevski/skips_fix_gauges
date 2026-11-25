import SkipsLean.OneBlock.AttentionBiases
import SkipsLean.OneBlock.AttentionStepOne
import SkipsLean.Symmetry.AttentionHeadsBiases

/-!
# The one-block theorem for an attention block with biases: Step 1

Paper (skips paper), proof of Theorem B.1 (i), "Part (i) for attention blocks", "Step 1: the
directions that keep `M`, `B_i` and `C_i`": "Hence `η_{Q,i} = −X W_{Q,i} + W_{Q,i} Γ_i`,
`η_{K,i} = −X W_{K,i} − W_{K,i} Γ_i^⊤`, `η_{V,i} = −X W_{V,i} + W_{V,i} Γ'_i` and
`η_{O,i} = W_{O,i} Y − Γ'_i W_{O,i}` […] In the residual network
`D_θ M η = E (X − Y) D = 0` gives `X = Y`. […] With biases, `D_θ β_i η = 0` gives
`η_{b_Q,i} = b_{Q,i} Γ_i − g W_{Q,i}` with `g = η_{b_E} − b_E X`, since `W_{K,i}^⊤ E^⊤` has full
row rank, and `D_θ γ η = 0` determines `η_{b_D}`. This leaves `g`, `η_{b_O}` and the entries of
`η` at the key and value biases free, `2 d_model + 2 H d_h` dimensions, which the translations at
`h_0` and `h_1`, the shifts of the key biases and the value biases moved into the output bias
span."

Here, under the conditions `OneBlockGenericAttention` on the weights (they do not involve the
biases), for a direction `η` of weights and biases that keeps every `B_i`, `C_i`, `β_i` and the
constant `γ` to first order (`OneBlock/AttentionBiases.lean`):

* without the skip, `η = cobDirB p X + (0, translateAtDir θ g) + headDirB p (Γ, Γ', κ, ν)`: two
  changes of basis and two translations of the hidden states, and the symmetries inside the block
  (`Symmetry/AttentionHeadsBiases.lean`);
* with the skip, if `η` also keeps `M = E D`,
  `η = cobDirB p (X, X) + (0, translateDir θ g) + headDirB p (Γ, Γ', κ, ν)`: one change of basis
  and the two translations of Lemma A.8.

Pure linear algebra on top of `exists_cobDir_add_headDir_of_keeps`
(`OneBlock/AttentionStepOne.lean`); no mask and no input enters. With
`g_0 = η_{b_E} − b_E X_0`: `κ_i = η_{b_K,i} + g_0 W_{K,i} + b_{K,i} Γ_i^⊤`,
`ν_i = η_{b_V,i} + g_0 W_{V,i} − b_{V,i} Γ'_i` and `g_1 = η_{b_O} − b_O X_1 + ∑_i ν_i W_{O,i}`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-! ### Helpers -/

/-- Helper (copy of `cancel_left_of_rank_obd` of `OneBlock/AttentionDim.lean`): a matrix whose
rank is its number of columns cancels on the left, via a left inverse. -/
private theorem cancel_left_of_rank_abs {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ}
    (h : M * X = M * Y) : X = Y := by
  obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (B * ·) h
  simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul] using this

/-- Helper (copy of `cancel_right_of_rank_obd` of `OneBlock/AttentionDim.lean`): a matrix whose
rank is its number of rows cancels on the right, via a right inverse. -/
private theorem cancel_right_of_rank_abs {m n k : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ}
    (h : X * M = Y * M) : X = Y := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM)
  have := congrArg (· * R) h
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one] using this

/-- Helper: if `E` and `K` have rank equal to their numbers of columns, `K^⊤ E^⊤` has a right
inverse `(E^+)^⊤ (K^+)^⊤` (full row rank). -/
private theorem exists_right_inverse_KE_abs {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq n] [DecidableEq k] (E : Matrix m n ℝ) (K : Matrix n k ℝ)
    (hE : E.rank = Fintype.card n) (hK : K.rank = Fintype.card k) :
    ∃ R : Matrix m k ℝ, Kᵀ * Eᵀ * R = 1 := by
  obtain ⟨E', hE'⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hE)
  obtain ⟨K', hK'⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp
    (Matrix.vecMul_surjective_iff_rank_eq_card.mpr hK)
  have hEt : Eᵀ * E'ᵀ = 1 := by rw [← Matrix.transpose_mul, hE', Matrix.transpose_one]
  have hKt : Kᵀ * K'ᵀ = 1 := by rw [← Matrix.transpose_mul, hK', Matrix.transpose_one]
  exact ⟨E'ᵀ * K'ᵀ, by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Eᵀ, hEt, Matrix.one_mul, hKt]⟩

/-- Helper (copy of `Symmetry/BiasesFlat.lean`): `∑_{k ≤ 0} g_k = g_0`. -/
private theorem sum_Iic_zero_abs {L : ℕ} {W : Type*} [AddCommMonoid W] (g : Fin (L + 1) → W) :
    ∑ k ∈ Finset.Iic (0 : Fin (L + 1)), g k = g 0 := by
  have hs : Finset.Iic (0 : Fin (L + 1)) = {0} := by
    ext k
    simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_iff_val_le_val, Fin.ext_iff,
      Fin.val_zero]
    omega
  rw [hs, Finset.sum_singleton]

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the components of `cobDir θ X + headDirQK θ Γ + headDirVO θ Γ'` (one block):
`E X_0`, `−X_1 D`, `−X_0 W_Q + W_Q Γ`, `−X_0 W_K − W_K Γ^⊤`, `−X_0 W_V + W_V Γ'`,
`W_O X_1 − Γ' W_O`. -/
private theorem comps_of_eq_abs
    (θ η₁ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (X : Fin 2 → Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
    (h : η₁ = cobDir θ X + headDirQK θ Γ + headDirVO θ Γ') :
    η₁.E = θ.E * X 0 ∧ η₁.D = -(X 1 * θ.D) ∧
      (∀ i, attnQ η₁ i = -(X 0 * attnQ θ i) + attnQ θ i * Γ 0 i) ∧
      (∀ i, attnK η₁ i = -(X 0 * attnK θ i) - attnK θ i * (Γ 0 i)ᵀ) ∧
      (∀ i, attnV η₁ i = -(X 0 * attnV θ i) + attnV θ i * Γ' 0 i) ∧
      (∀ i, attnO η₁ i = attnO θ i * X 1 - Γ' 0 i * attnO θ i) := by
  subst h
  refine ⟨?_, ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · show θ.E * X 0 + 0 + 0 = θ.E * X 0
    rw [add_zero, add_zero]
  · show -(X (Fin.last 1) * θ.D) + 0 + 0 = -(X 1 * θ.D)
    rw [add_zero, add_zero]
    rfl
  · ext a k
    show (-(X 0 * θ.read 0)) a (i, Sum.inl k) + (∑ k', θ.read 0 a (i, Sum.inl k') * Γ 0 i k' k)
        + 0 = (-(X 0 * attnQ θ i)) a k + (attnQ θ i * Γ 0 i) a k
    rw [add_zero]
    rfl
  · ext a k
    show (-(X 0 * θ.read 0)) a (i, Sum.inr (Sum.inl k))
        + -(∑ k', θ.read 0 a (i, Sum.inr (Sum.inl k')) * Γ 0 i k k') + 0
      = (-(X 0 * attnK θ i)) a k - (attnK θ i * (Γ 0 i)ᵀ) a k
    rw [add_zero, sub_eq_add_neg]
    rfl
  · ext a k
    show (-(X 0 * θ.read 0)) a (i, Sum.inr (Sum.inr k)) + 0
        + (∑ k', θ.read 0 a (i, Sum.inr (Sum.inr k')) * Γ' 0 i k' k)
      = (-(X 0 * attnV θ i)) a k + (attnV θ i * Γ' 0 i) a k
    rw [add_zero]
    rfl
  · ext k c
    show (θ.write 0 * X 1) (i, k) c + 0 + -(∑ k', Γ' 0 i k k' * θ.write 0 (i, k') c)
      = (attnO θ i * X 1) k c - (Γ' 0 i * attnO θ i) k c
    rw [add_zero, sub_eq_add_neg]
    rfl

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: with the components of `η` on the weights substituted, `D_θ β_i η` is
`(g_0 W_Q + η_{b_Q} − b_Q Γ) W_K^⊤ E^⊤ / √d_h`, `g_0 = η_{b_E} − b_E X_0`. -/
private theorem dAttnScoreBias_eq_abs
    (p η : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (X : Fin 2 → Matrix d d ℝ) (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) (g₀ : d → ℝ)
    (hg₀ : g₀ = η.2.E - p.2.E ᵥ* X 0) (hE : η.1.E = p.1.E * X 0) (i : H 0)
    (hQ : attnQ η.1 i = -(X 0 * attnQ p.1 i) + attnQ p.1 i * Γ 0 i)
    (hK : attnK η.1 i = -(X 0 * attnK p.1 i) - attnK p.1 i * (Γ 0 i)ᵀ) :
    dAttnScoreBias p η i = (Real.sqrt (Fintype.card (dh 0)))⁻¹ •
      ((g₀ ᵥ* attnQ p.1 i + attnBQ η.2 i - attnBQ p.2 i ᵥ* Γ 0 i)
        ᵥ* ((attnK p.1 i)ᵀ * p.1.Eᵀ)) := by
  rw [dAttnScoreBias, hE, hQ, hK, hg₀]
  congr 1
  simp only [Matrix.transpose_sub, Matrix.transpose_neg, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.sub_mul, Matrix.neg_mul, Matrix.mul_assoc,
    Matrix.add_vecMul, Matrix.vecMul_add, Matrix.sub_vecMul, Matrix.vecMul_sub,
    Matrix.neg_vecMul, Matrix.vecMul_neg, Matrix.vecMul_vecMul]
  abel

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: with the components of `η` on the weights substituted, `D_θ γ η` is
`η_{b_E} S_0 D − b_E S_0 X_1 D + g_1 D + η_{b_D}`, with `g_1 = η_{b_O} − b_O X_1 + ∑_i ν_i W_{O,i}`
and `ν_i = η_{b_V,i} + g_0 W_{V,i} − b_{V,i} Γ'_i`. -/
private theorem dAttnConst_eq_abs (S : Fin 1 → Matrix d d ℝ)
    (p η : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (X : Fin 2 → Matrix d d ℝ) (Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) (g₀ : d → ℝ)
    (ν : ∀ ℓ, H ℓ → dh ℓ → ℝ) (hg₀ : g₀ = η.2.E - p.2.E ᵥ* X 0)
    (hν : ∀ i, ν 0 i = attnBV η.2 i + g₀ ᵥ* attnV p.1 i - attnBV p.2 i ᵥ* Γ' 0 i)
    (hD : η.1.D = -(X 1 * p.1.D))
    (hV : ∀ i, attnV η.1 i = -(X 0 * attnV p.1 i) + attnV p.1 i * Γ' 0 i)
    (hO : ∀ i, attnO η.1 i = attnO p.1 i * X 1 - Γ' 0 i * attnO p.1 i) :
    dAttnConst S p η = η.2.E ᵥ* (S 0 * p.1.D) - p.2.E ᵥ* (S 0 * (X 1 * p.1.D))
      + (η.2.write 0 - p.2.write 0 ᵥ* X 1 + ∑ i, ν 0 i ᵥ* attnO p.1 i) ᵥ* p.1.D + η.2.D := by
  -- head `i` contributes `ν_i W_{O,i} D`
  have hhead : ∀ i, (η.2.E ᵥ* attnV p.1 i + p.2.E ᵥ* attnV η.1 i + attnBV η.2 i)
          ᵥ* (attnO p.1 i * p.1.D)
        + (p.2.E ᵥ* attnV p.1 i + attnBV p.2 i)
          ᵥ* (attnO η.1 i * p.1.D + attnO p.1 i * η.1.D)
      = ν 0 i ᵥ* (attnO p.1 i * p.1.D) := by
    intro i
    rw [hV i, hO i, hD, hν i, hg₀]
    simp only [Matrix.sub_mul, Matrix.mul_neg, Matrix.mul_assoc, Matrix.add_vecMul,
      Matrix.vecMul_add, Matrix.sub_vecMul, Matrix.vecMul_sub, Matrix.neg_vecMul,
      Matrix.vecMul_neg, Matrix.vecMul_vecMul]
    abel
  rw [dAttnConst]
  simp only [hhead]
  rw [hD]
  simp only [Matrix.add_vecMul, Matrix.sub_vecMul, Matrix.sum_vecMul, Matrix.vecMul_vecMul,
    Matrix.mul_neg, Matrix.vecMul_neg]
  abel

/-- Helper (from `D_θ β_i η = 0`): `η_{b_Q,i} = b_{Q,i} Γ_i − g_0 W_{Q,i}`, since `W_{K,i}^⊤ E^⊤`
has full row rank; nothing to prove if `d_h = 0`. -/
private theorem queryBias_abs
    (p : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hp : OneBlockGenericAttention p.1)
    (η : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (X : Fin 2 → Matrix d d ℝ) (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) (g₀ : d → ℝ)
    (hg₀ : g₀ = η.2.E - p.2.E ᵥ* X 0) (hE : η.1.E = p.1.E * X 0)
    (hQ : ∀ i, attnQ η.1 i = -(X 0 * attnQ p.1 i) + attnQ p.1 i * Γ 0 i)
    (hK : ∀ i, attnK η.1 i = -(X 0 * attnK p.1 i) - attnK p.1 i * (Γ 0 i)ᵀ)
    (hβ : ∀ i, dAttnScoreBias p η i = 0) (i : H 0) :
    attnBQ η.2 i = attnBQ p.2 i ᵥ* Γ 0 i - g₀ ᵥ* attnQ p.1 i := by
  classical
  -- the degenerate case `d_h = 0`: no coordinates
  by_cases h0 : Fintype.card (dh 0) = 0
  · have : IsEmpty (dh 0) := Fintype.card_eq_zero_iff.mp h0
    funext k
    exact isEmptyElim k
  -- otherwise `1 / √d_h ≠ 0`
  have hc : (Real.sqrt (Fintype.card (dh 0)))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)))
  have h1 := hβ i
  rw [dAttnScoreBias_eq_abs p η X Γ g₀ hg₀ hE i (hQ i) (hK i)] at h1
  have h2 := (smul_eq_zero.mp h1).resolve_left hc
  -- `W_{K,i}^⊤ E^⊤` has a right inverse
  obtain ⟨R, hR⟩ := exists_right_inverse_KE_abs p.1.E (attnK p.1 i) hp.rank_E (hp.rank_K i)
  have h3 : g₀ ᵥ* attnQ p.1 i + attnBQ η.2 i - attnBQ p.2 i ᵥ* Γ 0 i = 0 := by
    have := congrArg (· ᵥ* R) h2
    simpa only [Matrix.vecMul_vecMul, hR, Matrix.vecMul_one, Matrix.zero_vecMul] using this
  calc attnBQ η.2 i = (g₀ ᵥ* attnQ p.1 i + attnBQ η.2 i - attnBQ p.2 i ᵥ* Γ 0 i)
        + (attnBQ p.2 i ᵥ* Γ 0 i - g₀ ᵥ* attnQ p.1 i) := by abel
    _ = _ := by rw [h3, zero_add]

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (assembling `η`): if the weights of `η` are
`cobDir θ X + headDirQK θ Γ + headDirVO θ Γ'`, its query biases are `b_Q Γ − g_0 W_Q`, its
readout bias is `−g_D D`, `κ`, `ν`, `g_1` are as in the header and `B` is a translation of the
biases with `g_0` at `h_0`, `g_1` at `h_1` and readout bias `−g_D D`, then
`η = cobDirB p X + (0, B) + headDirB p (Γ, Γ', κ, ν)`. -/
private theorem eq_of_comps_abs
    (p η : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (X : Fin 2 → Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
    (κ ν : ∀ ℓ, H ℓ → dh ℓ → ℝ) (g₀ g₁ gD : d → ℝ)
    (B : Biases (Arch.attention (T := T) (d := d) sees id H dh) dOut)
    (hη₁ : η.1 = cobDir p.1 X + headDirQK p.1 Γ + headDirVO p.1 Γ')
    (hg₀ : g₀ = η.2.E - p.2.E ᵥ* X 0)
    (hQb : ∀ i, attnBQ η.2 i = attnBQ p.2 i ᵥ* Γ 0 i - g₀ ᵥ* attnQ p.1 i)
    (hκ : ∀ i, κ 0 i = attnBK η.2 i + g₀ ᵥ* attnK p.1 i + attnBK p.2 i ᵥ* (Γ 0 i)ᵀ)
    (hν : ∀ i, ν 0 i = attnBV η.2 i + g₀ ᵥ* attnV p.1 i - attnBV p.2 i ᵥ* Γ' 0 i)
    (hg₁ : g₁ = η.2.write 0 - p.2.write 0 ᵥ* X 1 + ∑ i, ν 0 i ᵥ* attnO p.1 i)
    (hDb : η.2.D = -(gD ᵥ* p.1.D))
    (hBE : B.E = g₀) (hBr : B.read 0 = -(g₀ ᵥ* p.1.read 0)) (hBw : B.write 0 = g₁)
    (hBD : B.D = -(gD ᵥ* p.1.D)) :
    η = cobDirB p X + (0, B) + headDirB p (Γ, Γ', κ, ν) := by
  refine Prod.ext ?_ (Biases.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
  · -- the weights
    show η.1 = cobDir p.1 X + 0 + (headDirQK p.1 Γ + headDirVO p.1 Γ' + 0 + 0)
    rw [hη₁]
    simp only [add_zero, add_assoc]
  · -- the embedding bias: `b_E X_0 + g_0`
    show η.2.E = p.2.E ᵥ* X 0 + B.E + (0 + 0 + 0 + 0)
    rw [hBE, hg₀]
    abel
  · -- the read bias, head by head
    obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
    show η.2.read 0 = 0 + B.read 0 + (headDirB p (Γ, Γ', κ, ν)).2.read 0
    rw [hBr]
    funext q
    obtain ⟨i, k | k | k⟩ := q
    · -- the queries: `b_Q Γ − g_0 W_Q`
      have h := congrFun (hQb i) k
      change η.2.read 0 (i, Sum.inl k) = (∑ k', p.2.read 0 (i, Sum.inl k') * Γ 0 i k' k)
        - ∑ a, g₀ a * p.1.read 0 a (i, Sum.inl k) at h
      show η.2.read 0 (i, Sum.inl k) = 0 + -(∑ a, g₀ a * p.1.read 0 a (i, Sum.inl k))
        + ((∑ k', p.2.read 0 (i, Sum.inl k') * Γ 0 i k' k) + 0 + 0 + 0)
      rw [h]
      ring
    · -- the keys: `−g_0 W_K − b_K Γ^⊤ + κ`
      show η.2.read 0 (i, Sum.inr (Sum.inl k))
        = 0 + -(∑ a, g₀ a * p.1.read 0 a (i, Sum.inr (Sum.inl k)))
          + (-(∑ k', p.2.read 0 (i, Sum.inr (Sum.inl k')) * Γ 0 i k k') + 0 + κ 0 i k + 0)
      rw [hκ i]
      show η.2.read 0 (i, Sum.inr (Sum.inl k))
        = 0 + -(∑ a, g₀ a * p.1.read 0 a (i, Sum.inr (Sum.inl k)))
          + (-(∑ k', p.2.read 0 (i, Sum.inr (Sum.inl k')) * Γ 0 i k k') + 0
            + (η.2.read 0 (i, Sum.inr (Sum.inl k))
              + ∑ a, g₀ a * p.1.read 0 a (i, Sum.inr (Sum.inl k))
              + ∑ k', p.2.read 0 (i, Sum.inr (Sum.inl k')) * Γ 0 i k k') + 0)
      ring
    · -- the values: `−g_0 W_V + b_V Γ' + ν`
      show η.2.read 0 (i, Sum.inr (Sum.inr k))
        = 0 + -(∑ a, g₀ a * p.1.read 0 a (i, Sum.inr (Sum.inr k)))
          + (0 + (∑ k', p.2.read 0 (i, Sum.inr (Sum.inr k')) * Γ' 0 i k' k) + 0 + ν 0 i k)
      rw [hν i]
      show η.2.read 0 (i, Sum.inr (Sum.inr k))
        = 0 + -(∑ a, g₀ a * p.1.read 0 a (i, Sum.inr (Sum.inr k)))
          + (0 + (∑ k', p.2.read 0 (i, Sum.inr (Sum.inr k')) * Γ' 0 i k' k) + 0
            + (η.2.read 0 (i, Sum.inr (Sum.inr k))
              + ∑ a, g₀ a * p.1.read 0 a (i, Sum.inr (Sum.inr k))
              - ∑ k', p.2.read 0 (i, Sum.inr (Sum.inr k')) * Γ' 0 i k' k))
      ring
  · -- the write bias: `b_O X_1 + g_1 − ∑_i ν_i W_{O,i}`
    obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
    funext c
    have hs : (∑ i, ν 0 i ᵥ* attnO p.1 i) c = ∑ i, ∑ k, ν 0 i k * p.1.write 0 (i, k) c := by
      rw [Finset.sum_apply]
      rfl
    show η.2.write 0 c = (p.2.write 0 ᵥ* X 1) c + B.write 0 c
      + (0 + 0 + 0 + -∑ i, ∑ k, ν 0 i k * p.1.write 0 (i, k) c)
    rw [hBw, hg₁]
    show η.2.write 0 c = (p.2.write 0 ᵥ* X 1) c
      + (η.2.write 0 c - (p.2.write 0 ᵥ* X 1) c + (∑ i, ν 0 i ᵥ* attnO p.1 i) c)
      + (0 + 0 + 0 + -∑ i, ∑ k, ν 0 i k * p.1.write 0 (i, k) c)
    rw [hs]
    ring
  · -- the readout bias
    show η.2.D = 0 + B.D + (0 + 0 + 0 + 0)
    rw [hBD, hDb]
    simp only [add_zero, zero_add]

/-- **Proof of Theorem B.1 (i) for attention blocks with biases, Step 1, without the skip:**
under the conditions of the proof on the weights, a direction `η` of weights and biases that
keeps every `B_i`, every `C_i`, every `β_i` and the constant `γ` of the skipless network to first
order is the sum of the direction of two changes of basis and two translations of the hidden
states and of a direction of the symmetries inside the block. -/
theorem exists_dirs_of_keeps_attention_biases
    (p : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hp : OneBlockGenericAttention p.1)
    (η : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hB : ∀ i, dAttnScore p.1 η.1 i = 0) (hC : ∀ i, dAttnValue p.1 η.1 i = 0)
    (hβ : ∀ i, dAttnScoreBias p η i = 0) (hγ : dAttnConst 0 p η = 0) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ)
      (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) (κ ν : ∀ ℓ, H ℓ → dh ℓ → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g) + headDirB p (Γ, Γ', κ, ν) := by
  classical
  -- Step 1 on the weights: `η_θ = cobDir θ X + headDirQK θ Γ + headDirVO θ Γ'`
  obtain ⟨X, Γ, Γ', hη₁⟩ := exists_cobDir_add_headDir_of_keeps p.1 hp η.1 hB hC
  obtain ⟨hE₁, hD₁, hQ₁, hK₁, hV₁, hO₁⟩ := comps_of_eq_abs p.1 η.1 X Γ Γ' hη₁
  -- the translation at `h_0`, and the query biases from `D_θ β_i η = 0`
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, g₀ = η.2.E - p.2.E ᵥ* X 0 := ⟨_, rfl⟩
  have hQb := queryBias_abs p hp η X Γ g₀ hg₀ hE₁ hQ₁ hK₁ hβ
  -- the shifts of the key biases and of the value biases, and the translation at `h_1`
  obtain ⟨κ, hκ⟩ : ∃ κ : ∀ ℓ, H ℓ → dh ℓ → ℝ,
      ∀ i, κ 0 i = attnBK η.2 i + g₀ ᵥ* attnK p.1 i + attnBK p.2 i ᵥ* (Γ 0 i)ᵀ :=
    ⟨fun ℓ => Fin.cases (motive := fun ℓ => H ℓ → dh ℓ → ℝ)
      (fun i => attnBK η.2 i + g₀ ᵥ* attnK p.1 i + attnBK p.2 i ᵥ* (Γ 0 i)ᵀ)
      (fun j => j.elim0) ℓ, fun _ => rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : ∀ ℓ, H ℓ → dh ℓ → ℝ,
      ∀ i, ν 0 i = attnBV η.2 i + g₀ ᵥ* attnV p.1 i - attnBV p.2 i ᵥ* Γ' 0 i :=
    ⟨fun ℓ => Fin.cases (motive := fun ℓ => H ℓ → dh ℓ → ℝ)
      (fun i => attnBV η.2 i + g₀ ᵥ* attnV p.1 i - attnBV p.2 i ᵥ* Γ' 0 i)
      (fun j => j.elim0) ℓ, fun _ => rfl⟩
  obtain ⟨g₁, hg₁⟩ : ∃ g₁, g₁ = η.2.write 0 - p.2.write 0 ᵥ* X 1 + ∑ i, ν 0 i ᵥ* attnO p.1 i :=
    ⟨_, rfl⟩
  -- the readout bias from `D_θ γ η = 0`: `η_{b_D} = −g_1 D`
  have hDb : η.2.D = -(g₁ ᵥ* p.1.D) := by
    have h := hγ
    rw [dAttnConst_eq_abs 0 p η X Γ' g₀ ν hg₀ hν hD₁ hV₁ hO₁, ← hg₁] at h
    simp only [Pi.zero_apply, Matrix.zero_mul, Matrix.vecMul_zero, sub_zero, zero_add] at h
    exact eq_neg_of_add_eq_zero_right h
  exact ⟨X, ![g₀, g₁], Γ, Γ', κ, ν, eq_of_comps_abs p η X Γ Γ' κ ν g₀ g₁ g₁
    (translateAtDir p.1 ![g₀, g₁]) hη₁ hg₀ hQb hκ hν hg₁ hDb rfl rfl rfl rfl⟩

/-- **Proof of Theorem B.1 (i) for attention blocks with biases, Step 1, with the skip:** under
the conditions of the proof on the weights, a direction `η` of weights and biases that keeps
`M = E D`, every `B_i`, every `C_i`, every `β_i` and the constant `γ` of the residual network to
first order is the sum of the direction of one change of basis of both hidden states, of the two
translations of Lemma A.8 and of a direction of the symmetries inside the block. -/
theorem exists_dirs_of_keeps_attention_biases_residual
    (p : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hp : OneBlockGenericAttention p.1)
    (η : ParamsB (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hM : η.1.E * p.1.D + p.1.E * η.1.D = 0)
    (hB : ∀ i, dAttnScore p.1 η.1 i = 0) (hC : ∀ i, dAttnValue p.1 η.1 i = 0)
    (hβ : ∀ i, dAttnScoreBias p η i = 0) (hγ : dAttnConst 1 p η = 0) :
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ)
      (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) (κ ν : ∀ ℓ, H ℓ → dh ℓ → ℝ),
      η = cobDirB p (fun _ => X) + (0, translateDir p.1 g) + headDirB p (Γ, Γ', κ, ν) := by
  sorry

end Skips
