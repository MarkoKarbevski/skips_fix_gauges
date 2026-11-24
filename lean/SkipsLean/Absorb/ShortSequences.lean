import SkipsLean.Absorb.ShortSequencesPoly
import SkipsLean.Network.Defs

/-!
# Attention networks on short sequences (absorb paper, Theorem 4.2 (iii))

Paper (absorb paper), Theorem 4.2: "Without normalization or with pre-RMSNorm and `ε > 0`, let a
residual network of `L` attention blocks have `E D ≠ 0`. Consider skipless networks of `L' ≥ 1`
attention blocks, with any numbers of heads and any head dimensions. […] (iii) Short sequences.
Without normalization and with a causal mask, in every other case, `T ≤ L` or `T = L + 1 ≤ L'`,
some residual network of `L` blocks with `E D ≠ 0` equals a skipless network of `L'` blocks."
After the theorem: "For `T = 2` and heads whose scores vanish, the residual block
`h ↦ h − 3 U h` equals the composition `h ↦ −2 U² h` of two skipless blocks."

Its proof: equation (10) (`Absorb/ShortSequencesPoly.lean`), then: "Let `Π = diag(1, 1, 0, …, 0)`,
and let the `d_model × d_model` matrix `J` have the entries `J_12 = −1` and `J_21 = 1` and zeros
elsewhere, so that `J² = −Π` and `J Π = Π J = J`. […] Let every score matrix vanish, in both
networks. Then every attention matrix is `U`, block `ℓ` is the linear map `h ↦ h + U h V_ℓ`, and
the residual network is `X ↦ ∑_k U^k X Λ_k`, where `∑_k Λ_k z^k = E ∏_ℓ (I + z V_ℓ) D`. […] the
residual network is `X ↦ Q(U) X E D`. […] The skipless network with the same `E` and `D` whose
blocks have `V'_1 = γ' Π` and `V'_ℓ = Π` for `ℓ ≥ 2` is `X ↦ γ' U^{L'} X E D`, so the two
networks are equal. A block has the sum `V` once its heads have value–output products that add up
to `V`, which two heads of any dimension allow for matrices of rank at most 2."

Here, with the tokens `Fin n`, the causal mask `fun t s => s ≤ t`, the skipless network of
`L' + 1` blocks (the paper's `L'`), every model dimension `m + 2 ≥ 2`, input and output
dimensions `a + 1` and `b + 1`, and two heads of dimension one in every block of both networks:

* `one_sub_three_smul_attnWeights_causal_two`: the identity `I − 3 U = −2 U²` for two tokens;
* `exists_residual_eq_skipless_attention_causal_short`: part (iii), for at least one token, with
  one clause more than the paper: the common function of the two networks is not zero. (For
  `n ≤ L` the statement of the paper is also met by a residual network whose function is zero,
  with `V_ℓ = −ℓ Π` for `ℓ ≤ n`; the construction of the paper gives a nonzero one.)
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

/-- Helper: the entries of the causal weights at zero scores: row `t` is uniform on the tokens
`s ≤ t`. -/
private theorem attnWeights_causal_ssq {n : ℕ} (t s : Fin n) :
    attnWeights (fun t s : Fin n => s ≤ t) 0 t s = if s ≤ t then 1 / ((t : ℝ) + 1) else 0 := by
  simp only [attnWeights, Matrix.of_apply, Matrix.zero_apply, Real.exp_zero]
  split_ifs with h
  · rw [Finset.sum_boole, Finset.filter_ge_eq_Iic, Fin.card_Iic]
    push_cast
    rfl
  · rfl

/-- **After Theorem 4.2:** for two tokens under the causal mask and zero scores, with `U` the
matrix of the attention weights, `I − 3 U = −2 U²`: "the residual block `h ↦ h − 3 U h` equals
the composition `h ↦ −2 U² h` of two skipless blocks". -/
theorem one_sub_three_smul_attnWeights_causal_two :
    (1 : Matrix (Fin 2) (Fin 2) ℝ)
        - (3 : ℝ) • attnWeights (fun t s : Fin 2 => s ≤ t) (0 : Matrix (Fin 2) (Fin 2) ℝ)
      = (-2 : ℝ) • (attnWeights (fun t s : Fin 2 => s ≤ t) (0 : Matrix (Fin 2) (Fin 2) ℝ)
          * attnWeights (fun t s : Fin 2 => s ≤ t) (0 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  -- `U = !![1, 0; 1/2, 1/2]`: check the four entries
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [attnWeights_causal_ssq, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- The networks of the construction: causal attention, no normalization, two heads of
dimension one in every block. -/
private noncomputable abbrev arch_ssq (n m L : ℕ) : Arch (Fin n) (Fin (m + 2)) L :=
  Arch.attention (T := Fin n) (d := Fin (m + 2)) (L := L) (fun t s => s ≤ t) id
    (fun _ => Fin 2) (fun _ => Fin 1)

/-- The matrix `α Π + β J` of the complex number `w = α + β i`. -/
private noncomputable def vmat_ssq (m : ℕ) (w : ℂ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  Matrix.of fun p q =>
    if p = 0 then (if q = 0 then w.re else if q = 1 then -w.im else 0)
    else if p = 1 then (if q = 0 then w.im else if q = 1 then w.re else 0) else 0

/-- The hidden state that codes the complex column `ζ`: column `0` holds `re ζ`, column `1`
holds `-im ζ`, the other columns are `0`. -/
private noncomputable def enc_ssq {n : ℕ} (m : ℕ) (ζ : Fin n → ℂ) :
    Matrix (Fin n) (Fin (m + 2)) ℝ :=
  Matrix.of fun t p => if p = 0 then (ζ t).re else if p = 1 then -(ζ t).im else 0

/-- The model coordinate of head `i`. -/
private def emb_ssq (m : ℕ) (i : Fin 2) : Fin (m + 2) := if i = 0 then 0 else 1

/-- The parameters of the construction: in block `ℓ`, zero queries and keys, and value–output
products of the two heads that add up to `vmat_ssq m (z ℓ)`; `E = e₀ e₀ᵀ`, row `0` of `D` all
ones. -/
private noncomputable def params_ssq (n m a b L : ℕ) (z : Fin L → ℂ) :
    Params (arch_ssq n m L) (Fin (a + 1)) (Fin (b + 1)) where
  E := Matrix.of fun i p => if i = 0 ∧ p = 0 then 1 else 0
  read ℓ := Matrix.of fun p c =>
    Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) fun _ => vmat_ssq m (z ℓ) p (emb_ssq m c.1)) c.2
  write _ := Matrix.of fun c q => if q = emb_ssq m c.1 then 1 else 0
  D := Matrix.of fun p _ => if p = 0 then 1 else 0

/-- Helper: a sum over the model coordinates of a function that vanishes outside `0, 1`. -/
private theorem sum_fin_two_ssq (m : ℕ) (f : Fin (m + 2) → ℝ)
    (hf : ∀ p, p ≠ 0 → p ≠ 1 → f p = 0) : ∑ p, f p = f 0 + f 1 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ,
    Finset.sum_eq_zero fun p _ => hf _ (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one p)]
  simp

/-- Helper: the product `E D` has the entry `1` at `(0, 0)`. -/
private theorem ED_ssq (n m a b L : ℕ) (z : Fin L → ℂ) :
    ((params_ssq n m a b L z).E * (params_ssq n m a b L z).D) 0 0 = 1 := by
  simp [params_ssq, Matrix.mul_apply]

/-- Helper, **a block at zero scores:** block `ℓ` maps `h` to `U h V(z ℓ)`. -/
private theorem block_ssq (n m a b L : ℕ) (z : Fin L → ℂ) (ℓ : Fin L)
    (h : Matrix (Fin n) (Fin (m + 2)) ℝ) :
    (arch_ssq n m L).f ℓ (h * (params_ssq n m a b L z).read ℓ)
        * (params_ssq n m a b L z).write ℓ
      = attnWeights (fun t s : Fin n => s ≤ t) 0 * h * vmat_ssq m (z ℓ) := by
  rw [f_attention_mul]
  simp only [attentionBlock, attnHeads]
  -- the queries vanish, so every score matrix is `0`
  have hQ : ∀ i : Fin 2, ((params_ssq n m a b L z).read ℓ).submatrix id
      (fun k : Fin 1 => (i, Sum.inl k)) = 0 := by
    intro i; ext p k; simp [params_ssq]
  simp only [hQ, Matrix.zero_mul, smul_zero, Matrix.mul_zero]
  rw [← Matrix.mul_sum]
  congr 1
  -- the value–output products of the two heads add up to `V(z ℓ)`
  ext p q
  simp [Matrix.sum_apply, Fin.sum_univ_two, Matrix.mul_apply, params_ssq, emb_ssq, vmat_ssq]
  by_cases hq0 : q = 0
  · subst hq0; simp
  · by_cases hq1 : q = 1
    · subst hq1; simp
    · simp [hq0, hq1]

/-- Helper, **the rows as complex numbers:** `U h V(w)` codes `w (U ζ)` when `h` codes `ζ`. -/
private theorem mul_enc_vmat_ssq {n : ℕ} (m : ℕ) (U : Matrix (Fin n) (Fin n) ℝ)
    (ζ : Fin n → ℂ) (w : ℂ) :
    U * enc_ssq m ζ * vmat_ssq m w = enc_ssq m (w • (U.map Complex.ofReal *ᵥ ζ)) := by
  ext t q
  -- the columns `0` and `1` of `U h` are `re (U ζ)` and `-im (U ζ)`
  have h0 : (U * enc_ssq m ζ) t 0 = ((U.map Complex.ofReal *ᵥ ζ) t).re := by
    simp [Matrix.mul_apply, enc_ssq, Matrix.mulVec, dotProduct, Complex.re_sum]
  have h1 : (U * enc_ssq m ζ) t 1 = -((U.map Complex.ofReal *ᵥ ζ) t).im := by
    simp [Matrix.mul_apply, enc_ssq, Matrix.mulVec, dotProduct, Complex.im_sum]
  rw [Matrix.mul_apply, sum_fin_two_ssq m _ fun p hp0 hp1 => by simp [vmat_ssq, hp0, hp1], h0,
    h1]
  by_cases hq0 : q = 0
  · subst hq0; simp [vmat_ssq, enc_ssq]; ring
  · by_cases hq1 : q = 1
    · subst hq1; simp [vmat_ssq, enc_ssq]; ring
    · simp [vmat_ssq, enc_ssq, hq0, hq1]

/-- Helper: the stream and the block add up as complex columns. -/
private theorem enc_smul_add_ssq {n : ℕ} (m : ℕ) (s : ℝ) (ζ η : Fin n → ℂ) :
    enc_ssq m ζ * (s • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)) + enc_ssq m η
      = enc_ssq m ((s : ℂ) • ζ + η) := by
  ext t p
  by_cases hp0 : p = 0
  · subst hp0; simp [enc_ssq]
  · by_cases hp1 : p = 1
    · subst hp1; simp [enc_ssq]; ring
    · simp [enc_ssq, hp0, hp1]

/-- The complex columns coded by the hidden states: `ζ_0 = x`,
`ζ_{ℓ+1} = s ζ_ℓ + z_ℓ U ζ_ℓ`. -/
private noncomputable def zeta_ssq {n L : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (z : Fin L → ℂ)
    (s : ℝ) (x : Fin n → ℂ) : Fin (L + 1) → Fin n → ℂ :=
  Fin.induction (motive := fun _ => Fin n → ℂ) x
    (fun ℓ ζ => (s : ℂ) • ζ + z ℓ • (U.map Complex.ofReal *ᵥ ζ))

/-- Helper: `ζ_0 = x`. -/
private theorem zeta_zero_ssq {n L : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (z : Fin L → ℂ)
    (s : ℝ) (x : Fin n → ℂ) : zeta_ssq U z s x 0 = x := rfl

/-- Helper: `ζ_{ℓ+1} = s ζ_ℓ + z_ℓ U ζ_ℓ`. -/
private theorem zeta_succ_ssq {n L : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (z : Fin L → ℂ)
    (s : ℝ) (x : Fin n → ℂ) (ℓ : Fin L) :
    zeta_ssq U z s x ℓ.succ
      = (s : ℂ) • zeta_ssq U z s x ℓ.castSucc
        + z ℓ • (U.map Complex.ofReal *ᵥ zeta_ssq U z s x ℓ.castSucc) := by
  simp only [zeta_ssq, Fin.induction_succ]

/-- Helper: the networks have no normalization. -/
private theorem chi_ssq (n m L : ℕ) (h : Matrix (Fin n) (Fin (m + 2)) ℝ) :
    (arch_ssq n m L).χ h = h := rfl

/-- Helper, **the hidden states:** with the stream matrices `s I`, the hidden state `h_k` codes
the complex column `ζ_k`, `ζ_0 = x` the column `0` of the input. -/
private theorem hidden_ssq (n m a b L : ℕ) (z : Fin L → ℂ) (s : ℝ)
    (M : Fin L → Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) (hM : ∀ ℓ, M ℓ = s • 1)
    (X : Matrix (Fin n) (Fin (a + 1)) ℝ) (k : Fin (L + 1)) :
    hidden (arch_ssq n m L) M (params_ssq n m a b L z) X k
      = enc_ssq m (zeta_ssq (attnWeights (fun t s : Fin n => s ≤ t) 0) z s
          (fun t => (X t 0 : ℂ)) k) := by
  induction k using Fin.induction with
  | zero =>
    -- `h_0 = X E` holds the column `0` of `X` in its column `0`
    rw [hidden_zero, zeta_zero_ssq]
    ext t p
    by_cases hp0 : p = 0
    · subst hp0; simp [params_ssq, enc_ssq, Matrix.mul_apply]
    · simp [params_ssq, enc_ssq, Matrix.mul_apply, hp0]
  | succ ℓ ih =>
    -- block `ℓ` adds `z_ℓ U ζ_ℓ` to the stream `s ζ_ℓ`
    rw [hidden_succ, block_ssq, chi_ssq, hM, ih, mul_enc_vmat_ssq, zeta_succ_ssq]
    exact enc_smul_add_ssq m s _ _

/-- Helper, **the output:** row `0` of `D` is all ones, so the output is `re ζ_L`. -/
private theorem eval_ssq (n m a b L : ℕ) (z : Fin L → ℂ) (s : ℝ)
    (M : Fin L → Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) (hM : ∀ ℓ, M ℓ = s • 1)
    (X : Matrix (Fin n) (Fin (a + 1)) ℝ) (t : Fin n) (o : Fin (b + 1)) :
    eval (arch_ssq n m L) M (params_ssq n m a b L z) X t o
      = (zeta_ssq (attnWeights (fun t s : Fin n => s ≤ t) 0) z s
          (fun t => (X t 0 : ℂ)) (Fin.last L) t).re := by
  rw [eval, hidden_ssq n m a b L z s M hM X, chi_ssq]
  simp [Matrix.mul_apply, params_ssq, enc_ssq]

/-- Helper: the real matrix `B`, as a complex matrix, on a real column. -/
private theorem mulVec_ofReal_ssq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    B.map Complex.ofReal *ᵥ (fun t => (v t : ℂ)) = fun t => ((B *ᵥ v) t : ℂ) := by
  ext t
  simp [Matrix.mulVec, dotProduct]

/-- Helper, **the residual network:** `ζ_k = ∏_{ℓ < k} (1 + c_ℓ U) x`, written as a polynomial
in `U`. -/
private theorem zeta_res_ssq {n L : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (c : Fin L → ℂ)
    (x : Fin n → ℂ) (k : Fin (L + 1)) :
    zeta_ssq U c 1 x k
      = Polynomial.aeval (U.map Complex.ofReal)
          (∏ j ∈ Finset.univ.filter (fun j : Fin L => (j : ℕ) < k),
            (1 + Polynomial.C (c j) * Polynomial.X)) *ᵥ x := by
  induction k using Fin.induction with
  | zero => simp [zeta_zero_ssq]
  | succ ℓ ih =>
    -- the blocks before `ℓ + 1` are those before `ℓ`, and `ℓ`
    have hs : Finset.univ.filter (fun j : Fin L => (j : ℕ) < (ℓ.succ : ℕ))
        = insert ℓ (Finset.univ.filter (fun j : Fin L => (j : ℕ) < (ℓ.castSucc : ℕ))) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.val_succ,
        Fin.val_castSucc, Fin.ext_iff]
      omega
    have hn : ℓ ∉ Finset.univ.filter (fun j : Fin L => (j : ℕ) < (ℓ.castSucc : ℕ)) := by simp
    -- block `ℓ` multiplies by `1 + c_ℓ U`
    rw [zeta_succ_ssq, ih, hs, Finset.prod_insert hn, map_mul, ← Matrix.mulVec_mulVec]
    generalize Polynomial.aeval (R := ℂ) (U.map Complex.ofReal) _ *ᵥ x = y
    simp [Matrix.add_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]

/-- Helper, **the polynomial over `ℂ`:** `Q(U)` computed with complex coefficients is the real
matrix `Q(U)`. -/
private theorem aeval_map_ssq {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (Q : Polynomial ℝ) :
    Polynomial.aeval (U.map Complex.ofReal) (Q.map (algebraMap ℝ ℂ))
      = (Polynomial.aeval U Q).map Complex.ofReal := by
  rw [Polynomial.aeval_map_algebraMap ℂ]
  have h := Polynomial.aeval_algHom_apply (Complex.ofRealAm.mapMatrix (m := Fin n)) U Q
  simpa [AlgHom.mapMatrix_apply, Complex.ofRealAm_coe] using h

/-- Helper, **the skipless network:** with `z_0 = γ` and `z_ℓ = 1` after, and no stream,
`ζ_k = γ U^k x` for `k ≥ 1`. -/
private theorem zeta_skip_ssq {n L : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ)
    (v : Fin n → ℝ) (k : Fin (L + 2)) :
    zeta_ssq U (fun ℓ : Fin (L + 1) => if ℓ = 0 then (γ : ℂ) else 1) 0 (fun t => (v t : ℂ)) k
      = fun t => (((if (k : ℕ) = 0 then 1 else γ) • (U ^ (k : ℕ) *ᵥ v)) t : ℂ) := by
  induction k using Fin.induction with
  | zero => simp [zeta_zero_ssq]
  | succ ℓ ih =>
    rw [zeta_succ_ssq, ih, mulVec_ofReal_ssq]
    ext t
    by_cases h0 : ℓ = 0
    · subst h0; simp
    · have h0' : (ℓ : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
      simp [h0, h0', pow_succ', Matrix.mulVec_smul, ← Matrix.mulVec_mulVec]

/-- Helper: token `0` sees only itself, so row `0` of `U^k` is `e_0`. -/
private theorem pow_mulVec_zero_ssq {n : ℕ} (hn1 : 1 ≤ n) (v : Fin n → ℝ) (k : ℕ) :
    ((attnWeights (fun t s : Fin n => s ≤ t) 0) ^ k *ᵥ v) ⟨0, hn1⟩ = v ⟨0, hn1⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct,
      Finset.sum_eq_single (⟨0, hn1⟩ : Fin n), attnWeights_causal_ssq, ih]
    · simp
    · intro s _ hs
      rw [attnWeights_causal_ssq, ite_eq_right fun h => hs (Fin.ext (by
        have := Fin.le_def.1 h; simp at this; omega)), zero_mul]
    · simp

/-- **Theorem 4.2 (iii), short sequences:** without normalization, with the causal mask on
`n ≥ 1` tokens, when `n ≤ L`, or `n = L + 1` and `L ≤ L'`: for every model dimension `m + 2`,
some residual network of `L` attention blocks with `E D ≠ 0` equals a skipless network of
`L' + 1` attention blocks with the same model dimension at every input, and their common
function is not zero. Both networks have two heads of dimension one in every block. -/
theorem exists_residual_eq_skipless_attention_causal_short (n L L' m a b : ℕ) (hn1 : 1 ≤ n)
    (hn : n ≤ L ∨ (n = L + 1 ∧ L ≤ L')) :
    ∃ (θ : Params (Arch.attention (T := Fin n) (d := Fin (m + 2)) (L := L)
          (fun t s => s ≤ t) id (fun _ => Fin 2) (fun _ => Fin 1)) (Fin (a + 1)) (Fin (b + 1)))
      (θ' : Params (Arch.attention (T := Fin n) (d := Fin (m + 2)) (L := L' + 1)
          (fun t s => s ≤ t) id (fun _ => Fin 2) (fun _ => Fin 1)) (Fin (a + 1)) (Fin (b + 1))),
      θ.E * θ.D ≠ 0
        ∧ (∀ X : Matrix (Fin n) (Fin (a + 1)) ℝ,
            eval (Arch.attention (fun t s => s ≤ t) id (fun _ => Fin 2) (fun _ => Fin 1)) 1 θ X
              = eval (Arch.attention (fun t s => s ≤ t) id (fun _ => Fin 2) (fun _ => Fin 1))
                  0 θ' X)
        ∧ ∃ X : Matrix (Fin n) (Fin (a + 1)) ℝ,
            eval (Arch.attention (fun t s => s ≤ t) id (fun _ => Fin 2) (fun _ => Fin 1)) 1 θ X
              ≠ 0 := by
  -- the numbers: `Q(z_t) = γ z_t^{L'+1}` (10), and the factors `1 + c_ℓ z` of `Q` over `ℂ`
  obtain ⟨Q, γ, hdeg, h0, hγ, hQ⟩ := exists_polynomial_short n L L' hn
  obtain ⟨c, hc⟩ := exists_complex_factors L Q hdeg h0
  -- `Q(U) = γ U^{L'+1}`, as `U` has the eigenvalues `z_t`
  have hQU : Polynomial.aeval (attnWeights (fun t s : Fin n => s ≤ t) 0) Q
      = γ • attnWeights (fun t s : Fin n => s ≤ t) 0 ^ (L' + 1) := by
    have h := aeval_attnWeights_causal_eq_zero n (Q - Polynomial.C γ * Polynomial.X ^ (L' + 1))
      fun t => by simp [hQ t]
    rw [map_sub, sub_eq_zero] at h
    rw [h]
    simp [Algebra.algebraMap_eq_smul_one]
  -- the residual network, with `V_ℓ = V(c_ℓ)`, computes `X ↦ Q(U) x = γ U^{L'+1} x`
  have hres : ∀ X t o, eval (arch_ssq n m L) 1 (params_ssq n m a b L c) X t o
      = γ * ((attnWeights (fun t s : Fin n => s ≤ t) 0 ^ (L' + 1)) *ᵥ fun t => X t 0) t := by
    intro X t o
    rw [eval_ssq n m a b L c 1 1 (fun ℓ => by rw [Pi.one_apply, one_smul]) X t o, zeta_res_ssq,
      Finset.filter_true_of_mem fun j _ => j.isLt, ← hc, aeval_map_ssq, hQU, mulVec_ofReal_ssq]
    simp [Matrix.smul_mulVec]
  -- the skipless network, with `V'_0 = γ Π` and `V'_ℓ = Π` after, computes `γ U^{L'+1} x`
  have hskip : ∀ X t o, eval (arch_ssq n m (L' + 1)) 0
      (params_ssq n m a b (L' + 1) fun ℓ => if ℓ = 0 then (γ : ℂ) else 1) X t o
      = γ * ((attnWeights (fun t s : Fin n => s ≤ t) 0 ^ (L' + 1)) *ᵥ fun t => X t 0) t := by
    intro X t o
    rw [eval_ssq n m a b (L' + 1) _ 0 0 (fun ℓ => by simp) X t o, zeta_skip_ssq]
    simp
  refine ⟨params_ssq n m a b L c,
    params_ssq n m a b (L' + 1) (fun ℓ => if ℓ = 0 then (γ : ℂ) else 1), ?_, ?_, ?_⟩
  · -- `E D ≠ 0`
    intro h
    have h1 := ED_ssq n m a b L c
    rw [h] at h1
    simp at h1
  · -- the two networks are equal
    intro X
    ext t o
    rw [hres, hskip]
  · -- at the input `e_0 e_0ᵀ` the output at token `0` is `γ ≠ 0`
    refine ⟨Matrix.of fun t i => if t = ⟨0, hn1⟩ ∧ i = 0 then 1 else 0, fun h => hγ ?_⟩
    have h1 := congrFun (congrFun h ⟨0, hn1⟩) 0
    rw [hres, pow_mulVec_zero_ssq hn1] at h1
    simpa using h1

end Skips
