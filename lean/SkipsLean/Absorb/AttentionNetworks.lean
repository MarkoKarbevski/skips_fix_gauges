import SkipsLean.Absorb.AttentionZero
import SkipsLean.Basic.RMSNorm
import SkipsLean.Generic.Params
import Mathlib.Algebra.Polynomial.RuleOfSigns

/-!
# Attention networks on long sequences

Paper (absorb paper): Theorem 4.2 (Attention networks on long and short sequences), parts (i)
and (ii): "Without normalization or with pre-RMSNorm and `ε > 0`, let a residual network of `L`
attention blocks have `E D ≠ 0`. Consider skipless networks of `L' ≥ 1` attention blocks, with
any numbers of heads and any head dimensions. (i) If the attention has no mask, no such skipless
network equals the residual one. With a causal mask on `T` tokens, the same holds when
`T ≥ L + 2`, and when `T = L + 1` and `L' ≤ L`. (ii) For almost every choice of weights of the
residual network, no such skipless network equals it, whatever `L'`."

Its proof compares the Jacobians at `X = 0` (`Absorb/AttentionZero.lean`) on the inputs `a b`
with `U a = λ a`. Without a mask, `U a = 0` for a column `a ≠ 0` whose entries add up to `0`.
With a causal mask, `U` is lower triangular with the diagonal entries `1, 1/2, …, 1/T`, and "the
matrix polynomial `p(z) = ∑_{k=0}^L Λ_k z^k − Λ' z^{L'}` vanishes at the `T` points
`z = 1, 1/2, …, 1/T`. If `L' ≤ L`, every entry of `p` is a polynomial of degree at most `L` with
`T ≥ L + 1` roots, so `p = 0`. If `L' > L`, the hypothesis gives `T ≥ L + 2`, and every entry of
`p` has at most `L + 2` nonzero coefficients. By Descartes' rule of signs […] again `p = 0`."
Part (ii): "From `p(1) = 0` and `p(1/2) = 0`, `∑_k (2^{−k} − 2^{−L'}) Λ_k = 0`. The left side
is a polynomial in the weights of the residual network. When all value–output products vanish it
equals `(1 − 2^{−L'}) ξ E D`, so it is not the zero polynomial".

Stated here in the frame of `Arch.attention` (`Network/Attention.lean`): the residual network
has `L` blocks (stream matrices `1`), the skipless network `L' + 1` blocks (stream matrices
`0`), any heads and head dimensions and any model dimension `d'`; without normalization
(`χ = id` in both) and under pre-RMSNorm (`rmsNorm ε`, `rmsNorm ε'`, `ε, ε' > 0`). Without a
mask the tokens are any finite type with at least two elements and `sees = fun _ _ => True`;
with the causal mask the tokens are `Fin n` and `sees t s` is `s ≤ t`. Descartes' rule of signs
is Mathlib's `Polynomial.roots_countP_pos_le_signVariations`. Part (iii) is not stated here.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

omit [Fintype T] in
/-- Helper: RMSNorm vanishes at `0` (as `rmsNorm_zero_mat` in `Absorb/Networks.lean`). -/
private theorem rmsNorm_zero_mat_atn {m : Type*} [Fintype m] (ε : ℝ) :
    rmsNorm ε (0 : Matrix T m ℝ) = 0 := by
  ext t i
  simp [rmsNorm, rmsRow]

/-- Helper: RMSNorm with `ε > 0` has the derivative `I / √ε` at `0` (as
`hasFDerivAt_rmsNorm_zero` in `Absorb/Networks.lean`). -/
private theorem hasFDerivAt_rmsNorm_zero_atn {m : Type*} [Fintype m] {ε : ℝ} (hε : 0 < ε) :
    HasFDerivAt (rmsNorm ε : Matrix T m ℝ → Matrix T m ℝ)
      ((Real.sqrt ε)⁻¹ • ContinuousLinearMap.id ℝ (Matrix T m ℝ)) 0 := by
  refine hasFDerivAt_pi'' fun t => hasFDerivAt_pi'' fun i => ?_
  have hq : Differentiable ℝ fun h : Matrix T m ℝ => (h t ⬝ᵥ h t) / (Fintype.card m : ℝ) + ε := by
    simp only [dotProduct]
    fun_prop
  have h00 : (0 : Matrix T m ℝ) t = 0 := rfl
  have hq0 : ((0 : Matrix T m ℝ) t ⬝ᵥ (0 : Matrix T m ℝ) t) / (Fintype.card m : ℝ) + ε = ε := by
    rw [h00, zero_dotProduct, zero_div, zero_add]
  have hs : DifferentiableAt ℝ
      (fun h : Matrix T m ℝ => (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card m : ℝ) + ε))⁻¹) 0 := by
    have hpos : 0 < ((0 : Matrix T m ℝ) t ⬝ᵥ (0 : Matrix T m ℝ) t) / (Fintype.card m : ℝ) + ε := by
      rw [hq0]
      exact hε
    exact ((hq 0).sqrt hpos.ne').inv (Real.sqrt_pos.2 hpos).ne'
  have hp : HasFDerivAt (fun h : Matrix T m ℝ => h t i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : m => ℝ) i).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => m → ℝ) t)) 0 :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : m => ℝ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => m → ℝ) t)).hasFDerivAt
  have h := hs.hasFDerivAt.mul hp
  show HasFDerivAt (fun h : Matrix T m ℝ =>
    (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card m : ℝ) + ε))⁻¹ * h t i) _ 0
  refine h.congr_fderiv (ContinuousLinearMap.ext fun M => ?_)
  show (Real.sqrt (((0 : Matrix T m ℝ) t ⬝ᵥ (0 : Matrix T m ℝ) t) / (Fintype.card m : ℝ) + ε))⁻¹
      * M t i + (0 : Matrix T m ℝ) t i * _ = (Real.sqrt ε)⁻¹ * M t i
  rw [hq0, Matrix.zero_apply, zero_mul, add_zero]

/-- Helper: `(c A_1) ⋯ (c A_k) = c^k A_1 ⋯ A_k`. -/
private theorem prod_ofFn_smul_atn {m : Type*} [Fintype m] [DecidableEq m] (c : ℝ) {k : ℕ}
    (A : Fin k → Matrix m m ℝ) :
    (List.ofFn fun ℓ => c • A ℓ).prod = c ^ k • (List.ofFn A).prod := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ih fun ℓ => A ℓ.succ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ']

/-- Helper: `ξ E ∏_ℓ (I + ξ λ V_ℓ) D`: the residual network multiplies the row `b` by this
matrix along `a b`, for `U a = λ a`. -/
private noncomputable def resMat_atn {sees : T → T → Prop} [DecidableRel sees]
    {χ : Matrix T d ℝ → Matrix T d ℝ} (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (ξ lam : ℝ) : Matrix dIn dOut ℝ :=
  ξ • (θ.E * (List.ofFn fun ℓ => 1 + (ξ * lam) • valueOutput θ ℓ).prod * θ.D)

/-- Helper, **the core of the proof of Theorem 4.2**: if the residual network (stream matrices
`1`) equals the skipless one (stream matrices `0`, `L' + 1` blocks), then for every eigenvalue
`λ` of `U` with an eigencolumn `a ≠ 0`, `ξ E ∏_ℓ (I + ξ λ V_ℓ) D = λ^{L'+1} Λ'`, with
`Λ' = ξ'^{L'+2} E' V'_1 ⋯ V'_{L'+1} D'` not depending on `λ`. -/
private theorem core_atn {sees : T → T → Prop} [DecidableRel sees]
    {χ : Matrix T d ℝ → Matrix T d ℝ} {ξ : ℝ} (hχ0 : χ 0 = 0)
    (hχ : HasFDerivAt χ (ξ • ContinuousLinearMap.id ℝ (Matrix T d ℝ)) 0)
    {L' : ℕ} {d' : Type*} [Fintype d'] [DecidableEq d'] {χ' : Matrix T d' ℝ → Matrix T d' ℝ}
    {ξ' : ℝ} (hχ0' : χ' 0 = 0)
    (hχ' : HasFDerivAt χ' (ξ' • ContinuousLinearMap.id ℝ (Matrix T d' ℝ)) 0)
    {H' dh' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)]
    (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (θ' : Params (Arch.attention sees χ' H' dh') dIn dOut)
    (heq : ∀ X, eval (Arch.attention sees χ H dh) 1 θ X
      = eval (Arch.attention sees χ' H' dh') 0 θ' X)
    {a : T → ℝ} {lam : ℝ} (ha : attnWeights sees 0 *ᵥ a = lam • a) (ha0 : a ≠ 0) :
    resMat_atn θ ξ lam = lam ^ (L' + 1) • (ξ' ^ (L' + 2)
      • (θ'.E * (List.ofFn fun ℓ => valueOutput θ' ℓ).prod * θ'.D)) := by
  -- a token `t` with `a t ≠ 0`
  obtain ⟨t, ht⟩ := Function.ne_iff.1 ha0
  -- the two networks agree on the line `τ a b`, so their derivatives at `τ = 0` agree
  have hrow : ∀ b : dIn → ℝ,
      ξ • (b ᵥ* (θ.E * (List.ofFn fun ℓ => (1 : ℝ) • (1 : Matrix d d ℝ)
        + (ξ * lam) • valueOutput θ ℓ).prod * θ.D))
      = ξ' • (b ᵥ* (θ'.E * (List.ofFn fun ℓ => (0 : ℝ) • (1 : Matrix d' d' ℝ)
        + (ξ' * lam) • valueOutput θ' ℓ).prod * θ'.D)) := by
    intro b
    have h1 := hasDerivAt_eval_attention_zero sees χ ξ hχ0 hχ H dh θ 1 a lam ha b
    have h2 := hasDerivAt_eval_attention_zero sees χ' ξ' hχ0' hχ' H' dh' θ' 0 a lam ha b
    have hfun : (fun τ : ℝ => eval (Arch.attention sees χ H dh)
        (fun _ => (1 : ℝ) • (1 : Matrix d d ℝ)) θ (τ • vecMulVec a b))
        = fun τ => eval (Arch.attention sees χ' H' dh')
          (fun _ => (0 : ℝ) • (1 : Matrix d' d' ℝ)) θ' (τ • vecMulVec a b) := by
      funext τ
      simp only [one_smul, zero_smul]
      exact heq _
    rw [hfun] at h1
    have h := h1.unique h2
    -- the entry `(t, o)` of `a (ξ b M) = a (ξ' b M')`, divided by `a t ≠ 0`
    funext o
    have h' := congrFun (congrFun h t) o
    simp only [vecMulVec_apply] at h'
    exact mul_left_cancel₀ ht h'
  -- the rows `b = e_i` give the matrices
  have hM : ξ • (θ.E * (List.ofFn fun ℓ => (1 : ℝ) • (1 : Matrix d d ℝ)
        + (ξ * lam) • valueOutput θ ℓ).prod * θ.D)
      = ξ' • (θ'.E * (List.ofFn fun ℓ => (0 : ℝ) • (1 : Matrix d' d' ℝ)
        + (ξ' * lam) • valueOutput θ' ℓ).prod * θ'.D) := by
    classical
    ext i o
    have h := congrFun (hrow (Pi.single i 1)) o
    simp only [single_one_vecMul, Pi.smul_apply, Matrix.row_apply] at h
    simpa only [Matrix.smul_apply] using h
  simp only [one_smul, zero_smul, zero_add] at hM
  -- pull `ξ' λ` out of the `L' + 1` factors
  rw [resMat_atn, hM, prod_ofFn_smul_atn, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul]
  congr 1
  ring

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: at `λ = 0` the matrix `ξ E ∏_ℓ (I + ξ λ V_ℓ) D` is `ξ E D`. -/
private theorem resMat_zero_atn {sees : T → T → Prop} [DecidableRel sees]
    {χ : Matrix T d ℝ → Matrix T d ℝ} (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (ξ : ℝ) : resMat_atn θ ξ 0 = ξ • (θ.E * θ.D) := by
  simp [resMat_atn]

/-- Helper: without a mask every entry of `U` is `1 / T`, so `U a = 0` for the column
`a = e_{t₁} − e_{t₂} ≠ 0`. -/
private theorem exists_kernel_noMask_atn (hT : 2 ≤ Fintype.card T) :
    ∃ a : T → ℝ, a ≠ 0 ∧ attnWeights (fun _ _ : T => True) 0 *ᵥ a = (0 : ℝ) • a := by
  classical
  obtain ⟨t₁, t₂, h12⟩ := Fintype.one_lt_card_iff.1 hT
  refine ⟨Pi.single t₁ 1 - Pi.single t₂ 1, fun h => ?_, ?_⟩
  · have h1 := congrFun h t₁
    simp [h12] at h1
  · ext t
    simp [attnWeights, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_pi_single']

/-- Helper: under the causal mask row `t` of `U` is uniform on the `t + 1` tokens `s ≤ t`. -/
private theorem attnWeights_causal_atn {n : ℕ} (t s : Fin n) :
    attnWeights (fun t s : Fin n => s ≤ t) 0 t s = if s ≤ t then 1 / ((t : ℝ) + 1) else 0 := by
  simp only [attnWeights, Matrix.of_apply, Matrix.zero_apply, Real.exp_zero]
  split_ifs with h
  · rw [Finset.sum_boole, Finset.filter_ge_eq_Iic, Fin.card_Iic]
    push_cast
    rfl
  · rfl

/-- Helper: under the causal mask `U` is lower triangular with the diagonal entries
`1 / (t + 1)`, so each `1 / (t + 1)` is an eigenvalue with a nonzero eigencolumn. -/
private theorem exists_eigen_causal_atn {n : ℕ} (t : Fin n) {lam : ℝ}
    (hlam : lam = 1 / ((t : ℝ) + 1)) :
    ∃ a : Fin n → ℝ, a ≠ 0 ∧ attnWeights (fun t s : Fin n => s ≤ t) 0 *ᵥ a = lam • a := by
  set M := attnWeights (fun t s : Fin n => s ≤ t) 0 - lam • (1 : Matrix (Fin n) (Fin n) ℝ)
    with hM
  -- `U − λ I` is lower triangular with the diagonal entry `0` at `t`
  have hlow : M.IsLowerTriangular := fun i j hij => by
    have hij' : i < j := hij
    rw [hM, Matrix.sub_apply, attnWeights_causal_atn, Matrix.smul_apply,
      Matrix.one_apply_ne hij'.ne, ite_eq_right (not_le.2 hij'), smul_zero, sub_zero]
  have hdet : M.det = 0 := by
    rw [Matrix.det_of_isLowerTriangular M hlow]
    refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
    rw [hM, Matrix.sub_apply, attnWeights_causal_atn, ite_eq_left le_rfl, Matrix.smul_apply,
      Matrix.one_apply_eq, hlam, smul_eq_mul, mul_one, sub_self]
  obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine ⟨a, ha0, ?_⟩
  rw [hM, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at ha
  exact ha

/-- Helper, **Theorem 4.2 (i) without a mask**, for any `χ` with `χ(0) = 0` and the derivative
`ξ I` at `0`, `ξ ≠ 0`: at `λ = 0` the core gives `ξ E D = 0`. -/
private theorem noMask_atn (hT : 2 ≤ Fintype.card T) {χ : Matrix T d ℝ → Matrix T d ℝ} {ξ : ℝ}
    (hξ : ξ ≠ 0) (hχ0 : χ 0 = 0)
    (hχ : HasFDerivAt χ (ξ • ContinuousLinearMap.id ℝ (Matrix T d ℝ)) 0)
    (θ : Params (Arch.attention (fun _ _ => True) χ H dh) dIn dOut) (hED : θ.E * θ.D ≠ 0)
    {L' : ℕ} {d' : Type*} [Fintype d'] [DecidableEq d'] {χ' : Matrix T d' ℝ → Matrix T d' ℝ}
    {ξ' : ℝ} (hχ0' : χ' 0 = 0)
    (hχ' : HasFDerivAt χ' (ξ' • ContinuousLinearMap.id ℝ (Matrix T d' ℝ)) 0)
    {H' dh' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)]
    (θ' : Params (Arch.attention (fun _ _ => True) χ' H' dh') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.attention (fun _ _ => True) χ H dh) 1 θ X
        ≠ eval (Arch.attention (fun _ _ => True) χ' H' dh') 0 θ' X := by
  by_contra hne
  have heq : ∀ X, eval (Arch.attention (fun _ _ => True) χ H dh) 1 θ X
      = eval (Arch.attention (fun _ _ => True) χ' H' dh') 0 θ' X :=
    fun X => by_contra fun hX => hne ⟨X, hX⟩
  -- `U a = 0 a` for a column `a ≠ 0`; at `λ = 0` the core reads `ξ E D = 0^{L'+1} Λ' = 0`
  obtain ⟨a, ha0, ha⟩ := exists_kernel_noMask_atn (T := T) hT
  have h := core_atn hχ0 hχ hχ0' hχ' θ θ' heq ha ha0
  rw [resMat_zero_atn, zero_pow (Nat.succ_ne_zero L'), zero_smul] at h
  exact hED ((smul_eq_zero.1 h).resolve_left hξ)

/-- **Theorem 4.2 (i), no mask, without normalization:** with at least two tokens, a residual
network of `L` attention blocks with `E D ≠ 0` differs from every skipless network of one or more
attention blocks, with any heads, head dimensions and model dimension. -/
theorem exists_ne_residual_skipless_attention_noMask (hT : 2 ≤ Fintype.card T)
    (θ : Params (Arch.attention (T := T) (d := d) (fun _ _ => True) id H dh) dIn dOut)
    (hED : θ.E * θ.D ≠ 0) {L' : ℕ} {d' : Type*} [Fintype d'] [DecidableEq d']
    {H' dh' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)]
    (θ' : Params (Arch.attention (T := T) (d := d') (fun _ _ => True) id H' dh') dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.attention (fun _ _ => True) id H dh) 1 θ X
        ≠ eval (Arch.attention (fun _ _ => True) id H' dh') 0 θ' X := by
  -- without normalization `χ = id`: `χ(0) = 0` and the derivative is `1 • I`
  exact noMask_atn hT one_ne_zero rfl (by rw [one_smul]; exact hasFDerivAt_id 0) θ hED rfl
    (by rw [one_smul]; exact hasFDerivAt_id 0) θ'

/-- **Theorem 4.2 (i), no mask, under pre-RMSNorm with `ε > 0`.** -/
theorem exists_ne_residual_skipless_attention_noMask_rmsNorm (hT : 2 ≤ Fintype.card T)
    {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    (θ : Params (Arch.attention (T := T) (d := d) (fun _ _ => True) (rmsNorm ε) H dh) dIn dOut)
    (hED : θ.E * θ.D ≠ 0) {L' : ℕ} {d' : Type*} [Fintype d'] [DecidableEq d']
    {H' dh' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)]
    (θ' : Params (Arch.attention (T := T) (d := d') (fun _ _ => True) (rmsNorm ε') H' dh')
      dIn dOut) :
    ∃ X : Matrix T dIn ℝ,
      eval (Arch.attention (fun _ _ => True) (rmsNorm ε) H dh) 1 θ X
        ≠ eval (Arch.attention (fun _ _ => True) (rmsNorm ε') H' dh') 0 θ' X := by
  -- RMSNorm: `N(0) = 0` and the derivative `I / √ε` at `0`, with `1 / √ε ≠ 0`
  exact noMask_atn hT (inv_ne_zero (Real.sqrt_pos.2 hε).ne') (rmsNorm_zero_mat_atn ε)
    (hasFDerivAt_rmsNorm_zero_atn hε) θ hED (rmsNorm_zero_mat_atn ε')
    (hasFDerivAt_rmsNorm_zero_atn hε') θ'

/-- **Theorem 4.2 (i), causal mask, without normalization:** on `n` tokens with the causal mask,
a residual network of `L` attention blocks with `E D ≠ 0` differs from every skipless network of
`L' + 1` attention blocks when `n ≥ L + 2`, and when `n = L + 1` and `L' + 1 ≤ L`. -/
theorem exists_ne_residual_skipless_attention_causal {n : ℕ}
    (θ : Params (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) id H dh) dIn dOut)
    (hED : θ.E * θ.D ≠ 0) {L' : ℕ} {d' : Type*} [Fintype d'] [DecidableEq d']
    {H' dh' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)]
    (θ' : Params (Arch.attention (T := Fin n) (d := d') (fun t s => s ≤ t) id H' dh') dIn dOut)
    (hn : L + 2 ≤ n ∨ (n = L + 1 ∧ L' + 1 ≤ L)) :
    ∃ X : Matrix (Fin n) dIn ℝ,
      eval (Arch.attention (fun t s => s ≤ t) id H dh) 1 θ X
        ≠ eval (Arch.attention (fun t s => s ≤ t) id H' dh') 0 θ' X := by
  sorry

/-- **Theorem 4.2 (i), causal mask, under pre-RMSNorm with `ε > 0`.** -/
theorem exists_ne_residual_skipless_attention_causal_rmsNorm {n : ℕ} {ε ε' : ℝ} (hε : 0 < ε)
    (hε' : 0 < ε')
    (θ : Params (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) (rmsNorm ε) H dh)
      dIn dOut)
    (hED : θ.E * θ.D ≠ 0) {L' : ℕ} {d' : Type*} [Fintype d'] [DecidableEq d']
    {H' dh' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)]
    (θ' : Params (Arch.attention (T := Fin n) (d := d') (fun t s => s ≤ t) (rmsNorm ε') H' dh')
      dIn dOut)
    (hn : L + 2 ≤ n ∨ (n = L + 1 ∧ L' + 1 ≤ L)) :
    ∃ X : Matrix (Fin n) dIn ℝ,
      eval (Arch.attention (fun t s => s ≤ t) (rmsNorm ε) H dh) 1 θ X
        ≠ eval (Arch.attention (fun t s => s ≤ t) (rmsNorm ε') H' dh') 0 θ' X := by
  sorry

/-- **Theorem 4.2 (ii), causal mask, without normalization:** on `n ≥ 2` tokens with the causal
mask, for almost every choice of weights of the residual network of `L` attention blocks, no
skipless network of one or more attention blocks equals it, whatever its depth, heads, head
dimensions and model dimension. -/
theorem ae_forall_ne_residual_skipless_attention_causal [Nonempty d] [Nonempty dIn]
    [Nonempty dOut] {n : ℕ} (hn : 2 ≤ n)
    (μ : Measure (Params (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) id H dh)
      dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] [DecidableEq d'] (H' dh' : Fin (L' + 1) → Type)
      [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)]
      (θ' : Params (Arch.attention (T := Fin n) (d := d') (fun t s => s ≤ t) id H' dh')
        dIn dOut),
      ∃ X : Matrix (Fin n) dIn ℝ,
        eval (Arch.attention (fun t s => s ≤ t) id H dh) 1 θ X
          ≠ eval (Arch.attention (fun t s => s ≤ t) id H' dh') 0 θ' X := by
  sorry

/-- **Theorem 4.2 (ii), causal mask, under pre-RMSNorm with `ε > 0`.** -/
theorem ae_forall_ne_residual_skipless_attention_causal_rmsNorm [Nonempty d] [Nonempty dIn]
    [Nonempty dOut] {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] [DecidableEq d'] (H' dh' : Fin (L' + 1) → Type)
      [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)] (ε' : ℝ), 0 < ε' →
      ∀ θ' : Params (Arch.attention (T := Fin n) (d := d') (fun t s => s ≤ t) (rmsNorm ε') H' dh')
        dIn dOut,
      ∃ X : Matrix (Fin n) dIn ℝ,
        eval (Arch.attention (fun t s => s ≤ t) (rmsNorm ε) H dh) 1 θ X
          ≠ eval (Arch.attention (fun t s => s ≤ t) (rmsNorm ε') H' dh') 0 θ' X := by
  sorry

end Skips
