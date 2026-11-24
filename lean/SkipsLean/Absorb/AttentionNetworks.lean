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

/-- Helper: the factor `I + ξ z V` of a block, as a matrix of polynomials in `z`. -/
private noncomputable def polyFactor_atn (ξ : ℝ) (V : Matrix d d ℝ) :
    Matrix d d (Polynomial ℝ) :=
  1 + (Polynomial.C ξ * Polynomial.X) • V.map Polynomial.C

/-- Helper: the entry `(i, o)` of `ξ E ∏_ℓ (I + ξ z V_ℓ) D`, a polynomial in `z`. -/
private noncomputable def polyEntry_atn {sees : T → T → Prop} [DecidableRel sees]
    {χ : Matrix T d ℝ → Matrix T d ℝ} (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (ξ : ℝ) (i : dIn) (o : dOut) : Polynomial ℝ :=
  Polynomial.C ξ * (θ.E.map Polynomial.C
    * (List.ofFn fun ℓ => polyFactor_atn ξ (valueOutput θ ℓ)).prod * θ.D.map Polynomial.C) i o

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: at `z = λ` the entry polynomial is the entry of `ξ E ∏_ℓ (I + ξ λ V_ℓ) D`. -/
private theorem eval_polyEntry_atn {sees : T → T → Prop} [DecidableRel sees]
    {χ : Matrix T d ℝ → Matrix T d ℝ} (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (ξ lam : ℝ) (i : dIn) (o : dOut) :
    (polyEntry_atn θ ξ i o).eval lam = resMat_atn θ ξ lam i o := by
  have hE : (θ.E.map Polynomial.C).map (Polynomial.evalRingHom lam) = θ.E := by
    ext
    simp
  have hD : (θ.D.map Polynomial.C).map (Polynomial.evalRingHom lam) = θ.D := by
    ext
    simp
  -- evaluation at `λ` is a ring map, so it commutes with the product of the factors
  have hprod : ((List.ofFn fun ℓ => polyFactor_atn ξ (valueOutput θ ℓ)).prod).map
      (Polynomial.evalRingHom lam) = (List.ofFn fun ℓ => 1 + (ξ * lam) • valueOutput θ ℓ).prod := by
    rw [← RingHom.mapMatrix_apply, map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun ℓ => ?_))
    ext a b
    by_cases hab : a = b <;> simp [polyFactor_atn, hab]
  have hentry : (polyEntry_atn θ ξ i o).eval lam
      = ξ * ((θ.E.map Polynomial.C * (List.ofFn fun ℓ => polyFactor_atn ξ (valueOutput θ ℓ)).prod
        * θ.D.map Polynomial.C).map (Polynomial.evalRingHom lam)) i o := by
    rw [polyEntry_atn, Polynomial.eval_mul, Polynomial.eval_C]
    rfl
  rw [hentry, Matrix.map_mul, Matrix.map_mul, hE, hD, hprod, resMat_atn, Matrix.smul_apply,
    smul_eq_mul]

/-- Helper: the entries of a product of matrices of polynomials of degrees `≤ a` and `≤ b` have
degree `≤ a + b`. -/
private theorem natDegree_mul_apply_le_atn {m n p : Type*} [Fintype n]
    {M : Matrix m n (Polynomial ℝ)} {N : Matrix n p (Polynomial ℝ)} {a b : ℕ}
    (hM : ∀ i j, (M i j).natDegree ≤ a) (hN : ∀ i j, (N i j).natDegree ≤ b) (i : m) (j : p) :
    ((M * N) i j).natDegree ≤ a + b := by
  rw [Matrix.mul_apply]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ =>
    Polynomial.natDegree_mul_le.trans (add_le_add (hM i k) (hN k j))

/-- Helper: the entries of `∏_{ℓ < k} (I + ξ z V_ℓ)` have degree `≤ k`. -/
private theorem natDegree_prod_atn (ξ : ℝ) {k : ℕ} (V : Fin k → Matrix d d ℝ) (i j : d) :
    ((List.ofFn fun ℓ => polyFactor_atn ξ (V ℓ)).prod i j).natDegree ≤ k := by
  induction k generalizing i j with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil, Matrix.one_apply]
    split_ifs <;> simp
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    -- each factor has entries of degree `≤ 1`
    have hF : ∀ i j, (polyFactor_atn ξ (V 0) i j).natDegree ≤ 1 := by
      intro i j
      simp only [polyFactor_atn, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
        smul_eq_mul, Matrix.one_apply]
      refine Polynomial.natDegree_add_le_of_degree_le ?_ ?_
      · split_ifs <;> simp
      · compute_degree
    have h := natDegree_mul_apply_le_atn hF (ih fun ℓ => V ℓ.succ) i j
    omega

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: the entry polynomial has degree `≤ L`. -/
private theorem natDegree_polyEntry_atn {sees : T → T → Prop} [DecidableRel sees]
    {χ : Matrix T d ℝ → Matrix T d ℝ} (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (ξ : ℝ) (i : dIn) (o : dOut) : (polyEntry_atn θ ξ i o).natDegree ≤ L := by
  have hE : ∀ i j, (θ.E.map Polynomial.C i j).natDegree ≤ 0 := fun i j => by simp
  have hD : ∀ i j, (θ.D.map Polynomial.C i j).natDegree ≤ 0 := fun i j => by simp
  have h := natDegree_mul_apply_le_atn (natDegree_mul_apply_le_atn hE
    (natDegree_prod_atn ξ fun ℓ => valueOutput θ ℓ)) hD i o
  rw [polyEntry_atn]
  exact (Polynomial.natDegree_C_mul_le _ _).trans (h.trans (by omega))

/-- Helper: a list has fewer sign variations than entries. -/
private theorem signVariations_le_length_atn (l : List ℝ) :
    l.signVariations ≤ l.length - 1 := by
  unfold List.signVariations
  apply Nat.sub_le_sub_right
  exact (List.destutter_sublist _ _).length_le.trans
    ((List.length_filter_le _ _).trans (List.length_map _).le)

/-- Helper: a polynomial has at most as many sign variations as its degree. -/
private theorem signVariations_le_natDegree_atn (q : Polynomial ℝ) :
    q.signVariations ≤ q.natDegree := by
  classical
  have h := signVariations_le_length_atn q.coeffList
  rw [Polynomial.length_coeffList_eq_ite] at h
  unfold Polynomial.signVariations
  split_ifs at h <;> omega

/-- Helper, **the root count**: let `p = q − c z^m`, `deg q ≤ L`, vanish at the `n` points
`1 / (t + 1)`. If `n ≥ L + 2`, or `n = L + 1` and `m ≤ L`, then `p = 0`. If `c = 0` or `m ≤ L`,
`p` has degree `≤ L < n` and `n` roots. Otherwise `m > L`, `n ≥ L + 2`, and by Descartes' rule
of signs `p ≠ 0` would have at most `L + 1` positive roots (dropping its leading term `−c z^m`
leaves `q`, with at most `L` sign variations). -/
private theorem poly_eq_zero_atn {n m : ℕ} (q : Polynomial ℝ) (c : ℝ) (hq : q.natDegree ≤ L)
    (hroot : ∀ t : Fin n,
      (q - Polynomial.C c * Polynomial.X ^ m).eval (1 / ((t : ℝ) + 1)) = 0)
    (hn : L + 2 ≤ n ∨ (n = L + 1 ∧ m ≤ L)) : q - Polynomial.C c * Polynomial.X ^ m = 0 := by
  -- the points `1 / (t + 1)` are distinct
  have hinj : Function.Injective fun t : Fin n => 1 / ((t : ℝ) + 1) := by
    intro x y hxy
    simp only [one_div, _root_.inv_inj, add_left_inj, Nat.cast_inj] at hxy
    exact Fin.ext hxy
  -- a polynomial of degree `< n` with these `n` roots is `0`
  have hcard : (q - Polynomial.C c * Polynomial.X ^ m).natDegree < n →
      q - Polynomial.C c * Polynomial.X ^ m = 0 := fun h =>
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj hroot
      (by rwa [Fintype.card_fin])
  by_cases hc : c = 0
  · apply hcard
    rw [hc, Polynomial.C_0, zero_mul, sub_zero]
    omega
  by_cases hm : m ≤ L
  · apply hcard
    have := (Polynomial.natDegree_sub_le _ _).trans
      (max_le hq ((Polynomial.natDegree_C_mul_X_pow_le c m).trans hm))
    omega
  -- `m > L`, so `n ≥ L + 2`: Descartes' rule of signs
  have hn2 : L + 2 ≤ n := by omega
  by_contra hp0
  -- `p` has the `n` distinct positive roots `1 / (t + 1)`
  have hroots : n ≤ (q - Polynomial.C c * Polynomial.X ^ m).roots.countP (0 < ·) := by
    classical
    have hS : (Finset.univ.image fun t : Fin n => 1 / ((t : ℝ) + 1)).card = n := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    rw [Multiset.countP_eq_card_filter, ← hS]
    refine Multiset.card_le_card ((Multiset.le_iff_subset (Finset.nodup _)).2 fun x hx => ?_)
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_def.2 hx)
    refine Multiset.mem_filter.2 ⟨(Polynomial.mem_roots hp0).2 (hroot t), ?_⟩
    show 0 < 1 / ((t : ℝ) + 1)
    positivity
  -- dropping the leading term `−c z^m` leaves `q`
  have hlead : (q - Polynomial.C c * Polynomial.X ^ m).eraseLead = q := by
    rw [sub_eq_add_neg, ← neg_mul, ← Polynomial.C_neg,
      Polynomial.eraseLead_add_of_natDegree_lt_right, Polynomial.eraseLead_C_mul_X_pow, add_zero]
    rw [Polynomial.natDegree_C_mul_X_pow m (-c) (neg_ne_zero.2 hc)]
    omega
  have h1 := Polynomial.roots_countP_pos_le_signVariations (q - Polynomial.C c * Polynomial.X ^ m)
  have h2 := Polynomial.signVariations_le_eraseLead_succ (q - Polynomial.C c * Polynomial.X ^ m)
  have h3 := signVariations_le_natDegree_atn q
  rw [hlead] at h2
  omega

/-- Helper, **Theorem 4.2 (i) with the causal mask**, for any `χ` as in `noMask_atn`: every
entry of `ξ E ∏_ℓ (I + ξ z V_ℓ) D − z^{L'+1} Λ'` vanishes at the `n` eigenvalues `1 / (t + 1)`
of `U`, so it is the zero polynomial (`poly_eq_zero_atn`); at `z = 0` it is `ξ E D`. -/
private theorem causal_atn {n : ℕ} {χ : Matrix (Fin n) d ℝ → Matrix (Fin n) d ℝ} {ξ : ℝ}
    (hξ : ξ ≠ 0) (hχ0 : χ 0 = 0)
    (hχ : HasFDerivAt χ (ξ • ContinuousLinearMap.id ℝ (Matrix (Fin n) d ℝ)) 0)
    (θ : Params (Arch.attention (fun t s : Fin n => s ≤ t) χ H dh) dIn dOut)
    (hED : θ.E * θ.D ≠ 0) {L' : ℕ} {d' : Type*} [Fintype d'] [DecidableEq d']
    {χ' : Matrix (Fin n) d' ℝ → Matrix (Fin n) d' ℝ} {ξ' : ℝ} (hχ0' : χ' 0 = 0)
    (hχ' : HasFDerivAt χ' (ξ' • ContinuousLinearMap.id ℝ (Matrix (Fin n) d' ℝ)) 0)
    {H' dh' : Fin (L' + 1) → Type} [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)]
    (θ' : Params (Arch.attention (fun t s : Fin n => s ≤ t) χ' H' dh') dIn dOut)
    (hn : L + 2 ≤ n ∨ (n = L + 1 ∧ L' + 1 ≤ L)) :
    ∃ X : Matrix (Fin n) dIn ℝ,
      eval (Arch.attention (fun t s : Fin n => s ≤ t) χ H dh) 1 θ X
        ≠ eval (Arch.attention (fun t s : Fin n => s ≤ t) χ' H' dh') 0 θ' X := by
  by_contra hne
  have heq : ∀ X, eval (Arch.attention (fun t s : Fin n => s ≤ t) χ H dh) 1 θ X
      = eval (Arch.attention (fun t s : Fin n => s ≤ t) χ' H' dh') 0 θ' X :=
    fun X => by_contra fun hX => hne ⟨X, hX⟩
  -- `Λ' = ξ'^{L'+2} E' V'_1 ⋯ V'_{L'+1} D'`
  obtain ⟨Λ', hΛ'⟩ : ∃ Λ' : Matrix dIn dOut ℝ,
      Λ' = ξ' ^ (L' + 2) • (θ'.E * (List.ofFn fun ℓ => valueOutput θ' ℓ).prod * θ'.D) :=
    ⟨_, rfl⟩
  apply hED
  ext i o
  -- the entry polynomial `q − Λ'_{io} z^{L'+1}` vanishes at every `1 / (t + 1)`
  have hroot : ∀ t : Fin n, (polyEntry_atn θ ξ i o
      - Polynomial.C (Λ' i o) * Polynomial.X ^ (L' + 1)).eval (1 / ((t : ℝ) + 1)) = 0 := by
    intro t
    obtain ⟨a, ha0, ha⟩ := exists_eigen_causal_atn t rfl
    have h := core_atn hχ0 hχ hχ0' hχ' θ θ' heq ha ha0
    rw [← hΛ'] at h
    rw [Polynomial.eval_sub, eval_polyEntry_atn, h, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Matrix.smul_apply, smul_eq_mul]
    ring
  have hp := poly_eq_zero_atn _ _ (natDegree_polyEntry_atn θ ξ i o) hroot hn
  -- at `z = 0`: `ξ (E D)_{io} = 0`
  have h0 := congrArg (Polynomial.eval 0) hp
  rw [Polynomial.eval_sub, eval_polyEntry_atn, resMat_zero_atn, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, zero_pow (Nat.succ_ne_zero L'),
    mul_zero, sub_zero, Polynomial.eval_zero, Matrix.smul_apply, smul_eq_mul] at h0
  exact (mul_eq_zero.1 h0).resolve_left hξ

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
  -- without normalization `χ = id`: `χ(0) = 0` and the derivative is `1 • I`
  exact causal_atn one_ne_zero rfl (by rw [one_smul]; exact hasFDerivAt_id 0) θ hED rfl
    (by rw [one_smul]; exact hasFDerivAt_id 0) θ' hn

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
  -- RMSNorm: `N(0) = 0` and the derivative `I / √ε` at `0`, with `1 / √ε ≠ 0`
  exact causal_atn (inv_ne_zero (Real.sqrt_pos.2 hε).ne') (rmsNorm_zero_mat_atn ε)
    (hasFDerivAt_rmsNorm_zero_atn hε) θ hED (rmsNorm_zero_mat_atn ε')
    (hasFDerivAt_rmsNorm_zero_atn hε') θ' hn

/-- Helper: the entries of a product of two matrices with analytic entries are analytic (as
`analyticOnNhd_mul_entry` in `Absorb/Networks.lean`). -/
private theorem analyticOnNhd_mul_entry_atn {P m n p : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [Fintype n] {M : P → Matrix m n ℝ} {N : P → Matrix n p ℝ}
    (hM : ∀ i j, AnalyticOnNhd ℝ (fun y => M y i j) Set.univ)
    (hN : ∀ i j, AnalyticOnNhd ℝ (fun y => N y i j) Set.univ) (i : m) (j : p) :
    AnalyticOnNhd ℝ (fun y => (M y * N y) i j) Set.univ := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticOnNhd_fun_sum _ fun k _ => (hM i k).mul (hN k j)

/-- Helper: the entries of `A_1 ⋯ A_k` are analytic if those of every `A_ℓ` are. -/
private theorem analyticOnNhd_prod_atn {P m : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [Fintype m] [DecidableEq m] {k : ℕ} {A : P → Fin k → Matrix m m ℝ}
    (hA : ∀ ℓ i j, AnalyticOnNhd ℝ (fun y => A y ℓ i j) Set.univ) (i j : m) :
    AnalyticOnNhd ℝ (fun y => (List.ofFn (A y)).prod i j) Set.univ := by
  induction k generalizing i j with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil]
    exact analyticOnNhd_const
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact analyticOnNhd_mul_entry_atn (hA 0) (ih (A := fun y ℓ => A y ℓ.succ) fun ℓ => hA ℓ.succ)
      i j

/-- Helper: a linear functional on a finite-dimensional space is analytic. -/
private theorem analyticOnNhd_of_linear_atn {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] (l : P →ₗ[ℝ] ℝ) : AnalyticOnNhd ℝ l Set.univ := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).analyticOnNhd _

/-- Helper: every entry of `ξ E ∏_ℓ (I + ξ λ V_ℓ) D` is an analytic (polynomial) function of the
weights: the entries of `E`, `D`, the reads and the writes are linear in them. -/
private theorem analyticOnNhd_resMat_atn {sees : T → T → Prop} [DecidableRel sees]
    {χ : Matrix T d ℝ → Matrix T d ℝ} (ξ lam : ℝ) (i : dIn) (o : dOut) :
    AnalyticOnNhd ℝ (fun θ : Params (Arch.attention sees χ H dh) dIn dOut =>
      resMat_atn θ ξ lam i o) Set.univ := by
  have hE : ∀ i j, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention sees χ H dh) dIn dOut => θ.E i j) Set.univ := fun i j =>
    analyticOnNhd_of_linear_atn
      { toFun := fun θ : Params (Arch.attention sees χ H dh) dIn dOut => θ.E i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  have hD : ∀ i j, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention sees χ H dh) dIn dOut => θ.D i j) Set.univ := fun i j =>
    analyticOnNhd_of_linear_atn
      { toFun := fun θ : Params (Arch.attention sees χ H dh) dIn dOut => θ.D i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  -- `V_ℓ = ∑_h W_{V,h} W_{O,h}` is quadratic in the weights
  have hV : ∀ ℓ i j, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention sees χ H dh) dIn dOut => valueOutput θ ℓ i j)
      Set.univ := by
    intro ℓ i j
    simp only [valueOutput, Matrix.sum_apply, Matrix.mul_apply, Matrix.submatrix_apply, id]
    refine Finset.analyticOnNhd_fun_sum _ fun h _ => Finset.analyticOnNhd_fun_sum _ fun k _ => ?_
    exact (analyticOnNhd_of_linear_atn
      { toFun := fun θ : Params (Arch.attention sees χ H dh) dIn dOut =>
          θ.read ℓ i (h, Sum.inr (Sum.inr k))
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }).mul (analyticOnNhd_of_linear_atn
      { toFun := fun θ : Params (Arch.attention sees χ H dh) dIn dOut => θ.write ℓ (h, k) j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })
  have hF : ∀ ℓ i j, AnalyticOnNhd ℝ (fun θ : Params (Arch.attention sees χ H dh) dIn dOut =>
      (1 + (ξ * lam) • valueOutput θ ℓ) i j) Set.univ := by
    intro ℓ i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact analyticOnNhd_const.add (analyticOnNhd_const.mul (hV ℓ i j))
  simp only [resMat_atn, Matrix.smul_apply, smul_eq_mul]
  exact analyticOnNhd_const.mul (analyticOnNhd_mul_entry_atn (analyticOnNhd_mul_entry_atn hE
    (analyticOnNhd_prod_atn (A := fun θ ℓ => 1 + (ξ * lam) • valueOutput θ ℓ) hF)) hD i o)

/-- Helper, **Theorem 4.2 (ii)**, for any `χ` as in `noMask_atn`: let `F_θ(λ) =
ξ E ∏_ℓ (I + ξ λ V_ℓ) D` and `Q_{L'}(θ) = F_θ(1/2) − 2^{−(L'+1)} F_θ(1)`. A skipless network of
`L' + 1` blocks equal to `θ` gives `Q_{L'}(θ) = 0` (the core at the eigenvalues `1` and `1/2`).
An entry of `Q_{L'}` is a polynomial in the weights, equal to `ξ (1 − 2^{−(L'+1)}) ≠ 0` at
weights with all writes `0` and `(E D)_{io} = 1`, so it vanishes only on a null set; and so does
the union over `L'`. -/
private theorem ae_causal_atn [Nonempty d] [Nonempty dIn] [Nonempty dOut] {n : ℕ} (hn : 2 ≤ n)
    {χ : Matrix (Fin n) d ℝ → Matrix (Fin n) d ℝ} {ξ : ℝ} (hξ : ξ ≠ 0) (hχ0 : χ 0 = 0)
    (hχ : HasFDerivAt χ (ξ • ContinuousLinearMap.id ℝ (Matrix (Fin n) d ℝ)) 0)
    (μ : Measure (Params (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) χ H dh)
      dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ (L' : ℕ) (d' : Type) [Fintype d'] [DecidableEq d'] (H' dh' : Fin (L' + 1) → Type)
      [∀ ℓ, Fintype (H' ℓ)] [∀ ℓ, Fintype (dh' ℓ)] (χ' : Matrix (Fin n) d' ℝ → Matrix (Fin n) d' ℝ)
      (ξ' : ℝ), χ' 0 = 0 → HasFDerivAt χ' (ξ' • ContinuousLinearMap.id ℝ (Matrix (Fin n) d' ℝ)) 0 →
      ∀ θ' : Params (Arch.attention (T := Fin n) (d := d') (fun t s => s ≤ t) χ' H' dh') dIn dOut,
      ∃ X : Matrix (Fin n) dIn ℝ,
        eval (Arch.attention (fun t s => s ≤ t) χ H dh) 1 θ X
          ≠ eval (Arch.attention (fun t s => s ≤ t) χ' H' dh') 0 θ' X := by
  obtain ⟨i₀⟩ := ‹Nonempty dIn›
  obtain ⟨o₀⟩ := ‹Nonempty dOut›
  obtain ⟨k₀⟩ := ‹Nonempty d›
  -- the entry `(i₀, o₀)` of `Q_{L'}(θ)`
  let g : ℕ → Params (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) χ H dh) dIn dOut
      → ℝ := fun L' θ =>
    resMat_atn θ ξ (1 / 2) i₀ o₀ - (1 / 2) ^ (L' + 1) * resMat_atn θ ξ 1 i₀ o₀
  have hg : ∀ L', AnalyticOnNhd ℝ (g L') Set.univ := fun L' =>
    (analyticOnNhd_resMat_atn ξ (1 / 2) i₀ o₀).sub
      (analyticOnNhd_const.mul (analyticOnNhd_resMat_atn ξ 1 i₀ o₀))
  -- at weights with all writes `0` and `(E D)_{i₀ o₀} = 1`: `g = ξ (1 − 2^{−(L'+1)}) ≠ 0`
  have hne : ∀ L', ∃ θ₀, g L' θ₀ ≠ 0 := by
    intro L'
    classical
    let θ₀ : Params (Arch.attention (T := Fin n) (d := d) (fun t s => s ≤ t) χ H dh) dIn dOut :=
      ⟨Matrix.single i₀ k₀ 1, fun _ => 0, fun _ => 0, Matrix.single k₀ o₀ 1⟩
    have hV : ∀ ℓ, valueOutput θ₀ ℓ = 0 := fun ℓ => by
      simp [valueOutput, θ₀]
    have hR : ∀ lam, resMat_atn θ₀ ξ lam = ξ • (θ₀.E * θ₀.D) := fun lam => by
      simp [resMat_atn, hV]
    have hED : (θ₀.E * θ₀.D) i₀ o₀ = 1 := by
      simp [θ₀]
    have hlt : ((1 : ℝ) / 2) ^ (L' + 1) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero L')
    refine ⟨θ₀, fun h => ?_⟩
    simp only [g, hR, Matrix.smul_apply, hED, smul_eq_mul, mul_one] at h
    exact mul_ne_zero hξ (sub_ne_zero.2 hlt.ne') (by linear_combination h)
  -- so almost everywhere `g_{L'} ≠ 0` for all `L'` at once
  have hgen : ∀ᵐ θ ∂μ, ∀ L', g L' θ ≠ 0 := by
    rw [ae_all_iff]
    intro L'
    rw [ae_iff]
    simpa only [ne_eq, not_not] using measure_zeroSet_of_analytic μ (hg L') (hne L')
  filter_upwards [hgen] with θ hθ
  intro L' d' _ _ H' dh' _ _ χ' ξ' hχ0' hχ' θ'
  by_contra hne'
  have heq : ∀ X, eval (Arch.attention (fun t s : Fin n => s ≤ t) χ H dh) 1 θ X
      = eval (Arch.attention (fun t s : Fin n => s ≤ t) χ' H' dh') 0 θ' X :=
    fun X => by_contra fun hX => hne' ⟨X, hX⟩
  -- the eigenvalues `1` (token `0`) and `1/2` (token `1`): `F(1) = Λ'`, `F(1/2) = 2^{−(L'+1)} Λ'`
  obtain ⟨a₁, ha₁0, ha₁⟩ := exists_eigen_causal_atn (⟨0, by omega⟩ : Fin n) (lam := 1)
    (by norm_num)
  obtain ⟨a₂, ha₂0, ha₂⟩ := exists_eigen_causal_atn (⟨1, by omega⟩ : Fin n) (lam := 1 / 2)
    (by norm_num)
  have h1 := core_atn hχ0 hχ hχ0' hχ' θ θ' heq ha₁ ha₁0
  have h2 := core_atn hχ0 hχ hχ0' hχ' θ θ' heq ha₂ ha₂0
  apply hθ L'
  simp only [g, h1, h2, one_pow, Matrix.smul_apply, smul_eq_mul, one_mul, sub_self]

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
  -- without normalization `χ = id`: `χ(0) = 0` and the derivative is `1 • I`
  filter_upwards [ae_causal_atn hn (χ := id) one_ne_zero rfl
    (by rw [one_smul]; exact hasFDerivAt_id 0) μ] with θ hθ
  intro L' d' _ _ H' dh' _ _ θ'
  exact hθ L' d' H' dh' id 1 rfl (by rw [one_smul]; exact hasFDerivAt_id 0) θ'

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
  -- RMSNorm: `N(0) = 0` and the derivative `I / √ε` at `0`, with `1 / √ε ≠ 0`
  filter_upwards [ae_causal_atn hn (χ := rmsNorm ε) (inv_ne_zero (Real.sqrt_pos.2 hε).ne')
    (rmsNorm_zero_mat_atn ε) (hasFDerivAt_rmsNorm_zero_atn hε) μ] with θ hθ
  intro L' d' _ _ H' dh' _ _ ε' hε' θ'
  exact hθ L' d' H' dh' (rmsNorm ε') _ (rmsNorm_zero_mat_atn ε') (hasFDerivAt_rmsNorm_zero_atn hε')
    θ'

end Skips
