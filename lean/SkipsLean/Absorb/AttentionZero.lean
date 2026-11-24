import SkipsLean.Network.Attention
import SkipsLean.Network.Defs
import SkipsLean.Imports

/-!
# Networks of attention blocks near the input `0`

Paper (absorb paper): proof of Theorem 4.2 (Attention networks on long and short sequences), its
first two paragraphs: "Let `ξ = 1` without normalization and `ξ = 1/√ε` with pre-RMSNorm, so that
`N(h) = ξ h + O(‖h‖³)` near `h = 0` in the second case. The scores `h Γ_i h^⊤` of an attention
block are quadratic in `h`, so `P_{Γ_i}(h) = U + O(‖h‖²)`, where `U = softmax(0)` is the `T × T`
matrix whose row `t` is uniform on the tokens that token `t` attends to […]. Hence
`B_θ(h) = U h V + O(‖h‖³)`, where `V = ∑_i W_{V,i} W_{O,i}` is the sum of the value–output
products of the heads. Every map below fixes `0`, so the Jacobians at `0` compose. […] At
`X = 0` the skipless network has the Jacobian `δ ↦ U^{L'} δ Λ'` […]. Block `ℓ` of the residual
network has the Jacobian `δ ↦ δ + ξ U δ V_ℓ` at `0`."

The proof then uses these Jacobians only on the inputs `δ = a b` with `a` a column with
`U a = λ a` and `b` a row. On such `δ` block `ℓ` multiplies the row by `s I + ξ λ V_ℓ`, with
`s = 1` with the skip and `s = 0` without. This file states the derivative of the network at
`X = 0` along `a b` in that form, for a map `χ` with `χ(0) = 0` and the derivative `ξ I` at `0`
(the identity, or RMSNorm with `ε > 0`), and any mask.

* `valueOutput θ ℓ`: the matrix `V_ℓ` of block `ℓ`.
* `hasDerivAt_eval_attention_zero`: the derivative at `τ = 0` of the output at the input
  `τ • a b`, with the stream matrices `s I`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The sum `V_ℓ = ∑_i W_{V,i} W_{O,i}` of the value–output products of the heads of block
`ℓ`** of a network of attention blocks. -/
def valueOutput {sees : T → T → Prop} [DecidableRel sees] {χ : Matrix T d ℝ → Matrix T d ℝ}
    {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
    (θ : Params (Arch.attention sees χ H dh) dIn dOut) (ℓ : Fin L) : Matrix d d ℝ :=
  ∑ i : H ℓ, ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
    * ((θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id)

omit [Fintype d] [DecidableEq d] in
/-- Helper: the attention weights are continuous in the scores. -/
private theorem continuous_attnWeights_atz (sees : T → T → Prop) [DecidableRel sees] :
    Continuous (attnWeights sees) := by
  refine continuous_pi fun t => continuous_pi fun s => ?_
  simp only [attnWeights, Matrix.of_apply]
  refine continuous_if_const _ (fun hts => ?_) fun _ => continuous_const
  have he : ∀ s' : T, Continuous fun Z : Matrix T T ℝ => Real.exp (Z t s') := fun s' =>
    Real.continuous_exp.comp ((continuous_apply s').comp (continuous_apply t))
  refine (he s).div (continuous_finsetSum _ fun s' _ =>
    continuous_if_const _ (fun _ => he s') fun _ => continuous_const) fun Z => ?_
  -- the denominator is at least the term of the token `s`, which `t` sees
  have h1 := Finset.single_le_sum (f := fun s' => if sees t s' then Real.exp (Z t s') else 0)
    (fun s' _ => by positivity) (Finset.mem_univ s)
  simp only [hts, ite_true] at h1
  exact (lt_of_lt_of_le (Real.exp_pos _) h1).ne'

omit [DecidableEq d] in
/-- Helper: `τ ↦ P(τ) g(τ) C` with `P` continuous at `0` and `g(0) = 0` has the derivative
`P(0) g'(0) C` at `0`: its slope is `P(τ) (g(τ)/τ) C`. -/
private theorem hasDerivAt_mul_mul_atz {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n]
    [Fintype p] {P : ℝ → Matrix l m ℝ} {g : ℝ → Matrix m n ℝ} {g' : Matrix m n ℝ}
    (C : Matrix n p ℝ) (hP : ContinuousAt P 0) (hg : HasDerivAt g g' 0) (hg0 : g 0 = 0) :
    HasDerivAt (fun τ => P τ * g τ * C) (P 0 * g' * C) 0 := by
  have hs := hasDerivAt_iff_tendsto_slope.1 hg
  refine hasDerivAt_iff_tendsto_slope.2 ?_
  have hc : Continuous fun q : Matrix l m ℝ × Matrix m n ℝ => q.1 * q.2 * C :=
    (continuous_fst.matrix_mul continuous_snd).matrix_mul continuous_const
  have h := (hc.tendsto (P 0, g')).comp
    ((hP.tendsto.mono_left nhdsWithin_le_nhds).prodMk_nhds hs)
  refine h.congr fun τ => ?_
  simp only [Function.comp_apply, slope_def_module, hg0, Matrix.mul_zero, Matrix.zero_mul,
    sub_zero, Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq d] in
/-- Helper: an attention block vanishes at `0`. -/
private theorem attnHeads_zero_atz (sees : T → T → Prop) [DecidableRel sees] {H : Type*}
    [Fintype H] (Γ C : H → Matrix d d ℝ) : attnHeads sees Γ C (0 : Matrix T d ℝ) = 0 := by
  simp only [attnHeads, Matrix.mul_zero, Matrix.zero_mul, Finset.sum_const_zero]

omit [DecidableEq d] in
/-- Helper: an attention block along a curve `g` through `0` with the velocity `g'` has the
velocity `U g' ∑_i C_i`, `U = softmax(0)`. -/
private theorem hasDerivAt_attnHeads_atz (sees : T → T → Prop) [DecidableRel sees] {H : Type*}
    [Fintype H] (Γ C : H → Matrix d d ℝ) {g : ℝ → Matrix T d ℝ} {g' : Matrix T d ℝ}
    (hg : HasDerivAt g g' 0) (hg0 : g 0 = 0) :
    HasDerivAt (fun τ => attnHeads sees Γ C (g τ)) (attnWeights sees 0 * g' * ∑ i, C i) 0 := by
  -- head `i`: its weights `P_i(τ) = softmax(g Γ_i gᵀ)` are continuous at `τ = 0`
  have hP : ∀ i, ContinuousAt (fun τ => attnWeights sees (g τ * Γ i * (g τ)ᵀ)) 0 := fun i => by
    have hc : Continuous fun h : Matrix T d ℝ => attnWeights sees (h * Γ i * hᵀ) :=
      (continuous_attnWeights_atz sees).comp
        ((continuous_id.matrix_mul continuous_const).matrix_mul continuous_id.matrix_transpose)
    exact hc.continuousAt.comp hg.continuousAt
  -- so head `i` has the velocity `P_i(0) g' C_i`, and `P_i(0) = softmax(0)`
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    hasDerivAt_mul_mul_atz (C i) (hP i) hg hg0
  simp only [hg0, Matrix.zero_mul, Matrix.transpose_zero, Matrix.mul_zero] at h
  rw [Matrix.mul_sum]
  exact h

omit [DecidableEq d] in
/-- Helper: the right multiplication by a fixed matrix, as a continuous linear map. -/
private noncomputable def mulRightL_atz {m n : Type*} [Fintype m] [Fintype n]
    (R : Matrix m n ℝ) : Matrix T m ℝ →L[ℝ] Matrix T n ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M * R
      map_add' := fun a b => Matrix.add_mul a b R
      map_smul' := fun r a => Matrix.smul_mul r a R }

/-- Helper: one attention block with the stream `s I` along a curve `γ` through `0` whose
velocity is `a w`, with `U a = λ a`: the hidden state after the block passes through `0` with the
velocity `a w (s I + ξ λ ∑_i C_i)`. -/
private theorem hasDerivAt_step_atz (sees : T → T → Prop) [DecidableRel sees]
    {χ : Matrix T d ℝ → Matrix T d ℝ} {ξ : ℝ} (hχ0 : χ 0 = 0)
    (hχ : HasFDerivAt χ (ξ • ContinuousLinearMap.id ℝ (Matrix T d ℝ)) 0) {H : Type*}
    [Fintype H] (Γ C : H → Matrix d d ℝ) (s : ℝ) {a : T → ℝ} {lam : ℝ}
    (ha : attnWeights sees (0 : Matrix T T ℝ) *ᵥ a = lam • a) {γ : ℝ → Matrix T d ℝ}
    {w : d → ℝ} (hγ : HasDerivAt γ (vecMulVec a w) 0) (hγ0 : γ 0 = 0) :
    s • γ 0 + attnHeads sees Γ C (χ (γ 0)) = 0 ∧
      HasDerivAt (fun τ => s • γ τ + attnHeads sees Γ C (χ (γ τ)))
        (vecMulVec a (w ᵥ* (s • (1 : Matrix d d ℝ) + (ξ * lam) • ∑ i, C i))) 0 := by
  refine ⟨by rw [hγ0, smul_zero, hχ0, attnHeads_zero_atz, add_zero], ?_⟩
  -- the read `χ(γ)` passes through `0` with the velocity `ξ a w`
  have h2 := hχ.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have h20 : (χ ∘ γ) 0 = 0 := by rw [Function.comp_apply, hγ0, hχ0]
  -- so the block has the velocity `U (ξ a w) ∑_i C_i`
  have h3 := hasDerivAt_attnHeads_atz sees Γ C h2 h20
  refine ((hγ.const_smul s).add h3).congr_deriv ?_
  -- `U (ξ a w) V = ξ (U a) w V = ξ λ a (w V)`
  show s • vecMulVec a w + attnWeights sees 0 * (ξ • vecMulVec a w) * ∑ i, C i = _
  rw [Matrix.mul_smul, Matrix.mul_vecMulVec, ha, Matrix.smul_vecMulVec, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.vecMulVec_mul, smul_smul, Matrix.vecMul_add, Matrix.vecMul_smul,
    Matrix.vecMul_smul, Matrix.vecMul_one, Matrix.vecMulVec_add, Matrix.vecMulVec_smul,
    Matrix.vecMulVec_smul]

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the block `ℓ` of a network of attention blocks, on a hidden state `h`, is an
attention block whose value–output products sum to `valueOutput θ ℓ`. -/
private theorem block_atz (sees : T → T → Prop) [DecidableRel sees]
    (χ : Matrix T d ℝ → Matrix T d ℝ) (H dh : Fin L → Type) [∀ ℓ, Fintype (H ℓ)]
    [∀ ℓ, Fintype (dh ℓ)] (θ : Params (Arch.attention sees χ H dh) dIn dOut) (ℓ : Fin L) :
    ∃ Γ C : H ℓ → Matrix d d ℝ, (∀ h : Matrix T d ℝ,
      (Arch.attention sees χ H dh).f ℓ (h * θ.read ℓ) * θ.write ℓ = attnHeads sees Γ C h) ∧
      ∑ i, C i = valueOutput θ ℓ :=
  ⟨_, _, fun h => f_attention_mul sees χ H dh ℓ h (θ.read ℓ) (θ.write ℓ), rfl⟩

/-- Helper: the product of the first `ℓ + 1` factors. -/
private theorem prod_take_succ_atz (M : Fin L → Matrix d d ℝ) (ℓ : Fin L) :
    ((List.ofFn M).take (ℓ.succ : ℕ)).prod = ((List.ofFn M).take (ℓ.castSucc : ℕ)).prod * M ℓ := by
  simp only [Fin.val_succ, List.take_add_one, List.length_ofFn, ℓ.isLt, getElem?_pos,
    List.getElem_ofFn, Fin.eta, Option.toList_some, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one, Fin.val_castSucc]

omit [Fintype dOut] in
/-- Helper: along the line `τ ↦ τ a b`, the hidden state `h_k` passes through `0` at `τ = 0` with
the velocity `a (b E ∏_{ℓ < k} M_ℓ)`, `M_ℓ = s I + ξ λ V_ℓ`. -/
private theorem hidden_line_atz (sees : T → T → Prop) [DecidableRel sees]
    (χ : Matrix T d ℝ → Matrix T d ℝ) (ξ : ℝ) (hχ0 : χ 0 = 0)
    (hχ : HasFDerivAt χ (ξ • ContinuousLinearMap.id ℝ (Matrix T d ℝ)) 0)
    (H dh : Fin L → Type) [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
    (θ : Params (Arch.attention sees χ H dh) dIn dOut) (s : ℝ) (a : T → ℝ) (lam : ℝ)
    (ha : attnWeights sees (0 : Matrix T T ℝ) *ᵥ a = lam • a) (b : dIn → ℝ)
    (k : Fin (L + 1)) :
    hidden (Arch.attention sees χ H dh) (fun _ => s • (1 : Matrix d d ℝ)) θ
        ((0 : ℝ) • Matrix.vecMulVec a b) k = 0 ∧
      HasDerivAt (fun τ : ℝ => hidden (Arch.attention sees χ H dh)
          (fun _ => s • (1 : Matrix d d ℝ)) θ (τ • Matrix.vecMulVec a b) k)
        (Matrix.vecMulVec a (b ᵥ* (θ.E * ((List.ofFn fun ℓ : Fin L =>
          s • (1 : Matrix d d ℝ) + (ξ * lam) • valueOutput θ ℓ).take k).prod))) 0 := by
  induction k using Fin.induction with
  | zero =>
    refine ⟨by rw [hidden_zero, zero_smul, Matrix.zero_mul], ?_⟩
    simp only [hidden_zero, Fin.val_zero, List.take_zero, List.prod_nil, Matrix.mul_one]
    -- `h_0 = τ a b E` has the velocity `a b E = a (b E)`
    rw [← Matrix.vecMulVec_mul]
    have h := (hasDerivAt_id (0 : ℝ)).smul_const (vecMulVec a b * θ.E)
    rw [one_smul] at h
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
    exact Matrix.smul_mul τ _ _
  | succ ℓ ih =>
    obtain ⟨h0, hd⟩ := ih
    -- block `ℓ` is an attention block with `∑_i C_i = V_ℓ`
    obtain ⟨Γ, C, hB, hC⟩ := block_atz sees χ H dh θ ℓ
    have h := hasDerivAt_step_atz sees hχ0 hχ Γ C s ha hd h0
    rw [hC] at h
    simp only [hidden_succ, hB, Matrix.mul_smul, Matrix.mul_one]
    refine ⟨h.1, h.2.congr_deriv ?_⟩
    -- `(b E ∏_{ℓ' < ℓ} M_ℓ') M_ℓ = b E ∏_{ℓ' ≤ ℓ} M_ℓ'`
    rw [Matrix.vecMul_vecMul, prod_take_succ_atz, Matrix.mul_assoc]

/-- **Proof of Theorem 4.2, the Jacobians at `X = 0`, on the inputs `a b`:** let `χ(0) = 0` and
let `χ` have the derivative `ξ I` at `0`, and let the column `a` satisfy `U a = λ a` for
`U = softmax(0)`. For a network of attention blocks with the stream matrices `s I`, the
derivative at `τ = 0` of the output at the input `τ • a b` is `a` times the row
`ξ b E ∏_ℓ (s I + ξ λ V_ℓ) D`, the product taken in the order of the blocks. -/
theorem hasDerivAt_eval_attention_zero (sees : T → T → Prop) [DecidableRel sees]
    (χ : Matrix T d ℝ → Matrix T d ℝ) (ξ : ℝ) (hχ0 : χ 0 = 0)
    (hχ : HasFDerivAt χ (ξ • ContinuousLinearMap.id ℝ (Matrix T d ℝ)) 0)
    (H dh : Fin L → Type) [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
    (θ : Params (Arch.attention sees χ H dh) dIn dOut) (s : ℝ) (a : T → ℝ) (lam : ℝ)
    (ha : attnWeights sees (0 : Matrix T T ℝ) *ᵥ a = lam • a) (b : dIn → ℝ) :
    HasDerivAt
      (fun τ : ℝ => eval (Arch.attention sees χ H dh) (fun _ => s • (1 : Matrix d d ℝ)) θ
        (τ • Matrix.vecMulVec a b))
      (Matrix.vecMulVec a (ξ • (b ᵥ* (θ.E
        * (List.ofFn fun ℓ : Fin L => s • (1 : Matrix d d ℝ) + (ξ * lam) • valueOutput θ ℓ).prod
        * θ.D))))
      0 := by
  -- the last hidden state passes through `0` with the velocity `a (b E ∏_ℓ M_ℓ)`
  obtain ⟨h0, hd⟩ := hidden_line_atz sees χ ξ hχ0 hχ H dh θ s a lam ha b (Fin.last L)
  -- the readout `χ(h_L) D` has the velocity `ξ a (b E ∏_ℓ M_ℓ) D`
  have h1 := hχ.comp_hasDerivAt_of_eq (0 : ℝ) hd h0.symm
  have h2 := (mulRightL_atz (T := T) θ.D).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  refine h2.congr_deriv ?_
  show (ξ • vecMulVec a _) * θ.D = _
  rw [Fin.val_last, List.take_of_length_le (by rw [List.length_ofFn]), Matrix.smul_mul,
    Matrix.vecMulVec_mul, Matrix.vecMul_vecMul, Matrix.vecMulVec_smul]

end Skips
