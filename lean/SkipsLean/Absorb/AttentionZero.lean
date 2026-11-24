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
  sorry

end Skips
