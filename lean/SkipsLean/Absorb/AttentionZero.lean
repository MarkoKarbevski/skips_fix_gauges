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
