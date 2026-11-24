import SkipsLean.Network.Attention
import SkipsLean.OneBlock.Tanh

/-!
# A sum of attention heads is determined to first order by its matrices

Paper (dimension paper, proof of Theorem C.1, "Attention blocks"; skips paper, "Part (i) for
attention blocks" and the proof of Lemma A.27, "let the heads of all attention blocks form one
attention block"): a family of heads with the matrices `B_j` (scores `x_t B_j x_s^⊤`) and `C_j`
gives the output `∑_j P_j(x) x C_j`. "With `u = x_2` and `v = x_2 − x_1`, head `i` puts the weight
`1/(1 + k e^{−u B_i v^⊤})` on the second token and the rest on the copies of the first, and
`1/(1 + e^{−z}) = ½ + ½ tanh(z/2)` gives the output at the second token
`y_2 = u S − ½ v S + ½ ∑_i tanh(½ (u B_i v^⊤ − log k)) v C_i`  (8)." And Step 2: "For such a `v`,
(8) is, as a function of `u`, the function `G` of Lemma C.3 with one tanh hidden unit per head
[…] and Lemma C.3 for tanh shows that all of these vanish. This holds for all `v` in an open set,
so `D_θ B_i η = 0` and `D_θ C_i η = 0` for every head."

Here these two steps for any finite family `J` of heads given by matrices, with no network: the
heads may be those of one block (`OneBlock/Attention.lean` proves this case for the parameters
of one block) or of all blocks of a network (Lemma A.27 of the skips paper). The mask enters
through a token `t₂` that sees itself and another token `t₁`.

* `twoTokenInput t₂ u v`: the input with the row `u` at `t₂` and the row `u − v` elsewhere.
* `attnFamily_two_tokens`: equation (8) for a family of heads.
* `attnFamily_rigid`: if, along curves `M(τ)`, `B_j(τ)`, `C_j(τ)` of matrices, the output
  `x M(τ) + ∑_j P_{B_j(τ)}(x) x C_j(τ)` has derivative `0` at `τ = 0` at every input `x`, and some
  `v` has the `B_j(0) v^⊤` nonzero and pairwise non-collinear and every `v C_j(0)` nonzero, then
  the derivatives of `M`, of every `B_j` and of every `C_j` at `0` vanish.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T dIn dOut J : Type*} [Fintype T] [Fintype dIn] [Fintype dOut] [Fintype J]
variable {sees : T → T → Prop} [DecidableRel sees]

/-- **The inputs of the proof:** the row `u` at the token `t₂` and the row `u − v` at every other
token. -/
def twoTokenInput [DecidableEq T] (t₂ : T) (u v : dIn → ℝ) : Matrix T dIn ℝ :=
  Matrix.of fun t => if t = t₂ then u else u - v

/-- **Equation (8) for a family of heads:** let token `t₂` see itself and another token `t₁`, and
let `k` be the number of tokens other than `t₂` that `t₂` sees. At the input `twoTokenInput t₂ u v`
the sum of the heads has at `t₂` the row
`u ∑_j C_j − ½ v ∑_j C_j + ½ ∑_j tanh(½ (u B_j v^⊤ − log k)) v C_j`. -/
theorem attnFamily_two_tokens [DecidableEq T] (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂)
    (hs1 : sees t₂ t₁) (B : J → Matrix dIn dIn ℝ) (C : J → Matrix dIn dOut ℝ)
    (u v : dIn → ℝ) :
    (∑ j, attnWeights sees (twoTokenInput t₂ u v * B j * (twoTokenInput t₂ u v)ᵀ)
        * twoTokenInput t₂ u v * C j) t₂
      = u ᵥ* (∑ j, C j) - (1 / 2 : ℝ) • (v ᵥ* ∑ j, C j)
        + ∑ j, ((1 / 2 : ℝ) * Real.tanh ((1 / 2) * (u ⬝ᵥ (B j *ᵥ v)
            - Real.log ((Finset.univ.filter fun s => sees t₂ s ∧ s ≠ t₂).card : ℝ))))
          • (v ᵥ* C j) := by
  sorry

/-- **Step 2 for a family of heads:** let token `t₂` see itself and another token `t₁`. Let
`M(τ)`, `B_j(τ)`, `C_j(τ)` be curves of matrices with the derivatives `dM`, `dB_j`, `dC_j` at
`τ = 0`, and let some `v` have the columns `B_j(0) v^⊤` nonzero and pairwise non-collinear and
every row `v C_j(0)` nonzero. If at every input `x` the output
`x M(τ) + ∑_j P_{B_j(τ)}(x) x C_j(τ)` has derivative `0` at `τ = 0`, then `dM = 0` and
`dB_j = 0`, `dC_j = 0` for every head. -/
theorem attnFamily_rigid (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (Mc : ℝ → Matrix dIn dOut ℝ) (Bc : J → ℝ → Matrix dIn dIn ℝ)
    (Cc : J → ℝ → Matrix dIn dOut ℝ) (dM : Matrix dIn dOut ℝ) (dB : J → Matrix dIn dIn ℝ)
    (dC : J → Matrix dIn dOut ℝ) (hM : HasDerivAt Mc dM 0)
    (hB : ∀ j, HasDerivAt (Bc j) (dB j) 0) (hC : ∀ j, HasDerivAt (Cc j) (dC j) 0)
    (hv : ∃ v : dIn → ℝ, (∀ j, Bc j 0 *ᵥ v ≠ 0)
      ∧ (∀ i j, i ≠ j → ∀ r : ℝ, Bc i 0 *ᵥ v ≠ r • (Bc j 0 *ᵥ v))
      ∧ (∀ j, v ᵥ* Cc j 0 ≠ 0))
    (hflat : ∀ x : Matrix T dIn ℝ, HasDerivAt
      (fun τ : ℝ => x * Mc τ + ∑ j, attnWeights sees (x * Bc j τ * xᵀ) * x * Cc j τ) 0 0) :
    dM = 0 ∧ ∀ j, dB j = 0 ∧ dC j = 0 := by
  sorry

end Skips
