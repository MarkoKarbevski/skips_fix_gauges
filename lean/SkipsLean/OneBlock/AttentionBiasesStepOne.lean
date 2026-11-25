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
  sorry

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
