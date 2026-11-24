import SkipsLean.OneBlock.AttentionStepOne
import SkipsLean.OneBlock.AttentionGeneric
import SkipsLean.Dimension.UpperBoundAttention

/-!
# The one-block theorem for an attention block: the functional dimension

Paper (dimension paper): Theorem 5.1 (Theorem C.1 in the appendix) for an attention block:
"Let `d_model ≥ 2` and `d_in, d_out ≥ d_model`, let inputs range over all of `ℝ^{T × d_in}`, and
consider networks with one block, without normalization and without biases. The block is […] an
attention block of `H` heads of width `d_h ≤ d_model` with `H d_h ≥ d_model`, causal or not, on
sequences of at least two tokens. At generic parameters the functional dimension is
`P − 2 d_model² − s`", with `s = 2 H d_h²` for an attention block. Its proof, Step 3: "So
`dim K(θ) = 2 d_model² + 2 H d_h²`, and the functional dimension `P − dim K(θ)` is the value of
the theorem."

Paper (skips paper): Theorem B.1 (i) for an attention block, without biases: "Let the network
have no normalization […] and let the block have width at least `d_model`, where the width of an
attention block is `H d_h`. For generic parameters the skipless network has functional dimension
`P − 2 d_model² − s` and the residual network `P − d_model² − s` […] and the skip raises the
functional dimension by exactly `d_model²`." Its proof for the residual network: a direction that
keeps `M = E D` and every `B_i`, `C_i` has `E (X − Y) D = 0`, so `X = Y`, one change of basis.

Here, from Steps 1 and 2 (`OneBlock/Attention.lean`, `OneBlock/AttentionStepOne.lean`), the
upper bounds (`Dimension/UpperBoundAttention.lean`) and the conditions at generic parameters
(`OneBlock/AttentionGeneric.lean`), for a mask with a token `t₂` that sees itself and another
token `t₁` (two tokens at least; causal or not):

* the flat directions of the skipless and of the residual network of one attention block;
* `fd = P − 2 d² − 2 H d_h²` without the skip and `fd = P − d² − 2 H d_h²` with it, under the
  conditions of the proof and at almost every parameter;
* the skip raises the functional dimension by exactly `d²` at almost every parameter.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-- **Proof of Theorem C.1 for attention blocks, Steps 1 and 2:** under the conditions of the
proof, with a token that sees itself and another token, every flat direction of the skipless
network of one attention block is the sum of the direction of two changes of basis of the hidden
states and of the directions of the changes of basis inside the heads. -/
theorem flat_attention_oneBlock (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂)
    (hs1 : sees t₂ t₁) (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hθ : OneBlockGenericAttention θ)
    (η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hη : η ∈ flat (Arch.attention sees id H dh) 0 θ) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      η = cobDir θ X + headDirQK θ Γ + headDirVO θ Γ' := by
  sorry

/-- **Proof of Theorem B.1 (i) of the skips paper for attention blocks, the residual network:**
under the same conditions, every flat direction of the residual network of one attention block is
the sum of the direction of one change of basis, the same at `h_0` and at `h_1`, and of the
directions of the changes of basis inside the heads. -/
theorem flat_attention_oneBlock_residual (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂)
    (hs1 : sees t₂ t₁) (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hθ : OneBlockGenericAttention θ)
    (η : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hη : η ∈ flat (Arch.attention sees id H dh) 1 θ) :
    ∃ (X : Matrix d d ℝ) (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
      η = cobDir θ (fun _ => X) + headDirQK θ Γ + headDirVO θ Γ' := by
  sorry

/-- **Theorem C.1 for an attention block, at one parameter:** under the conditions of the proof,
with a token that sees itself and another token, the skipless network of one attention block has
`fd = P − 2 d² − 2 H d_h²`. -/
theorem funDim_attention_oneBlock (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂)
    (hs1 : sees t₂ t₁) (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hθ : OneBlockGenericAttention θ) :
    funDim (Arch.attention sees id H dh) 0 θ
        + (2 * Fintype.card d ^ 2 + 2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2))
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

/-- **Theorem 5.1 / C.1 for an attention block:** for `d_in, d_out ≥ d ≥ 2`, `H` heads of width
`d_h ≤ d` with `H d_h ≥ d`, and a token that sees itself and another token (two tokens at least;
causal or not), at almost every parameter the skipless network of one attention block has the
functional dimension `P − 2 d² − 2 H d_h²`. -/
theorem ae_funDim_attention_oneBlock
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 0 θ
        + (2 * Fintype.card d ^ 2 + 2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2))
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

/-- **Theorem B.1 (i) of the skips paper for an attention block with its skip, at one
parameter:** under the conditions of the proof, with a token that sees itself and another token,
the residual network of one attention block has `fd = P − d² − 2 H d_h²`. -/
theorem funDim_attention_oneBlock_residual (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂)
    (hs1 : sees t₂ t₁) (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (hθ : OneBlockGenericAttention θ) :
    funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2 + 2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2))
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

/-- **Theorem B.1 (i) of the skips paper for an attention block with its skip:** for
`d_in, d_out ≥ d ≥ 2`, `H` heads of width `d_h ≤ d` with `H d_h ≥ d`, and a token that sees
itself and another token, at almost every parameter the residual network of one attention block
has the functional dimension `P − d² − 2 H d_h²`. -/
theorem ae_funDim_attention_oneBlock_residual
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ
        + (Fintype.card d ^ 2 + 2 * (Fintype.card (H 0) * Fintype.card (dh 0) ^ 2))
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  sorry

/-- **The skip raises the functional dimension by exactly `d²`** (Theorem 4.6 (i) / B.1 (i) of
the skips paper), for one attention block, at almost every parameter. -/
theorem ae_funDim_attention_oneBlock_residual_eq_add
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ
      = funDim (Arch.attention sees id H dh) 0 θ + Fintype.card d ^ 2 := by
  sorry

end Skips
