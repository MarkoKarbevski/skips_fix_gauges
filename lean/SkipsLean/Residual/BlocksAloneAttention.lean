import SkipsLean.Residual.BlocksAlone
import SkipsLean.Residual.DepthAttentionDim

/-!
# Attention-only residual networks without an embedding and a readout

Paper (skips paper): Corollary 4.10 (Attention-only transformers: Conjecture 2.4 of Henry, 2026):
"Without normalization, consider a residual network of `L` attention blocks at generic
parameters, and let `s = 2 L d_model² / H`. […] (ii) Without an embedding and a readout, so that
`h_0 = x ∈ ℝ^{T × d_model}` and `y = h_L`, its functional dimension is
`P − s = L (4 d_model² − 2 d_model² / H)`." Lemma A.27, fourth value: "`fd(θ_τ) = P − s` (no
embedding, readout, biases or normalization)". Its proof: "Without an embedding and a readout,
`M = I` is fixed, so `ψ_M = 0` for every direction, and the flat directions are the rescalings
alone, of dimension `s`"; for attention blocks: "So the flat directions form a space of dimension
`d_model² + s`, and of dimension `s` without an embedding and a readout." Proof of Corollary 4.10:
"For part (ii), without an embedding and a readout, the last value of Lemma A.27 is `r = P − s`,
and at generic parameters the changes of basis inside the heads move the parameters in `s`
independent directions. […] With heads of total width `H d_h = d_model`, a block has `4 d_model²`
parameters and `H` heads, each with two changes of basis of dimension `d_h² = d_model² / H²`. So
`P = 4 L d_model²` and `s = 2 L d_model² / H`."

Here, for `Arch.attention sees id H dh` (heads of width `1 ≤ d_h ≤ d`, any numbers of heads,
`s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`), `d ≥ 2`, a mask with a token that sees itself and another token, and
the network without an embedding and a readout of `Residual/BlocksAlone.lean`:

* `eventually_funDimBlocks_smallWrites_attention`: Lemma A.27, fourth value, under the conditions
  of its proof (`SmallWritesGenericAttention` at `E = D = I`);
* `ae_funDimBlocks_attention_residual`: Corollary 4.10 (ii), `fd = P − s` at almost every
  parameter of the blocks;
* `ae_funDimBlocks_attention_residual_of_width`: the same in the setting of the main text, `H`
  heads of total width `H d_h = d` in every block: `fd = L (4 d² − 2 d² / H)`.

Numeric check of the value in 14 cases: `attention_blocks_alone_check_2026-11-24.py` (notes).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-- **Lemma A.27 (Small writes), fourth value, for attention blocks, under the conditions of its
proof:** let the network with `E = D = I` and the blocks of `β` satisfy the conditions of the
lemma, and let a token see itself and another token. For all small `τ ≠ 0`, the residual network
without an embedding and a readout has `fd(β_τ) = P − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`, with `P` the number of
parameters of the blocks. -/
theorem eventually_funDimBlocks_smallWrites_attention (t₁ t₂ : T) (h12 : t₁ ≠ t₂)
    (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (β : BlockParams (Arch.attention (T := T) (d := d) sees id H dh))
    (hβ : SmallWritesGenericAttention β.toParams) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimBlocks (Arch.attention sees id H dh) 1 (β.smallWrites τ)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
        = Module.finrank ℝ (BlockParams (Arch.attention (T := T) (d := d) sees id H dh)) := by
  sorry

/-- **Corollary 4.10 (ii) of the skips paper (attention-only transformers without an embedding
and a readout):** without normalization, with `d ≥ 2`, `L` attention blocks with heads of width
`1 ≤ d_h ≤ d` and a token that sees itself and another token, at almost every parameter of the
blocks the residual network without an embedding and a readout has the functional dimension
`P − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDimBlocks_attention_residual
    (μ : Measure (BlockParams (Arch.attention (T := T) (d := d) sees id H dh)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.attention sees id H dh) 1 β
        + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
      = Module.finrank ℝ (BlockParams (Arch.attention (T := T) (d := d) sees id H dh)) := by
  sorry

/-- **Corollary 4.10 (ii) in the setting of the main text:** `Hn` heads of total width
`H d_h = d` in every block. At almost every parameter of the blocks, the residual network without
an embedding and a readout has the functional dimension `L (4 d² − 2 d² / H)`. -/
theorem ae_funDimBlocks_attention_residual_of_width (Hn : ℕ)
    (μ : Measure (BlockParams (Arch.attention (T := T) (d := d) sees id H dh)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hHn : ∀ ℓ, Fintype.card (H ℓ) = Hn)
    (hHd : ∀ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) = Fintype.card d)
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.attention sees id H dh) 1 β
      = L * (4 * Fintype.card d ^ 2 - 2 * Fintype.card d ^ 2 / Hn) := by
  sorry

end Skips
