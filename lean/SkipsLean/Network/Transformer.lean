import SkipsLean.Network.Sum

/-!
# Networks of attention blocks and MLP blocks

Papers. Skips paper, Section 2: "A transformer layer has two blocks, its attention and MLP
sub-layers: a transformer of 12 layers has `L = 24`, and per block means per sub-layer." Scope:
"all MLP blocks are of one kind". Lemma A.27: "let each block, in any order and of any width, be
an attention block with heads of width at most `d_model`, causal or not, on sequences of at least
two tokens, or an MLP block, with all MLP blocks tanh, all GELU, all SwiGLU or all GeGLU blocks."

Names for the two sums of `Network/Sum.lean` that these statements are about. Block `ℓ` has the
heads `H ℓ` of width `dh ℓ` and the hidden units `hid ℓ`: it is an attention block if `hid ℓ` is
empty and an MLP block (or a gated block) if `H ℓ` is empty (`f_sum_mul_of_isEmpty_right`,
`f_sum_mul_of_isEmpty_left`), and the two may also stand side by side in one block.
-/

namespace Skips

open Matrix

variable {T d : Type*} {L : ℕ} [Fintype T]

/-- **A network of attention blocks and MLP blocks with the activation `σ`,** in any order:
block `ℓ` has the heads `H ℓ` of width `dh ℓ` and the hidden units `hid ℓ`. -/
noncomputable abbrev Arch.attentionMlp (sees : T → T → Prop) [DecidableRel sees] (σ : ℝ → ℝ)
    (χ : Matrix T d ℝ → Matrix T d ℝ) (H dh hid : Fin L → Type) [∀ ℓ, Fintype (H ℓ)]
    [∀ ℓ, Fintype (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] : Arch T d L :=
  (Arch.attention sees χ H dh).sum (Arch.mlp σ χ hid)

/-- **A network of attention blocks and gated blocks with the gate activation `σ`,** in any
order: block `ℓ` has the heads `H ℓ` of width `dh ℓ` and the gated hidden units `hid ℓ`. -/
noncomputable abbrev Arch.attentionGated (sees : T → T → Prop) [DecidableRel sees] (σ : ℝ → ℝ)
    (χ : Matrix T d ℝ → Matrix T d ℝ) (H dh hid : Fin L → Type) [∀ ℓ, Fintype (H ℓ)]
    [∀ ℓ, Fintype (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] : Arch T d L :=
  (Arch.attention sees χ H dh).sum (Arch.gated σ χ hid)

end Skips
