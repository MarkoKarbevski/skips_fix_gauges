import SkipsLean.Symmetry.BiasesGeneratedGroupSum
import SkipsLean.Symmetry.BiasesGeneratedGroupAttention

/-!
# The symmetries inside attention heads with biases act block by block

Paper (skips paper), Section 4.1 and Appendix A.6: the changes of basis inside the heads of an
attention block, between queries and keys and between values and outputs; with biases also the
shift of the key biases, and the value biases moved into the output bias.

`Symmetry/BiasesGeneratedGroupSum.lean` asks of a family of symmetries inside the blocks, to be
used in a network with two kinds of block, that it acts block by block (`InsideBlocksLocal`).
Here: the family `headsAct` of `Symmetry/BiasesGeneratedGroupAttention.lean` does, when every
token sees a token. It moves the write bias of a block by `−∑_i ν_i W_{O,i}`, a row that depends
on the writes alone.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise ENNReal

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees] {χ : Matrix T d ℝ → Matrix T d ℝ}
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-- **The symmetries inside attention heads with biases act block by block,** when every token
sees a token. -/
theorem insideBlocksLocal_heads (hsee : ∀ t, ∃ s, sees t s) :
    InsideBlocksLocal (A := Arch.attention (T := T) (d := d) sees χ H dh) (dIn := dIn)
      (dOut := dOut) headsAct (headsSet H dh) := by
  sorry

end Skips
