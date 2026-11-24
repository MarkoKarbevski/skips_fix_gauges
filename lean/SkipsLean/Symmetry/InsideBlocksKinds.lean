import SkipsLean.Symmetry.InsideBlocks
import SkipsLean.Symmetry.AttentionHeads
import SkipsLean.Dimension.Rescaling

/-!
# The symmetries inside attention blocks and gated blocks are symmetries inside the blocks

Paper (skips paper), Section 4.1: the symmetries inside the blocks are "the rescaling of the value
of a hidden unit of a gated block, and the changes of basis inside an attention head" (and the
rescaling of a hidden unit of a ReLU or ReLU² block, not stated here). Each of them leaves "the
map of that block unchanged".

Here: the directions `headDirQK θ Γ`, `headDirVO θ Γ'` of the changes of basis inside the heads
(`Symmetry/AttentionHeads.lean`) and the directions `rescaleDir θ α` of the rescalings of the
values of gated units (`Dimension/Rescaling.lean`) are directions of symmetries inside the blocks
in the sense of `Symmetry/InsideBlocks.lean`: the curves `θ.headsQK (exp (τ Γ))`,
`θ.headsVO (exp (τ Γ'))` and the rescaling by `exp (τ α)` keep `E`, `D` and the map of every
block. For any `χ`, any mask, and any gate activation `σ`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees] {χ : Matrix T d ℝ → Matrix T d ℝ}
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **The changes of basis between the queries and the keys of the heads are symmetries inside
the blocks.** -/
theorem insideBlocks_headDirQK (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    InsideBlocks (Arch.attention sees χ H dh) θ (headDirQK θ Γ) := by
  sorry

/-- **The changes of basis between the values and the outputs of the heads are symmetries inside
the blocks.** -/
theorem insideBlocks_headDirVO (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (Γ : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) :
    InsideBlocks (Arch.attention sees χ H dh) θ (headDirVO θ Γ) := by
  sorry

/-- **The rescalings of the values of gated units are symmetries inside the blocks.** -/
theorem insideBlocks_rescaleDir (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (α : ∀ ℓ, hid ℓ → ℝ) :
    InsideBlocks (Arch.gated σ χ hid) θ (rescaleDir θ α) := by
  sorry

end Skips
