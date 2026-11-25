import SkipsLean.Symmetry.BiasesGeneratedGroupSum
import SkipsLean.Symmetry.BiasesGeneratedGroupRescale

/-!
# The rescalings of hidden units act block by block

Paper (skips paper), Section 4.1: "the rescaling of a hidden unit of a ReLU or ReLU² block, the
rescaling of the value of a hidden unit of a gated block", and for ReGLU also of its gate
(Appendix A.6).

`Symmetry/BiasesGeneratedGroupSum.lean` asks of a family of symmetries inside the blocks, to be
used in a network with two kinds of block, that it acts block by block (`InsideBlocksLocal`): it
keeps `E`, `D`, the embedding bias and the readout bias, the map of every block and the span of
the rows of every write, and moves the reads, the writes and the read biases through these alone.
Here: the three families of rescalings of `Symmetry/BiasesGeneratedGroupRescale.lean` do.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise ENNReal

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- **The rescalings of the hidden units of MLP blocks act block by block,** for an activation
that is positively homogeneous of degree `k`. -/
theorem insideBlocksLocal_rescaleMlp {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) :
    InsideBlocksLocal (A := Arch.mlp (T := T) (d := d) σ χ hid) (dIn := dIn) (dOut := dOut)
      (rescaleMlpAct k) (posRescalings hid) := by
  sorry

/-- **The rescalings of the values of gated units act block by block,** for any gate. -/
theorem insideBlocksLocal_rescale :
    InsideBlocksLocal (A := Arch.gated (T := T) (d := d) σ χ hid) (dIn := dIn) (dOut := dOut)
      rescaleAct (posRescalings hid) := by
  sorry

/-- **The rescalings of the values and of the gates act block by block,** for a gate that is
positively homogeneous of degree `k`. -/
theorem insideBlocksLocal_rescaleBoth {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) :
    InsideBlocksLocal (A := Arch.gated (T := T) (d := d) σ χ hid) (dIn := dIn) (dOut := dOut)
      (rescaleBothAct k) (posRescalings hid ×ˢ posRescalings hid) := by
  sorry

end Skips
