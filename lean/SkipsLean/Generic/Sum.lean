import SkipsLean.Symmetry.InsideBlocksSum
import SkipsLean.Generic.Params

/-!
# Generic parameters of a network with two kinds of block

Papers: "A statement holds at generic parameters if it holds outside a set of Lebesgue measure
zero" (Section 2 of the dimension paper and of the skips paper).

The parameters of a network of `A.sum B` (`Network/Sum.lean`) are, up to a linear change of
coordinates, the parameters of a network of `A` together with the reads and the writes of `B`.
So a condition on the first part `θ.sumFst` that holds at generic parameters of `A` holds at
generic parameters of the sum, and likewise for the second part: the preimage of a null set under
a surjective linear map is a null set (Fubini). This carries the conditions of the proofs for
networks of one kind of block (`ae_smallWritesGenericAttention`, `ae_smallWritesGeneric`, …) to
networks of attention blocks and MLP blocks.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {A B : Arch T d L}

/-- **A condition that holds at generic parameters of `A` holds for the first part of generic
parameters of `A.sum B`.** -/
theorem ae_sumFst (μ : Measure (Params (A.sum B) dIn dOut)) [μ.IsAddHaarMeasure]
    {p : Params A dIn dOut → Prop}
    (hp : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), p θ) :
    ∀ᵐ θ ∂μ, p θ.sumFst := by
  sorry

/-- **A condition that holds at generic parameters of `B` holds for the second part of generic
parameters of `A.sum B`.** -/
theorem ae_sumSnd (μ : Measure (Params (A.sum B) dIn dOut)) [μ.IsAddHaarMeasure]
    {p : Params B dIn dOut → Prop}
    (hp : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params B dIn dOut)), p θ) :
    ∀ᵐ θ ∂μ, p θ.sumSnd := by
  sorry

end Skips
