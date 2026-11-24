import SkipsLean.Residual.DepthAttention
import SkipsLean.OneBlock.Common
import SkipsLean.Generic.Params

/-!
# Residual networks of attention blocks: the conditions of Lemma A.27 at generic parameters

Paper (skips paper), Lemma A.27: "Let `d_model ≥ 2` […] an attention block with heads of width at
most `d_model` […]. For generic parameters […]", and the generic conditions of "Part (i) for
attention blocks" of Theorem B.1, for the heads of all blocks together.

Here: for `d_in, d_out ≥ d ≥ 2` and heads of width `1 ≤ d_h ≤ d` in every block (any numbers of
heads, any total widths), `SmallWritesGenericAttention θ` (`Residual/DepthAttention.lean`) holds
at almost every `θ`, for every additive Haar measure on the parameters.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-- The conditions of Lemma A.27 for attention blocks hold at generic parameters, for
`d_in, d_out ≥ d ≥ 2` and heads of width `1 ≤ d_h ≤ d`. -/
theorem ae_smallWritesGenericAttention
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, SmallWritesGenericAttention θ := by
  sorry

end Skips
