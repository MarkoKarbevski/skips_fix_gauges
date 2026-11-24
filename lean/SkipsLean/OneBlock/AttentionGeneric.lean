import SkipsLean.OneBlock.Attention
import SkipsLean.OneBlock.Common

/-!
# The one-block theorem for an attention block: the conditions hold at generic parameters

Paper (dimension paper), proof of Theorem C.1, "Attention blocks": "For generic parameters `E`
and `D` have rank `d_model`; every `W_{Q,i}`, `W_{K,i}`, `W_{V,i}` and `W_{O,i}^⊤` has rank
`d_h`, since `d_h ≤ d_model`; and the queries […] and the output projection […] of all heads
have rank `d_model`, since `H d_h ≥ d_model`" (Step 1), and "For generic parameters and generic
`v` the columns `B_i v^⊤` are nonzero and pairwise non-collinear, since `d_model ≥ 2`, and every
row `v C_i` is nonzero" (Step 2).

Here: for `d_in, d_out ≥ d ≥ 2`, `d_h ≤ d` and `H d_h ≥ d`, the conditions
`OneBlockGenericAttention θ` of `OneBlock/Attention.lean` hold at almost every `θ`, for every
additive Haar measure on the parameters.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-- The conditions of the proof of Theorem C.1 for an attention block hold at generic
parameters, for `d_in, d_out ≥ d ≥ 2`, heads of width `d_h ≤ d` and total width `H d_h ≥ d`. -/
theorem ae_oneBlockGenericAttention
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0)) :
    ∀ᵐ θ ∂μ, OneBlockGenericAttention θ := by
  sorry

end Skips
