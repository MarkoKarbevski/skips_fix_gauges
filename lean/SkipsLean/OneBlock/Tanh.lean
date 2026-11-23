import SkipsLean.Network.Blocks
import SkipsLean.OneBlock.Factorization
import SkipsLean.OneBlock.UnitsTanh
import SkipsLean.Generic.Params

/-!
# The one-block theorem for a tanh block

Paper (dimension paper): Theorem 5.1 (Theorem C.1 in the appendix), for a `tanh` block: with one
block, without normalization and without biases, at generic parameters the functional dimension is
`P - 2 d²`.

The network is `x ↦ tanh(x E W_read) W_write D`. With `C = E W_read` and `A = W_write D`, let `c_i`
be the columns of `C` and `a_i` the rows of `A`. The conditions that the proof uses are: `E`, `D`,
`W_read` and `W_write` have rank `d`, every `a_i` is nonzero, and the `c_i` are nonzero and pairwise
non-collinear. Under them the flat directions are exactly the directions of the two changes of
basis (Lemma C.2 and Lemma C.3), and they hold at generic parameters when
`d_in, d_out, d_hidden ≥ d ≥ 2`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- The conditions on the parameters of one MLP block that the proof of the one-block theorem
uses. -/
structure OneBlockGeneric (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :
    Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_read : (θ.read 0).rank = Fintype.card d
  rank_write : (θ.write 0).rank = Fintype.card d
  /-- every row `a_i` of `A = W_write D` is nonzero -/
  row_ne_zero : ∀ i, (θ.write 0 * θ.D) i ≠ 0
  /-- every column `c_i` of `C = E W_read` is nonzero -/
  col_ne_zero : ∀ i, (θ.E * θ.read 0)ᵀ i ≠ 0
  /-- the columns of `C` are pairwise non-collinear -/
  col_not_collinear : ∀ i j, i ≠ j → ∀ r : ℝ, (θ.E * θ.read 0)ᵀ i ≠ r • (θ.E * θ.read 0)ᵀ j

variable (θ : Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut)

/-- Under the conditions, every flat direction of one `tanh` block is the direction of two changes
of basis (Steps 1 to 3 of the proof of Theorem C.1). -/
theorem flat_le_range_cobDir_tanh (hθ : OneBlockGeneric θ) (η : Params _ dIn dOut)
    (hη : η ∈ flat (Arch.mlp Real.tanh id hid) 0 θ) :
    ∃ X : Fin 2 → Matrix d d ℝ, η = cobDir θ X := by
  sorry

/-- **Theorem 5.1 for a `tanh` block, under the conditions of its proof:** the functional
dimension is `P - 2 d²`. -/
theorem funDim_tanh_oneBlock (hθ : OneBlockGeneric θ) :
    funDim (Arch.mlp Real.tanh id hid) 0 θ + 2 * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) := by
  sorry

/-- The conditions hold at generic parameters, when `d_in, d_out, d_hidden ≥ d ≥ 2`. -/
theorem ae_oneBlockGeneric
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, OneBlockGeneric θ := by
  sorry

/-- **Theorem 5.1 for a `tanh` block:** with one block, without normalization and without biases,
with `d_in, d_out, d_hidden ≥ d ≥ 2`, the functional dimension is `P - 2 d²` at generic
parameters. -/
theorem ae_funDim_tanh_oneBlock
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh id hid) 0 θ + 2 * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) := by
  sorry

end Skips
