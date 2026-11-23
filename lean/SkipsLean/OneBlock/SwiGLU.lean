import SkipsLean.Dimension.Rescaling
import SkipsLean.OneBlock.Factorization
import SkipsLean.OneBlock.UnitsSwiGLU
import SkipsLean.Generic.Params

/-!
# The one-block theorem for a SwiGLU block

Paper (dimension paper): Theorem 5.1 (Theorem C.1 in the appendix), for a SwiGLU block: with one
block, without normalization and without biases, at generic parameters the functional dimension is
`P - 2 d² - s`, where `s = d_hidden` counts the rescalings of the values of the hidden units.

The network is `x ↦ f(x E W_read) W_write D` with `W_read = [W_g | W_v]` and
`f(z, w)_i = silu(z_i) w_i`. With `C = E W_read` and `A = W_write D`, hidden unit `i` has the gate
column `c_i` (column `Sum.inl i` of `C`), the value column `e_i` (column `Sum.inr i` of `C`) and
the write row `a_i` (row `i` of `A`). The conditions that the proof uses are: `E`, `D`, `W_read`
and `W_write` have rank `d`, every `a_i` and every `e_i` is nonzero, and the `c_i` are nonzero and
pairwise non-collinear. Under them the flat directions are exactly the sums of a direction of the
two changes of basis and a direction of the rescalings (Lemmas C.2 and C.3).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- The conditions on the parameters of one SwiGLU block that the proof of the one-block theorem
uses. -/
structure OneBlockGenericGated
    (θ : Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_read : (θ.read 0).rank = Fintype.card d
  rank_write : (θ.write 0).rank = Fintype.card d
  /-- every row `a_i` of `A = W_write D` is nonzero -/
  row_ne_zero : ∀ i, (θ.write 0 * θ.D) i ≠ 0
  /-- every gate column `c_i` of `C = E W_read` is nonzero -/
  gate_ne_zero : ∀ i : hid 0, (θ.E * θ.read 0)ᵀ (Sum.inl i) ≠ 0
  /-- the gate columns of `C` are pairwise non-collinear -/
  gate_not_collinear : ∀ i j : hid 0, i ≠ j → ∀ r : ℝ,
    (θ.E * θ.read 0)ᵀ (Sum.inl i) ≠ r • (θ.E * θ.read 0)ᵀ (Sum.inl j)
  /-- every value column `e_i` of `C` is nonzero -/
  value_ne_zero : ∀ i : hid 0, (θ.E * θ.read 0)ᵀ (Sum.inr i) ≠ 0

variable (θ : Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut)

/-- Under the conditions, every flat direction of one SwiGLU block is the sum of the direction of
two changes of basis and the direction of a rescaling of the values of the hidden units (Steps 1
to 3 of the proof of Theorem C.1). -/
theorem flat_le_cobDir_add_rescaleDir_swiglu (hθ : OneBlockGenericGated θ) (η : Params _ dIn dOut)
    (hη : η ∈ flat (Arch.gated silu id hid) 0 θ) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), η = cobDir θ X + rescaleDir θ α := by
  sorry

/-- **Theorem 5.1 for a SwiGLU block, under the conditions of its proof:** the functional
dimension is `P - 2 d² - d_hidden`. -/
theorem funDim_swiglu_oneBlock (hθ : OneBlockGenericGated θ) :
    funDim (Arch.gated silu id hid) 0 θ + (2 * Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) := by
  sorry

/-- The conditions hold at generic parameters, when `d_in, d_out, d_hidden ≥ d ≥ 2`. -/
theorem ae_oneBlockGenericGated
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, OneBlockGenericGated θ := by
  sorry

/-- **Theorem 5.1 for a SwiGLU block:** with one block, without normalization and without biases,
with `d_in, d_out, d_hidden ≥ d ≥ 2`, the functional dimension is `P - 2 d² - d_hidden` at generic
parameters. -/
theorem ae_funDim_swiglu_oneBlock
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated silu id hid) 0 θ
        + (2 * Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) := by
  sorry

end Skips
