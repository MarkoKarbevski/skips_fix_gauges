import SkipsLean.OneBlock.Gated
import SkipsLean.OneBlock.UnitsSwiGLU

/-!
# The one-block theorem for a SwiGLU block

Paper (dimension paper): Theorem 5.1 (Theorem C.1 in the appendix), for a SwiGLU block: with one
block, without normalization and without biases, at generic parameters the functional dimension is
`P - 2 d² - s`, where `s = d_hidden` counts the rescalings of the values of the hidden units.

The network is `x ↦ f(x E W_read) W_write D` with `W_read = [W_g | W_v]` and
`f(z, w)_i = silu(z_i) w_i`. The theorem is the general statement of `Gated.lean` for the gate
activation SiLU, for which Lemma C.3 holds (`UnitsSwiGLU.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- Lemma C.3 for SwiGLU, in the form that the one-block theorem takes. -/
theorem silu_gatedUnitsRescale (n k q : Type*) [Fintype n] [Fintype k] [Fintype q] :
    GatedUnitsRescale silu siluDeriv n k q :=
  fun c β e β' a ψM ψγ ψc ψβ ψe ψβ' ψa ha hc hcol he h =>
    silu_gated_units_flat_of_value_ne_zero c β e β' a ψM ψγ ψc ψβ ψe ψβ' ψa ha hc hcol he h

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

variable (θ : Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut)

/-- Under the conditions, every flat direction of one SwiGLU block is the sum of the direction of
two changes of basis and of the direction of a rescaling of the values of the hidden units
(Steps 1 to 3 of the proof of Theorem C.1). -/
theorem flat_le_cobDir_add_rescaleDir_swiglu (hθ : OneBlockGenericGated θ) (η : Params _ dIn dOut)
    (hη : η ∈ flat (Arch.gated silu id hid) 0 θ) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), η = cobDir θ X + rescaleDir θ α :=
  flat_le_cobDir_add_rescaleDir_gated hasDerivAt_silu (silu_gatedUnitsRescale _ _ _) θ hθ η hη

/-- **Theorem 5.1 for a SwiGLU block, under the conditions of its proof:** the functional
dimension is `P - 2 d² - d_hidden`. -/
theorem funDim_swiglu_oneBlock (hθ : OneBlockGenericGated θ) :
    funDim (Arch.gated silu id hid) 0 θ + (2 * Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) :=
  funDim_gated_oneBlock hasDerivAt_silu (silu_gatedUnitsRescale _ _ _) θ hθ

/-- **Theorem 5.1 for a SwiGLU block:** with one block, without normalization and without biases,
with `d_in, d_out, d_hidden ≥ d ≥ 2`, the functional dimension is `P - 2 d² - d_hidden` at generic
parameters. -/
theorem ae_funDim_swiglu_oneBlock
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated silu id hid) 0 θ
        + (2 * Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) :=
  ae_funDim_gated_oneBlock hasDerivAt_silu (silu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut hhid

end Skips
