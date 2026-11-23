import SkipsLean.OneBlock.Gated
import SkipsLean.OneBlock.UnitsGeGLU

/-!
# The one-block theorem for a GeGLU block

Paper (dimension paper): Theorem 5.1 (Theorem C.1 in the appendix), for a GeGLU block: with one
block, without normalization and without biases, at generic parameters the functional dimension is
`P - 2 d² - s`, where `s = d_hidden` counts the rescalings of the values of the hidden units.

The network is `x ↦ f(x E W_read) W_write D` with `W_read = [W_g | W_v]` and
`f(z, w)_i = σ(z_i) w_i`, `σ(z) = z Φ(z)`. The theorem is the general statement of `Gated.lean`
for the gate activation GELU, for which Lemma C.3 holds (`UnitsGeGLU.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- Lemma C.3 for GeGLU, in the form that the one-block theorem takes. -/
theorem gelu_gatedUnitsRescale (n k q : Type*) [Fintype n] [Fintype k] [Fintype q] :
    GatedUnitsRescale gelu geluDeriv n k q :=
  fun c β e β' a ψM ψγ ψc ψβ ψe ψβ' ψa ha hc hcol he h =>
    gelu_gated_units_flat_of_value_ne_zero c β e β' a ψM ψγ ψc ψβ ψe ψβ' ψa ha hc hcol he h

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

variable (θ : Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut)

/-- Under the conditions, every flat direction of one GeGLU block is the sum of the direction of
two changes of basis and of the direction of a rescaling of the values of the hidden units
(Steps 1 to 3 of the proof of Theorem C.1). -/
theorem flat_le_cobDir_add_rescaleDir_geglu (hθ : OneBlockGenericGated θ) (η : Params _ dIn dOut)
    (hη : η ∈ flat (Arch.gated gelu id hid) 0 θ) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), η = cobDir θ X + rescaleDir θ α :=
  flat_le_cobDir_add_rescaleDir_gated hasDerivAt_gelu (gelu_gatedUnitsRescale _ _ _) θ hθ η hη

/-- **Theorem 5.1 for a GeGLU block, under the conditions of its proof:** the functional
dimension is `P - 2 d² - d_hidden`. -/
theorem funDim_geglu_oneBlock (hθ : OneBlockGenericGated θ) :
    funDim (Arch.gated gelu id hid) 0 θ + (2 * Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) :=
  funDim_gated_oneBlock hasDerivAt_gelu (gelu_gatedUnitsRescale _ _ _) θ hθ

/-- **Theorem 5.1 for a GeGLU block:** with one block, without normalization and without biases,
with `d_in, d_out, d_hidden ≥ d ≥ 2`, the functional dimension is `P - 2 d² - d_hidden` at generic
parameters. -/
theorem ae_funDim_geglu_oneBlock
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated gelu id hid) 0 θ
        + (2 * Fintype.card d ^ 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) :=
  ae_funDim_gated_oneBlock hasDerivAt_gelu (gelu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut hhid

end Skips
