import SkipsLean.OneBlock.LearnedSkipTriangular
import SkipsLean.OneBlock.LearnedSkipNarrowGated

/-!
# One tanh, GELU, SwiGLU or GeGLU block of any width with an upper triangular learned skip, `ε > 0`

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. For generic parameters and `ε > 0`, its functional
dimension exceeds that of the residual network of part (ii) by exactly `d_model (d_model + 1)/2`,
and it satisfies the equality condition." Step 5 of its proof: "For an upper triangular `A` […]
`K(θ)` is larger than for the residual network by `d_model (d_model − 1)/2`, respectively `0`,
while the network has `d_model²`, respectively `d_model (d_model + 1)/2`, more parameters. In both
cases the functional dimension is larger by `d_model (d_model + 1)/2`."

`OneBlock/LearnedSkipTriangular.lean` has the upper triangular skip for these four kinds of
block of width at least `d_model`. Here the same **for blocks of any width with at least one
hidden unit**, from the values for the full skip (`OneBlock/LearnedSkipNarrowMlp.lean`,
`OneBlock/LearnedSkipNarrowGated.lean`) and the step from the full to the upper triangular
family of `OneBlock/LearnedSkipTriangular.lean`: at almost every weights and upper triangular
skip `(θ, A)` (for every Haar measure on the pairs), the value
`P + d (d + 1)/2 − d (d − 1)/2 − s` (`s = 0` for tanh and GELU, `s = d_hidden` for SwiGLU and
GeGLU), and the difference `d (d + 1)/2` to the residual network with the same weights `θ`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [LinearOrder d] [Fintype dIn] [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)] {ε : ℝ}

/-- **Theorem B.1 (iii) of the skips paper for one tanh block of any width with an upper
triangular learned skip, `ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and at least one hidden unit, at
almost every `(θ, A)`, `A` upper triangular, the functional dimension is
`P + d (d + 1)/2 − d (d − 1)/2`. -/
theorem ae_funDimLearnedTri_tanh_rmsNorm_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.mlp Real.tanh (rmsNorm ε) hid) p
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly
`d_model (d_model + 1)/2`", for one tanh block of any width with an upper triangular learned
skip, `ε > 0`:** at almost every `(θ, A)`, `A` upper triangular, the functional dimension is that
of the residual network with the weights `θ` plus `d (d + 1)/2`. -/
theorem ae_funDimLearnedTri_tanh_rmsNorm_eq_residual_add_of_nonempty (hε : 0 < ε)
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.mlp Real.tanh (rmsNorm ε) hid) p
      = funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 p.1
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one GELU block of any width with an upper
triangular learned skip, `ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and at least one hidden unit, at
almost every `(θ, A)`, `A` upper triangular, the functional dimension is
`P + d (d + 1)/2 − d (d − 1)/2`. -/
theorem ae_funDimLearnedTri_gelu_rmsNorm_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.mlp gelu (rmsNorm ε) hid) p
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly
`d_model (d_model + 1)/2`", for one GELU block of any width with an upper triangular learned
skip, `ε > 0`:** at almost every `(θ, A)`, `A` upper triangular, the functional dimension is that
of the residual network with the weights `θ` plus `d (d + 1)/2`. -/
theorem ae_funDimLearnedTri_gelu_rmsNorm_eq_residual_add_of_nonempty (hε : 0 < ε)
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.mlp gelu (rmsNorm ε) hid) p
      = funDim (Arch.mlp gelu (rmsNorm ε) hid) 1 p.1
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one SwiGLU block of any width with an upper
triangular learned skip, `ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and at least one hidden unit, at
almost every `(θ, A)`, `A` upper triangular, the functional dimension is
`P + d (d + 1)/2 − d (d − 1)/2 − d_hidden`. -/
theorem ae_funDimLearnedTri_swiglu_rmsNorm_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.gated silu (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly
`d_model (d_model + 1)/2`", for one SwiGLU block of any width with an upper triangular learned
skip, `ε > 0`:** at almost every `(θ, A)`, `A` upper triangular, the functional dimension is that
of the residual network with the weights `θ` plus `d (d + 1)/2`. -/
theorem ae_funDimLearnedTri_swiglu_rmsNorm_eq_residual_add_of_nonempty (hε : 0 < ε)
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.gated silu (rmsNorm ε) hid) p
      = funDim (Arch.gated silu (rmsNorm ε) hid) 1 p.1
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one GeGLU block of any width with an upper
triangular learned skip, `ε > 0`:** for `d_in, d_out ≥ d ≥ 2` and at least one hidden unit, at
almost every `(θ, A)`, `A` upper triangular, the functional dimension is
`P + d (d + 1)/2 − d (d − 1)/2 − d_hidden`. -/
theorem ae_funDimLearnedTri_geglu_rmsNorm_of_nonempty (hε : 0 < ε) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.gated gelu (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly
`d_model (d_model + 1)/2`", for one GeGLU block of any width with an upper triangular learned
skip, `ε > 0`:** at almost every `(θ, A)`, `A` upper triangular, the functional dimension is that
of the residual network with the weights `θ` plus `d (d + 1)/2`. -/
theorem ae_funDimLearnedTri_geglu_rmsNorm_eq_residual_add_of_nonempty (hε : 0 < ε)
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.gated gelu (rmsNorm ε) hid) p
      = funDim (Arch.gated gelu (rmsNorm ε) hid) 1 p.1
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

end Skips
