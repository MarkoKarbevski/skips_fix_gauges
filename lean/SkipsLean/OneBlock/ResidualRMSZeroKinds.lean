import SkipsLean.OneBlock.ResidualRMSZeroGain
import SkipsLean.Absorb.RMSNormAttention

/-!
# One block under pre-RMSNorm with `ε = 0`: the gain of the skip for the five kinds of block

Paper (skips paper), Theorem B.1 (v): "Let the network be pre-RMSNorm with `ε = 0`, without biases,
with a tanh, GELU, SwiGLU, GeGLU or attention block. For generic parameters the skip raises the
functional dimension by at least `d_model (d_model − 1)/2 + 1`, the dimension of `CO(d_model)`."
(Theorem B.1: "Let `d_model ≥ 2`, let the input and output dimensions be at least `d_model` […] an
attention block of `H` heads of width `d_h ≤ d_model`, causal or not, on sequences of at least two
tokens.")

Its proof uses of the parameters: `E` and `D` of rank `d`, and "For generic parameters `w E` and
`g(w)` are linearly independent for all `w` in an open set, since otherwise the block would map
every point of the sphere to a multiple of itself."

Here: this condition at almost every parameter, in the form of
`OneBlock/ResidualRMSZeroSteps.lean` (one input `w` at which, for every token, the rows of `w E`
and of `g(w)` are linearly independent), for MLP blocks whose activation is continuous and
nonzero on the positive reals, for gated blocks with such a gate, and for attention blocks; and
Theorem B.1 (v) at almost every parameter for these kinds, with tanh, GELU, SwiGLU and GeGLU by
name. The functional dimension is the one on the inputs at which no normalized row vanishes
(`funDimOn`, `residualZeroDomain`, `skiplessZeroDomain`), on both sides at the same parameter
`θ`: "the skip raises the functional dimension". The blocks may have any width with at least one
hidden unit (one head of positive width); for attention every token sees some token (the paper's
two masks), and the number of tokens is not restricted.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid H dh : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, Fintype (H ℓ)]
  [∀ ℓ, Fintype (dh ℓ)]
variable {σ : ℝ → ℝ}

/-! ### The condition of the proof at generic parameters -/

/-- **Proof of Theorem B.1 (v), "For generic parameters `w E` and `g(w)` are linearly independent",
for an MLP block** whose activation is continuous and nonzero on the positive reals, with at least
one hidden unit: for almost every `θ` some input `w` has, for every token, the rows of `w E` and
of `g(w)` linearly independent. -/
theorem ae_exists_linearIndependent_rows_mlp (hσc : Continuous σ) (hσp : ∀ z, 0 < z → σ z ≠ 0)
    [Nonempty (hid 0)] (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn
        dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t,
        ((Arch.mlp σ (rmsNorm 0) hid).f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t] := by
  sorry

/-- **The same for a gated block** whose gate is continuous and nonzero on the positive reals,
with at least one hidden unit. -/
theorem ae_exists_linearIndependent_rows_gated (hσc : Continuous σ) (hσp : ∀ z, 0 < z → σ z ≠ 0)
    [Nonempty (hid 0)] (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn
        dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t,
        ((Arch.gated σ (rmsNorm 0) hid).f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t] := by
  sorry

/-- **The same for an attention block** with a head of positive width, for a mask in which every
token sees some token: on an input with equal rows `v` every token gets `N_0(v E) ∑_i W_V W_O`. -/
theorem ae_exists_linearIndependent_rows_attention (sees : T → T → Prop) [DecidableRel sees]
    (hsees : ∀ t, ∃ s, sees t s) [Nonempty (H 0)] [Nonempty (dh 0)]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t,
        ((Arch.attention sees (rmsNorm 0) H dh).f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0)
            t] := by
  sorry

/-! ### Theorem B.1 (v) at generic parameters -/

/-- **Theorem B.1 (v) of the skips paper for an MLP block** whose activation is analytic and
nonzero on the positive reals, with at least one hidden unit: with `d_in, d_out ≥ d ≥ 2`, under
pre-RMSNorm with `ε = 0`, at generic parameters the skip raises the functional dimension by at
least `d(d−1)/2 + 1`, the dimension of `CO(d)`. -/
theorem ae_funDimOn_skipless_add_le_mlp_oneBlock_residual_rmsNorm_zero
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hσp : ∀ z, 0 < z → σ z ≠ 0) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDimOn (Arch.mlp σ (rmsNorm 0) hid) 0 θ (skiplessZeroDomain (Arch.mlp σ (rmsNorm 0)
        hid) θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn (Arch.mlp σ (rmsNorm 0) hid) 1 θ (residualZeroDomain (Arch.mlp σ (rmsNorm 0) hid)
          θ) := by
  sorry

/-- **Theorem B.1 (v) of the skips paper for a tanh block.** -/
theorem ae_funDimOn_skipless_add_le_tanh_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDimOn (Arch.mlp Real.tanh (rmsNorm 0) hid) 0 θ (skiplessZeroDomain (Arch.mlp
        Real.tanh (rmsNorm 0) hid) θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn (Arch.mlp Real.tanh (rmsNorm 0) hid) 1 θ (residualZeroDomain (Arch.mlp Real.tanh
          (rmsNorm 0) hid) θ) := by
  sorry

/-- **Theorem B.1 (v) of the skips paper for a GELU block.** -/
theorem ae_funDimOn_skipless_add_le_gelu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDimOn (Arch.mlp gelu (rmsNorm 0) hid) 0 θ (skiplessZeroDomain (Arch.mlp gelu
        (rmsNorm 0) hid) θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn (Arch.mlp gelu (rmsNorm 0) hid) 1 θ (residualZeroDomain (Arch.mlp gelu (rmsNorm 0)
          hid) θ) := by
  sorry

/-- **Theorem B.1 (v) of the skips paper for a gated block** whose gate is analytic and nonzero on
the positive reals, with at least one hidden unit. -/
theorem ae_funDimOn_skipless_add_le_gated_oneBlock_residual_rmsNorm_zero
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hσp : ∀ z, 0 < z → σ z ≠ 0) [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDimOn (Arch.gated σ (rmsNorm 0) hid) 0 θ (skiplessZeroDomain (Arch.gated σ (rmsNorm
        0) hid) θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn (Arch.gated σ (rmsNorm 0) hid) 1 θ (residualZeroDomain (Arch.gated σ (rmsNorm 0)
          hid) θ) := by
  sorry

/-- **Theorem B.1 (v) of the skips paper for a SwiGLU block.** -/
theorem ae_funDimOn_skipless_add_le_swiglu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDimOn (Arch.gated silu (rmsNorm 0) hid) 0 θ (skiplessZeroDomain (Arch.gated silu
        (rmsNorm 0) hid) θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn (Arch.gated silu (rmsNorm 0) hid) 1 θ (residualZeroDomain (Arch.gated silu
          (rmsNorm 0) hid) θ) := by
  sorry

/-- **Theorem B.1 (v) of the skips paper for a GeGLU block.** -/
theorem ae_funDimOn_skipless_add_le_geglu_oneBlock_residual_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDimOn (Arch.gated gelu (rmsNorm 0) hid) 0 θ (skiplessZeroDomain (Arch.gated gelu
        (rmsNorm 0) hid) θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn (Arch.gated gelu (rmsNorm 0) hid) 1 θ (residualZeroDomain (Arch.gated gelu
          (rmsNorm 0) hid) θ) := by
  sorry

/-- **Theorem B.1 (v) of the skips paper for an attention block** with a head of positive width,
for a mask in which every token sees some token (without a mask, or causal). -/
theorem ae_funDimOn_skipless_add_le_attention_oneBlock_residual_rmsNorm_zero
    (sees : T → T → Prop) [DecidableRel sees] (hsees : ∀ t, ∃ s, sees t s) [Nonempty (H 0)]
    [Nonempty (dh 0)] (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh)
        dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDimOn (Arch.attention sees (rmsNorm 0) H dh) 0 θ (skiplessZeroDomain
        (Arch.attention sees (rmsNorm 0) H dh) θ)
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ funDimOn (Arch.attention sees (rmsNorm 0) H dh) 1 θ (residualZeroDomain (Arch.attention
          sees (rmsNorm 0) H dh) θ) := by
  sorry

end Skips
