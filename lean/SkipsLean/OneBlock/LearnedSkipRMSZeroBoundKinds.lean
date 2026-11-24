import SkipsLean.OneBlock.LearnedSkipRMSZeroBound

/-!
# One block with a learned skip under pre-RMSNorm with `ε = 0`: "at most", at generic parameters

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. […] For `ε = 0` it exceeds that of the residual
network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and
ReGLU blocks."

`OneBlock/LearnedSkipRMSZeroBound.lean` has the "at most" at one parameter, for a full learned
skip and a block with an analytic fixed map. Here: at almost every weights and skip `(θ, A)`,
for any such block whose conditions hold at almost every `θ`, and for the kinds of block: MLP
blocks with an analytic activation that is nonzero on the positive reals (tanh and GELU by name),
gated blocks with such a gate (SwiGLU and GeGLU by name), attention blocks. As in
`OneBlock/ResidualRMSZeroKinds.lean`, the blocks may have any width with at least one hidden unit
(one head of positive width), and `d_in, d_out ≥ d ≥ 2`.

Both functional dimensions are those on the inputs at which no normalized row vanishes
(`funDimSkipsOn` on `learnedZeroDomain`, `funDimOn` on `residualZeroDomain`), and the two networks
have the same weights `θ`. Not stated: the upper triangular skip; ReLU, ReLU², ReGLU blocks.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", at generic weights and skip,
for a block with an analytic fixed map:** if at almost every `θ` the embedding and the readout
have rank `d` and some input `w` has the rows of `w E` and `g(w)` independent for every token,
then at almost every `(θ, A)` the functional dimension of the network with the full learned skip
`A` exceeds that of the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_learned_le_funDimOn_residual_add_rmsNorm_zero {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d) (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ)
    (μ : Measure (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))) [μ.IsAddHaarMeasure]
    (hgen : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)),
      θ.E.rank = Fintype.card d ∧ θ.D.rank = Fintype.card d ∧
      ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
        ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t]) :
    ∀ᵐ p ∂μ, funDimSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
        (learnedZeroDomain A p.1 p.2)
      ≤ funDimOn A 1 p.1 (residualZeroDomain A p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  sorry

variable {hid H dh : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, Fintype (H ℓ)]
  [∀ ℓ, Fintype (dh ℓ)]
variable {σ : ℝ → ℝ}

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one MLP block with an
analytic activation that is nonzero on the positive reals:** for `d_in, d_out ≥ d ≥ 2`, at almost
every weights and full learned skip `(θ, A)` the functional dimension exceeds that of the residual
network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_learned_le_residual_add_mlp_oneBlock_rmsNorm_zero
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hσp : ∀ z, 0 < z → σ z ≠ 0)
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp σ (rmsNorm 0) hid)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
        (learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) p.1 p.2)
      ≤ funDimOn (Arch.mlp σ (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.mlp σ (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one tanh block:** for `d_in,
d_out ≥ d ≥ 2`, at almost every weights and full learned skip `(θ, A)` the functional dimension
exceeds that of the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_learned_le_residual_add_tanh_oneBlock_rmsNorm_zero
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp Real.tanh (rmsNorm 0) hid)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
        (learnedZeroDomain (Arch.mlp Real.tanh (rmsNorm 0) hid) p.1 p.2)
      ≤ funDimOn (Arch.mlp Real.tanh (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.mlp Real.tanh (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one GELU block:** for `d_in,
d_out ≥ d ≥ 2`, at almost every weights and full learned skip `(θ, A)` the functional dimension
exceeds that of the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_learned_le_residual_add_gelu_oneBlock_rmsNorm_zero
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp gelu (rmsNorm 0) hid)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
        (learnedZeroDomain (Arch.mlp gelu (rmsNorm 0) hid) p.1 p.2)
      ≤ funDimOn (Arch.mlp gelu (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.mlp gelu (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one gated block with an
analytic gate that is nonzero on the positive reals:** for `d_in, d_out ≥ d ≥ 2`, at almost every
weights and full learned skip `(θ, A)` the functional dimension exceeds that of the residual
network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_learned_le_residual_add_gated_oneBlock_rmsNorm_zero
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hσp : ∀ z, 0 < z → σ z ≠ 0)
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.gated σ (rmsNorm 0) hid)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
        (learnedZeroDomain (Arch.gated σ (rmsNorm 0) hid) p.1 p.2)
      ≤ funDimOn (Arch.gated σ (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.gated σ (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one SwiGLU block:** for
`d_in, d_out ≥ d ≥ 2`, at almost every weights and full learned skip `(θ, A)` the functional
dimension exceeds that of the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_learned_le_residual_add_swiglu_oneBlock_rmsNorm_zero
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.gated silu (rmsNorm 0) hid)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
        (learnedZeroDomain (Arch.gated silu (rmsNorm 0) hid) p.1 p.2)
      ≤ funDimOn (Arch.gated silu (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.gated silu (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one GeGLU block:** for
`d_in, d_out ≥ d ≥ 2`, at almost every weights and full learned skip `(θ, A)` the functional
dimension exceeds that of the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_learned_le_residual_add_geglu_oneBlock_rmsNorm_zero
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.gated gelu (rmsNorm 0) hid)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
        (learnedZeroDomain (Arch.gated gelu (rmsNorm 0) hid) p.1 p.2)
      ≤ funDimOn (Arch.gated gelu (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.gated gelu (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one attention block with a
head of positive width and a mask in which every token sees some token:** for `d_in, d_out ≥ d ≥
2`, at almost every weights and full learned skip `(θ, A)` the functional dimension exceeds that of
the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_learned_le_residual_add_attention_oneBlock_rmsNorm_zero
    (sees : T → T → Prop) [DecidableRel sees] (hsees : ∀ t, ∃ s, sees t s)
    [Nonempty (H 0)] [Nonempty (dh 0)]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.attention sees (rmsNorm 0) H dh)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
        (learnedZeroDomain (Arch.attention sees (rmsNorm 0) H dh) p.1 p.2)
      ≤ funDimOn (Arch.attention sees (rmsNorm 0) H dh) 1 p.1
          (residualZeroDomain (Arch.attention sees (rmsNorm 0) H dh) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  sorry

end Skips
