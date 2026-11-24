import SkipsLean.Residual.SmallWritesRMSSteps
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.OneBlock.SwiGLU
import SkipsLean.OneBlock.GeGLU
import SkipsLean.Activations.Analytic

/-!
# Residual networks of SwiGLU and GeGLU blocks at any depth, under pre-RMSNorm

Paper (skips paper): Lemma A.27 (Small writes), its second value `fd(θ_τ) = P - d(d-1)/2 - s`
(pre-RMSNorm with `ε > 0`, no biases), and Theorem 4.7 under pre-RMSNorm, for gated blocks:
SwiGLU and GeGLU. Here `s` is the number of hidden units of all blocks. The blocks may have any
widths.

As in `Residual/DepthMlpRMS.lean`, with Lemma B.3 for gated units (`GatedUnitsRescale`, "with `E`
and `D` replaced by the identity and `M = 0`") applied to the hidden units of all blocks together:
a direction `η` that is flat for the limit `J_0` has `η_E = E Y`, `η_D = -Y D` with `Y`
antisymmetric, no component at the gates, and rescales every hidden unit. These directions form a
space of dimension `d(d-1)/2 + s`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **The conditions on `θ` in Lemma A.27 under pre-RMSNorm, for gated blocks:** `E` and `D` have
rank `d`, and the hypotheses of Lemma B.3 hold for the units of all blocks together, "with `E` and
`D` replaced by the identity": every row of every `W_write^ℓ` and every value column of every
`W_read^ℓ` is nonzero, and the gate columns of the `W_read^ℓ`, over all blocks `ℓ` and hidden
units `i`, are nonzero and pairwise non-collinear. -/
structure SmallWritesGenericGatedRMS
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  /-- every row of `W_write^ℓ` is nonzero -/
  row_ne_zero : ∀ ℓ i, θ.write ℓ i ≠ 0
  /-- every gate column of `W_read^ℓ` is nonzero -/
  gate_ne_zero : ∀ ℓ (i : hid ℓ), (θ.read ℓ)ᵀ (Sum.inl i) ≠ 0
  /-- the gate columns of the reads of all blocks together are pairwise non-collinear -/
  gate_not_collinear : ∀ p q : (Σ ℓ, hid ℓ), p ≠ q → ∀ r : ℝ,
    (θ.read p.1)ᵀ (Sum.inl p.2) ≠ r • (θ.read q.1)ᵀ (Sum.inl q.2)
  /-- every value column of `W_read^ℓ` is nonzero -/
  value_ne_zero : ∀ ℓ (i : hid ℓ), (θ.read ℓ)ᵀ (Sum.inr i) ≠ 0

/-- **Proof of Lemma A.27 under pre-RMSNorm, gated blocks, the flat directions of `J_0`:** under
the conditions of the lemma, a direction `η` with `(J_0 η)(x) = 0` at every input `x` has
`η_E = E Y` and `η_D = -Y D` for one antisymmetric matrix `Y`, vanishes at every gate column of a
read, and rescales every hidden unit: for numbers `α_{ℓ,i}`, the value column of unit `i` of block
`ℓ` in `η_read^ℓ` is `-α_{ℓ,i}` times that of `W_read^ℓ`, and its row in `η_write^ℓ` is `α_{ℓ,i}`
times that of `W_write^ℓ`. -/
theorem smallWritesLimitNorm_eq_zero_gated_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : SmallWritesGenericGatedRMS θ)
    (η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hη : ∀ x, smallWritesLimitNorm (Arch.gated σ (rmsNorm ε) hid) θ η x = 0) :
    ∃ (Y : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D)
      ∧ (∀ ℓ (i : hid ℓ) a, η.read ℓ a (Sum.inl i) = 0)
      ∧ (∀ ℓ (i : hid ℓ) a, η.read ℓ a (Sum.inr i) = -(α ℓ i) * θ.read ℓ a (Sum.inr i))
      ∧ (∀ ℓ (i : hid ℓ) a, η.write ℓ i a = α ℓ i * θ.write ℓ i a) := by
  sorry

/-- **Lemma A.27 (Small writes), second value, for gated blocks, under the conditions of its
proof:** under pre-RMSNorm with `ε > 0`, for all small `τ ≠ 0` the residual network has
`fd(θ_τ) = P - d(d-1)/2 - s`, with `s` the number of hidden units. -/
theorem eventually_funDim_smallWrites_gated_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : SmallWritesGenericGatedRMS θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated σ (rmsNorm ε) hid) 1 (θ.smallWrites τ)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- The conditions of Lemma A.27 under pre-RMSNorm for gated blocks hold at generic parameters,
for `d_in, d_out ≥ d ≥ 2` and blocks of any widths. -/
theorem ae_smallWritesGenericGatedRMS
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, SmallWritesGenericGatedRMS θ := by
  sorry

/-- **Lemma A.27 (Small writes), second value, for gated blocks:** with `d_in, d_out ≥ d ≥ 2` and
blocks of any widths, under pre-RMSNorm with `ε > 0`, for generic parameters `θ` and all small
`τ ≠ 0`, the residual network has `fd(θ_τ) = P - d(d-1)/2 - s`. -/
theorem ae_eventually_funDim_smallWrites_gated_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated σ (rmsNorm ε) hid) 1 (θ.smallWrites τ)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for gated blocks under pre-RMSNorm:** with
`d_in, d_out ≥ d ≥ 2`, `L` blocks of any widths and `ε > 0`, at generic parameters the residual
network has the functional dimension `P - d(d-1)/2 - s`, with `s` the number of hidden units. -/
theorem ae_funDim_gated_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-! ### The two kinds of block -/

/-- **Lemma A.27 (Small writes), second value, for SwiGLU blocks under pre-RMSNorm.** -/
theorem ae_eventually_funDim_smallWrites_swiglu_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated silu (rmsNorm ε) hid) 1 (θ.smallWrites τ)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Lemma A.27 (Small writes), second value, for GeGLU blocks under pre-RMSNorm.** -/
theorem ae_eventually_funDim_smallWrites_geglu_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.gated gelu (rmsNorm ε) hid) 1 (θ.smallWrites τ)
          + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for SwiGLU blocks under pre-RMSNorm:** with `ε > 0`, at
generic parameters the residual network of `L` blocks has the functional dimension
`P - d(d-1)/2 - s`. -/
theorem ae_funDim_swiglu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated silu (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for GeGLU blocks under pre-RMSNorm.** -/
theorem ae_funDim_geglu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated gelu (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut) := by
  sorry

end Skips
