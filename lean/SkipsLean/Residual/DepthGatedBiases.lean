import SkipsLean.Residual.SmallWritesBiases
import SkipsLean.Residual.DepthGated
import SkipsLean.Symmetry.BiasesRescaleCount
import SkipsLean.OneBlock.MlpBiases

/-!
# Residual networks of SwiGLU and GeGLU blocks with biases at any depth

Paper (skips paper), Lemma A.27 (Small writes), its third value: "For all small `τ ≠ 0`, the
residual network has" the functional dimension "`fd(θ_τ) = P − d_model² − (L + 1) d_model − s`"
for "MLP blocks with biases, no normalization", where the MLP blocks may be "all SwiGLU or all
GeGLU blocks". Its proof: "For the gated blocks, the read of a unit has a gate and a value: `c_i`
and `β_i` belong to the gate, and `e_i`, `β_i′`, `ψ_{e_i}` and `ψ_{β_i′}` are the same
quantities for the value. […] So the flat directions form a space of dimension `d_model² + s`
without biases, and `d_model² + (L + 1) d_model + s` with biases."

Here for gated blocks with biases (`Network/Biases.lean`) of any widths and a gate activation
with the conclusion of Lemma B.3 for SwiGLU and GeGLU (`GatedUnitsRescale`) for the units of all
blocks together, under the conditions `SmallWritesGenericGated` of `Residual/DepthGated.lean` on
the weights; `s` is the number of hidden units of all blocks. The twins: `Residual/DepthGated.lean`
without biases, `Residual/DepthMlpBiases.lean` for `s = 0`; the frame is
`Residual/SmallWritesBiases.lean`.

* `smallWritesLimitB_eq_zero_gated`: a direction that is flat for `J_0` has `η_E = EX`,
  `η_D = −XD`, no component at the gate columns and gate biases, rescales the value of every
  hidden unit (value column and value bias times `−α`, write row times `α`), and has
  `η_{b_D} = −(η_{b_E} − b_E X + ∑_ℓ η_{b_write^ℓ}) D`: a space of dimension
  `d² + (L + 1) d + s`.
* `eventually_funDimB_smallWritesB_gated`: `fd(θ_τ) = P − d² − (L + 1) d − s` for all small
  `τ ≠ 0`, `P` counting the biases; the upper bound is `funDimB_add_le_residual_gated`
  (`Symmetry/BiasesRescaleCount.lean`).
* The same for generic weights and biases (`d_in, d_out ≥ d ≥ 2`), and at generic weights and
  biases the residual network with biases has `fd = P − d² − (L + 1) d − s` at any depth (the
  count of Lemma A.8, attained; not a numbered statement of the paper). Named for SwiGLU and
  GeGLU.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **Proof of Lemma A.27, gated blocks with biases without normalization, the flat directions of
`J_0`:** under the conditions of the lemma on the weights, a direction `η` of weights and biases
with `(J_0 η)(x) = 0` at every input `x` has `η_E = E X` and `η_D = −X D` for one matrix `X`,
vanishes at every gate column of a read and at every gate bias, and rescales the value of every
hidden unit: for numbers `α_{ℓ,i}`, the value column and the value bias of unit `i` of block `ℓ`
move by `−α_{ℓ,i}` times themselves and its write row by `α_{ℓ,i}` times itself; and
`η_{b_D} = −(η_{b_E} − b_E X + ∑_ℓ η_{b_write^ℓ}) D`. -/
theorem smallWritesLimitB_eq_zero_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hp : SmallWritesGenericGated p.1)
    (η : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hη : ∀ x, smallWritesLimitB (Arch.gated σ id hid) p η x = 0) :
    ∃ (X : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η.1.E = p.1.E * X ∧ η.1.D = -(X * p.1.D) ∧
      (∀ ℓ (i : hid ℓ) a, η.1.read ℓ a (Sum.inl i) = 0) ∧
      (∀ ℓ (i : hid ℓ) a, η.1.read ℓ a (Sum.inr i) = -(α ℓ i) * p.1.read ℓ a (Sum.inr i)) ∧
      (∀ ℓ (i : hid ℓ) a, η.1.write ℓ i a = α ℓ i * p.1.write ℓ i a) ∧
      (∀ ℓ (i : hid ℓ), η.2.read ℓ (Sum.inl i) = 0) ∧
      (∀ ℓ (i : hid ℓ), η.2.read ℓ (Sum.inr i) = -(α ℓ i) * p.2.read ℓ (Sum.inr i)) ∧
      η.2.D = -((η.2.E - p.2.E ᵥ* X + ∑ ℓ, η.2.write ℓ) ᵥ* p.1.D) := by
  sorry

/-- **Lemma A.27 (Small writes), third value, for gated blocks, under the conditions of its
proof:** for all small `τ ≠ 0` the residual network with biases has
`fd(θ_τ) = P − d² − (L + 1) d − s`, with `s` the number of hidden units and `P` counting the
biases. -/
theorem eventually_funDimB_smallWritesB_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hp : SmallWritesGenericGated p.1) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimB (Arch.gated σ id hid) 1 (smallWritesB p τ)
          + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Lemma A.27 (Small writes), third value, for gated blocks:** with `d_in, d_out ≥ d ≥ 2` and
blocks of any widths, for generic weights and biases and all small `τ ≠ 0`, the residual network
with biases has `fd(θ_τ) = P − d² − (L + 1) d − s`. -/
theorem ae_eventually_funDimB_smallWritesB_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimB (Arch.gated σ id hid) 1 (smallWritesB p τ)
          + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_smallWritesGenericGated ν hd hdIn hdOut) μ).mono
    fun p hp => eventually_funDimB_smallWritesB_gated hσ hσa hU p hp

/-- **Residual networks of gated blocks with biases, at any depth, at generic weights and
biases** (as Theorem 4.7 follows from the first value of Lemma A.27; the count of Lemma A.8,
attained): with `d_in, d_out ≥ d ≥ 2` and `L` blocks of any widths, the residual network with
biases has the functional dimension `P − d² − (L + 1) d − s`. -/
theorem ae_funDimB_gated_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated σ id hid) 1 p
        + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-! ### The two kinds of block -/

/-- **Lemma A.27 (Small writes), third value, for SwiGLU blocks with biases, without
normalization.** -/
theorem ae_eventually_funDimB_smallWritesB_swiglu
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimB (Arch.gated silu id hid) 1 (smallWritesB p τ)
          + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) :=
  ae_eventually_funDimB_smallWritesB_gated hasDerivAt_silu analyticOnNhd_silu
    (silu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut

/-- **Residual networks of SwiGLU blocks with biases at any depth:** at generic weights and
biases the functional dimension is `P − d² − (L + 1) d − s`. -/
theorem ae_funDimB_swiglu_residual
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated silu id hid) 1 p
        + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) :=
  ae_funDimB_gated_residual hasDerivAt_silu analyticOnNhd_silu
    (silu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut

/-- **Lemma A.27 (Small writes), third value, for GeGLU blocks with biases, without
normalization.** -/
theorem ae_eventually_funDimB_smallWritesB_geglu
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimB (Arch.gated gelu id hid) 1 (smallWritesB p τ)
          + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) :=
  ae_eventually_funDimB_smallWritesB_gated hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut

/-- **Residual networks of GeGLU blocks with biases at any depth:** at generic weights and
biases the functional dimension is `P − d² − (L + 1) d − s`. -/
theorem ae_funDimB_geglu_residual
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated gelu id hid) 1 p
        + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) :=
  ae_funDimB_gated_residual hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut

end Skips
