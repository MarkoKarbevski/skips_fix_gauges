import SkipsLean.OneBlock.MlpBiases
import SkipsLean.Symmetry.BiasesRescaleCount

/-!
# The one-block theorem with biases, for SwiGLU and GeGLU blocks

Paper (skips paper), Theorem B.1 (i): "Let the network have no normalization, with or without
biases, and let the block have width at least `d_model` […]. For generic parameters the skipless
network has functional dimension `P − 2 d_model² − s` and the residual network
`P − d_model² − s`; with biases on the embedding, the block and the readout, counted in `P`, both
values are `2 d_model` lower […]. Both networks satisfy the equality condition, and the skip
raises the functional dimension by exactly `d_model²`."

Appendix B, "Reduction": "For the gated blocks ReGLU, SwiGLU and GeGLU, in the same way, the value
weights `(e_i, β_i′)` of each unit, introduced below, have `e_i ≠ 0` and are not proportional to
its gate weights `(c_i, β_i)`." Step 3: "A rescaling of the units by numbers `λ_i` is also a
direction in parameter space […], and similarly for ReGLU and for the values of SwiGLU and GeGLU
[…]. So every flat direction is the sum of a direction of the changes of basis and translations
of Lemma B.2 and a rescaling of the units".

Here, for one gated block `Arch.gated σ id hid` with biases (`Network/Biases.lean`), a gate
activation with the conclusion of Lemma B.3 for SwiGLU and GeGLU (`GatedUnitsRescale`, whose
statement has the biases `β`, `β′` and `γ`), under the conditions `OneBlockGenericGated` on the
weights (they do not involve the biases); `s = d_hidden`, the rescalings of the values. The twin
for MLP blocks with `s = 0` is `OneBlock/MlpBiases.lean`; without biases: `OneBlock/Gated.lean`
and `OneBlock/Residual.lean`.

* `flatB_le_range_gated_skipless`, `flatB_le_range_gated_residual`: a flat direction is the sum of
  a direction of changes of basis and translations and a direction of the rescalings of the
  values with their biases (`rescaleDirB`).
* `funDimB_gated_oneBlock`, `funDimB_gated_oneBlock_residual`: `fd = P − 2 d² − 2 d − d_hidden`
  without the skip and `fd = P − d² − 2 d − d_hidden` with it, `P` counting the biases.
* The same at generic `(θ, b)` for `d_in, d_out, d_hidden ≥ d ≥ 2`, and "the skip raises the
  functional dimension by exactly `d_model²`"; named for SwiGLU and GeGLU.

Numeric check (SwiGLU, `d = d_in = d_out = 2`, one block of 2 units, `P = 30`: 16 and 20):
`ai_notes/biases_inside_blocks_check_2026-11-25.py`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **Lemma B.2 with biases, after Lemma B.3, for one skipless SwiGLU or GeGLU block:** under the
conditions `OneBlockGenericGated` on the weights, every flat direction of the skipless network
with biases is the sum of the direction of changes of basis `X_0, X_1` and translations
`g_0, g_1` of the two hidden states and of a direction of the rescalings of the values. -/
theorem flatB_le_range_gated_skipless (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hp : OneBlockGenericGated p.1)
    (η : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flatB (Arch.gated σ id hid) 0 p) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g) + rescaleDirB p α := by
  sorry

/-- **Theorem B.1 (i) of the skips paper with biases, the skipless network, at one parameter, for
a SwiGLU or GeGLU block:** under the conditions `OneBlockGenericGated` on the weights, the
skipless network with biases has `fd = P − 2 d² − 2 d − d_hidden`, with `P` counting the
biases. -/
theorem funDimB_gated_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hp : OneBlockGenericGated p.1) :
    funDimB (Arch.gated σ id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Lemma B.2 with biases, after Lemma B.3, for one residual SwiGLU or GeGLU block:** under the
conditions `OneBlockGenericGated` on the weights, every flat direction of the residual network
with biases is the sum of the direction of one change of basis `X` of both hidden states and of
the translations `g_0, g_1` of Lemma A.8 and of a direction of the rescalings of the values. -/
theorem flatB_le_range_gated_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hp : OneBlockGenericGated p.1)
    (η : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flatB (Arch.gated σ id hid) 1 p) :
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η = cobDirB p (fun _ => X) + (0, translateDir p.1 g) + rescaleDirB p α := by
  sorry

/-- **Theorem B.1 (i) of the skips paper with biases, the residual network, at one parameter, for
a SwiGLU or GeGLU block:** under the conditions `OneBlockGenericGated` on the weights, the
residual network with biases has `fd = P − d² − 2 d − d_hidden`, with `P` counting the
biases. -/
theorem funDimB_gated_oneBlock_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hp : OneBlockGenericGated p.1) :
    funDimB (Arch.gated σ id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (i) of the skips paper with biases, the skipless network, for a SwiGLU or GeGLU
block:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases the skipless network
has `fd = P − 2 d² − 2 d − d_hidden`. -/
theorem ae_funDimB_gated_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated σ id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGenericGated ν hd hdIn hdOut hhid) μ).mono
    fun p hp => funDimB_gated_oneBlock hσ hU p hp

/-- **Theorem B.1 (i) of the skips paper with biases, the residual network, for a SwiGLU or GeGLU
block:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases the residual network
has `fd = P − d² − 2 d − d_hidden`. -/
theorem ae_funDimB_gated_oneBlock_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated σ id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGenericGated ν hd hdIn hdOut hhid) μ).mono
    fun p hp => funDimB_gated_oneBlock_residual hσ hU p hp

/-- **Theorem B.1 (i) of the skips paper with biases, "the skip raises the functional dimension
by exactly `d_model²`", for a SwiGLU or GeGLU block:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at
generic weights and biases. -/
theorem ae_funDimB_gated_oneBlock_residual_eq_add (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : GatedUnitsRescale σ σ' dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated σ id hid) 1 p
      = funDimB (Arch.gated σ id hid) 0 p + Fintype.card d ^ 2 := by
  filter_upwards [ae_funDimB_gated_oneBlock hσ hU μ hd hdIn hdOut hhid,
    ae_funDimB_gated_oneBlock_residual hσ hU μ hd hdIn hdOut hhid] with p h0 h1
  omega

/-- **Theorem B.1 (i) with biases for one SwiGLU block:** the skip raises the functional
dimension by exactly `d²`. -/
theorem ae_funDimB_swiglu_oneBlock_residual_eq_add
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated silu id hid) 1 p
      = funDimB (Arch.gated silu id hid) 0 p + Fintype.card d ^ 2 :=
  ae_funDimB_gated_oneBlock_residual_eq_add hasDerivAt_silu (silu_gatedUnitsRescale _ _ _) μ hd
    hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one GeGLU block:** the skip raises the functional dimension
by exactly `d²`. -/
theorem ae_funDimB_geglu_oneBlock_residual_eq_add
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated gelu id hid) 1 p
      = funDimB (Arch.gated gelu id hid) 0 p + Fintype.card d ^ 2 :=
  ae_funDimB_gated_oneBlock_residual_eq_add hasDerivAt_gelu (gelu_gatedUnitsRescale _ _ _) μ hd
    hdIn hdOut hhid

end Skips
