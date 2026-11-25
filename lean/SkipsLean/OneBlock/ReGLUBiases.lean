import SkipsLean.OneBlock.ReGLU
import SkipsLean.OneBlock.MlpBiases
import SkipsLean.Symmetry.BiasesRescaleCount
import SkipsLean.Dimension.FunctionalBiasesOn

/-!
# The one-block theorem with biases, for a ReGLU block

Paper (skips paper), Theorem B.1 (i): "Let the network have no normalization, with or without
biases, and let the block have width at least `d_model` […]. For generic parameters the skipless
network has functional dimension `P − 2 d_model² − s` and the residual network
`P − d_model² − s`; with biases on the embedding, the block and the readout, counted in `P`, both
values are `2 d_model` lower […]. Both networks satisfy the equality condition, and the skip
raises the functional dimension by exactly `d_model²`."

Appendix B, "Reduction": "For the gated blocks ReGLU, SwiGLU and GeGLU, in the same way, the value
weights `(e_i, β_i′)` of each unit, introduced below, have `e_i ≠ 0` and are not proportional to
its gate weights `(c_i, β_i)`." Step 3: "`s` is the number of rescalings: `d_hidden` for ReLU,
ReLU², SwiGLU and GeGLU, `2 d_hidden` for ReGLU, none for tanh and GELU."

Here, for one ReGLU block `Arch.gated relu id hid` with biases (`Network/Biases.lean`), under the
conditions `OneBlockGenericReGLU` on the weights (no value column of `E W_read` is proportional
to the gate column of the same unit; then the pair of the value column and the value bias is not
proportional to the pair of the gate column and the gate bias, which is what Lemma B.3 for ReGLU,
`relu_gated_units_flat`, asks); `s = 2 d_hidden`. The twins: `OneBlock/ReGLU.lean` without
biases; `OneBlock/RescaleBiases.lean` and `OneBlock/GatedBiases.lean` with biases.

* `noKinkGateB p`: the inputs at which no gate sits at its kink: every gate pre-activation
  `(x E W_read)_{t, gate i} + β_i`, `β = b_E W_read + b_read`, is nonzero.
* `differentiableAt_evalB_of_mem_noKinkGateB`: at such an input the output is differentiable in
  the weights and biases, with the skip and without it.
* `flatOnB_noKinkGateB_le_reglu`, `flatOnB_noKinkGateB_le_reglu_residual`: a direction that is
  flat at every such input is the sum of a direction of changes of basis and translations, a
  direction of the rescalings of the values and a direction of the rescalings of the gates, with
  their biases (`rescaleDirB`, `rescaleDirGateB 1`).
* `funDimB_reglu_oneBlock`, `funDimB_reglu_oneBlock_residual`: `fd = P − 2 d² − 2 d − 2 d_hidden`
  without the skip and `fd = P − d² − 2 d − 2 d_hidden` with it, `P` counting the biases; each
  with the same rank on a finite batch of inputs with no gate at its kink
  (`exists_jacobianRankB_reglu_oneBlock`, `exists_jacobianRankB_reglu_oneBlock_residual`), as in
  `OneBlock/RescaleBiases.lean`.
* The same at generic `(θ, b)` for `d_in, d_out, d_hidden ≥ d ≥ 2`, and "the skip raises the
  functional dimension by exactly `d_model²`".

Numeric check (`d = d_in = d_out = 2`, one block of 2 units, `P = 30`: 14 and 18):
`ai_notes/biases_inside_blocks_check_2026-11-25.py`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ}

/-- The inputs at which no gate of the block with biases sits at its kink: every gate
pre-activation `(x E W_read)_{t, gate i} + (b_E W_read + b_read)_{gate i}` (one per token and
hidden unit) is nonzero. -/
def noKinkGateB (p : ParamsB (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    Set (Matrix T dIn ℝ) :=
  {x | ∀ (t : T) (i : hid 0),
    (x * p.1.E * p.1.read 0) t (Sum.inl i) + (p.2.E ᵥ* p.1.read 0 + p.2.read 0) (Sum.inl i) ≠ 0}

/-- At an input with no gate at its kink, the output of a network of one ReGLU block with biases
is differentiable in the weights and biases, for every stream matrix (with the skip and without
it). -/
theorem differentiableAt_evalB_of_mem_noKinkGateB (S : Fin 1 → Matrix d d ℝ)
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (hx : x ∈ noKinkGateB p) :
    DifferentiableAt ℝ
      (fun q : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut =>
        evalB (Arch.gated relu id hid) S q.1 q.2 x) p := by
  sorry

/-- **Lemma B.2 with biases, after Lemma B.3, for one skipless ReGLU block:** under the conditions
`OneBlockGenericReGLU` on the weights, a direction that is flat at every input with no gate at
its kink is the sum of the direction of changes of basis `X_0, X_1` and translations `g_0, g_1`
of the two hidden states, a direction of the rescalings of the values and a direction of the
rescalings of the gates, with their biases. -/
theorem flatOnB_noKinkGateB_le_reglu
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hp : OneBlockGenericReGLU p.1)
    (η : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hη : η ∈ flatOnB (Arch.gated relu id hid) 0 p (noKinkGateB p)) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ) (α β : ∀ ℓ, hid ℓ → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g) + rescaleDirB p α + rescaleDirGateB 1 p β := by
  sorry

/-- **Theorem B.1 (i) of the skips paper with biases, the skipless network, at one parameter, for
a ReGLU block:** under the conditions `OneBlockGenericReGLU` on the weights,
`fd = P − 2 d² − 2 d − 2 d_hidden`, with `P` counting the biases. -/
theorem funDimB_reglu_oneBlock
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hp : OneBlockGenericReGLU p.1) :
    funDimB (Arch.gated relu id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- The same rank on a batch of inputs with no gate at its kink, as the paper takes the Jacobian
for ReGLU blocks. -/
theorem exists_jacobianRankB_reglu_oneBlock
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hp : OneBlockGenericReGLU p.1) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateB p) ∧
      jacobianRankB (Arch.gated relu id hid) 0 X p
          + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Lemma B.2 with biases, after Lemma B.3, for one residual ReGLU block:** under the conditions
`OneBlockGenericReGLU` on the weights, a direction that is flat for the residual network at every
input with no gate at its kink is the sum of the direction of one change of basis `X` of both
hidden states and of the translations `g_0, g_1` of Lemma A.8, a direction of the rescalings of
the values and a direction of the rescalings of the gates, with their biases. -/
theorem flatOnB_noKinkGateB_le_reglu_residual
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hp : OneBlockGenericReGLU p.1)
    (η : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hη : η ∈ flatOnB (Arch.gated relu id hid) 1 p (noKinkGateB p)) :
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ) (α β : ∀ ℓ, hid ℓ → ℝ),
      η = cobDirB p (fun _ => X) + (0, translateDir p.1 g) + rescaleDirB p α
        + rescaleDirGateB 1 p β := by
  sorry

/-- **Theorem B.1 (i) of the skips paper with biases, the residual network, at one parameter, for
a ReGLU block:** under the conditions `OneBlockGenericReGLU` on the weights,
`fd = P − d² − 2 d − 2 d_hidden`, with `P` counting the biases. -/
theorem funDimB_reglu_oneBlock_residual
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hp : OneBlockGenericReGLU p.1) :
    funDimB (Arch.gated relu id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- The same rank on a batch of inputs with no gate at its kink. -/
theorem exists_jacobianRankB_reglu_oneBlock_residual
    (p : ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut)
    (hp : OneBlockGenericReGLU p.1) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateB p) ∧
      jacobianRankB (Arch.gated relu id hid) 1 X p
          + (Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-! ### At generic weights and biases -/

/-- **Theorem B.1 (i) with biases for one ReGLU block, without the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases
`fd = P − 2 d² − 2 d − 2 d_hidden`. -/
theorem ae_funDimB_reglu_oneBlock
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated relu id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGenericReGLU ν hd hdIn hdOut hhid) μ).mono
    fun p hp => funDimB_reglu_oneBlock p hp

/-- **Theorem B.1 (i) with biases for one ReGLU block, without the skip, on the paper's inputs:**
the rank `P − 2 d² − 2 d − 2 d_hidden` on a batch of inputs with no gate at its kink. -/
theorem ae_exists_jacobianRankB_reglu_oneBlock
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateB p) ∧
      jacobianRankB (Arch.gated relu id hid) 0 X p
          + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGenericReGLU ν hd hdIn hdOut hhid) μ).mono
    fun p hp => exists_jacobianRankB_reglu_oneBlock p hp

/-- **Theorem B.1 (i) with biases for one ReGLU block, with the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − d² − 2 d − 2 d_hidden`. -/
theorem ae_funDimB_reglu_oneBlock_residual
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated relu id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGenericReGLU ν hd hdIn hdOut hhid) μ).mono
    fun p hp => funDimB_reglu_oneBlock_residual p hp

/-- **Theorem B.1 (i) with biases for one ReGLU block, with the skip, on the paper's inputs:** the
rank `P − d² − 2 d − 2 d_hidden` on a batch of inputs with no gate at its kink. -/
theorem ae_exists_jacobianRankB_reglu_oneBlock_residual
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkGateB p) ∧
      jacobianRankB (Arch.gated relu id hid) 1 X p
          + (Fintype.card d ^ 2 + 2 * Fintype.card d + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGenericReGLU ν hd hdIn hdOut hhid) μ).mono
    fun p hp => exists_jacobianRankB_reglu_oneBlock_residual p hp

/-- **Theorem B.1 (i) with biases for one ReGLU block:** at generic weights and biases the skip
raises the functional dimension by exactly `d²`. -/
theorem ae_funDimB_reglu_oneBlock_residual_eq_add
    (μ : Measure (ParamsB (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.gated relu id hid) 1 p
      = funDimB (Arch.gated relu id hid) 0 p + Fintype.card d ^ 2 := by
  filter_upwards [ae_funDimB_reglu_oneBlock μ hd hdIn hdOut hhid,
    ae_funDimB_reglu_oneBlock_residual μ hd hdIn hdOut hhid] with p h0 h1
  omega

end Skips
