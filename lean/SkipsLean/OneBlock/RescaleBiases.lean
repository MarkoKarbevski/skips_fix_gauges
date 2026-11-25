import SkipsLean.OneBlock.ResidualRescale
import SkipsLean.OneBlock.MlpBiases
import SkipsLean.Symmetry.BiasesRescaleCount
import SkipsLean.Dimension.FunctionalBiasesOn

/-!
# The one-block theorem with biases, for ReLU and ReLU² blocks

Paper (skips paper), Theorem B.1 (i): "Let the network have no normalization, with or without
biases, and let the block have width at least `d_model` […]. For generic parameters the skipless
network has functional dimension `P − 2 d_model² − s` and the residual network
`P − d_model² − s`; with biases on the embedding, the block and the readout, counted in `P`, both
values are `2 d_model` lower […]. Both networks satisfy the equality condition, and the skip
raises the functional dimension by exactly `d_model²`."

Appendix B, "Notation and flat directions": "For the ReLU-type activations, `F(θ, x)` is
differentiable in `θ` at the inputs `x` at which no hidden unit sits at its kink, which form an
open set of full measure, and "every input" means every such input." Step 3: "A rescaling of the
units by numbers `λ_i` is also a direction in parameter space: it scales column `i` of `W_read`
and entry `i` of `b_read` by `λ_i` and row `i` of `W_write` by `−λ_i` for ReLU, by `−2 λ_i` for
ReLU² […]. So every flat direction is the sum of a direction of the changes of basis and
translations of Lemma B.2 and a rescaling of the units".

Here, for one MLP block `Arch.mlp σ id hid` with biases (`Network/Biases.lean`) and an activation
that is positively homogeneous of degree `k`, differentiable away from `0`, with the conclusion
of Lemma B.3 with the rescalings (`UnitsRescale`, whose statement has the biases; ReLU with
`k = 1`, ReLU² with `k = 2`), under the conditions `OneBlockGeneric` on the weights;
`s = d_hidden`. The twins: `OneBlock/Rescale.lean` and `OneBlock/ResidualRescale.lean` without
biases, `OneBlock/MlpBiases.lean` for `s = 0` with biases.

* `noKinkB p`: the inputs at which no hidden unit sits at its kink: every pre-activation
  `(x E W_read)_{t,i} + β_i`, `β = b_E W_read + b_read`, is nonzero. With biases the kinks are
  hyperplanes that need not pass through the origin.
* `differentiableAt_evalB_of_mem_noKinkB`: at such an input the output is differentiable in the
  weights and biases, with the skip and without it.
* `flatOnB_noKinkB_le_mlp_rescale`, `flatOnB_noKinkB_le_mlp_rescale_residual`: a direction that is
  flat at every such input is the sum of a direction of changes of basis and translations and of
  a direction of the rescalings of the units with their biases (`rescaleDirMlpB`).
* `funDimB_mlp_oneBlock_rescale`, `funDimB_mlp_oneBlock_rescale_residual`:
  `fd = P − 2 d² − 2 d − d_hidden` without the skip and `fd = P − d² − 2 d − d_hidden` with it,
  `P` counting the biases. As without biases, Lean's functional dimension uses every input at
  which the output is differentiable in the parameters, a set that contains `noKinkB p`; so the
  value is stated together with
* `exists_jacobianRankB_mlp_oneBlock_rescale`, `exists_jacobianRankB_mlp_oneBlock_rescale_residual`:
  the same rank on a finite batch of inputs with no hidden unit at its kink (the paper's inputs).
* The same at generic `(θ, b)` for `d_in, d_out, d_hidden ≥ d ≥ 2`, and "the skip raises the
  functional dimension by exactly `d_model²`"; named for ReLU and ReLU².

Numeric check (ReLU and ReLU², `d = d_in = d_out = 2`, one block of 2 units, `P = 24`: 10 and
14): `ai_notes/biases_inside_blocks_check_2026-11-25.py`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- The inputs at which no hidden unit of the block with biases sits at its kink: every
pre-activation `(x E W_read)_{t,i} + (b_E W_read + b_read)_i` (one per token and hidden unit) is
nonzero. -/
def noKinkB (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Set (Matrix T dIn ℝ) :=
  {x | ∀ (t : T) (i : hid 0),
    (x * p.1.E * p.1.read 0) t i + (p.2.E ᵥ* p.1.read 0 + p.2.read 0) i ≠ 0}

/-- At an input with no hidden unit at its kink, the output of a network of one block with biases
is differentiable in the weights and biases, when `σ` is differentiable away from `0`; for every
stream matrix (with the skip and without it). -/
theorem differentiableAt_evalB_of_mem_noKinkB (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (S : Fin 1 → Matrix d d ℝ)
    (x : Matrix T dIn ℝ) (hx : x ∈ noKinkB p) :
    DifferentiableAt ℝ
      (fun q : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        evalB (Arch.mlp σ id hid) S q.1 q.2 x) p := by
  sorry

/-- **Lemma B.2 with biases, after Lemma B.3, for one skipless block with the rescalings:** under
the conditions `OneBlockGeneric` on the weights, a direction that is flat at every input with no
hidden unit at its kink is the sum of the direction of changes of basis `X_0, X_1` and
translations `g_0, g_1` of the two hidden states and of a direction of the rescalings of the
hidden units with their biases. -/
theorem flatOnB_noKinkB_le_mlp_rescale {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1)
    (η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flatOnB (Arch.mlp σ id hid) 0 p (noKinkB p)) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g) + rescaleDirMlpB k p α := by
  sorry

/-- **Theorem B.1 (i) of the skips paper with biases, the skipless network, at one parameter, for
a block with the rescalings:** under the conditions `OneBlockGeneric` on the weights,
`fd = P − 2 d² − 2 d − d_hidden`, with `P` counting the biases. -/
theorem funDimB_mlp_oneBlock_rescale {k : ℕ} (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1) :
    funDimB (Arch.mlp σ id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- The same rank on a batch of inputs with no hidden unit at its kink, as the paper takes the
Jacobian for ReLU blocks. -/
theorem exists_jacobianRankB_mlp_oneBlock_rescale {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkB p) ∧
      jacobianRankB (Arch.mlp σ id hid) 0 X p
          + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Lemma B.2 with biases, after Lemma B.3, for one residual block with the rescalings:** under
the conditions `OneBlockGeneric` on the weights, a direction that is flat for the residual
network at every input with no hidden unit at its kink is the sum of the direction of one change
of basis `X` of both hidden states and of the translations `g_0, g_1` of Lemma A.8 and of a
direction of the rescalings of the hidden units with their biases. -/
theorem flatOnB_noKinkB_le_mlp_rescale_residual {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1)
    (η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flatOnB (Arch.mlp σ id hid) 1 p (noKinkB p)) :
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η = cobDirB p (fun _ => X) + (0, translateDir p.1 g) + rescaleDirMlpB k p α := by
  sorry

/-- **Theorem B.1 (i) of the skips paper with biases, the residual network, at one parameter, for
a block with the rescalings:** under the conditions `OneBlockGeneric` on the weights,
`fd = P − d² − 2 d − d_hidden`, with `P` counting the biases. -/
theorem funDimB_mlp_oneBlock_rescale_residual {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1) :
    funDimB (Arch.mlp σ id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- The same rank on a batch of inputs with no hidden unit at its kink. -/
theorem exists_jacobianRankB_mlp_oneBlock_rescale_residual {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkB p) ∧
      jacobianRankB (Arch.mlp σ id hid) 1 X p
          + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-! ### At generic weights and biases -/

/-- **Theorem B.1 (i) of the skips paper with biases, the skipless network, for a block with the
rescalings:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases
`fd = P − 2 d² − 2 d − d_hidden`. -/
theorem ae_funDimB_mlp_oneBlock_rescale {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp σ id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGeneric ν hd hdIn hdOut hhid) μ).mono
    fun p hp => funDimB_mlp_oneBlock_rescale hσ hhom hU p hp

/-- The same on the paper's inputs: at generic weights and biases the Jacobian of the skipless
network has the rank `P − 2 d² − 2 d − d_hidden` on a batch of inputs with no hidden unit at its
kink. -/
theorem ae_exists_jacobianRankB_mlp_oneBlock_rescale {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkB p) ∧
      jacobianRankB (Arch.mlp σ id hid) 0 X p
          + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGeneric ν hd hdIn hdOut hhid) μ).mono
    fun p hp => exists_jacobianRankB_mlp_oneBlock_rescale hσ hhom hU p hp

/-- **Theorem B.1 (i) of the skips paper with biases, the residual network, for a block with the
rescalings:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases
`fd = P − d² − 2 d − d_hidden`. -/
theorem ae_funDimB_mlp_oneBlock_rescale_residual {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp σ id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGeneric ν hd hdIn hdOut hhid) μ).mono
    fun p hp => funDimB_mlp_oneBlock_rescale_residual hσ hhom hU p hp

/-- The same on the paper's inputs: at generic weights and biases the Jacobian of the residual
network has the rank `P − d² − 2 d − d_hidden` on a batch of inputs with no hidden unit at its
kink. -/
theorem ae_exists_jacobianRankB_mlp_oneBlock_rescale_residual {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkB p) ∧
      jacobianRankB (Arch.mlp σ id hid) 1 X p
          + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGeneric ν hd hdIn hdOut hhid) μ).mono
    fun p hp => exists_jacobianRankB_mlp_oneBlock_rescale_residual hσ hhom hU p hp

/-- **Theorem B.1 (i) of the skips paper with biases, "the skip raises the functional dimension
by exactly `d_model²`", for a block with the rescalings:** for `d_in, d_out, d_hidden ≥ d ≥ 2`,
at generic weights and biases. -/
theorem ae_funDimB_mlp_oneBlock_rescale_residual_eq_add {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescale σ σ' k dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp σ id hid) 1 p
      = funDimB (Arch.mlp σ id hid) 0 p + Fintype.card d ^ 2 := by
  filter_upwards [ae_funDimB_mlp_oneBlock_rescale hσ hhom hU μ hd hdIn hdOut hhid,
    ae_funDimB_mlp_oneBlock_rescale_residual hσ hhom hU μ hd hdIn hdOut hhid] with p h0 h1
  omega

/-! ### ReLU -/

/-- **Theorem B.1 (i) with biases for one ReLU block, without the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − 2 d² − 2 d − d_hidden`. -/
theorem ae_funDimB_relu_oneBlock
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp relu id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) :=
  ae_funDimB_mlp_oneBlock_rescale (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous (relu_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one ReLU block, without the skip, on the paper's inputs:**
the rank `P − 2 d² − 2 d − d_hidden` on a batch of inputs with no hidden unit at its kink. -/
theorem ae_exists_jacobianRankB_relu_oneBlock
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkB p) ∧
      jacobianRankB (Arch.mlp relu id hid) 0 X p
          + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) :=
  ae_exists_jacobianRankB_mlp_oneBlock_rescale (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous (relu_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one ReLU block, with the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − d² − 2 d − d_hidden`. -/
theorem ae_funDimB_relu_oneBlock_residual
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp relu id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) :=
  ae_funDimB_mlp_oneBlock_rescale_residual (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous (relu_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one ReLU block, with the skip, on the paper's inputs:** the
rank `P − d² − 2 d − d_hidden` on a batch of inputs with no hidden unit at its kink. -/
theorem ae_exists_jacobianRankB_relu_oneBlock_residual
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkB p) ∧
      jacobianRankB (Arch.mlp relu id hid) 1 X p
          + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) :=
  ae_exists_jacobianRankB_mlp_oneBlock_rescale_residual (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous (relu_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one ReLU block:** the skip raises the functional dimension
by exactly `d²`. -/
theorem ae_funDimB_relu_oneBlock_residual_eq_add
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp relu id hid) 1 p
      = funDimB (Arch.mlp relu id hid) 0 p + Fintype.card d ^ 2 :=
  ae_funDimB_mlp_oneBlock_rescale_residual_eq_add (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous (relu_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-! ### ReLU² -/

/-- **Theorem B.1 (i) with biases for one ReLU² block, without the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − 2 d² − 2 d − d_hidden`. -/
theorem ae_funDimB_reluSq_oneBlock
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp reluSq id hid) 0 p
        + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) :=
  ae_funDimB_mlp_oneBlock_rescale (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous (reluSq_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one ReLU² block, without the skip, on the paper's inputs:**
the rank `P − 2 d² − 2 d − d_hidden` on a batch of inputs with no hidden unit at its kink. -/
theorem ae_exists_jacobianRankB_reluSq_oneBlock
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkB p) ∧
      jacobianRankB (Arch.mlp reluSq id hid) 0 X p
          + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) :=
  ae_exists_jacobianRankB_mlp_oneBlock_rescale (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous (reluSq_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one ReLU² block, with the skip:** for
`d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases `fd = P − d² − 2 d − d_hidden`. -/
theorem ae_funDimB_reluSq_oneBlock_residual
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp reluSq id hid) 1 p
        + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) :=
  ae_funDimB_mlp_oneBlock_rescale_residual (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous (reluSq_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one ReLU² block, with the skip, on the paper's inputs:** the
rank `P − d² − 2 d − d_hidden` on a batch of inputs with no hidden unit at its kink. -/
theorem ae_exists_jacobianRankB_reluSq_oneBlock_residual
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i ∈ noKinkB p) ∧
      jacobianRankB (Arch.mlp reluSq id hid) 1 X p
          + (Fintype.card d ^ 2 + 2 * Fintype.card d + Fintype.card (hid 0))
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) :=
  ae_exists_jacobianRankB_mlp_oneBlock_rescale_residual (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous (reluSq_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

/-- **Theorem B.1 (i) with biases for one ReLU² block:** the skip raises the functional dimension
by exactly `d²`. -/
theorem ae_funDimB_reluSq_oneBlock_residual_eq_add
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp reluSq id hid) 1 p
      = funDimB (Arch.mlp reluSq id hid) 0 p + Fintype.card d ^ 2 :=
  ae_funDimB_mlp_oneBlock_rescale_residual_eq_add (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous (reluSq_unitsRescale dIn dOut (hid 0)) μ hd hdIn hdOut hhid

end Skips
