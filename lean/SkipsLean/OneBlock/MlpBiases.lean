import SkipsLean.OneBlock.Residual
import SkipsLean.Symmetry.BiasesFlat

/-!
# The one-block theorem with biases, for MLP blocks without symmetries inside the hidden units

Paper (skips paper), Theorem B.1 (i): "Let the network have no normalization, with or without
biases, and let the block have width at least `d_model` […]. For generic parameters the skipless
network has functional dimension `P − 2 d_model² − s` and the residual network
`P − d_model² − s`; with biases on the embedding, the block and the readout, counted in `P`, both
values are `2 d_model` lower […]. Both networks satisfy the equality condition, and the skip
raises the functional dimension by exactly `d_model²`."

Appendix B, "Reduction": "With biases `b_E`, `b_read`, `b_write` and `b_D`, the skipless network
computes `F(θ, x) = f(xC + β)A + γ_0` and the residual network `F(θ, x) = xM + f(xC + β)A + γ`,
where `M = ED`, `C = E W_read`, `A = W_write D`, `β = b_E W_read + b_read`,
`γ_0 = b_write D + b_D`, `γ = b_E D + γ_0`." Lemma B.2: "With biases, it keeps `β` and `γ_0`,
respectively `β` and `γ`, fixed as well if and only if moreover `η_{b_E} = b_E X + g_0`,
`η_{b_read} = −g_0 W_read`, `η_{b_write} = b_write Y + g_1` and `η_{b_D} = −g_1 D`, respectively
`η_{b_D} = −(g_0 + g_1) D`, for some row vectors `g_0, g_1`."

Here, for one MLP block `Arch.mlp σ id hid` with biases (`Network/Biases.lean`), an activation
with the conclusion of Lemma B.3 with `s = 0` (`UnitsRigid`, whose statement has the biases `β`
and `γ`; tanh and GELU), under the conditions `OneBlockGeneric` on the weights (they do not
involve the biases):

* `flatB_le_range_mlp_skipless`, `flatB_le_range_mlp_residual`: a flat direction is the direction
  of changes of basis and translations (Lemma B.2 with biases, after Lemma B.3): without the
  skip `cobDirB p X + (0, translateAtDir θ g)` with `X_0, X_1` and `g_0, g_1`; with it
  `cobDirB p (X, X) + (0, translateDir θ g)`.
* `funDimB_mlp_oneBlock`, `funDimB_mlp_oneBlock_residual`: `fd = P − 2 d² − 2 d` without the
  skip and `fd = P − d² − 2 d` with it, `P` counting the biases.
* `ae_paramsB_of_forall_ae`: a property of the weights that holds at generic weights holds at
  generic `(θ, b)`.
* `ae_funDimB_mlp_oneBlock`, `ae_funDimB_mlp_oneBlock_residual`,
  `ae_funDimB_mlp_oneBlock_residual_eq_add`: the same at generic `(θ, b)` for
  `d_in, d_out, d_hidden ≥ d ≥ 2`, and "the skip raises the functional dimension by exactly
  `d_model²`"; named for tanh and GELU.

Numeric check (tanh, `d = 2`, one block of 3 units: 21 and 17 of 29):
`biases_count_check_2026-11-25.py`. Not stated here: ReLU, ReLU², ReGLU, SwiGLU, GeGLU blocks and
attention blocks with biases.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **Lemma B.2 with biases, after Lemma B.3, for one skipless MLP block with `s = 0`:** under the
conditions `OneBlockGeneric` on the weights, every flat direction of the skipless network with
biases is the direction of changes of basis `X_0, X_1` and translations `g_0, g_1` of the two
hidden states. -/
theorem flatB_le_range_mlp_skipless (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1)
    (η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flatB (Arch.mlp σ id hid) 0 p) :
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g) := by
  sorry

/-- **Theorem B.1 (i) of the skips paper with biases, the skipless network, at one parameter, for
an MLP block with `s = 0`:** under the conditions `OneBlockGeneric` on the weights, the skipless
network with biases has `fd = P − 2 d² − 2 d`, with `P` counting the biases. -/
theorem funDimB_mlp_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1) :
    funDimB (Arch.mlp σ id hid) 0 p + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Lemma B.2 with biases, after Lemma B.3, for one residual MLP block with `s = 0`:** under
the conditions `OneBlockGeneric` on the weights, every flat direction of the residual network
with biases is the direction of one change of basis `X` of both hidden states and of the
translations `g_0, g_1` of Lemma A.8. -/
theorem flatB_le_range_mlp_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1)
    (η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flatB (Arch.mlp σ id hid) 1 p) :
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ),
      η = cobDirB p (fun _ => X) + (0, translateDir p.1 g) := by
  sorry

/-- **Theorem B.1 (i) of the skips paper with biases, the residual network, at one parameter, for
an MLP block with `s = 0`:** under the conditions `OneBlockGeneric` on the weights, the residual
network with biases has `fd = P − d² − 2 d`, with `P` counting the biases. -/
theorem funDimB_mlp_oneBlock_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : OneBlockGeneric p.1) :
    funDimB (Arch.mlp σ id hid) 1 p + (Fintype.card d ^ 2 + 2 * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

omit [Nonempty T] [DecidableEq d] in
/-- **A property of the weights that holds at generic weights holds at generic weights and
biases:** if `P θ` holds at almost every `θ` for every Haar measure on the weights, then
`P p.1` holds at almost every `p = (θ, b)` for every Haar measure on the pairs. -/
theorem ae_paramsB_of_forall_ae {L : ℕ} {A : Arch T d L} {P : Params A dIn dOut → Prop}
    (h : ∀ (ν : Measure (Params A dIn dOut)) [ν.IsAddHaarMeasure], ∀ᵐ θ ∂ν, P θ)
    (μ : Measure (ParamsB A dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ p ∂μ, P p.1 := by
  sorry

/-- **Theorem B.1 (i) of the skips paper with biases, the skipless network, for an MLP block with
`s = 0`:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases the skipless
network has `fd = P − 2 d² − 2 d`. -/
theorem ae_funDimB_mlp_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp σ id hid) 0 p + (2 * Fintype.card d ^ 2 + 2 * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGeneric ν hd hdIn hdOut hhid) μ).mono
    fun p hp => funDimB_mlp_oneBlock hσ hU p hp

/-- **Theorem B.1 (i) of the skips paper with biases, the residual network, for an MLP block with
`s = 0`:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at generic weights and biases the residual
network has `fd = P − d² − 2 d`. -/
theorem ae_funDimB_mlp_oneBlock_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp σ id hid) 1 p + (Fintype.card d ^ 2 + 2 * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_oneBlockGeneric ν hd hdIn hdOut hhid) μ).mono
    fun p hp => funDimB_mlp_oneBlock_residual hσ hU p hp

/-- **Theorem B.1 (i) of the skips paper with biases, "the skip raises the functional dimension
by exactly `d_model²`", for an MLP block with `s = 0`:** for `d_in, d_out, d_hidden ≥ d ≥ 2`, at
generic weights and biases. -/
theorem ae_funDimB_mlp_oneBlock_residual_eq_add (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp σ id hid) 1 p
      = funDimB (Arch.mlp σ id hid) 0 p + Fintype.card d ^ 2 := by
  filter_upwards [ae_funDimB_mlp_oneBlock hσ hU μ hd hdIn hdOut hhid,
    ae_funDimB_mlp_oneBlock_residual hσ hU μ hd hdIn hdOut hhid] with p h0 h1
  omega

/-- **Theorem B.1 (i) with biases for one `tanh` block:** the skip raises the functional dimension
by exactly `d²`. -/
theorem ae_funDimB_tanh_oneBlock_residual_eq_add
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp Real.tanh id hid) 1 p
      = funDimB (Arch.mlp Real.tanh id hid) 0 p + Fintype.card d ^ 2 :=
  ae_funDimB_mlp_oneBlock_residual_eq_add hasDerivAt_tanh (tanh_unitsRigid _ _ _) μ hd hdIn hdOut
    hhid

/-- **Theorem B.1 (i) with biases for one GELU block:** the skip raises the functional dimension
by exactly `d²`. -/
theorem ae_funDimB_gelu_oneBlock_residual_eq_add
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp gelu id hid) 1 p
      = funDimB (Arch.mlp gelu id hid) 0 p + Fintype.card d ^ 2 :=
  ae_funDimB_mlp_oneBlock_residual_eq_add hasDerivAt_gelu (gelu_unitsRigid _ _ _) μ hd hdIn hdOut
    hhid

end Skips
