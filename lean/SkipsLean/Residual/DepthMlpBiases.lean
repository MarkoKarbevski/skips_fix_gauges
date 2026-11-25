import SkipsLean.Residual.SmallWritesBiases
import SkipsLean.Residual.DepthMlp
import SkipsLean.Symmetry.BiasesFlat
import SkipsLean.OneBlock.MlpBiases

/-!
# Residual networks of `tanh` and GELU blocks with biases at any depth

Paper (skips paper), Lemma A.27 (Small writes), its third value: "For all small `τ ≠ 0`, the
residual network has" the functional dimension "`fd(θ_τ) = P − d_model² − (L + 1) d_model − s`"
for "MLP blocks with biases, no normalization". Its proof: "At generic parameters the hypotheses
of Lemma B.3 hold for the units of all blocks together, as for one block (Appendix B). So for a
flat `η` the lemma gives
`ψ_M = 0`, `ψ_γ = 0` and a rescaling at every unit. As `E` and `D` have rank `d_model`,
`ψ_M = 0` gives `η_E = EX` and `η_D = −XD` for some `X ∈ ℝ^{d_model × d_model}`. The rescalings
determine `η_read` and `η_write` through `ψ_C` and `ψ_A`, and then `η_{b_read}` through `ψ_β`.
Finally `ψ_γ = 0` determines `η_{b_D}` once `η_{b_E}` and the `η_{b_write^ℓ}` are chosen. So
the flat directions form a space of dimension `d_model² + s` without biases, and
`d_model² + (L + 1) d_model + s` with biases."

Here for MLP blocks whose hidden units have no symmetry of their own (`s = 0`: `tanh` and GELU),
with biases (`Network/Biases.lean`), of any widths, under the conditions `SmallWritesGeneric` of
`Residual/DepthMlp.lean` on the weights (they do not involve the biases). The twin without biases
is `Residual/DepthMlp.lean`; the frame is `Residual/SmallWritesBiases.lean`.

* `smallWritesLimitB_eq_zero_mlp`: a direction that is flat for `J_0` has `η_E = EX`,
  `η_D = −XD`, `η_read^ℓ = 0`, `η_write^ℓ = 0`, `η_{b_read^ℓ} = 0` and
  `η_{b_D} = −(η_{b_E} − b_E X + ∑_ℓ η_{b_write^ℓ}) D`: a space of dimension `d² + (L + 1) d`
  (`X`, `η_{b_E}` and the `η_{b_write^ℓ}` are free).
* `eventually_funDimB_smallWritesB_mlp`: `fd(θ_τ) = P − d² − (L + 1) d` for all small `τ ≠ 0`,
  `P` counting the biases; the upper bound is `funDimB_add_le_residual`
  (`Symmetry/BiasesFlat.lean`).
* The same for generic weights and biases (`d_in, d_out ≥ d ≥ 2`), and, as Theorem 4.7 follows
  from the first value: at generic weights and biases the residual network with biases has
  `fd = P − d² − (L + 1) d` (the paper states this count in Lemma A.8 and checks it in Table 6
  for `tanh` networks with biases; it is not a numbered statement of its own). Named for `tanh`
  and GELU.

Numeric check: `ai_notes/small_writes_biases_check_2026-11-25.py`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **Proof of Lemma A.27, MLP blocks with biases without normalization, the flat directions of
`J_0`:** under the conditions of the lemma on the weights, a direction `η` of weights and biases
with `(J_0 η)(x) = 0` at every input `x` has `η_E = E X` and `η_D = −X D` for one matrix `X`,
`η_read^ℓ = 0`, `η_write^ℓ = 0` and `η_{b_read^ℓ} = 0` for every block, and
`η_{b_D} = −(η_{b_E} − b_E X + ∑_ℓ η_{b_write^ℓ}) D`. Stated for every activation that
satisfies the conclusion of Lemma B.3 with `s = 0` (`UnitsRigid`) for the hidden units of all
blocks together. -/
theorem smallWritesLimitB_eq_zero_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : SmallWritesGeneric p.1)
    (η : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : ∀ x, smallWritesLimitB (Arch.mlp σ id hid) p η x = 0) :
    ∃ X : Matrix d d ℝ, η.1.E = p.1.E * X ∧ η.1.D = -(X * p.1.D) ∧
      (∀ ℓ, η.1.read ℓ = 0) ∧ (∀ ℓ, η.1.write ℓ = 0) ∧ (∀ ℓ, η.2.read ℓ = 0) ∧
      η.2.D = -((η.2.E - p.2.E ᵥ* X + ∑ ℓ, η.2.write ℓ) ᵥ* p.1.D) := by
  sorry

/-- **Lemma A.27 (Small writes), third value, for MLP blocks with `s = 0`, under the conditions of
its proof:** for all small `τ ≠ 0` the residual network with biases has
`fd(θ_τ) = P − d² − (L + 1) d`, with `P` counting the biases. -/
theorem eventually_funDimB_smallWritesB_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (p : ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hp : SmallWritesGeneric p.1) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimB (Arch.mlp σ id hid) 1 (smallWritesB p τ)
          + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d)
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Lemma A.27 (Small writes), third value, for MLP blocks with `s = 0`:** with
`d_in, d_out ≥ d ≥ 2` and blocks of any widths, for generic weights and biases and all small
`τ ≠ 0`, the residual network with biases has `fd(θ_τ) = P − d² − (L + 1) d`. -/
theorem ae_eventually_funDimB_smallWritesB_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimB (Arch.mlp σ id hid) 1 (smallWritesB p τ)
          + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d)
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_paramsB_of_forall_ae (fun ν _ => ae_smallWritesGeneric ν hd hdIn hdOut) μ).mono
    fun p hp => eventually_funDimB_smallWritesB_mlp hσ hσa hU p hp

/-- **Residual networks of MLP blocks with `s = 0` with biases, at any depth, at generic weights
and biases** (as Theorem 4.7 follows from the first value of Lemma A.27; the count of Lemma A.8,
attained): with `d_in, d_out ≥ d ≥ 2` and `L` blocks of any widths, the residual network with
biases has the functional dimension `P − d² − (L + 1) d`. -/
theorem ae_funDimB_mlp_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp σ id hid) 1 p
        + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-! ### The two kinds of block -/

/-- **Lemma A.27 (Small writes), third value, for `tanh` blocks with biases, without
normalization.** -/
theorem ae_eventually_funDimB_smallWritesB_tanh
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimB (Arch.mlp Real.tanh id hid) 1 (smallWritesB p τ)
          + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d)
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :=
  ae_eventually_funDimB_smallWritesB_mlp hasDerivAt_tanh analyticOnNhd_tanh
    (tanh_unitsRigid _ _ _) μ hd hdIn hdOut

/-- **Residual networks of `tanh` blocks with biases at any depth:** at generic weights and
biases the functional dimension is `P − d² − (L + 1) d`. -/
theorem ae_funDimB_tanh_residual
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp Real.tanh id hid) 1 p
        + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut) :=
  ae_funDimB_mlp_residual hasDerivAt_tanh analyticOnNhd_tanh
    (tanh_unitsRigid _ _ _) μ hd hdIn hdOut

/-- **Lemma A.27 (Small writes), third value, for GELU blocks with biases, without
normalization.** -/
theorem ae_eventually_funDimB_smallWritesB_gelu
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimB (Arch.mlp gelu id hid) 1 (smallWritesB p τ)
          + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d)
        = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) :=
  ae_eventually_funDimB_smallWritesB_mlp hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_unitsRigid _ _ _) μ hd hdIn hdOut

/-- **Residual networks of GELU blocks with biases at any depth:** at generic weights and
biases the functional dimension is `P − d² − (L + 1) d`. -/
theorem ae_funDimB_gelu_residual
    (μ : Measure (ParamsB (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimB (Arch.mlp gelu id hid) 1 p
        + (Fintype.card d ^ 2 + (L + 1) * Fintype.card d)
      = Module.finrank ℝ (ParamsB (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut) :=
  ae_funDimB_mlp_residual hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_unitsRigid _ _ _) μ hd hdIn hdOut

end Skips
