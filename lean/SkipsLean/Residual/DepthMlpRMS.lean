import SkipsLean.Residual.SmallWritesRMSSteps
import SkipsLean.OneBlock.Tanh
import SkipsLean.OneBlock.GELU
import SkipsLean.Activations.Analytic

/-!
# Residual networks of `tanh` and GELU blocks at any depth, under pre-RMSNorm

Paper (skips paper): Lemma A.27 (Small writes), its second value `fd(θ_τ) = P - d(d-1)/2 - s`
(pre-RMSNorm with `ε > 0`, no biases), and Theorem 4.7 (Equality for residual networks at any
depth) under pre-RMSNorm, for MLP blocks whose hidden units have no symmetry of their own
(`s = 0`): `tanh` blocks and GELU blocks. The blocks may have any widths.

Steps 1 to 3 of the paragraph "Under pre-RMSNorm" of the proof of Lemma A.27 are in
`Residual/SmallWritesRMSSteps.lean`. Here, as in Steps 4 and 5 of the proof of Theorem B.1 (ii):
the derivative of the wide block `n ↦ ∑_ℓ f_ℓ(n W_read^ℓ) W_write^ℓ` along the entries of `η`
vanishes for `n` in the image of `x ↦ N_ε(x E)`, an open set, hence for all `n` (the activation is
real-analytic); Lemma B.3 "with `E` and `D` replaced by the identity and `M = 0`", for the units of
all blocks together, gives `η_read^ℓ = 0` and `η_write^ℓ = 0`. So the flat directions of `J_0` are
`η_E = E Y`, `η_D = -Y D` with `Y` antisymmetric, a space of dimension `d(d-1)/2`.

Theorem 4.7 follows as without normalization (`Residual/DepthMlp.lean`).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **The conditions on `θ` in Lemma A.27 under pre-RMSNorm, for MLP blocks:** `E` and `D` have
rank `d`, and the hypotheses of Lemma B.3 hold for the units of all blocks together, "with `E` and
`D` replaced by the identity": every row of every `W_write^ℓ` is nonzero, and the columns of the
`W_read^ℓ`, over all blocks `ℓ` and hidden units `i`, are nonzero and pairwise non-collinear. -/
structure SmallWritesGenericRMS
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  /-- every row of `W_write^ℓ` is nonzero -/
  row_ne_zero : ∀ ℓ i, θ.write ℓ i ≠ 0
  /-- every column of `W_read^ℓ` is nonzero -/
  col_ne_zero : ∀ ℓ i, (θ.read ℓ)ᵀ i ≠ 0
  /-- the columns of the reads of all blocks together are pairwise non-collinear -/
  col_not_collinear : ∀ p q : (Σ ℓ, hid ℓ), p ≠ q → ∀ r : ℝ,
    (θ.read p.1)ᵀ p.2 ≠ r • (θ.read q.1)ᵀ q.2

/-- **Proof of Lemma A.27 under pre-RMSNorm, MLP blocks, the flat directions of `J_0`:** under
the conditions of the lemma, a direction `η` with `(J_0 η)(x) = 0` at every input `x` has
`η_E = E Y` and `η_D = -Y D` for one antisymmetric matrix `Y`, and `η_read^ℓ = 0`,
`η_write^ℓ = 0` for every block. -/
theorem smallWritesLimitNorm_eq_zero_mlp_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : SmallWritesGenericRMS θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hη : ∀ x, smallWritesLimitNorm (Arch.mlp σ (rmsNorm ε) hid) θ η x = 0) :
    ∃ Y : Matrix d d ℝ, Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D)
      ∧ (∀ ℓ, η.read ℓ = 0) ∧ (∀ ℓ, η.write ℓ = 0) := by
  sorry

/-- **Lemma A.27 (Small writes), second value, for MLP blocks with `s = 0`, under the conditions
of its proof:** under pre-RMSNorm with `ε > 0`, for all small `τ ≠ 0` the residual network has
`fd(θ_τ) = P - d(d-1)/2`. -/
theorem eventually_funDim_smallWrites_mlp_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : SmallWritesGenericRMS θ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp σ (rmsNorm ε) hid) 1 (θ.smallWrites τ)
          + Fintype.card d * (Fintype.card d - 1) / 2
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- The conditions of Lemma A.27 under pre-RMSNorm hold at generic parameters, for
`d_in, d_out ≥ d ≥ 2` and blocks of any widths. -/
theorem ae_smallWritesGenericRMS
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, SmallWritesGenericRMS θ := by
  sorry

/-- **Lemma A.27 (Small writes), second value, for MLP blocks with `s = 0`:** with
`d_in, d_out ≥ d ≥ 2` and blocks of any widths, under pre-RMSNorm with `ε > 0`, for generic
parameters `θ` and all small `τ ≠ 0`, the residual network has `fd(θ_τ) = P - d(d-1)/2`. -/
theorem ae_eventually_funDim_smallWrites_mlp_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp σ (rmsNorm ε) hid) 1 (θ.smallWrites τ)
          + Fintype.card d * (Fintype.card d - 1) / 2
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for MLP blocks with `s = 0`, under pre-RMSNorm:** with
`d_in, d_out ≥ d ≥ 2`, `L` blocks of any widths and `ε > 0`, at generic parameters the residual
network has the functional dimension `P - d(d-1)/2`. -/
theorem ae_funDim_mlp_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-! ### The two kinds of block -/

/-- **Lemma A.27 (Small writes), second value, for `tanh` blocks under pre-RMSNorm.** -/
theorem ae_eventually_funDim_smallWrites_tanh_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 (θ.smallWrites τ)
          + Fintype.card d * (Fintype.card d - 1) / 2
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Lemma A.27 (Small writes), second value, for GELU blocks under pre-RMSNorm.** -/
theorem ae_eventually_funDim_smallWrites_gelu_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.mlp gelu (rmsNorm ε) hid) 1 (θ.smallWrites τ)
          + Fintype.card d * (Fintype.card d - 1) / 2
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for `tanh` blocks under pre-RMSNorm:** with `ε > 0`, at
generic parameters the residual network of `L` blocks has the functional dimension
`P - d(d-1)/2`. -/
theorem ae_funDim_tanh_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem 4.7 of the skips paper for GELU blocks under pre-RMSNorm.** -/
theorem ae_funDim_gelu_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp gelu (rmsNorm ε) hid) 1 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut) := by
  sorry

end Skips
