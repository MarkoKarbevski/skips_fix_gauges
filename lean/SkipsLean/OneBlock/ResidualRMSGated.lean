import SkipsLean.OneBlock.ResidualRMSSteps
import SkipsLean.OneBlock.SwiGLU
import SkipsLean.OneBlock.GeGLU
import SkipsLean.Activations.Analytic

/-!
# One residual SwiGLU or GeGLU block under pre-RMSNorm

Paper (skips paper): Theorem 4.6 (ii), first sentence (Theorem B.1 (ii) in the appendix), for
`ε > 0` and no biases, for gated blocks: SwiGLU and GeGLU. At generic parameters the residual
network of one block has the functional dimension `P - d(d-1)/2 - s`, with `s` the number of
hidden units (one rescaling per hidden unit). The block may have any width.

Steps 1 to 3 of the proof are in `OneBlock/ResidualRMSSteps.lean`. Steps 4 and 5 are as in
`OneBlock/ResidualRMSMlp.lean`, with Lemma B.3 for gated units (`GatedUnitsRescale`, "with `E` and
`D` replaced by the identity and `M = 0`"): it "makes the entries of `η'` at each hidden unit a
rescaling". So the flat directions are those of the orthogonal change of basis and of the
rescalings of the hidden units, a space of dimension `d(d-1)/2 + s`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **The conditions on `θ` in the proof of Theorem B.1 (ii), for one gated block:** `E` and `D`
have rank `d`, and the hypotheses of Lemma B.3 hold "with `E` and `D` replaced by the identity":
every row of `W_write` and every value column of `W_read` is nonzero, and the gate columns of
`W_read` are nonzero and pairwise non-collinear. -/
structure OneBlockGenericGatedRMS
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  /-- every row of `W_write` is nonzero -/
  row_ne_zero : ∀ i, θ.write 0 i ≠ 0
  /-- every gate column of `W_read` is nonzero -/
  gate_ne_zero : ∀ i : hid 0, (θ.read 0)ᵀ (Sum.inl i) ≠ 0
  /-- the gate columns of `W_read` are pairwise non-collinear -/
  gate_not_collinear : ∀ i j : hid 0, i ≠ j → ∀ r : ℝ,
    (θ.read 0)ᵀ (Sum.inl i) ≠ r • (θ.read 0)ᵀ (Sum.inl j)
  /-- every value column of `W_read` is nonzero -/
  value_ne_zero : ∀ i : hid 0, (θ.read 0)ᵀ (Sum.inr i) ≠ 0

/-- **Proof of Theorem B.1 (ii), Steps 1 to 4, for one gated block:** under the conditions of the
proof, every flat direction of the residual network under pre-RMSNorm (`ε > 0`) is the sum of
the direction of one antisymmetric `Y` at both hidden states and of the direction of a rescaling
of the values of the hidden units. -/
theorem flat_le_cobDir_const_add_rescaleDir_gated_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (hid 0))
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericGatedRMS θ)
    (η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hη : η ∈ flat (Arch.gated σ (rmsNorm ε) hid) 1 θ) :
    ∃ (Y : Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
      η = cobDir θ (fun _ => Y) + rescaleDir θ α := by
  sorry

/-- **Theorem 4.6 (ii) of the skips paper, first sentence, for one gated block, under the
conditions of its proof:** under pre-RMSNorm with `ε > 0` the residual network has the functional
dimension `P - d(d-1)/2 - d_hidden`. -/
theorem funDim_gated_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (hid 0))
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : OneBlockGenericGatedRMS θ) :
    funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- The conditions of the proof hold at generic parameters, for `d_in, d_out ≥ d ≥ 2` and a block
of any width. -/
theorem ae_oneBlockGenericGatedRMS
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, OneBlockGenericGatedRMS θ := by
  sorry

/-- **Theorem 4.6 (ii) of the skips paper, first sentence, for one gated block:** with
`d_in, d_out ≥ d ≥ 2` and a block of any width, under pre-RMSNorm with `ε > 0`, at generic
parameters the residual network has the functional dimension `P - d(d-1)/2 - d_hidden`. -/
theorem ae_funDim_gated_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (hid 0))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-! ### The two kinds of block -/

/-- **Theorem 4.6 (ii) of the skips paper, first sentence, for a SwiGLU block:** under pre-RMSNorm
with `ε > 0`, at generic parameters the residual network of one block has the functional
dimension `P - d(d-1)/2 - d_hidden`. -/
theorem ae_funDim_swiglu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated silu (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem 4.6 (ii) of the skips paper, first sentence, for a GeGLU block.** -/
theorem ae_funDim_geglu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated gelu (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut) := by
  sorry

end Skips
