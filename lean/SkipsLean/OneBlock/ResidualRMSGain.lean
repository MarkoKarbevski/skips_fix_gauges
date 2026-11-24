import SkipsLean.OneBlock.ResidualRMSMlp
import SkipsLean.OneBlock.ResidualRMSGated
import SkipsLean.Generic.Params
import SkipsLean.Generic.Gated

/-!
# One block under pre-RMSNorm: the gain of the skip

Paper (skips paper): Theorem 4.6 (ii), "the skip raises the functional dimension by at least
`d(d-1)/2`" (Theorem B.1 (ii), Step 5, last sentence), for `ε > 0` and no biases, for `tanh`, GELU,
SwiGLU and GeGLU blocks: "If the block has width at least `d`, the skipless network with the same
shapes has functional dimension at most `P - d(d-1) - s` by Theorem A.17 (ii), Lemma A.18, so the
skip adds at least `d(d-1)/2`."
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **Theorem 4.6 (ii) of the skips paper, the gain, for one MLP block with `s = 0`:** with
`d_in, d_out, d_hidden ≥ d ≥ 2`, under pre-RMSNorm with `ε > 0`, at generic parameters the skip
raises the functional dimension by at least `d(d-1)/2`. -/
theorem ae_funDim_skipless_add_le_mlp_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (hid 0))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm ε) hid) 0 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ := by
  -- `fd_1 + d(d-1)/2 = P` with the skip, `fd_0 + 2 · d(d-1)/2 ≤ P` without (Theorem 4.2)
  filter_upwards [ae_funDim_mlp_oneBlock_residual_rmsNorm hε hσ hσa hU μ hd hdIn hdOut,
    ae_funDim_add_le_skipless_rmsNorm μ hε rfl
      (fun ℓ => differentiable_f_mlp (fun z => (hσ z).differentiableAt) ℓ) hdIn hhid]
    with θ h1 h0
  omega

/-- **Theorem 4.6 (ii) of the skips paper, the gain, for a `tanh` block.** -/
theorem ae_funDim_skipless_add_le_tanh_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 θ :=
  ae_funDim_skipless_add_le_mlp_oneBlock_residual_rmsNorm hε hasDerivAt_tanh analyticOnNhd_tanh
    (tanh_unitsRigid _ _ _) μ hd hdIn hdOut hhid

/-- **Theorem 4.6 (ii) of the skips paper, the gain, for a GELU block.** -/
theorem ae_funDim_skipless_add_le_gelu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp gelu (rmsNorm ε) hid) 0 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ funDim (Arch.mlp gelu (rmsNorm ε) hid) 1 θ :=
  ae_funDim_skipless_add_le_mlp_oneBlock_residual_rmsNorm hε hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_unitsRigid _ _ _) μ hd hdIn hdOut hhid

/-- **Theorem 4.6 (ii) of the skips paper, the gain, for one gated block:** with
`d_in, d_out, d_hidden ≥ d ≥ 2`, under pre-RMSNorm with `ε > 0`, at generic parameters the skip
raises the functional dimension by at least `d(d-1)/2`. -/
theorem ae_funDim_skipless_add_le_gated_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (hid 0))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 0 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- `fd_1 + d(d-1)/2 + s = P` with the skip, `fd_0 + 2 · d(d-1)/2 + s ≤ P` without
  filter_upwards [ae_funDim_gated_oneBlock_residual_rmsNorm hε hσ hσa hU μ hd hdIn hdOut,
    ae_funDim_add_le_skipless_gated_rmsNorm hε (fun z => (hσ z).differentiableAt) μ hdIn hhid]
    with θ h1 h0
  rw [Fin.sum_univ_one] at h0
  omega

/-- **Theorem 4.6 (ii) of the skips paper, the gain, for a SwiGLU block.** -/
theorem ae_funDim_skipless_add_le_swiglu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated silu (rmsNorm ε) hid) 0 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ funDim (Arch.gated silu (rmsNorm ε) hid) 1 θ :=
  ae_funDim_skipless_add_le_gated_oneBlock_residual_rmsNorm hε hasDerivAt_silu analyticOnNhd_silu
    (silu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut hhid

/-- **Theorem 4.6 (ii) of the skips paper, the gain, for a GeGLU block.** -/
theorem ae_funDim_skipless_add_le_geglu_oneBlock_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated gelu (rmsNorm ε) hid) 0 θ
        + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ funDim (Arch.gated gelu (rmsNorm ε) hid) 1 θ :=
  ae_funDim_skipless_add_le_gated_oneBlock_residual_rmsNorm hε hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_gatedUnitsRescale _ _ _) μ hd hdIn hdOut hhid

end Skips
