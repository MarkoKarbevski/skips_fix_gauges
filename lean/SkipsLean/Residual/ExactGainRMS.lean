import SkipsLean.Residual.DepthMlpRMS
import SkipsLean.Residual.DepthGatedRMS
import SkipsLean.Depth.TanhRMS
import SkipsLean.Depth.GeluGatedTheorem
import SkipsLean.Generic.Params
import SkipsLean.Generic.Gated

/-!
# The gain of the skip connections at any depth, under pre-RMSNorm

Paper (skips paper): Theorem 4.7, second sentence, and Corollary 4.8 (Exact gain), under
pre-RMSNorm with `ε > 0`, where `dim 𝒢 = d(d-1)/2`: "At generic parameters, the skips raise the
functional dimension by exactly `L dim 𝒢` … by `L d(d-1)/2` under pre-RMSNorm", for all `tanh`, all
SwiGLU, all GeGLU or all GELU blocks.

The residual network has `fd = P - d(d-1)/2 - s` at generic parameters (Theorem 4.7,
`Residual/DepthMlpRMS.lean` and `Residual/DepthGatedRMS.lean`). The skipless network with blocks
of width at least `d` has `fd ≤ P - (L+1) d(d-1)/2 - s` (Theorem 4.2), with equality for the four
kinds of block (Theorem 5.2 of the dimension paper). The statements below are the differences.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **Theorem 4.7 of the skips paper, the gain, for MLP blocks with `s = 0` under pre-RMSNorm:**
with `d_in, d_out ≥ d ≥ 2`, blocks of width at least `d` and `ε > 0`, at generic parameters the
skips raise the functional dimension by at least `L d(d-1)/2`. -/
theorem ae_funDim_skipless_add_le_residual_mlp_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm ε) hid) 0 θ
        + L * (Fintype.card d * (Fintype.card d - 1) / 2)
      ≤ funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ := by
  -- `fd_1 + c = P` with the skips, `fd_0 + (L+1) c ≤ P` without, `c = d(d-1)/2`
  filter_upwards [ae_funDim_mlp_residual_rmsNorm hε hσ hσa hU μ hd hdIn hdOut,
    ae_funDim_add_le_skipless_rmsNorm μ hε rfl
      (fun ℓ => differentiable_f_mlp (fun z => (hσ z).differentiableAt) ℓ) hdIn hhid]
    with θ h1 h0
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = c at h0 h1 ⊢
  have h : (L + 1) * c = L * c + c := by ring
  omega

/-- **Theorem 4.7 of the skips paper, the gain, for gated blocks under pre-RMSNorm:** with
`d_in, d_out ≥ d ≥ 2`, blocks of width at least `d` and `ε > 0`, at generic parameters the skips
raise the functional dimension by at least `L d(d-1)/2`. -/
theorem ae_funDim_skipless_add_le_residual_gated_rmsNorm (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 0 θ
        + L * (Fintype.card d * (Fintype.card d - 1) / 2)
      ≤ funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  filter_upwards [ae_funDim_gated_residual_rmsNorm hε hσ hσa hU μ hd hdIn hdOut,
    ae_funDim_add_le_skipless_gated_rmsNorm hε (fun z => (hσ z).differentiableAt) μ hdIn hhid]
    with θ h1 h0
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = c at h0 h1 ⊢
  have h : (L + 1) * c = L * c + c := by ring
  omega

/-- **Corollary 4.8 of the skips paper for `tanh` blocks under pre-RMSNorm:** with
`d_in, d_out ≥ d ≥ 2`, blocks of width at least `d` and `ε > 0`, at generic parameters the skips
raise the functional dimension by exactly `L d(d-1)/2`. -/
theorem ae_funDim_tanh_residual_rmsNorm_eq_add (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 θ
      = funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 0 θ
        + L * (Fintype.card d * (Fintype.card d - 1) / 2) := by
  -- `fd_1 + c = P` (Theorem 4.7), `fd_0 + (L+1) c = P` (Theorem 5.2 (i) of the dimension paper)
  filter_upwards [ae_funDim_tanh_residual_rmsNorm hε μ hd hdIn hdOut,
    ae_funDim_tanh_skipless_rmsNorm hε μ hd hdIn hdOut hhid] with θ h1 h0
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = c at h0 h1 ⊢
  have h : (L + 1) * c = L * c + c := by ring
  omega

/-- **Corollary 4.8 of the skips paper for GELU blocks under pre-RMSNorm:** at generic parameters
the skips raise the functional dimension by exactly `L d(d-1)/2`. -/
theorem ae_funDim_gelu_residual_rmsNorm_eq_add (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp gelu (rmsNorm ε) hid) 1 θ
      = funDim (Arch.mlp gelu (rmsNorm ε) hid) 0 θ
        + L * (Fintype.card d * (Fintype.card d - 1) / 2) := by
  -- Theorem 4.7 and Theorem 5.2 (ii) of the dimension paper
  filter_upwards [ae_funDim_gelu_residual_rmsNorm hε μ hd hdIn hdOut,
    ae_funDim_gelu_skipless_rmsNorm hε μ hd hdIn hdOut hhid] with θ h1 h0
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = c at h0 h1 ⊢
  have h : (L + 1) * c = L * c + c := by ring
  omega

/-- **Corollary 4.8 of the skips paper for SwiGLU blocks under pre-RMSNorm:** at generic
parameters the skips raise the functional dimension by exactly `L d(d-1)/2`. -/
theorem ae_funDim_swiglu_residual_rmsNorm_eq_add (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated silu (rmsNorm ε) hid) 1 θ
      = funDim (Arch.gated silu (rmsNorm ε) hid) 0 θ
        + L * (Fintype.card d * (Fintype.card d - 1) / 2) := by
  -- Theorem 4.7 and Theorem 5.2 (iii) of the dimension paper
  filter_upwards [ae_funDim_swiglu_residual_rmsNorm hε μ hd hdIn hdOut,
    ae_funDim_swiglu_skipless_rmsNorm hε μ hd hdIn hdOut hhid] with θ h1 h0
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = c at h0 h1 ⊢
  have h : (L + 1) * c = L * c + c := by ring
  omega

/-- **Corollary 4.8 of the skips paper for GeGLU blocks under pre-RMSNorm:** at generic
parameters the skips raise the functional dimension by exactly `L d(d-1)/2`. -/
theorem ae_funDim_geglu_residual_rmsNorm_eq_add (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated gelu (rmsNorm ε) hid) 1 θ
      = funDim (Arch.gated gelu (rmsNorm ε) hid) 0 θ
        + L * (Fintype.card d * (Fintype.card d - 1) / 2) := by
  filter_upwards [ae_funDim_geglu_residual_rmsNorm hε μ hd hdIn hdOut,
    ae_funDim_geglu_skipless_rmsNorm hε μ hd hdIn hdOut hhid] with θ h1 h0
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = c at h0 h1 ⊢
  have h : (L + 1) * c = L * c + c := by ring
  omega

end Skips
