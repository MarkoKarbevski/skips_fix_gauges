import SkipsLean.Residual.DepthTransformer
import SkipsLean.Residual.DepthTransformerGated
import SkipsLean.Residual.DepthTransformerRMS
import SkipsLean.Residual.DepthTransformerGatedRMS

/-!
# The exact gain of the skips for transformers, as a conditional statement

Paper (skips paper), Theorem 4.7: "So the skips raise the functional dimension by at least
`L dim G`, and by exactly `L dim G` when the skipless network satisfies the equality condition
too."

Here the last clause for the networks of `Network/Transformer.lean` (attention blocks and MLP
blocks, or attention blocks and gated blocks, in any order), without normalization and under
pre-RMSNorm with `ε > 0`: at almost every parameter `θ`, if the skipless network attains its bound
at `θ` (`fd = P − (L + 1) dim G − s`), then the residual network has exactly `L dim G` more.
Whether the skipless network attains its bound is not proved in the papers for these networks.
The twins: `Residual/ExactGainAttention.lean` (attention blocks, the same conditional statement),
`Residual/ExactGain.lean`, `Residual/ExactGainRMS.lean` (MLP and gated blocks, where the skipless
value is proved).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **Theorem 4.7, "by exactly `L dim G`", for attention blocks and MLP blocks without
normalization:** at almost every parameter, if the skipless network has `fd = P − (L + 1) d² − s`,
the residual network has exactly `L d²` more (`s = 2 ∑ H d_h²`). -/
theorem ae_funDim_attentionMlp_residual_eq_add_of_skipless
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ,
      funDim (Arch.attentionMlp sees σ id H dh hid) 0 θ
          + ((L + 1) * Fintype.card d ^ 2
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ
            (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) →
      funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ
        = funDim (Arch.attentionMlp sees σ id H dh hid) 0 θ
          + L * Fintype.card d ^ 2 := by
  filter_upwards [ae_funDim_attentionMlp_residual hσ hσa hU μ hd hdIn hdOut hdh hdh0 t₁ t₂
    h12 hs2 hs1] with θ h1 h0
  rw [add_one_mul] at h0
  generalize Fintype.card d ^ 2 = g at h0 h1 ⊢
  omega

/-- **Theorem 4.7, "by exactly `L dim G`", for attention blocks and MLP blocks under pre-RMSNorm
with `ε > 0`:** at almost every parameter, if the skipless network has `fd = P − (L + 1) d(d−1)/2 −
s`, the residual network has exactly `L d(d−1)/2` more (`s = 2 ∑ H d_h²`). -/
theorem ae_funDim_attentionMlp_residual_rmsNorm_eq_add_of_skipless (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ,
      funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ
          + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ
            (Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) →
      funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ
        = funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ
          + L * (Fintype.card d * (Fintype.card d - 1) / 2) := by
  filter_upwards [ae_funDim_attentionMlp_residual_rmsNorm hε hσ hσa hU μ hd hdIn hdOut hdh hdh0 t₁
    t₂ h12 hs2 hs1] with θ h1 h0
  rw [add_one_mul] at h0
  generalize (Fintype.card d * (Fintype.card d - 1) / 2) = g at h0 h1 ⊢
  omega

/-- **Theorem 4.7, "by exactly `L dim G`", for attention blocks and gated blocks without
normalization:** at almost every parameter, if the skipless network has `fd = P − (L + 1) d² − s`,
the residual network has exactly `L d²` more (`s = 2 ∑ H d_h² + ∑ d_hidden`). -/
theorem ae_funDim_attentionGated_residual_eq_add_of_skipless
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ,
      funDim (Arch.attentionGated sees σ id H dh hid) 0 θ
          + ((L + 1) * Fintype.card d ^ 2
            + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
        = Module.finrank ℝ
            (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) →
      funDim (Arch.attentionGated sees σ id H dh hid) 1 θ
        = funDim (Arch.attentionGated sees σ id H dh hid) 0 θ
          + L * Fintype.card d ^ 2 := by
  filter_upwards [ae_funDim_attentionGated_residual hσ hσa hU μ hd hdIn hdOut hdh hdh0 t₁ t₂
    h12 hs2 hs1] with θ h1 h0
  rw [add_one_mul] at h0
  generalize Fintype.card d ^ 2 = g at h0 h1 ⊢
  omega

/-- **Theorem 4.7, "by exactly `L dim G`", for attention blocks and gated blocks under pre-RMSNorm
with `ε > 0`:** at almost every parameter, if the skipless network has `fd = P − (L + 1) d(d−1)/2 −
s`, the residual network has exactly `L d(d−1)/2` more (`s = 2 ∑ H d_h² + ∑ d_hidden`). -/
theorem ae_funDim_attentionGated_residual_rmsNorm_eq_add_of_skipless (hε : 0 < ε)
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ,
      funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ
          + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
            + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
        = Module.finrank ℝ
            (Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) →
      funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
        = funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ
          + L * (Fintype.card d * (Fintype.card d - 1) / 2) := by
  filter_upwards [ae_funDim_attentionGated_residual_rmsNorm hε hσ hσa hU μ hd hdIn hdOut hdh hdh0 t₁
    t₂ h12 hs2 hs1] with θ h1 h0
  rw [add_one_mul] at h0
  generalize (Fintype.card d * (Fintype.card d - 1) / 2) = g at h0 h1 ⊢
  omega

end Skips
