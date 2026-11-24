import SkipsLean.Residual.DepthAttentionDim
import SkipsLean.Residual.DepthAttentionRMSDim

/-!
# The exact gain of the skips for attention blocks, as a conditional statement

Paper (skips paper), Theorem 4.7: "So the skips raise the functional dimension by at least
`L dim G`, and by exactly `L dim G` when the skipless network satisfies the equality condition
too."

Here the last clause for attention blocks, without normalization and under pre-RMSNorm with
`ε > 0`: at almost every parameter `θ`, if the skipless network attains its bound at `θ`
(`fd = P − (L + 1) dim G − s`), then the residual network has exactly `L dim G` more. Whether the
skipless network attains its bound is not proved in the papers for `L ≥ 2` attention blocks, nor
under pre-RMSNorm for one attention block (skips paper, after Theorem B.1: "In part (ii), for the
skipless network we prove here only the bound"); for one block without normalization it does
(`OneBlock/AttentionDim.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)] {ε : ℝ}

/-- **Theorem 4.7, "by exactly `L dim G`", for attention blocks without normalization:** at
almost every parameter, if the skipless network has `fd = P − (L + 1) d² − s`, the residual
network has exactly `L d²` more. -/
theorem ae_funDim_attention_residual_eq_add_of_skipless
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ,
      funDim (Arch.attention sees id H dh) 0 θ
          + ((L + 1) * Fintype.card d ^ 2
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) →
      funDim (Arch.attention sees id H dh) 1 θ
        = funDim (Arch.attention sees id H dh) 0 θ + L * Fintype.card d ^ 2 := by
  filter_upwards [ae_funDim_attention_residual μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2 hs1]
    with θ h1 h0
  rw [add_one_mul] at h0
  omega

/-- **Theorem 4.7, "by exactly `L dim G`", for attention blocks under pre-RMSNorm with `ε > 0`:**
at almost every parameter, if the skipless network has `fd = P − (L + 1) d(d−1)/2 − s`, the
residual network has exactly `L d(d−1)/2` more. -/
theorem ae_funDim_attention_residual_rmsNorm_eq_add_of_skipless (hε : 0 < ε)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ,
      funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
          + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ
            (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) →
      funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
        = funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
          + L * (Fintype.card d * (Fintype.card d - 1) / 2) := by
  filter_upwards [ae_funDim_attention_residual_rmsNorm hε μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2
    hs1] with θ h1 h0
  rw [add_one_mul] at h0
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = g at h0 h1 ⊢
  omega

end Skips
