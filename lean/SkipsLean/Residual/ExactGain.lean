import SkipsLean.Residual.DepthMlp
import SkipsLean.Residual.DepthGated
import SkipsLean.Depth.Tanh
import SkipsLean.Depth.GeluGatedTheorem
import SkipsLean.Generic.Params
import SkipsLean.Generic.Gated

/-!
# The gain of the skip connections at any depth

Paper (skips paper): Theorem 4.7, second sentence ("So the skips raise the functional dimension
by at least `L dim 𝒢`, and by exactly `L dim 𝒢` when the skipless network satisfies the equality
condition too"), and Corollary 4.8 (Exact gain), both without normalization, where
`dim 𝒢 = d²`.

The residual network has `fd = P - d² - s` at generic parameters (Theorem 4.7,
`Residual/DepthMlp.lean` and `Residual/DepthGated.lean`). The skipless network with blocks of
width at least `d` has `fd ≤ P - (L+1) d² - s` at generic parameters (Theorem 4.2), with equality
for `tanh`, SwiGLU and GeGLU blocks (Theorem 5.2 of the dimension paper). The statements below
are the differences.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **Theorem 4.7 of the skips paper, the gain, for MLP blocks with `s = 0`, without
normalization:** with `d_in, d_out ≥ d ≥ 2` and blocks of width at least `d`, at generic
parameters the skips raise the functional dimension by at least `L d²`. -/
theorem ae_funDim_skipless_add_le_residual_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 0 θ + L * Fintype.card d ^ 2
      ≤ funDim (Arch.mlp σ id hid) 1 θ := by
  -- `fd_1 + d² = P` with the skips (Theorem 4.7), `fd_0 + (L+1) d² ≤ P` without (Theorem 4.2)
  filter_upwards [ae_funDim_mlp_residual hσ hσa hU μ hd hdIn hdOut,
    ae_funDim_add_le_skipless μ rfl
      (fun ℓ => differentiable_f_mlp (fun z => (hσ z).differentiableAt) ℓ) hdIn hhid]
    with θ h1 h0
  have h : (L + 1) * Fintype.card d ^ 2 = L * Fintype.card d ^ 2 + Fintype.card d ^ 2 := by ring
  omega

/-- **Theorem 4.7 of the skips paper, the gain, for GELU blocks without normalization:** at
generic parameters the skips raise the functional dimension by at least `L d²`. -/
theorem ae_funDim_skipless_add_le_residual_gelu
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp gelu id hid) 0 θ + L * Fintype.card d ^ 2
      ≤ funDim (Arch.mlp gelu id hid) 1 θ :=
  ae_funDim_skipless_add_le_residual_mlp hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_unitsRigid _ _ _) μ hd hdIn hdOut hhid

/-- **Theorem 4.7 of the skips paper, the gain, for gated blocks without normalization:** with
`d_in, d_out ≥ d ≥ 2` and blocks of width at least `d`, at generic parameters the skips raise the
functional dimension by at least `L d²`. -/
theorem ae_funDim_skipless_add_le_residual_gated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' dIn dOut (Σ ℓ, hid ℓ))
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 0 θ + L * Fintype.card d ^ 2
      ≤ funDim (Arch.gated σ id hid) 1 θ := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- `fd_1 + d² + s = P` with the skips, `fd_0 + (L+1) d² + s ≤ P` without
  filter_upwards [ae_funDim_gated_residual hσ hσa hU μ hd hdIn hdOut,
    ae_funDim_add_le_skipless_gated (fun z => (hσ z).differentiableAt) μ hdIn hhid]
    with θ h1 h0
  have h : (L + 1) * Fintype.card d ^ 2 = L * Fintype.card d ^ 2 + Fintype.card d ^ 2 := by ring
  omega

/-- **Corollary 4.8 of the skips paper for `tanh` blocks, without normalization:** with
`d_in, d_out ≥ d ≥ 2` and blocks of width at least `d`, at generic parameters the skips raise the
functional dimension by exactly `L d²`. -/
theorem ae_funDim_tanh_residual_eq_add
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp Real.tanh id hid) 1 θ
      = funDim (Arch.mlp Real.tanh id hid) 0 θ + L * Fintype.card d ^ 2 := by
  -- `fd_1 + d² = P` (Theorem 4.7), `fd_0 + (L+1) d² = P` (Theorem 5.2 (i) of the dimension paper)
  filter_upwards [ae_funDim_tanh_residual μ hd hdIn hdOut,
    ae_funDim_tanh_skipless μ hd hdIn hdOut hhid] with θ h1 h0
  have h : (L + 1) * Fintype.card d ^ 2 = L * Fintype.card d ^ 2 + Fintype.card d ^ 2 := by ring
  omega

/-- **Corollary 4.8 of the skips paper for SwiGLU blocks, without normalization:** at generic
parameters the skips raise the functional dimension by exactly `L d²`. -/
theorem ae_funDim_swiglu_residual_eq_add
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated silu id hid) 1 θ
      = funDim (Arch.gated silu id hid) 0 θ + L * Fintype.card d ^ 2 := by
  -- `fd_1 + d² + s = P` (Theorem 4.7), `fd_0 + (L+1) d² + s = P` (Theorem 5.2 (iii))
  filter_upwards [ae_funDim_swiglu_residual μ hd hdIn hdOut,
    ae_funDim_swiglu_skipless μ hd hdIn hdOut hhid] with θ h1 h0
  have h : (L + 1) * Fintype.card d ^ 2 = L * Fintype.card d ^ 2 + Fintype.card d ^ 2 := by ring
  omega

/-- **Corollary 4.8 of the skips paper for GeGLU blocks, without normalization:** at generic
parameters the skips raise the functional dimension by exactly `L d²`. -/
theorem ae_funDim_geglu_residual_eq_add
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated gelu id hid) 1 θ
      = funDim (Arch.gated gelu id hid) 0 θ + L * Fintype.card d ^ 2 := by
  filter_upwards [ae_funDim_geglu_residual μ hd hdIn hdOut,
    ae_funDim_geglu_skipless μ hd hdIn hdOut hhid] with θ h1 h0
  have h : (L + 1) * Fintype.card d ^ 2 = L * Fintype.card d ^ 2 + Fintype.card d ^ 2 := by ring
  omega

end Skips
