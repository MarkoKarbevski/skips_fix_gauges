import SkipsLean.Depth.GeluGatedExplicit
import SkipsLean.Dimension.GenericRank
import SkipsLean.Generic.Gated
import SkipsLean.Depth.SuffixRMS
import SkipsLean.Depth.SuffixGated
import SkipsLean.OneBlock.UnitsSwiGLU

/-!
# The bound is attained at any depth: GELU, SwiGLU and GeGLU blocks

Paper (dimension): Theorem 5.2. "Let `d_in, d_out ≥ d_model ≥ 2`, and consider networks without
biases whose blocks are all of one kind, tanh, GELU, SwiGLU or GeGLU, each with at least `d_model`
hidden units. In the following cases the functional dimension at generic parameters is
`P − (L + 1) dim G − s` … (ii) GELU blocks: under pre-RMSNorm with `ε > 0` and with `ε = 0`.
(iii) SwiGLU blocks, and GeGLU blocks: without normalization, and under pre-RMSNorm with `ε > 0`."
Here `s = 0` for GELU blocks and `s` is the number of hidden units of the network for SwiGLU and
GeGLU blocks; `dim G = d²` without normalization and `d (d − 1) / 2` under pre-RMSNorm with
`ε > 0`.

Stated here: part (ii) for `ε > 0` and part (iii). The proof is the last step of Appendix D.7: at
one parameter (`Depth/GeluGatedExplicit.lean`) the functional dimension has this value
(Proposition D.4); at generic parameters it is at least as large (`Dimension/GenericRank.lean`),
and it is at most this value by Theorem 4.3. Part (ii) for `ε = 0`: `Depth/GeluZero.lean`
(`ae_funDim_gelu_skipless_rmsNorm_zero`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Theorem 5.2 (ii), `ε > 0`:** for GELU blocks under pre-RMSNorm, at generic parameters
`fd = P − (L + 1) d (d − 1) / 2`. -/
theorem ae_funDim_gelu_skipless_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp gelu (rmsNorm ε) hid) 0 θ
        + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut) := by
  obtain ⟨θ₀, hθ, h0⟩ := exists_regular_claimRMS_gelu (T := T) (d := d) (dIn := dIn) (dOut := dOut)
    (hid := hid) hε hd hdIn hdOut hhid
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_gelu ℓ
  -- step 1: the value at `θ₀` (Proposition D.4)
  have h1 := funDim_of_claimRMS _ θ₀ hε rfl hf hθ h0
  -- step 2: generic parameters have at least this functional dimension
  have h2 := ae_funDim_ge (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) 0 hf
    (analyticOnNhd_rmsNorm hε) μ θ₀
  -- step 3: and at most the value (Theorem 4.3)
  have hfd : ∀ ℓ, Differentiable ℝ ((Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid).f ℓ) :=
    fun ℓ => differentiableOn_univ.1 (hf ℓ).differentiableOn
  have h3 := ae_funDim_add_le_skipless_rmsNorm
    (A := Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid)
    μ hε rfl hfd hdIn hhid
  filter_upwards [h2, h3] with θ h2 h3
  omega

/-- **Theorem 5.2 (iii), SwiGLU blocks without normalization:** at generic parameters
`fd = P − (L + 1) d² − ∑ d_hidden`. -/
theorem ae_funDim_swiglu_skipless [Nonempty T]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated silu id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu id hid) dIn dOut) := by
  obtain ⟨θ₀, hθ, hv, h0⟩ := exists_regular_claimGated_swiglu (T := T) (d := d)
    (dIn := dIn) (dOut := dOut)
    (hid := hid) hd hdIn hdOut hhid
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) silu id hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_gated analyticOnNhd_silu ℓ
  -- step 1: the value at `θ₀` (Proposition D.4)
  have h1 := funDim_of_claimGated analyticOnNhd_silu θ₀ hθ hv h0
  -- step 2: generic parameters have at least this functional dimension
  have h2 := ae_funDim_ge (Arch.gated (T := T) (d := d) silu id hid) 0 hf
    analyticOnNhd_id μ θ₀
  -- step 3: and at most the value (Theorem 4.3)
  have h3 := ae_funDim_add_le_skipless_gated (T := T) (d := d) (hid := hid)
    (fun z => (hasDerivAt_silu z).differentiableAt) μ hdIn hhid
  filter_upwards [h2, h3] with θ h2 h3
  omega

/-- **Theorem 5.2 (iii), SwiGLU blocks under pre-RMSNorm with `ε > 0`:** at generic parameters
`fd = P − (L + 1) d (d − 1) / 2 − ∑ d_hidden`. -/
theorem ae_funDim_swiglu_skipless_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated silu (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut) := by
  obtain ⟨θ₀, hθ, hv, h0⟩ := exists_regular_claimGated_swiglu_rmsNorm (T := T) (d := d)
    (dIn := dIn) (dOut := dOut)
    (hid := hid) hε hd hdIn hdOut hhid
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have hf : ∀ ℓ,
      AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_gated analyticOnNhd_silu ℓ
  -- step 1: the value at `θ₀` (Proposition D.4)
  have h1 := funDim_of_claimGated_rmsNorm hε analyticOnNhd_silu θ₀ hθ hv h0
  -- step 2: generic parameters have at least this functional dimension
  have h2 := ae_funDim_ge (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) 0 hf
    (analyticOnNhd_rmsNorm hε) μ θ₀
  -- step 3: and at most the value (Theorem 4.3)
  have h3 := ae_funDim_add_le_skipless_gated_rmsNorm (T := T) (d := d) (hid := hid) hε
    (fun z => (hasDerivAt_silu z).differentiableAt) μ hdIn hhid
  filter_upwards [h2, h3] with θ h2 h3
  omega

/-- **Theorem 5.2 (iii), GeGLU blocks without normalization.** -/
theorem ae_funDim_geglu_skipless [Nonempty T]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated gelu id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) gelu id hid) dIn dOut) := by
  obtain ⟨θ₀, hθ, hv, h0⟩ := exists_regular_claimGated_geglu (T := T) (d := d)
    (dIn := dIn) (dOut := dOut)
    (hid := hid) hd hdIn hdOut hhid
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) gelu id hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_gated analyticOnNhd_gelu ℓ
  -- step 1: the value at `θ₀` (Proposition D.4)
  have h1 := funDim_of_claimGated analyticOnNhd_gelu θ₀ hθ hv h0
  -- step 2: generic parameters have at least this functional dimension
  have h2 := ae_funDim_ge (Arch.gated (T := T) (d := d) gelu id hid) 0 hf
    analyticOnNhd_id μ θ₀
  -- step 3: and at most the value (Theorem 4.3)
  have h3 := ae_funDim_add_le_skipless_gated (T := T) (d := d) (hid := hid)
    (fun z => (hasDerivAt_gelu z).differentiableAt) μ hdIn hhid
  filter_upwards [h2, h3] with θ h2 h3
  omega

/-- **Theorem 5.2 (iii), GeGLU blocks under pre-RMSNorm with `ε > 0`.** -/
theorem ae_funDim_geglu_skipless_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated gelu (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut) := by
  obtain ⟨θ₀, hθ, hv, h0⟩ := exists_regular_claimGated_geglu_rmsNorm (T := T) (d := d)
    (dIn := dIn) (dOut := dOut)
    (hid := hid) hε hd hdIn hdOut hhid
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have hf : ∀ ℓ,
      AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_gated analyticOnNhd_gelu ℓ
  -- step 1: the value at `θ₀` (Proposition D.4)
  have h1 := funDim_of_claimGated_rmsNorm hε analyticOnNhd_gelu θ₀ hθ hv h0
  -- step 2: generic parameters have at least this functional dimension
  have h2 := ae_funDim_ge (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) 0 hf
    (analyticOnNhd_rmsNorm hε) μ θ₀
  -- step 3: and at most the value (Theorem 4.3)
  have h3 := ae_funDim_add_le_skipless_gated_rmsNorm (T := T) (d := d) (hid := hid) hε
    (fun z => (hasDerivAt_gelu z).differentiableAt) μ hdIn hhid
  filter_upwards [h2, h3] with θ h2 h3
  omega

end Skips
