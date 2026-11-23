import SkipsLean.Dimension.Rescaling
import SkipsLean.OneBlock.Common

/-!
# The upper bound for gated blocks at generic parameters

Paper (dimension paper): Theorem 4.3 for gated blocks (SwiGLU, GeGLU), with the number `s` of the
rescalings of the values of the hidden units: at generic parameters the functional dimension is at
most `P - (L + 1) dim G - s`, without normalization (`dim G = d²`) and under pre-RMSNorm
(`dim G = d (d - 1) / 2`).

The pointwise bounds are in `Dimension/Rescaling.lean`, under the conditions that `E` and every
write have rank `d` and that no value column of a read vanishes. Here these conditions are shown
to hold at generic parameters, when `d_in ≥ d` and every block has at least `d` hidden units.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- At generic parameters no value column of a read of a gated network vanishes. -/
theorem ae_value_ne_zero [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0 := by
  -- finitely many conditions, one for each hidden unit `i` of each block `ℓ`
  refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_
  -- an entry `k₀` of the value column
  obtain k₀ : d := Classical.arbitrary d
  -- the entry `θ ↦ θ.read ℓ k₀ (inr i)` is a linear functional of the parameters
  let l : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut →ₗ[ℝ] ℝ :=
    (Matrix.entryLinearMap ℝ ℝ k₀ (Sum.inr i)).comp
      (Params.linRead (A := Arch.gated (T := T) (d := d) σ χ hid) (dIn := dIn) (dOut := dOut) ℓ)
  have hl : ∀ θ, l θ = θ.read ℓ k₀ (Sum.inr i) := fun θ => rfl
  -- it is not zero at the parameters whose reads have all entries `1`
  have h₁ : l ⟨0, fun _ => Matrix.of fun _ _ => 1, 0, 0⟩ ≠ 0 := by
    rw [hl]
    exact one_ne_zero
  -- an analytic function that is not identically zero is nonzero almost everywhere
  have hne : ∀ᵐ θ ∂μ, l θ ≠ 0 :=
    ae_ne_zero_of_analytic μ (analyticOnNhd_linear l) ⟨_, h₁⟩
  -- and a function with a nonzero entry is not zero
  filter_upwards [hne] with θ h hz
  exact h (by rw [hl]; exact congrFun hz k₀)

/-- **Theorem 4.3 for gated blocks, without normalization, at generic parameters:** for
`d_in ≥ d` and at least `d` hidden units in every block, the functional dimension is at most
`P - (L + 1) d² - s`, with `s` the number of hidden units of the network. -/
theorem ae_funDim_add_le_skipless_gated [Nonempty d] (hσ : Differentiable ℝ σ)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the pointwise bound holds wherever `E` and the writes have rank `d` and no value column of a
  -- read vanishes
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_value_ne_zero μ] with θ h1 h2
  exact funDim_add_le_skipless_gated θ hσ h1.1 h1.2 h2

/-- **Theorem 4.3 for gated blocks under pre-RMSNorm (`ε > 0`), at generic parameters:** for
`d_in ≥ d` and at least `d` hidden units in every block, the functional dimension is at most
`P - (L + 1) d (d - 1) / 2 - s`, with `s` the number of hidden units of the network. -/
theorem ae_funDim_add_le_skipless_gated_rmsNorm [Nonempty d] {ε : ℝ} (hε : 0 < ε)
    (hσ : Differentiable ℝ σ)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
        (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  -- the pointwise bound holds wherever `E` and the writes have rank `d` and no value column of a
  -- read vanishes
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_value_ne_zero μ] with θ h1 h2
  exact funDim_add_le_skipless_gated_rmsNorm hε θ hσ h1.1 h1.2 h2

end Skips
