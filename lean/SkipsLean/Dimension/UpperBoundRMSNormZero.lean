import SkipsLean.Dimension.UpperBoundRMSNorm
import SkipsLean.Dimension.Rescaling
import SkipsLean.Symmetry.Normalized
import SkipsLean.Generic.Params
import SkipsLean.Generic.Gated

/-!
# The upper bound under pre-RMSNorm with `ε = 0`: the group `CO(d)`

Paper (dimension paper): Theorem 4.3 and the sentence after it, "For `ε = 0` the same bound holds,
with `𝒢 = CO(d_model)`, for the four kinds of block of the main result (Appendix D.2)"; `CO(d)` is
"the group of the matrices `cQ`, of dimension `d(d−1)/2 + 1`" (`c > 0`, `Q` orthogonal). The bound
is `fd ≤ P − (L + 1) (d(d−1)/2 + 1) − s`.

By Proposition 3.2 for `ε = 0` (`eval_cob_rmsNorm_zero`), with `G_ℓ = c_ℓ Q_ℓ` the writes (and `E`)
are multiplied by `G_ℓ` and the reads (and `D`) by `Q_ℓ⁻¹`: RMSNorm with `ε = 0` loses the scale.
So the directions of the symmetries at `θ` are `cobDir θ Y` with antisymmetric `Y_0, …, Y_L` (the
orthogonal part) and `scaleDir θ β` (the scales: `E ↦ β_0 E`, `W_write^ℓ ↦ β_ℓ W_write^ℓ`, the
reads and `D` unchanged), and for gated blocks the rescalings `rescaleDir θ α` of the hidden units.

RMSNorm with `ε = 0` is not differentiable at `0`, and the Lean `rmsNorm 0` maps a zero row to `0`.
The statements below hold at every parameter and for arbitrary maps `f_ℓ`: `flat` and `funDim` are
defined through the Fréchet derivative in the parameters, which Lean takes to be `0` where the
output is not differentiable (as in the statements with a prime of
`Dimension/UpperBoundRMSNorm.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

section General

variable {A : Arch T d L}

/-- The direction in which the scales `c_0, …, c_L > 0` of the hidden states move the parameters
under pre-RMSNorm with `ε = 0`: `E ↦ β_0 E` and `W_write^ℓ ↦ β_ℓ W_write^ℓ`; the reads and `D`
do not move. It is the derivative at `τ = 0` of `θ.cob (fun ℓ => exp (τ β_ℓ) • 1) (fun _ => 1)`. -/
def scaleDir (θ : Params A dIn dOut) (β : Fin (L + 1) → ℝ) : Params A dIn dOut where
  E := β 0 • θ.E
  read _ := 0
  write ℓ := β ℓ.succ • θ.write ℓ
  D := 0

variable (θ : Params A dIn dOut)

/-- **Proposition 3.2 for `ε = 0`, infinitesimal form, the scales:** without skip connections and
under pre-RMSNorm with `ε = 0`, every direction `scaleDir θ β` is flat, for arbitrary maps
`f_ℓ`. -/
theorem scaleDir_mem_flat_skipless_rmsNorm_zero (hA : A.χ = rmsNorm 0) (β : Fin (L + 1) → ℝ) :
    scaleDir θ β ∈ flat A 0 θ := by
  sorry

/-- **Lemma B.1 for `ε = 0`, infinitesimal form:** if `E` and every write have rank `d ≥ 1`, the
antisymmetric matrices `Y_0, …, Y_L` and the numbers `β_0, …, β_L` are determined by the direction
`cobDir θ Y + scaleDir θ β`. -/
theorem cobDir_add_scaleDir_injective [Nonempty d] (hE : θ.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    {Y Y' : Fin (L + 1) → Matrix d d ℝ} (hY : ∀ ℓ, (Y ℓ)ᵀ = -Y ℓ) (hY' : ∀ ℓ, (Y' ℓ)ᵀ = -Y' ℓ)
    {β β' : Fin (L + 1) → ℝ}
    (h : cobDir θ Y + scaleDir θ β = cobDir θ Y' + scaleDir θ β') :
    Y = Y' ∧ β = β' := by
  sorry

/-- **Theorem 4.3 of the dimension paper for `ε = 0`, for the group `CO(d)`, for arbitrary maps
`f_ℓ`:** if `E` and every write have rank `d ≥ 1`, the functional dimension of a network without
skip connections under pre-RMSNorm with `ε = 0` is at most `P − (L + 1) (d(d−1)/2 + 1)`. -/
theorem funDim_add_le_skipless_rmsNorm_zero [Nonempty d] (hA : A.χ = rmsNorm 0)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for `ε = 0` at generic parameters:** for `d_in ≥ d ≥ 1`
and writes of at least `d` rows (MLP blocks of at least `d` hidden units), the functional
dimension of a network without skip connections under pre-RMSNorm with `ε = 0` is at most
`P − (L + 1) (d(d−1)/2 + 1)`. -/
theorem ae_funDim_add_le_skipless_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] (hA : A.χ = rmsNorm 0)
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) :
    ∀ᵐ θ ∂μ, funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end General

section Gated

variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Theorem 4.3 of the dimension paper for `ε = 0`, for gated blocks:** if `E` and every write
have rank `d ≥ 1` and no value column of a read vanishes, the functional dimension of a network of
gated blocks without skip connections under pre-RMSNorm with `ε = 0` is at most
`P − (L + 1) (d(d−1)/2 + 1) − s`, with `s` the number of hidden units. -/
theorem funDim_add_le_skipless_gated_rmsNorm_zero [Nonempty d]
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm 0) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for `ε = 0`, for gated blocks, at generic parameters:**
for `d_in ≥ d ≥ 1` and at least `d` hidden units in every block, the functional dimension is at
most `P − (L + 1) (d(d−1)/2 + 1) − s`. -/
theorem ae_funDim_add_le_skipless_gated_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm 0) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

end Gated

end Skips
