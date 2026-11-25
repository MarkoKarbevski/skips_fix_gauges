import SkipsLean.Symmetry.LocallyFreeRMSZero
import SkipsLean.Symmetry.LocallyFreeGeneric
import SkipsLean.Symmetry.LocallyFreeReadoutGeneric

/-!
# Locally free action at generic parameters, `ε = 0`, with the symmetries inside blocks

Papers: Lemma A.18 of the skips paper and Lemma B.1 of the dimension paper, "at generic
parameters the changes of basis and the symmetries inside [the] blocks act locally freely", under
pre-RMSNorm with `ε = 0` ("With RMSNorm the changes of basis lie in `CO(d_model)` or
`O(d_model)`, and the argument is unchanged").

`Symmetry/LocallyFreeRMSZero.lean` states, at one parameter with rank conditions, that changes of
basis `G_ℓ = s_ℓ Q_ℓ` (`s_ℓ > 0`, `Q_ℓ` orthogonal; the writes multiplied by `G_ℓ`, the reads by
`Q_ℓ⁻¹`) with symmetries inside the blocks that fix `θ` are the identity. Here the same **at
almost every `θ`**: with the embedding for `d_in ≥ d ≥ 1` and the widths of the lemma; with the
readout for `d_out ≥ d ≥ 1`, `d_in ≥ 1` and at least `d` hidden units. The conditions at generic
parameters are those of `Symmetry/LocallyFreeGeneric.lean` and
`Symmetry/LocallyFreeReadoutGeneric.lean`, and `E ≠ 0`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- **`ε = 0`, with the embedding, ReLU and ReLU² blocks, at generic parameters** (any
activation and degree `k`; `d_in ≥ d ≥ 1`, at least `d` hidden units). -/
theorem ae_cob_rmsNorm_zero_rescaleMlp_eq_self_of_dIn [Nonempty d] (k : ℕ)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G Q : Fin (L + 1) → GL d ℝ) (s : Fin (L + 1) → ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
      (∀ ℓ, 0 < s ℓ) → (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) →
      (∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ)) →
      (θ.cob G Q).rescaleMlp k c = θ → (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  sorry

/-- **`ε = 0`, with the embedding, gated blocks with any gate, at generic parameters**
(`d_in ≥ d ≥ 1`, at least `d` hidden units). -/
theorem ae_cob_rmsNorm_zero_rescale_eq_self_of_dIn [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G Q : Fin (L + 1) → GL d ℝ) (s : Fin (L + 1) → ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
      (∀ ℓ, 0 < s ℓ) → (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) →
      (∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ)) →
      (θ.cob G Q).rescale c = θ → (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  sorry

/-- **`ε = 0`, with the embedding, ReGLU blocks, at generic parameters** (any gate and degree
`k`; `d_in ≥ d ≥ 1`, at least `d` hidden units). -/
theorem ae_cob_rmsNorm_zero_rescale_rescaleGate_eq_self_of_dIn [Nonempty d] (k : ℕ)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G Q : Fin (L + 1) → GL d ℝ) (s : Fin (L + 1) → ℝ) (c c' : ∀ ℓ, hid ℓ → ℝ),
      (∀ ℓ, 0 < s ℓ) → (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) →
      (∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ)) →
      ((θ.cob G Q).rescale c').rescaleGate k c = θ →
        (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ (∀ ℓ i, c ℓ i = 1) ∧ ∀ ℓ i, c' ℓ i = 1 := by
  sorry

/-- **`ε = 0`, with the readout, ReLU and ReLU² blocks, at generic parameters** (any activation
and degree `k`, positive rescalings; `d_out ≥ d ≥ 1`, `d_in ≥ 1`, at least `d` hidden units). -/
theorem ae_cob_rmsNorm_zero_rescaleMlp_eq_self_of_dOut [Nonempty d] [Nonempty dIn] (k : ℕ)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G Q : Fin (L + 1) → GL d ℝ) (s : Fin (L + 1) → ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
      (∀ ℓ, 0 < s ℓ) → (∀ ℓ i, 0 < c ℓ i) →
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) →
      (∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ)) →
      (θ.cob G Q).rescaleMlp k c = θ → (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  sorry

/-- **`ε = 0`, with the readout, gated blocks with any gate, at generic parameters**
(`d_out ≥ d ≥ 1`, `d_in ≥ 1`, at least `d` hidden units). -/
theorem ae_cob_rmsNorm_zero_rescale_eq_self_of_dOut [Nonempty d] [Nonempty dIn]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G Q : Fin (L + 1) → GL d ℝ) (s : Fin (L + 1) → ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
      (∀ ℓ, 0 < s ℓ) → (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) →
      (∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ)) →
      (θ.cob G Q).rescale c = θ → (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  sorry

/-- **`ε = 0`, with the readout, ReGLU blocks, at generic parameters** (any gate and degree `k`,
positive rescalings of the gates; `d_out ≥ d ≥ 1`, `d_in ≥ 1`, at least `d` hidden units). -/
theorem ae_cob_rmsNorm_zero_rescale_rescaleGate_eq_self_of_dOut [Nonempty d] [Nonempty dIn]
    (k : ℕ)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G Q : Fin (L + 1) → GL d ℝ) (s : Fin (L + 1) → ℝ) (c c' : ∀ ℓ, hid ℓ → ℝ),
      (∀ ℓ, 0 < s ℓ) → (∀ ℓ i, 0 < c ℓ i) →
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) →
      (∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ)) →
      ((θ.cob G Q).rescale c').rescaleGate k c = θ →
        (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ (∀ ℓ i, c ℓ i = 1) ∧ ∀ ℓ i, c' ℓ i = 1 := by
  sorry

variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-- **`ε = 0`, with the embedding, attention blocks, at generic parameters** (`d_in ≥ d ≥ 1`,
heads of width `d_h ≤ d` and total width `H d_h ≥ d`). -/
theorem ae_cob_rmsNorm_zero_headsQK_headsVO_eq_self_of_dIn [Nonempty d]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G Q : Fin (L + 1) → GL d ℝ) (s : Fin (L + 1) → ℝ)
      (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
      (∀ ℓ, 0 < s ℓ) → (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) →
      (∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ)) →
      ((θ.cob G Q).headsQK K).headsVO K' = θ → (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ K = 1 ∧ K' = 1 := by
  sorry

end Skips
