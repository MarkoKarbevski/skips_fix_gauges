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
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_read_col_ne_zero μ]
    with θ hθ hcol G Q s c hs hQ hG h
  exact cob_rmsNorm_zero_rescaleMlp_eq_self_of_rank_E k θ G Q s c hs hQ hG hθ.1 hθ.2 hcol h

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
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_value_ne_zero μ] with θ hθ hv G Q s c hs hQ hG h
  exact cob_rmsNorm_zero_rescale_eq_self_of_rank_E θ G Q s c hs hQ hG hθ.1 hθ.2 hv h

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
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_value_ne_zero μ, ae_gate_ne_zero μ]
    with θ hθ hv hg G Q s c c' hs hQ hG h
  exact cob_rmsNorm_zero_rescale_rescaleGate_eq_self_of_rank_E k θ G Q s c c' hs hQ hG hθ.1 hθ.2
    hv hg h

omit [Fintype T] [DecidableEq d] in
/-- Helper (a copy of the private `ae_E_ne_zero_lrg` of `Symmetry/LocallyFreeReadoutGeneric.lean`):
at generic parameters `E` is not zero (`d_in ≥ 1`, `d ≥ 1`): its entry `(i₀, a₀)` is a nonzero
linear functional of the parameters. -/
private theorem ae_E_ne_zero_lfy [Nonempty d] [Nonempty dIn] {A : Arch T d L}
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] : ∀ᵐ θ ∂μ, θ.E ≠ 0 := by
  obtain i₀ : dIn := Classical.arbitrary dIn
  obtain a₀ : d := Classical.arbitrary d
  -- the entry `θ ↦ θ.E i₀ a₀` is a linear functional of the parameters
  let l : Params A dIn dOut →ₗ[ℝ] ℝ :=
    (Matrix.entryLinearMap ℝ ℝ i₀ a₀).comp (Params.linE (A := A) (dIn := dIn) (dOut := dOut))
  have hl : ∀ θ, l θ = θ.E i₀ a₀ := fun θ => rfl
  -- it is not zero at the parameter whose embedding has all entries `1`
  have h₁ : l ⟨Matrix.of fun _ _ => 1, 0, 0, 0⟩ ≠ 0 := by
    rw [hl]
    exact one_ne_zero
  have hne : ∀ᵐ θ ∂μ, l θ ≠ 0 :=
    ae_ne_zero_of_analytic μ (analyticOnNhd_linear l) ⟨_, h₁⟩
  filter_upwards [hne] with θ h hz
  exact h (by rw [hl, hz]; rfl)

/-- **`ε = 0`, with the readout, ReLU and ReLU² blocks, at generic parameters** (any activation
and degree `k`, positive rescalings; `d_out ≥ d ≥ 1`, `d_in ≥ 1`, at least `d` hidden units). -/
theorem ae_cob_rmsNorm_zero_rescaleMlp_eq_self_of_dOut [Nonempty d] [Nonempty dIn] (k : ℕ)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G Q : Fin (L + 1) → GL d ℝ) (s : Fin (L + 1) → ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
      (∀ ℓ i, 0 < c ℓ i) →
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) →
      (∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ)) →
      (θ.cob G Q).rescaleMlp k c = θ → (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  filter_upwards [ae_rank_D_read μ hdOut hw, ae_E_ne_zero_lfy μ, ae_read_col_ne_zero μ,
    ae_write_row_ne_zero μ] with θ hθ hE hcol ha G Q s c hc hQ hG h
  exact cob_rmsNorm_zero_rescaleMlp_eq_self_of_rank_D k θ G Q s c hc hQ hG hθ.1 hθ.2 hE hcol
    ha h

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
  -- the reads have the `2 s_ℓ ≥ d` columns `hid ℓ ⊕ hid ℓ`
  have hr : ∀ ℓ, Fintype.card d
      ≤ Fintype.card ((Arch.gated (T := T) (d := d) σ χ hid).r ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card (hid ℓ ⊕ hid ℓ)
    rw [Fintype.card_sum]
    exact (hw ℓ).trans (Nat.le_add_right _ _)
  filter_upwards [ae_rank_D_read μ hdOut hr, ae_E_ne_zero_lfy μ, ae_value_ne_zero μ,
    ae_write_row_ne_zero μ] with θ hθ hE hv ha G Q s c hs hQ hG h
  exact cob_rmsNorm_zero_rescale_eq_self_of_rank_D θ G Q s c hs hQ hG hθ.1 hθ.2 hE hv ha h

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
  -- the reads have the `2 s_ℓ ≥ d` columns `hid ℓ ⊕ hid ℓ`
  have hr : ∀ ℓ, Fintype.card d
      ≤ Fintype.card ((Arch.gated (T := T) (d := d) σ χ hid).r ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card (hid ℓ ⊕ hid ℓ)
    rw [Fintype.card_sum]
    exact (hw ℓ).trans (Nat.le_add_right _ _)
  filter_upwards [ae_rank_D_read μ hdOut hr, ae_E_ne_zero_lfy μ, ae_value_ne_zero μ,
    ae_gate_ne_zero μ, ae_write_row_ne_zero μ] with θ hθ hE hv hg ha G Q s c c' hs hc hQ hG h
  exact cob_rmsNorm_zero_rescale_rescaleGate_eq_self_of_rank_D k θ G Q s c c' hs hc hQ hG hθ.1
    hθ.2 hE hv hg ha h

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
  -- the writes have `H_ℓ d_{h,ℓ} ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d
      ≤ Fintype.card ((Arch.attention (T := T) (d := d) sees χ H dh).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card (H ℓ × dh ℓ)
    rw [Fintype.card_prod]
    exact hH ℓ
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_uba μ hdh]
    with θ h1 h2 G Q s K K' hs hQ hG h
  exact cob_rmsNorm_zero_headsQK_headsVO_eq_self_of_rank_E θ G Q s K K' hs hQ hG h1.1 h1.2 h2.1
    h2.2 h

end Skips
