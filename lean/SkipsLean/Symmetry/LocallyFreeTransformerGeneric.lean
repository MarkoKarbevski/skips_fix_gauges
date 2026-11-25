import SkipsLean.Symmetry.LocallyFreeTransformer
import SkipsLean.Dimension.UpperBoundTransformerRescale

/-!
# Locally free action at generic parameters (attention with MLP blocks)

Paper (skips paper), Lemma A.18 (Locally free action), third sentence: "With an embedding of
rank `d_model`, it also holds for networks with attention blocks whose heads have width
`d_h ≤ d_model` and total width `H d_h ≥ d_model`", where "it" is "at generic parameters the
changes of basis and the symmetries inside blocks act locally freely".

`Symmetry/LocallyFreeTransformer.lean` states, at one parameter with rank conditions, that
changes of basis and symmetries inside the blocks that fix `θ` are the identity, for networks of
attention blocks and MLP or gated blocks in any order. Here the same **at almost every `θ`**, for
`d_in ≥ d ≥ 1`, heads of width `d_h ≤ d`, and blocks of total width `H d_h + d_hidden ≥ d` (a
block may be an attention block alone, with `H d_h ≥ d`, or an MLP block alone, with
`d_hidden ≥ d`). Each proof is the statement at one parameter at a generic one
(`ae_rank_E_write`, `ae_rank_QV_ubr`, `ae_sumSnd_col_ne_zero_ubr`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}
  {χ : Matrix T d ℝ → Matrix T d ℝ}

/-- **Lemma A.18, third sentence, at generic parameters: attention blocks with
MLP blocks with the rescalings of the hidden units**
(`d_in ≥ d ≥ 1`, `d_h ≤ d`, `H d_h + d_hidden ≥ d`). -/
theorem ae_cob_heads_rescaleMlp_eq_self_of_dIn [Nonempty d] (k : ℕ)
    (μ : Measure (Params (Arch.attentionMlp (T := T) (d := d) sees σ χ H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ)
      (c : ∀ ℓ, hid ℓ → ℝ),
      ((θ.sumFst.cob G G).headsQK K).headsVO K' = θ.sumFst →
      (θ.sumSnd.cob G G).rescaleMlp k c = θ.sumSnd →
        G = 1 ∧ K = 1 ∧ K' = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionMlp (T := T) (d := d) sees σ χ H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3 G K K' c e1 e2
  exact cob_heads_rescaleMlp_eq_self_of_rank_E k θ G K K' c h1.1 h1.2 h2.1 h2.2
    h3 e1 e2

/-- **Lemma A.18, third sentence, at generic parameters: attention blocks with
gated blocks with the rescalings of the values**
(`d_in ≥ d ≥ 1`, `d_h ≤ d`, `H d_h + d_hidden ≥ d`). -/
theorem ae_cob_heads_rescale_eq_self_of_dIn [Nonempty d]
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ)
      (c : ∀ ℓ, hid ℓ → ℝ),
      ((θ.sumFst.cob G G).headsQK K).headsVO K' = θ.sumFst →
      (θ.sumSnd.cob G G).rescale c = θ.sumSnd →
        G = 1 ∧ K = 1 ∧ K' = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3 G K K' c e1 e2
  exact cob_heads_rescale_eq_self_of_rank_E θ G K K' c h1.1 h1.2 h2.1 h2.2
    (fun ℓ i => h3 ℓ (Sum.inr i)) e1 e2

/-- **Lemma A.18, third sentence, at generic parameters: attention blocks with
ReGLU blocks with the rescalings of values and gates**
(`d_in ≥ d ≥ 1`, `d_h ≤ d`, `H d_h + d_hidden ≥ d`). -/
theorem ae_cob_heads_rescale_rescaleGate_eq_self_of_dIn [Nonempty d] (k : ℕ)
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ)
      (c c' : ∀ ℓ, hid ℓ → ℝ),
      ((θ.sumFst.cob G G).headsQK K).headsVO K' = θ.sumFst →
      ((θ.sumSnd.cob G G).rescale c').rescaleGate k c = θ.sumSnd →
        G = 1 ∧ K = 1 ∧ K' = 1 ∧ (∀ ℓ i, c ℓ i = 1) ∧ ∀ ℓ i, c' ℓ i = 1 := by
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3 G K K' c c' e1 e2
  exact cob_heads_rescale_rescaleGate_eq_self_of_rank_E k θ G K K' c c' h1.1 h1.2 h2.1 h2.2
    (fun ℓ i => h3 ℓ (Sum.inr i))
    (fun ℓ i => h3 ℓ (Sum.inl i)) e1 e2

/-- **The same for `ε = 0`** (`G_ℓ = s_ℓ Q_ℓ`, `s_ℓ > 0`, `Q_ℓ` orthogonal)**: attention blocks
with MLP blocks with the rescalings of the hidden units.** -/
theorem ae_cob_rmsNorm_zero_heads_rescaleMlp_eq_self_of_dIn [Nonempty d] (k : ℕ)
    (μ : Measure (Params (Arch.attentionMlp (T := T) (d := d) sees σ χ H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G Q : Fin (L + 1) → GL d ℝ) (s : Fin (L + 1) → ℝ)
      (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
      (∀ ℓ, 0 < s ℓ) → (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) →
      (∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ)) →
      ((θ.sumFst.cob G Q).headsQK K).headsVO K' = θ.sumFst →
      (θ.sumSnd.cob G Q).rescaleMlp k c = θ.sumSnd →
        (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ K = 1 ∧ K' = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionMlp (T := T) (d := d) sees σ χ H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3 G Q s K K' c hs hQ hG e1 e2
  exact cob_rmsNorm_zero_heads_rescaleMlp_eq_self_of_rank_E k θ G Q s K K' c hs hQ hG
    h1.1 h1.2 h2.1 h2.2 h3 e1 e2

/-- **The same for `ε = 0`** (`G_ℓ = s_ℓ Q_ℓ`, `s_ℓ > 0`, `Q_ℓ` orthogonal)**: attention blocks
with gated blocks with the rescalings of the values.** -/
theorem ae_cob_rmsNorm_zero_heads_rescale_eq_self_of_dIn [Nonempty d]
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G Q : Fin (L + 1) → GL d ℝ) (s : Fin (L + 1) → ℝ)
      (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
      (∀ ℓ, 0 < s ℓ) → (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) →
      (∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ)) →
      ((θ.sumFst.cob G Q).headsQK K).headsVO K' = θ.sumFst →
      (θ.sumSnd.cob G Q).rescale c = θ.sumSnd →
        (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ K = 1 ∧ K' = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3 G Q s K K' c hs hQ hG e1 e2
  exact cob_rmsNorm_zero_heads_rescale_eq_self_of_rank_E θ G Q s K K' c hs hQ hG
    h1.1 h1.2 h2.1 h2.2 (fun ℓ i => h3 ℓ (Sum.inr i)) e1 e2

/-- **The same for `ε = 0`** (`G_ℓ = s_ℓ Q_ℓ`, `s_ℓ > 0`, `Q_ℓ` orthogonal)**: attention blocks
with ReGLU blocks with the rescalings of values and gates.** -/
theorem ae_cob_rmsNorm_zero_heads_rescale_rescaleGate_eq_self_of_dIn [Nonempty d] (k : ℕ)
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G Q : Fin (L + 1) → GL d ℝ) (s : Fin (L + 1) → ℝ)
      (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c c' : ∀ ℓ, hid ℓ → ℝ),
      (∀ ℓ, 0 < s ℓ) → (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) →
      (∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ)) →
      ((θ.sumFst.cob G Q).headsQK K).headsVO K' = θ.sumFst →
      ((θ.sumSnd.cob G Q).rescale c').rescaleGate k c = θ.sumSnd →
        (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ K = 1 ∧ K' = 1 ∧ (∀ ℓ i, c ℓ i = 1) ∧ ∀ ℓ i, c' ℓ i = 1 := by
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionGated (T := T) (d := d) sees σ χ H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3 G Q s K K' c c' hs hQ hG e1 e2
  exact cob_rmsNorm_zero_heads_rescale_rescaleGate_eq_self_of_rank_E k θ G Q s K K' c c' hs hQ hG
    h1.1 h1.2 h2.1 h2.2 (fun ℓ i => h3 ℓ (Sum.inr i))
    (fun ℓ i => h3 ℓ (Sum.inl i)) e1 e2

end Skips
