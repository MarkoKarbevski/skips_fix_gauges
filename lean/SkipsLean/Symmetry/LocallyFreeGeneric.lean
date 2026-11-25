import SkipsLean.Symmetry.LocallyFreeEmbedding
import SkipsLean.Symmetry.LocallyFreeAttention
import SkipsLean.Generic.Gated
import SkipsLean.Dimension.UpperBoundAttention

/-!
# Locally free action at generic parameters (the form with the embedding)

Papers: Lemma B.1 of the dimension paper, "If `d_in ≥ d_model`, then at generic parameters the
changes of basis and the symmetries inside the blocks act locally freely", for blocks "with at
least `d_model` hidden units, or attention blocks whose heads have width `d_h ≤ d_model` and
total width `H d_h ≥ d_model`"; Lemma A.18 of the skips paper, first and third sentence ("If the
embedding has rank `d_model` and every block has width at least `d_model`, then at generic
parameters the changes of basis and the symmetries inside blocks act locally freely"; "With an
embedding of rank `d_model`, it also holds for networks with attention blocks […]").

`Symmetry/LocallyFreeEmbedding.lean` and `Symmetry/LocallyFreeAttention.lean` state, at one
parameter with rank conditions, that changes of basis and symmetries inside the blocks that fix
`θ` are the identity. Here the same **at almost every `θ`**, for `d_in ≥ d` and the widths of the
lemma: the rank conditions hold at generic parameters (`ae_rank_E_write`, `ae_read_col_ne_zero`,
`ae_value_ne_zero`, `ae_gate_ne_zero`, `ae_rank_QV_uba`). The statements with rescalings ask
`d ≥ 1`. Each proof is the statement at one parameter at a generic one.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- **Lemma B.1 / A.18 at generic parameters, the changes of basis** (any kind of block whose
write has at least `d` rows; `d_in ≥ d`): at almost every `θ`, changes of basis that fix `θ`
(`θ.cob G K = θ`) have `G = 1`. -/
theorem ae_cob_eq_self_of_dIn {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) :
    ∀ᵐ θ ∂μ, ∀ G K : Fin (L + 1) → GL d ℝ, θ.cob G K = θ → G = 1 := by
  filter_upwards [ae_rank_E_write μ hdIn hw] with θ hθ G K h
  exact cob_eq_self_of_rank_E θ G K hθ.1 hθ.2 h

/-- **Lemma B.1 / A.18 at generic parameters, ReLU and ReLU² blocks** (any activation and any
degree `k`; `d_in ≥ d ≥ 1`, at least `d` hidden units): at almost every `θ`, changes of basis `G`
with rescalings `c` of the hidden units that fix `θ` are the identity. -/
theorem ae_cob_rescaleMlp_eq_self_of_dIn [Nonempty d] (k : ℕ)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
      (θ.cob G G).rescaleMlp k c = θ → G = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_read_col_ne_zero μ] with θ hθ hcol G c h
  exact cob_rescaleMlp_eq_self_of_rank_E k θ G c hθ.1 hθ.2 hcol h

/-- **Lemma B.1 / A.18 at generic parameters, gated blocks with any gate** (`d_in ≥ d ≥ 1`, at
least `d` hidden units): at almost every `θ`, changes of basis `G` with rescalings `c` of the
values that fix `θ` are the identity. -/
theorem ae_cob_rescale_eq_self_of_dIn [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
      (θ.cob G G).rescale c = θ → G = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_value_ne_zero μ] with θ hθ hv G c h
  exact cob_rescale_eq_self_of_rank_E θ G c hθ.1 hθ.2 hv h

/-- **Lemma B.1 / A.18 at generic parameters, ReGLU blocks** (any gate and any degree `k`;
`d_in ≥ d ≥ 1`, at least `d` hidden units): at almost every `θ`, changes of basis `G` with
rescalings `c'` of the values and `c` of the gates that fix `θ` are the identity. -/
theorem ae_cob_rescale_rescaleGate_eq_self_of_dIn [Nonempty d] (k : ℕ)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G : Fin (L + 1) → GL d ℝ) (c c' : ∀ ℓ, hid ℓ → ℝ),
      ((θ.cob G G).rescale c').rescaleGate k c = θ →
        G = 1 ∧ (∀ ℓ i, c ℓ i = 1) ∧ ∀ ℓ i, c' ℓ i = 1 := by
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_value_ne_zero μ, ae_gate_ne_zero μ]
    with θ hθ hv hg G c c' h
  exact cob_rescale_rescaleGate_eq_self_of_rank_E k θ G c c' hθ.1 hθ.2 hv hg h

/-- **Lemma B.1 / A.18 at generic parameters, under pre-RMSNorm with `ε = 0`** (any kind of block
whose write has at least `d` rows; `d_in ≥ d ≥ 1`): at almost every `θ`, changes of basis
`G_ℓ = c_ℓ Q_ℓ` (`c_ℓ > 0`, `Q_ℓ` orthogonal; the writes multiplied by `G_ℓ`, the reads by
`Q_ℓ⁻¹`) that fix `θ` have `c_ℓ = 1` and `Q_ℓ = 1`. -/
theorem ae_cob_rmsNorm_zero_eq_self_of_dIn [Nonempty d] {A : Arch T d L}
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G Q : Fin (L + 1) → GL d ℝ) (c : Fin (L + 1) → ℝ), (∀ ℓ, 0 < c ℓ) →
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) →
      (∀ ℓ, (G ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ)) → θ.cob G Q = θ →
        (∀ ℓ, c ℓ = 1) ∧ Q = 1 := by
  filter_upwards [ae_rank_E_write μ hdIn hw] with θ hθ G Q c hc hQ hG h
  exact cob_rmsNorm_zero_eq_self_of_rank_E θ G Q c hc hQ hG hθ.1 hθ.2 h

variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-- **Lemma B.1 / A.18 at generic parameters, attention blocks** (`d_in ≥ d`, heads of width
`d_h ≤ d` and total width `H d_h ≥ d`): at almost every `θ`, changes of basis `G` of the hidden
states with changes of basis `K`, `K'` inside the heads that fix `θ` are the identity. -/
theorem ae_cob_headsQK_headsVO_eq_self_of_dIn
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, ∀ (G : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
      ((θ.cob G G).headsQK K).headsVO K' = θ → G = 1 ∧ K = 1 ∧ K' = 1 := by
  -- the writes have `H_ℓ d_{h,ℓ} ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d
      ≤ Fintype.card ((Arch.attention (T := T) (d := d) sees χ H dh).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card (H ℓ × dh ℓ)
    rw [Fintype.card_prod]
    exact hH ℓ
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_uba μ hdh] with θ h1 h2 G K K' h
  exact cob_headsQK_headsVO_eq_self_of_rank_E θ G K K' h1.1 h1.2 h2.1 h2.2 h

end Skips
