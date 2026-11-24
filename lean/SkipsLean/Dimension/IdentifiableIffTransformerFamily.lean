import SkipsLean.Dimension.IdentifiableIffTransformer
import SkipsLean.Dimension.IdentifiableConverseFamily

/-!
# The equality condition is local identifiability, with permutations and sign flips: skipless
    networks of attention blocks and MLP or gated blocks

Paper (dimension paper, Proposition 4.6; skips paper, Proposition 4.5): "A network satisfies the
equality condition if and only if, at generic parameters, it is locally identifiable up to its
symmetries." Definition 4.5 of the dimension paper (4.4 of the skips paper): "A network is
identifiable up to its symmetries at `θ` if every `θ′` with `F_{θ′} = F_θ` is the image of `θ`
under a symmetry: a change of basis […], a symmetry inside a block, or a composition of these."
The symmetries inside the blocks (dimension paper, Appendix B): "Permutations of hidden units or
heads and sign flips of tanh hidden units are finite and remove no parameters", beside the
continuous ones (rescalings, changes of basis inside the heads). The proof of the converse counts
them: "With the permutations and the sign flips, the symmetries form a Lie group of dimension `k`
with finitely many components".

`Dimension/IdentifiableIffTransformer.lean` states the equivalence with the continuous symmetries
    only. Here
the same statements with countably many further images `img j θ` of `θ`, one of which is `θ`
itself: every `θ'` near `θ` with the same function is, for some `j`, the image of `img j θ` under
the continuous symmetries. With `img j` running over the compositions of the permutations of
hidden units or heads and the sign flips of tanh units (finitely many linear maps of the
parameters, which normalize the continuous symmetries inside the blocks and commute with the
changes of basis) the right side is local identifiability up to all the symmetries of the papers.
The statements hold for any countably many maps `img j` of the parameters: they need not be
symmetries, linear or continuous.

The direction from the equality condition to local identifiability is the earlier statement (the
identity is among the `img j`); the other direction is
`Dimension/IdentifiableConverseFamily.lean` with the upper bounds of Theorem 4.3 (dimension
paper) and Theorem 4.2 (skips paper).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ} {ε : ℝ}

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, without normalization, with countably many further
images of `θ`:** `fd = P − (L + 1) d² − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only
if at almost every parameter `θ` every `θ'` near `θ` with the same function is, for some `j`, the
image `img j θ` of `θ` after changes of basis inside the heads and a change of basis by invertible
`G_0, …, G_L`. The maps `img j` are any countably many maps of the parameters, one of them the
identity; the permutations of hidden units or heads and the sign flips of tanh units, composed, are
finitely many such maps. -/
theorem ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads_family
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut →
      Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ id H dh hid) 0 θ' x
        = eval (Arch.attentionMlp sees σ id H dh hid) 0 θ x) →
        ∃ j : ι, ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (Params.sumOf (((img j θ).sumFst.headsQK K).headsVO K') (img j θ).sumSnd).cob G
                G) := by
  sorry

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and MLP blocks
with a real-analytic activation, in any order, under pre-RMSNorm with `ε > 0`, with countably many
further images of `θ`:** `fd = P − (L + 1) d(d−1)/2 − s` at almost every parameter (`s = 2 ∑ H
d_h²`) if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function is,
for some `j`, the image `img j θ` of `θ` after changes of basis inside the heads and a change of
basis by orthogonal `Q_0, …, Q_L`. The maps `img j` are any countably many maps of the parameters,
one of them the identity; the permutations of hidden units or heads and the sign flips of tanh
units, composed, are finitely many such maps. -/
theorem ae_funDim_attentionMlp_skipless_iff_ae_locally_cob_heads_rmsNorm_family
    (hε : 0 < ε) (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut →
      Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ' x
        = eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ x) →
        ∃ j : ι, ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (Params.sumOf (((img j θ).sumFst.headsQK K).headsVO K') (img j θ).sumSnd).cob Q
                Q) := by
  sorry

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and gated blocks
with a real-analytic gate, in any order, without normalization, with countably many further images
of `θ`:** `fd = P − (L + 1) d² − s` at almost every parameter (`s = 2 ∑ H d_h² + ∑ d_hidden`) if and
only if at almost every parameter `θ` every `θ'` near `θ` with the same function is, for some `j`,
the image `img j θ` of `θ` after changes of basis inside the heads, a rescaling of the values of the
hidden units by nonzero factors `c` and a change of basis by invertible `G_0, …, G_L`. The maps `img
j` are any countably many maps of the parameters, one of them the identity; the permutations of
hidden units or heads and the sign flips of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_attentionGated_skipless_iff_ae_locally_cob_heads_rescale_family
    [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut →
      Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ id H dh hid) 0 θ' x
        = eval (Arch.attentionGated sees σ id H dh hid) 0 θ x) →
        ∃ j : ι, ∃ (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (Params.sumOf (((img j θ).sumFst.headsQK K).headsVO K') ((img j θ).sumSnd.rescale
                c)).cob G G) := by
  sorry

/-- **Proposition 4.5 of the skips paper, for skipless networks of attention blocks and gated blocks
with a real-analytic gate, in any order, under pre-RMSNorm with `ε > 0`, with countably many further
images of `θ`:** `fd = P − (L + 1) d(d−1)/2 − s` at almost every parameter (`s = 2 ∑ H d_h² + ∑
d_hidden`) if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function
is, for some `j`, the image `img j θ` of `θ` after changes of basis inside the heads, a rescaling of
the values of the hidden units by nonzero factors `c` and a change of basis by orthogonal `Q_0, …,
Q_L`. The maps `img j` are any countably many maps of the parameters, one of them the identity; the
permutations of hidden units or heads and the sign flips of tanh units, composed, are finitely many
such maps. -/
theorem ae_funDim_attentionGated_skipless_iff_ae_locally_cob_heads_rescale_rmsNorm_family
    (hε : 0 < ε) [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut →
      Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      = Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ' x
        = eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ x) →
        ∃ j : ι, ∃ (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (Params.sumOf (((img j θ).sumFst.headsQK K).headsVO K') ((img j θ).sumSnd.rescale
                c)).cob Q Q) := by
  sorry

end Skips
