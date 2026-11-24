import SkipsLean.Dimension.IdentifiableIff
import SkipsLean.Dimension.IdentifiableConverseFamily

/-!
# The equality condition is local identifiability, with permutations and sign flips: networks
    without skip connections

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

`Dimension/IdentifiableIff.lean` states the equivalence with the continuous symmetries only. Here
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
  [∀ ℓ, DecidableEq (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {ε : ℝ}

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of any real-analytic blocks, without normalization, with countably many further images of
`θ`:** `fd = P − (L + 1) d²` at almost every parameter if and only if at almost every parameter `θ`
every `θ'` near `θ` with the same function is, for some `j`, the image `img j θ` of `θ` after a
change of basis by invertible `G_0, …, G_L`. The maps `img j` are any countably many maps of the
parameters, one of them the identity; the permutations of hidden units or heads and the sign flips
of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_skipless_iff_ae_locally_cob_family
    (A : Arch T d L) (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params
      A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params A dIn dOut →
      Params A dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim A 0 θ
        + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params
          A dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 0 θ' x
        = eval A 0 θ x) →
        ∃ j : ι, ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (img j θ).cob G G) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of any real-analytic blocks, under pre-RMSNorm with `ε > 0`, with countably many further
images of `θ`:** `fd = P − (L + 1) d(d−1)/2` at almost every parameter if and only if at almost
every parameter `θ` every `θ'` near `θ` with the same function is, for some `j`, the image `img j θ`
of `θ` after a change of basis by orthogonal `Q_0, …, Q_L`. The maps `img j` are any countably many
maps of the parameters, one of them the identity; the permutations of hidden units or heads and the
sign flips of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_skipless_iff_ae_locally_cob_rmsNorm_family
    (A : Arch T d L) (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params
      A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params A dIn dOut →
      Params A dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim A 0 θ
        + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params
          A dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval A 0 θ' x
        = eval A 0 θ x) →
        ∃ j : ι, ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (img j θ).cob Q Q) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of MLP blocks with a real-analytic activation (tanh, GELU), without normalization, with
countably many further images of `θ`:** `fd = P − (L + 1) d²` at almost every parameter if and only
if at almost every parameter `θ` every `θ'` near `θ` with the same function is, for some `j`, the
image `img j θ` of `θ` after a change of basis by invertible `G_0, …, G_L`. The maps `img j` are any
countably many maps of the parameters, one of them the identity; the permutations of hidden units or
heads and the sign flips of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_mlp_skipless_iff_ae_locally_cob_family
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut →
      Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 0 θ
        + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params
          (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp σ id hid) 0 θ' x
        = eval (Arch.mlp σ id hid) 0 θ x) →
        ∃ j : ι, ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (img j θ).cob G G) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of MLP blocks with a real-analytic activation (tanh, GELU), under pre-RMSNorm with `ε > 0`,
with countably many further images of `θ`:** `fd = P − (L + 1) d(d−1)/2` at almost every parameter
if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function is, for some
`j`, the image `img j θ` of `θ` after a change of basis by orthogonal `Q_0, …, Q_L`. The maps `img
j` are any countably many maps of the parameters, one of them the identity; the permutations of
hidden units or heads and the sign flips of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_mlp_skipless_iff_ae_locally_cob_rmsNorm_family
    (hε : 0 < ε) (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut →
      Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm ε) hid) 0 θ
        + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params
          (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.mlp σ (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.mlp σ (rmsNorm ε) hid) 0 θ x) →
        ∃ j : ι, ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (img j θ).cob Q Q) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of gated blocks with a real-analytic gate (SwiGLU, GeGLU), without normalization, with
countably many further images of `θ`:** `fd = P − (L + 1) d² − s` at almost every parameter (`s = ∑
d_hidden`) if and only if at almost every parameter `θ` every `θ'` near `θ` with the same function
is, for some `j`, the image `img j θ` of `θ` after a rescaling of the values of the hidden units by
nonzero factors `c` and a change of basis by invertible `G_0, …, G_L`. The maps `img j` are any
countably many maps of the parameters, one of them the identity; the permutations of hidden units or
heads and the sign flips of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_gated_skipless_iff_ae_locally_cob_rescale_family
    [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut →
      Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params
          (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ id hid) 0 θ' x
        = eval (Arch.gated σ id hid) 0 θ x) →
        ∃ j : ι, ∃ c : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = ((img j θ).rescale c).cob G G) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of gated blocks with a real-analytic gate (SwiGLU, GeGLU), under pre-RMSNorm with `ε > 0`,
with countably many further images of `θ`:** `fd = P − (L + 1) d(d−1)/2 − s` at almost every
parameter (`s = ∑ d_hidden`) if and only if at almost every parameter `θ` every `θ'` near `θ` with
the same function is, for some `j`, the image `img j θ` of `θ` after a rescaling of the values of
the hidden units by nonzero factors `c` and a change of basis by orthogonal `Q_0, …, Q_L`. The maps
`img j` are any countably many maps of the parameters, one of them the identity; the permutations of
hidden units or heads and the sign flips of tanh units, composed, are finitely many such maps. -/
theorem ae_funDim_gated_skipless_iff_ae_locally_cob_rescale_rmsNorm_family
    (hε : 0 < ε) [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut →
      Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params
          (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ (rmsNorm ε) hid) 0 θ' x
        = eval (Arch.gated σ (rmsNorm ε) hid) 0 θ x) →
        ∃ j : ι, ∃ c : ∀ ℓ, hid ℓ → ℝ, (∀ ℓ i, c ℓ i ≠ 0) ∧
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = ((img j θ).rescale c).cob Q Q) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of attention blocks, without normalization, with countably many further images of `θ`:**
`fd = P − (L + 1) d² − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only if at almost
every parameter `θ` every `θ'` near `θ` with the same function is, for some `j`, the image `img j θ`
of `θ` after changes of basis inside the heads and a change of basis by invertible `G_0, …, G_L`.
The maps `img j` are any countably many maps of the parameters, one of them the identity; the
permutations of hidden units or heads and the sign flips of tanh units, composed, are finitely many
such maps. -/
theorem ae_funDim_attention_skipless_iff_ae_locally_cob_heads_family
    (μ : Measure (Params
      (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut →
      Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) 0 θ' x
        = eval (Arch.attention sees id H dh) 0 θ x) →
        ∃ j : ι, ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ G : Fin (L + 1) → GL d ℝ,
            θ' = (((img j θ).headsQK K).headsVO K').cob G G) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and Proposition 4.5 of the skips paper, for skipless
networks of attention blocks, under pre-RMSNorm with `ε > 0`, with countably many further images of
`θ`:** `fd = P − (L + 1) d(d−1)/2 − s` at almost every parameter (`s = 2 ∑ H d_h²`) if and only if
at almost every parameter `θ` every `θ'` near `θ` with the same function is, for some `j`, the image
`img j θ` of `θ` after changes of basis inside the heads and a change of basis by orthogonal `Q_0,
…, Q_L`. The maps `img j` are any countably many maps of the parameters, one of them the identity;
the permutations of hidden units or heads and the sign flips of tanh units, composed, are finitely
many such maps. -/
theorem ae_funDim_attention_skipless_iff_ae_locally_cob_heads_rmsNorm_family
    (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ))
    {ι : Type*} [Countable ι]
    (img : ι → Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut →
      Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (j₀ : ι) (himg : ∀ θ, img j₀ θ = θ) :
    (∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params
          (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)) ↔
    (∀ᵐ θ ∂μ, ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
      (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees (rmsNorm ε) H dh) 0 θ' x
        = eval (Arch.attention sees (rmsNorm ε) H dh) 0 θ x) →
        ∃ j : ι, ∃ K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ,
          ∃ Q : Fin (L + 1) → GL d ℝ,
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            θ' = (((img j θ).headsQK K).headsVO K').cob Q Q) := by
  sorry

end Skips
