import SkipsLean.Dimension.IdentifiableIff

/-!
# The equality condition and local identifiability: the symmetries are close to the identity,
skipless networks of gated blocks and of attention blocks

Paper (dimension paper), Proposition 4.6: "A network satisfies the equality condition if and only
if, at generic parameters, it is locally identifiable up to its symmetries. Every symmetry that is
needed is then close to the identity." (Skips paper, Proposition 4.5, has the same sentences.)

The library has the last sentence at one parameter, under the rank conditions of the proof (the
theorems `exists_…_of_eval_eq_…`). Here it is one statement under the equality condition, for
skipless networks of gated blocks and of attention blocks:
if the bound on the functional dimension is attained at almost every parameter (the left side of
the equivalences of `IdentifiableIff.lean`), then at almost every parameter `θ`, for all
neighborhoods of the identity, every `θ'` close enough to `θ` with the same function is the image
of `θ` under symmetries in these neighborhoods. The twin for skipless networks of blocks with no
symmetry inside is `Dimension/LocalIdentifiabilityUnderEquality.lean`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)] [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {ε : ℝ}

/-- **Proposition 4.6 of the dimension paper and 4.5 of the skips paper, last sentence, under the
equality condition:** the form at almost every parameter of
`exists_cob_rescale_of_eval_eq_skipless_gated`.
If the bound is attained at almost every `θ`, then at almost every `θ`, for all neighborhoods of
the identity, every `θ'` close enough to `θ` with the same function is the image of `θ` under
symmetries in these neighborhoods. -/
theorem ae_exists_cob_rescale_of_eval_eq_skipless_gated_of_ae_funDim
    [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ))
    (hfd :
      ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 0 θ
          + ((L + 1) * Fintype.card d ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params
            (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) :
    ∀ᵐ θ ∂μ,
      ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ,
        ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ id hid) 0 θ' x
          = eval (Arch.gated σ id hid) 0 θ x) →
          ∃ (G : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
            (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V ∧ c ∈ W ∧ (∀ ℓ i, 0 < c ℓ i) ∧
            θ' = (θ.rescale c).cob G G := by
  sorry

/-- **Proposition 4.6 of the dimension paper and 4.5 of the skips paper, last sentence, under the
equality condition:** the form at almost every parameter of
`exists_cob_rescale_of_eval_eq_skipless_gated_rmsNorm`.
If the bound is attained at almost every `θ`, then at almost every `θ`, for all neighborhoods of
the identity, every `θ'` close enough to `θ` with the same function is the image of `θ` under
symmetries in these neighborhoods. -/
theorem ae_exists_cob_rescale_of_eval_eq_skipless_gated_rmsNorm_of_ae_funDim
    (hε : 0 < ε) [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ))
    (hfd :
      ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 0 θ
          + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
            + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params
            (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) :
    ∀ᵐ θ ∂μ,
      ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ,
        ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ (rmsNorm ε) hid) 0 θ' x
          = eval (Arch.gated σ (rmsNorm ε) hid) 0 θ x) →
          ∃ (Q : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
            (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V ∧ c ∈ W ∧ (∀ ℓ i, 0 < c ℓ i) ∧
            θ' = (θ.rescale c).cob Q Q := by
  sorry

/-- **Proposition 4.6 of the dimension paper and 4.5 of the skips paper, last sentence, under the
equality condition:** the form at almost every parameter of
`exists_cob_heads_of_eval_eq_skipless_attention`.
If the bound is attained at almost every `θ`, then at almost every `θ`, for all neighborhoods of
the identity, every `θ'` close enough to `θ` with the same function is the image of `θ` under
symmetries in these neighborhoods. -/
theorem ae_exists_cob_heads_of_eval_eq_skipless_attention_of_ae_funDim
    (μ : Measure (Params
      (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ))
    (hfd :
      ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 0 θ
          + ((L + 1) * Fintype.card d ^ 2
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ (Params
            (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)) :
    ∀ᵐ θ ∂μ,
      ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ),
        ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) 0 θ' x
          = eval (Arch.attention sees id H dh) 0 θ x) →
          ∃ (G : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
            (fun ℓ => (G ℓ : Matrix d d ℝ)) ∈ V
              ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
              ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
              ∧ θ' = ((θ.headsQK K).headsVO K').cob G G := by
  sorry

/-- **Proposition 4.6 of the dimension paper and 4.5 of the skips paper, last sentence, under the
equality condition:** the form at almost every parameter of
`exists_cob_heads_of_eval_eq_skipless_attention_rmsNorm`.
If the bound is attained at almost every `θ`, then at almost every `θ`, for all neighborhoods of
the identity, every `θ'` close enough to `θ` with the same function is the image of `θ` under
symmetries in these neighborhoods. -/
theorem ae_exists_cob_heads_of_eval_eq_skipless_attention_rmsNorm_of_ae_funDim
    (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ))
    (hfd :
      ∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
          + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ (Params
            (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)) :
    ∀ᵐ θ ∂μ,
      ∀ V ∈ 𝓝 (1 : Fin (L + 1) → Matrix d d ℝ),
        ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees (rmsNorm ε) H dh) 0 θ' x
          = eval (Arch.attention sees (rmsNorm ε) H dh) 0 θ x) →
          ∃ (Q : Fin (L + 1) → GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
            (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
              ∧ (fun ℓ => (Q ℓ : Matrix d d ℝ)) ∈ V
              ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
              ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
              ∧ θ' = ((θ.headsQK K).headsVO K').cob Q Q := by
  sorry

end Skips
