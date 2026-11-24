import SkipsLean.Residual.IdentifiableIff

/-!
# The equality condition and local identifiability: the symmetries are close to the identity,
residual networks of each kind of block

Paper (dimension paper), Proposition 4.6: "A network satisfies the equality condition if and only
if, at generic parameters, it is locally identifiable up to its symmetries. Every symmetry that is
needed is then close to the identity." (Skips paper, Proposition 4.5, has the same sentences.)

The library has the last sentence at one parameter, under the rank conditions of the proof (the
theorems `exists_…_of_eval_eq_…`). Here it is one statement under the equality condition, for
residual networks of each kind of block:
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
`exists_cob_heads_of_eval_eq_residual_attention`.
If the bound is attained at almost every `θ`, then at almost every `θ`, for all neighborhoods of
the identity, every `θ'` close enough to `θ` with the same function is the image of `θ` under
symmetries in these neighborhoods. -/
theorem ae_exists_cob_heads_of_eval_eq_residual_attention_of_ae_funDim
    (μ : Measure (Params
      (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hfd :
      ∀ᵐ θ ∂μ, funDim (Arch.attention sees id H dh) 1 θ
          + (Fintype.card d ^ 2
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ (Params
            (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut)) :
    ∀ᵐ θ ∂μ,
      ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
        ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees id H dh) 1 θ' x
          = eval (Arch.attention sees id H dh) 1 θ x) →
          ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
            (G : Matrix d d ℝ) ∈ V
              ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
              ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
              ∧ θ' = ((θ.headsQK K).headsVO K').cob (fun _ => G) (fun _ => G) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and 4.5 of the skips paper, last sentence, under the
equality condition:** the form at almost every parameter of
`exists_cob_of_eval_eq_residual`.
If the bound is attained at almost every `θ`, then at almost every `θ`, for all neighborhoods of
the identity, every `θ'` close enough to `θ` with the same function is the image of `θ` under
symmetries in these neighborhoods. -/
theorem ae_exists_cob_of_eval_eq_residual_of_ae_funDim
    (A : Arch T d L) (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params
      A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hfd :
      ∀ᵐ θ ∂μ, funDim A 1 θ
          + Fintype.card d ^ 2
        = Module.finrank ℝ (Params
            A dIn dOut)) :
    ∀ᵐ θ ∂μ,
      ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval A 1 θ' x = eval A 1 θ x) →
          ∃ G : GL d ℝ, (G : Matrix d d ℝ) ∈ V ∧ θ' = θ.cob (fun _ => G) (fun _ => G) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and 4.5 of the skips paper, last sentence, under the
equality condition:** the form at almost every parameter of
`exists_cob_of_eval_eq_residual_rmsNorm`.
If the bound is attained at almost every `θ`, then at almost every `θ`, for all neighborhoods of
the identity, every `θ'` close enough to `θ` with the same function is the image of `θ` under
symmetries in these neighborhoods. -/
theorem ae_exists_cob_of_eval_eq_residual_rmsNorm_of_ae_funDim
    (A : Arch T d L) (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params
      A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hfd :
      ∀ᵐ θ ∂μ, funDim A 1 θ
          + Fintype.card d * (Fintype.card d - 1) / 2
        = Module.finrank ℝ (Params
            A dIn dOut)) :
    ∀ᵐ θ ∂μ,
      ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval A 1 θ' x = eval A 1 θ x) →
          ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
            (Q : Matrix d d ℝ) ∈ V ∧ θ' = θ.cob (fun _ => Q) (fun _ => Q) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and 4.5 of the skips paper, last sentence, under the
equality condition:** the form at almost every parameter of
`exists_cob_rescale_of_eval_eq_residual_gated`.
If the bound is attained at almost every `θ`, then at almost every `θ`, for all neighborhoods of
the identity, every `θ'` close enough to `θ` with the same function is the image of `θ` under
symmetries in these neighborhoods. -/
theorem ae_exists_cob_rescale_of_eval_eq_residual_gated_of_ae_funDim
    [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.gated (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hfd :
      ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 1 θ
          + (Fintype.card d ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params
            (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) :
    ∀ᵐ θ ∂μ,
      ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ id hid) 1 θ' x
          = eval (Arch.gated σ id hid) 1 θ x) →
          ∃ (G : GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ), (G : Matrix d d ℝ) ∈ V ∧ c ∈ W ∧
            (∀ ℓ i, 0 < c ℓ i) ∧ θ' = (θ.rescale c).cob (fun _ => G) (fun _ => G) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and 4.5 of the skips paper, last sentence, under the
equality condition:** the form at almost every parameter of
`exists_cob_rescale_of_eval_eq_residual_gated_rmsNorm`.
If the bound is attained at almost every `θ`, then at almost every `θ`, for all neighborhoods of
the identity, every `θ'` close enough to `θ` with the same function is the image of `θ` under
symmetries in these neighborhoods. -/
theorem ae_exists_cob_rescale_of_eval_eq_residual_gated_rmsNorm_of_ae_funDim
    (hε : 0 < ε) [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hfd :
      ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
          + (Fintype.card d * (Fintype.card d - 1) / 2
            + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ (Params
            (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)) :
    ∀ᵐ θ ∂μ,
      ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval (Arch.gated σ (rmsNorm ε) hid) 1 θ' x
          = eval (Arch.gated σ (rmsNorm ε) hid) 1 θ x) →
          ∃ (Q : GL d ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
            (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V ∧ c ∈ W ∧
            (∀ ℓ i, 0 < c ℓ i) ∧ θ' = (θ.rescale c).cob (fun _ => Q) (fun _ => Q) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and 4.5 of the skips paper, last sentence, under the
equality condition:** the form at almost every parameter of
`exists_cob_heads_of_eval_eq_residual_attention_rmsNorm`.
If the bound is attained at almost every `θ`, then at almost every `θ`, for all neighborhoods of
the identity, every `θ'` close enough to `θ` with the same function is the image of `θ` under
symmetries in these neighborhoods. -/
theorem ae_exists_cob_heads_of_eval_eq_residual_attention_rmsNorm_of_ae_funDim
    (hε : 0 < ε)
    (μ : Measure (Params
      (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hfd :
      ∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
          + (Fintype.card d * (Fintype.card d - 1) / 2
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ (Params
            (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)) :
    ∀ᵐ θ ∂μ,
      ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
        ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval (Arch.attention sees (rmsNorm ε) H dh) 1 θ' x
          = eval (Arch.attention sees (rmsNorm ε) H dh) 1 θ x) →
          ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
            (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
              ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
              ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
              ∧ θ' = ((θ.headsQK K).headsVO K').cob (fun _ => Q) (fun _ => Q) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and 4.5 of the skips paper, last sentence, under the
equality condition:** the form at almost every parameter of
`exists_cob_heads_of_eval_eq_residual_attentionMlp`.
If the bound is attained at almost every `θ`, then at almost every `θ`, for all neighborhoods of
the identity, every `θ'` close enough to `θ` with the same function is the image of `θ` under
symmetries in these neighborhoods. -/
theorem ae_exists_cob_heads_of_eval_eq_residual_attentionMlp_of_ae_funDim
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hfd :
      ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ
          + (Fintype.card d ^ 2
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ (Params
            (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)) :
    ∀ᵐ θ ∂μ,
      ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
        ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ id H dh hid) 1 θ' x
          = eval (Arch.attentionMlp sees σ id H dh hid) 1 θ x) →
          ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
            (G : Matrix d d ℝ) ∈ V
              ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
              ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
              ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                  (fun _ => G) (fun _ => G) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and 4.5 of the skips paper, last sentence, under the
equality condition:** the form at almost every parameter of
`exists_cob_heads_of_eval_eq_residual_attentionMlp_rmsNorm`.
If the bound is attained at almost every `θ`, then at almost every `θ`, for all neighborhoods of
the identity, every `θ'` close enough to `θ` with the same function is the image of `θ` under
symmetries in these neighborhoods. -/
theorem ae_exists_cob_heads_of_eval_eq_residual_attentionMlp_rmsNorm_of_ae_funDim
    (hε : 0 < ε) (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hfd :
      ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ
          + (Fintype.card d * (Fintype.card d - 1) / 2
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ (Params
            (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) :
    ∀ᵐ θ ∂μ,
      ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
        ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ' x
          = eval (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ x) →
          ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ),
            (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
              ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
              ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
              ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') θ.sumSnd).cob
                  (fun _ => Q) (fun _ => Q) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and 4.5 of the skips paper, last sentence, under the
equality condition:** the form at almost every parameter of
`exists_cob_heads_of_eval_eq_residual_attentionGated`.
If the bound is attained at almost every `θ`, then at almost every `θ`, for all neighborhoods of
the identity, every `θ'` close enough to `θ` with the same function is the image of `θ` under
symmetries in these neighborhoods. -/
theorem ae_exists_cob_heads_of_eval_eq_residual_attentionGated_of_ae_funDim
    [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hfd :
      ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 1 θ
          + (Fintype.card d ^ 2
            + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
        = Module.finrank ℝ (Params
            (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)) :
    ∀ᵐ θ ∂μ,
      ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
        ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ id H dh hid) 1 θ' x
          = eval (Arch.attentionGated sees σ id H dh hid) 1 θ x) →
          ∃ (G : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
            (G : Matrix d d ℝ) ∈ V
              ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
              ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
              ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
              ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                  (fun _ => G) (fun _ => G) := by
  sorry

/-- **Proposition 4.6 of the dimension paper and 4.5 of the skips paper, last sentence, under the
equality condition:** the form at almost every parameter of
`exists_cob_heads_of_eval_eq_residual_attentionGated_rmsNorm`.
If the bound is attained at almost every `θ`, then at almost every `θ`, for all neighborhoods of
the identity, every `θ'` close enough to `θ` with the same function is the image of `θ` under
symmetries in these neighborhoods. -/
theorem ae_exists_cob_heads_of_eval_eq_residual_attentionGated_rmsNorm_of_ae_funDim
    (hε : 0 < ε) [Nonempty d] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hfd :
      ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
          + (Fintype.card d * (Fintype.card d - 1) / 2
            + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
              + ∑ ℓ, Fintype.card (hid ℓ)))
        = Module.finrank ℝ (Params
            (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)) :
    ∀ᵐ θ ∂μ,
      ∀ V ∈ 𝓝 (1 : Matrix d d ℝ), ∀ W ∈ 𝓝 (1 : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ),
        ∀ Wc ∈ 𝓝 (1 : ∀ ℓ, hid ℓ → ℝ), ∃ U ∈ 𝓝 θ, ∀ θ' ∈ U,
        (∀ x : Matrix T dIn ℝ, eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ' x
          = eval (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ x) →
          ∃ (Q : GL d ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (c : ∀ ℓ, hid ℓ → ℝ),
            (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧ (Q : Matrix d d ℝ) ∈ V
              ∧ (fun ℓ i => (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
              ∧ (fun ℓ i => (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ)) ∈ W
              ∧ c ∈ Wc ∧ (∀ ℓ i, 0 < c ℓ i)
              ∧ θ' = (Params.sumOf ((θ.sumFst.headsQK K).headsVO K') (θ.sumSnd.rescale c)).cob
                  (fun _ => Q) (fun _ => Q) := by
  sorry

end Skips
