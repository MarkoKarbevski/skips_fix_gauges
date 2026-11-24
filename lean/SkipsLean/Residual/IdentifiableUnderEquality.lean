import SkipsLean.Residual.IdentifiableIff

/-!
# The equality condition and local identifiability: the symmetries are close to the identity,
residual networks of each kind of block

Paper (skips paper), Proposition 4.5: "A network satisfies the equality condition if and only
if, at generic parameters, it is locally identifiable up to its symmetries. Every symmetry that is
needed is then close to the identity." (The dimension paper, Proposition 4.6, has the same
sentences for skipless networks of one kind of block.)

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

/-! ### Helpers: generic parameters (copies of private lemmas of `Residual/IdentifiableIff.lean`) -/

/-- Helper (the private `ae_rank_E_lia` of `Dimension/LocalIdentifiabilityAttention.lean`): at
generic parameters `E` has rank `d`, when `d_in ≥ d`. -/
private theorem ae_rank_E_iu2 {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d := by
  -- `d` rows `ρ` of `E`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  have h1 : (θ.E.submatrix ρ id).rank = Fintype.card d :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (hθ.2.2.1 ρ))
  have h2 := Matrix.rank_submatrix_le θ.E ρ id
  have h3 := Matrix.rank_le_card_width θ.E
  omega

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `analyticOnNhd_det_lia`): the determinant of a square matrix that depends
linearly on the parameters is an analytic function of the parameters. -/
private theorem analyticOnNhd_det_iu2 {A : Arch T d L} {n : Type*} [Fintype n] [DecidableEq n]
    (Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ) :
    AnalyticOnNhd ℝ (fun θ => (Φ θ).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ =>
      analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ (σ i) i).comp Φ))

/-- Helper (the private `exists_submatrix_eq_one_lia`): a matrix whose submatrix on the rows `r`
and the columns `c` (both injective) is the identity. -/
private theorem exists_submatrix_eq_one_iu2 {m p n : Type*} [DecidableEq n] {r : n → m}
    (hr : Function.Injective r) {c : n → p} (hc : Function.Injective c) :
    ∃ M : Matrix m p ℝ, M.submatrix r c = 1 := by
  classical
  refine ⟨Matrix.of fun a b => if ∃ x, r x = a ∧ c x = b then 1 else 0, ?_⟩
  ext x y
  simp [Matrix.one_apply, hr.eq_iff, hc.eq_iff]

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `ae_rank_read_cols_lia`): at generic parameters, `n ≤ d` distinct
columns `c` of the read of block `ℓ` form a matrix of rank `n`. -/
private theorem ae_rank_read_cols_iu2 {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*} [Fintype n] [DecidableEq n] {c : n → A.r ℓ}
    (hc : Function.Injective c) (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.read ℓ).submatrix id c).rank = Fintype.card n := by
  -- `n` rows `ρ`, and the square submatrix of the read on the rows `ρ` and the columns `c`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_iu2 ρ.injective hc
  let Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ :=
    { toFun := fun θ => ((θ.read ℓ).submatrix id c).submatrix ρ id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- it is the identity at the parameter whose read `ℓ` is `M`, so its determinant is not
  -- identically zero, and it is nonzero almost everywhere
  have hne : ∃ θ, (Φ θ).det ≠ 0 := by
    refine ⟨⟨0, Pi.single ℓ M, 0, 0⟩, ?_⟩
    show ((Pi.single (M := fun ℓ => Matrix d (A.r ℓ) ℝ) ℓ M ℓ).submatrix ρ c).det ≠ 0
    rw [Pi.single_eq_same, hM, Matrix.det_one]
    exact one_ne_zero
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_iu2 Φ) hne] with θ hθ
  -- an invertible `n × n` submatrix gives rank `≥ n`, and the rank is at most the width `n`
  have h1 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank = Fintype.card n :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hθ))
  have h2 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank
      ≤ ((θ.read ℓ).submatrix id c).rank :=
    Matrix.rank_submatrix_le _ ρ id
  have h3 := Matrix.rank_le_card_width ((θ.read ℓ).submatrix id c)
  omega

omit [DecidableEq d] in
/-- Helper (the private `ae_rank_QV_lia`): at generic parameters the query matrix and the value
matrix of every head have rank `d_h`, when `d_h ≤ d`. -/
private theorem ae_rank_QV_iu2 {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, (∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ)) ∧
      ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ) := by
  -- finitely many conditions, two for each head of each block
  refine (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_).and
    (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_)
  · exact ae_rank_read_cols_iu2 μ ℓ (c := fun k : dh ℓ => (i, Sum.inl k))
      (fun _ _ h => Sum.inl_injective (Prod.mk.inj h).2) (hdh ℓ)
  · exact ae_rank_read_cols_iu2 μ ℓ (c := fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
      (fun _ _ h => Sum.inr_injective (Sum.inr_injective (Prod.mk.inj h).2)) (hdh ℓ)

/-- **Proposition 4.5 of the skips paper, last sentence, under the
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
  -- at almost every `θ`, `E` has rank `d`, the query and value matrices of every head have rank
  -- `d_h`, and the bound is attained
  filter_upwards [ae_rank_E_iu2 μ hdIn, ae_rank_QV_iu2 μ hdh, hfd] with θ hE hQV hθfd
  exact exists_cob_heads_of_eval_eq_residual_attention θ hE hQV.1 hQV.2 hθfd

/-- **Proposition 4.5 of the skips paper, last sentence, under the
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
  -- at almost every `θ`, `E` has rank `d` and the bound is attained
  filter_upwards [ae_rank_E_iu2 μ hdIn, hfd] with θ hE hθfd
  exact exists_cob_of_eval_eq_residual A hA hf θ hE hθfd

/-- **Proposition 4.5 of the skips paper, last sentence, under the
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
  -- at almost every `θ`, `E` has rank `d` and the bound is attained
  filter_upwards [ae_rank_E_iu2 μ hdIn, hfd] with θ hE hθfd
  exact exists_cob_of_eval_eq_residual_rmsNorm A hε hA hf θ hE hθfd

/-- **Proposition 4.5 of the skips paper, last sentence, under the
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
  -- at almost every `θ`, `E` has rank `d`, no value column vanishes, and the bound is attained
  filter_upwards [ae_rank_E_iu2 μ hdIn, ae_value_ne_zero μ, hfd] with θ hE hv hθfd
  exact exists_cob_rescale_of_eval_eq_residual_gated hσ θ hE hv hθfd

/-- **Proposition 4.5 of the skips paper, last sentence, under the
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
  -- at almost every `θ`, `E` has rank `d`, no value column vanishes, and the bound is attained
  filter_upwards [ae_rank_E_iu2 μ hdIn, ae_value_ne_zero μ, hfd] with θ hE hv hθfd
  exact exists_cob_rescale_of_eval_eq_residual_gated_rmsNorm hε hσ θ hE hv hθfd

/-- **Proposition 4.5 of the skips paper, last sentence, under the
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
  -- at almost every `θ`, `E` has rank `d`, the query and value matrices of every head have rank
  -- `d_h`, and the bound is attained
  filter_upwards [ae_rank_E_iu2 μ hdIn, ae_rank_QV_iu2 μ hdh, hfd] with θ hE hQV hθfd
  exact exists_cob_heads_of_eval_eq_residual_attention_rmsNorm hε θ hE hQV.1 hQV.2 hθfd

omit [DecidableEq d] in
/-- Helper (the private `ae_rank_QV_lit`, for the first part of a sum): at generic parameters
the query matrix and the value matrix of every head have rank `d_h`, when `d_h ≤ d`. -/
private theorem ae_rank_QV_sum_iu2 {B : Arch T d L} {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees χ H dh).sum B) dIn dOut))
    [μ.IsAddHaarMeasure] (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, (∀ ℓ (i : H ℓ),
        ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
          = Fintype.card (dh ℓ)) ∧
      ∀ ℓ (i : H ℓ),
        ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
          = Fintype.card (dh ℓ) := by
  classical
  -- finitely many conditions, two for each head of each block; the read of the first part is
  -- made of columns of the read of the sum
  refine (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_).and
    (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_)
  · exact ae_rank_read_cols_iu2 μ ℓ (c := fun k : dh ℓ => Sum.inl (i, Sum.inl k))
      (fun _ _ h => Sum.inl_injective (Prod.mk.inj (Sum.inl_injective h)).2) (hdh ℓ)
  · exact ae_rank_read_cols_iu2 μ ℓ (c := fun k : dh ℓ => Sum.inl (i, Sum.inr (Sum.inr k)))
      (fun _ _ h => Sum.inr_injective (Sum.inr_injective (Prod.mk.inj (Sum.inl_injective h)).2))
      (hdh ℓ)

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `ae_value_ne_zero_lit`, for the second part of a sum): at generic
parameters no value column of the gated part of a read vanishes. -/
private theorem ae_value_ne_zero_sum_iu2 [Nonempty d] {A : Arch T d L}
    {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params (A.sum (Arch.gated (T := T) (d := d) σ χ hid)) dIn dOut))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0 := by
  -- finitely many conditions, one for each hidden unit `i` of each block `ℓ`
  refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_
  -- an entry `k₀` of the value column
  obtain k₀ : d := Classical.arbitrary d
  -- the entry `θ ↦ θ.read ℓ k₀ (inr (inr i))` is a linear functional of the parameters
  let l : Params (A.sum (Arch.gated (T := T) (d := d) σ χ hid)) dIn dOut →ₗ[ℝ] ℝ :=
    (Matrix.entryLinearMap ℝ ℝ k₀ (Sum.inr (Sum.inr i))).comp
      (Params.linRead (A := A.sum (Arch.gated (T := T) (d := d) σ χ hid)) (dIn := dIn)
        (dOut := dOut) ℓ)
  have hl : ∀ θ, l θ = θ.read ℓ k₀ (Sum.inr (Sum.inr i)) := fun θ => rfl
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

/-- **Proposition 4.5 of the skips paper, last sentence, under the
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
  -- at almost every `θ`, `E` has rank `d`, the query and value matrices of every head have rank
  -- `d_h`, and the bound is attained
  filter_upwards [ae_rank_E_iu2 μ hdIn, ae_rank_QV_sum_iu2 μ hdh, hfd] with θ hE hQV hθfd
  exact exists_cob_heads_of_eval_eq_residual_attentionMlp hσ θ hE hQV.1 hQV.2 hθfd

/-- **Proposition 4.5 of the skips paper, last sentence, under the
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
  -- at almost every `θ`, `E` has rank `d`, the query and value matrices of every head have rank
  -- `d_h`, and the bound is attained
  filter_upwards [ae_rank_E_iu2 μ hdIn, ae_rank_QV_sum_iu2 μ hdh, hfd] with θ hE hQV hθfd
  exact exists_cob_heads_of_eval_eq_residual_attentionMlp_rmsNorm hε hσ θ hE hQV.1 hQV.2 hθfd

/-- **Proposition 4.5 of the skips paper, last sentence, under the
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
  -- at almost every `θ`, `E` has rank `d`, the query and value matrices of every head have rank
  -- `d_h`, no value column of a gated unit vanishes, and the bound is attained
  filter_upwards [ae_rank_E_iu2 μ hdIn, ae_rank_QV_sum_iu2 μ hdh, ae_value_ne_zero_sum_iu2 μ,
    hfd] with θ hE hQV hv hθfd
  exact exists_cob_heads_of_eval_eq_residual_attentionGated hσ θ hE hQV.1 hQV.2 hv hθfd

/-- **Proposition 4.5 of the skips paper, last sentence, under the
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
  -- at almost every `θ`, `E` has rank `d`, the query and value matrices of every head have rank
  -- `d_h`, no value column of a gated unit vanishes, and the bound is attained
  filter_upwards [ae_rank_E_iu2 μ hdIn, ae_rank_QV_sum_iu2 μ hdh, ae_value_ne_zero_sum_iu2 μ,
    hfd] with θ hE hQV hv hθfd
  exact exists_cob_heads_of_eval_eq_residual_attentionGated_rmsNorm hε hσ θ hE hQV.1 hQV.2 hv
    hθfd

end Skips
