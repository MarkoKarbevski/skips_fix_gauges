import SkipsLean.OneBlock.LearnedSkipRMSZeroBound

/-!
# One block with a learned skip under pre-RMSNorm with `ε = 0`: "at most", at generic parameters

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. […] For `ε = 0` it exceeds that of the residual
network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and
ReGLU blocks."

`OneBlock/LearnedSkipRMSZeroBound.lean` has the "at most" at one parameter, for a full learned
skip and a block with an analytic fixed map. Here: at almost every weights and skip `(θ, A)`,
for any such block whose conditions hold at almost every `θ`, and for the kinds of block: MLP
blocks with an analytic activation that is nonzero on the positive reals (tanh and GELU by name),
gated blocks with such a gate (SwiGLU and GeGLU by name), attention blocks. As in
`OneBlock/ResidualRMSZeroKinds.lean`, the blocks may have any width with at least one hidden unit
(one head of positive width), and `d_in, d_out ≥ d ≥ 2`.

Both functional dimensions are those on the inputs at which no normalized row vanishes
(`funDimSkipsOn` on `learnedZeroDomain`, `funDimOn` on `residualZeroDomain`), and the two networks
have the same weights `θ`. Not stated here: the upper triangular skip
(`OneBlock/LearnedSkipTriangularRMSZeroBound.lean`); ReLU, ReLU², ReGLU blocks
(`OneBlock/LearnedSkipRMSZeroRescaleBound.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

omit [DecidableEq d] in
/-- Helper (copy of the private `borelSpace_skips_lsk` of `OneBlock/LearnedSkipKinds.lean`): the
skips `Fin 1 → Matrix d d ℝ` carry the Borel σ-algebra of their norm topology. -/
private theorem borelSpace_skips_lzk : BorelSpace (Fin 1 → Matrix d d ℝ) :=
  inferInstanceAs (BorelSpace (Fin 1 → d → d → ℝ))

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper (copy of the private `ae_fst_lsk` of `OneBlock/LearnedSkipKinds.lean`): a condition on
the weights that holds at almost every `θ` holds at almost every `(θ, v)`. -/
private theorem ae_fst_lzk {A : Arch T d 1} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] (hB : BorelSpace V)
    (μ : Measure (Params A dIn dOut × V)) (hμ : μ.IsAddHaarMeasure) {Q : Params A dIn dOut → Prop}
    (h : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), Q θ) :
    ∀ᵐ p ∂μ, Q p.1 := by
  -- a measurable null set `N` outside which `Q` holds
  rw [ae_iff] at h
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null h
  have hc : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)), θ ∈ Nᶜ :=
    measure_eq_zero_iff_ae_notMem.1 hN0
  have h1 := (ae_comp_linearMap_mem_iff (LinearMap.fst ℝ (Params A dIn dOut) V) μ
    Measure.addHaar (LinearMap.fst_surjective) hN.compl).2 hc
  refine h1.mono fun p hp => ?_
  by_contra hq
  exact hp (hsub hq)

omit [Nonempty T] in
/-- Helper (copy of the private `ae_isUnit_det_lsa` of `OneBlock/LearnedSkipAttention.lean`): if
a square matrix that depends linearly on a point of `E` is the identity at one point, it is
invertible at almost every point. -/
private theorem ae_isUnit_det_lzk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] (hB : BorelSpace E) (μ : Measure E)
    (hμ : μ.IsAddHaarMeasure) (Φ : E →ₗ[ℝ] Matrix d d ℝ) (x₀ : E) (h₀ : Φ x₀ = 1) :
    ∀ᵐ x ∂μ, IsUnit (Φ x).det := by
  -- the entries are linear, so the determinant is analytic
  have hentry : ∀ i j, AnalyticOnNhd ℝ (fun x => Φ x i j) Set.univ := fun i j =>
    (LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℝ ℝ i j) ∘ₗ Φ)).analyticOnNhd _
  have hφ : AnalyticOnNhd ℝ (fun x => (Φ x).det) Set.univ := by
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (σ i) i)
  -- it is `1` at `x₀`, so its zero set is null
  have hnull := measure_zeroSet_of_analytic μ hφ ⟨x₀, by rw [h₀, Matrix.det_one]; exact one_ne_zero⟩
  rw [ae_iff]
  simpa only [isUnit_iff_ne_zero, not_not] using hnull

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", at generic weights and skip,
for a block with an analytic fixed map:** if at almost every `θ` the embedding and the readout
have rank `d` and some input `w` has the rows of `w E` and `g(w)` independent for every token,
then at almost every `(θ, A)` the functional dimension of the network with the full learned skip
`A` exceeds that of the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_learned_le_funDimOn_residual_add_rmsNorm_zero {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d) (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ)
    (μ : Measure (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))) [μ.IsAddHaarMeasure]
    (hgen : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)),
      θ.E.rank = Fintype.card d ∧ θ.D.rank = Fintype.card d ∧
      ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
        ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t]) :
    ∀ᵐ p ∂μ, funDimSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
        (learnedZeroDomain A p.1 p.2)
      ≤ funDimOn A 1 p.1 (residualZeroDomain A p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  -- at almost every `(θ, A)`: `E`, `D` of rank `d` and the input `w` (from `θ`), and the skip
  -- `A_0` invertible (its determinant is a polynomial in `(θ, A)`, equal to `1` at `A = 1`)
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := borelSpace_skips_lzk
  have hBp : BorelSpace (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) := Prod.borelSpace
  have hdet : ∀ᵐ p ∂μ, IsUnit (p.2 0).det :=
    ae_isUnit_det_lzk hBp μ (by assumption)
      ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix d d ℝ) 0)
        ∘ₗ (LinearMap.snd ℝ _ (Fin 1 → Matrix d d ℝ))) (0, fun _ => 1) rfl
  filter_upwards [ae_fst_lzk hBs μ (by assumption) hgen, hdet] with p hp hdp
  obtain ⟨hE, hD, hw⟩ := hp
  -- the bound at one parameter
  exact funDimSkipsOn_learned_le_funDimOn_residual_add_rmsNorm_zero hA hd hf p.1 p.2 hE hD hdp hw

variable {hid H dh : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, Fintype (H ℓ)]
  [∀ ℓ, Fintype (dh ℓ)]
variable {σ : ℝ → ℝ}

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one MLP block with an
analytic activation that is nonzero on the positive reals:** for `d_in, d_out ≥ d ≥ 2`, at almost
every weights and full learned skip `(θ, A)` the functional dimension exceeds that of the residual
network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_learned_le_residual_add_mlp_oneBlock_rmsNorm_zero
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hσp : ∀ z, 0 < z → σ z ≠ 0)
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp σ (rmsNorm 0) hid)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
        (learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) p.1 p.2)
      ≤ funDimOn (Arch.mlp σ (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.mlp σ (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp hσa ℓ
  refine ae_funDimSkipsOn_learned_le_funDimOn_residual_add_rmsNorm_zero rfl hd (hf 0) μ ?_
  -- at almost every `θ`: `E` and `D` have rank `d`, and the input `w` of the proof exists
  filter_upwards [ae_turnGeneric _ (fun ℓ => continuousOn_univ.mp (hf ℓ).continuousOn)
    Measure.addHaar hd hdIn hdOut (ae_someBlockNonzero_mlp hσp ⟨0, inferInstance⟩ Measure.addHaar),
    ae_exists_linearIndependent_rows_mlp (continuousOn_univ.mp hσa.continuousOn) hσp Measure.addHaar
      hd hdIn hdOut] with θ hθ hw
  exact ⟨hθ.rank_E, hθ.rank_D, hw⟩

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one tanh block:** for `d_in,
d_out ≥ d ≥ 2`, at almost every weights and full learned skip `(θ, A)` the functional dimension
exceeds that of the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_learned_le_residual_add_tanh_oneBlock_rmsNorm_zero
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp Real.tanh (rmsNorm 0) hid)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
        (learnedZeroDomain (Arch.mlp Real.tanh (rmsNorm 0) hid) p.1 p.2)
      ≤ funDimOn (Arch.mlp Real.tanh (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.mlp Real.tanh (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  exact ae_funDimSkipsOn_learned_le_residual_add_mlp_oneBlock_rmsNorm_zero analyticOnNhd_tanh
    (fun _ hz => tanh_ne_zero_of_pos hz) μ hd hdIn hdOut

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one GELU block:** for `d_in,
d_out ≥ d ≥ 2`, at almost every weights and full learned skip `(θ, A)` the functional dimension
exceeds that of the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_learned_le_residual_add_gelu_oneBlock_rmsNorm_zero
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp gelu (rmsNorm 0) hid)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
        (learnedZeroDomain (Arch.mlp gelu (rmsNorm 0) hid) p.1 p.2)
      ≤ funDimOn (Arch.mlp gelu (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.mlp gelu (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  exact ae_funDimSkipsOn_learned_le_residual_add_mlp_oneBlock_rmsNorm_zero analyticOnNhd_gelu
    (fun _ hz => gelu_ne_zero_of_pos hz) μ hd hdIn hdOut

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one gated block with an
analytic gate that is nonzero on the positive reals:** for `d_in, d_out ≥ d ≥ 2`, at almost every
weights and full learned skip `(θ, A)` the functional dimension exceeds that of the residual
network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_learned_le_residual_add_gated_oneBlock_rmsNorm_zero
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hσp : ∀ z, 0 < z → σ z ≠ 0)
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.gated σ (rmsNorm 0) hid)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
        (learnedZeroDomain (Arch.gated σ (rmsNorm 0) hid) p.1 p.2)
      ≤ funDimOn (Arch.gated σ (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.gated σ (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid).f ℓ)
      Set.univ :=
    fun ℓ => analyticOnNhd_f_gated hσa ℓ
  refine ae_funDimSkipsOn_learned_le_funDimOn_residual_add_rmsNorm_zero rfl hd (hf 0) μ ?_
  -- at almost every `θ`: `E` and `D` have rank `d`, and the input `w` of the proof exists
  filter_upwards [ae_turnGeneric _ (fun ℓ => continuousOn_univ.mp (hf ℓ).continuousOn)
    Measure.addHaar hd hdIn hdOut
      (ae_someBlockNonzero_gated hσp ⟨0, inferInstance⟩ Measure.addHaar),
    ae_exists_linearIndependent_rows_gated (continuousOn_univ.mp hσa.continuousOn) hσp
      Measure.addHaar hd hdIn hdOut] with θ hθ hw
  exact ⟨hθ.rank_E, hθ.rank_D, hw⟩

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one SwiGLU block:** for
`d_in, d_out ≥ d ≥ 2`, at almost every weights and full learned skip `(θ, A)` the functional
dimension exceeds that of the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_learned_le_residual_add_swiglu_oneBlock_rmsNorm_zero
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.gated silu (rmsNorm 0) hid)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
        (learnedZeroDomain (Arch.gated silu (rmsNorm 0) hid) p.1 p.2)
      ≤ funDimOn (Arch.gated silu (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.gated silu (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  exact ae_funDimSkipsOn_learned_le_residual_add_gated_oneBlock_rmsNorm_zero analyticOnNhd_silu
    (fun _ hz => silu_ne_zero_of_pos hz) μ hd hdIn hdOut

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one GeGLU block:** for
`d_in, d_out ≥ d ≥ 2`, at almost every weights and full learned skip `(θ, A)` the functional
dimension exceeds that of the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_learned_le_residual_add_geglu_oneBlock_rmsNorm_zero
    [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.gated gelu (rmsNorm 0) hid)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
        (learnedZeroDomain (Arch.gated gelu (rmsNorm 0) hid) p.1 p.2)
      ≤ funDimOn (Arch.gated gelu (rmsNorm 0) hid) 1 p.1
          (residualZeroDomain (Arch.gated gelu (rmsNorm 0) hid) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  exact ae_funDimSkipsOn_learned_le_residual_add_gated_oneBlock_rmsNorm_zero analyticOnNhd_gelu
    (fun _ hz => gelu_ne_zero_of_pos hz) μ hd hdIn hdOut

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", for one attention block with a
head of positive width and a mask in which every token sees some token:** for `d_in, d_out ≥ d ≥
2`, at almost every weights and full learned skip `(θ, A)` the functional dimension exceeds that of
the residual network with the weights `θ` by at most `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_learned_le_residual_add_attention_oneBlock_rmsNorm_zero
    (sees : T → T → Prop) [DecidableRel sees] (hsees : ∀ t, ∃ s, sees t s)
    [Nonempty (H 0)] [Nonempty (dh 0)]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.attention sees (rmsNorm 0) H dh)
        (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p
        (learnedZeroDomain (Arch.attention sees (rmsNorm 0) H dh) p.1 p.2)
      ≤ funDimOn (Arch.attention sees (rmsNorm 0) H dh) 1 p.1
          (residualZeroDomain (Arch.attention sees (rmsNorm 0) H dh) p.1)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨t₁⟩ := (inferInstance : Nonempty T)
  obtain ⟨s₁, hs₁⟩ := hsees t₁
  have hf : ∀ ℓ, AnalyticOnNhd ℝ ((Arch.attention (T := T) (d := d) sees (rmsNorm 0) H dh).f ℓ)
      Set.univ :=
    fun ℓ => analyticOnNhd_f_attention sees _ H dh ℓ
  refine ae_funDimSkipsOn_learned_le_funDimOn_residual_add_rmsNorm_zero rfl hd (hf 0) μ ?_
  -- at almost every `θ`: `E` and `D` have rank `d`, and the input `w` of the proof exists
  filter_upwards [ae_turnGeneric _ (fun ℓ => continuousOn_univ.mp (hf ℓ).continuousOn)
    Measure.addHaar hd hdIn hdOut
      (ae_someBlockNonzero_attention ⟨0, inferInstance, inferInstance⟩ t₁ s₁ hs₁ Measure.addHaar),
    ae_exists_linearIndependent_rows_attention sees hsees Measure.addHaar hd hdIn hdOut]
    with θ hθ hw
  exact ⟨hθ.rank_E, hθ.rank_D, hw⟩

end Skips
