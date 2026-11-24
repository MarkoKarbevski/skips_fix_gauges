import SkipsLean.OneBlock.LearnedSkipTriangular
import SkipsLean.OneBlock.LearnedSkipAttention

/-!
# One block with an upper triangular learned skip under pre-RMSNorm: the general step, attention

Paper (skips paper): Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. For generic parameters and `ε > 0`, its functional
dimension exceeds that of the residual network of part (ii) by exactly `d_model (d_model + 1)/2`,
and it satisfies the equality condition." Its proof, Step 5: "For an upper triangular `A`,
`A Y − X_a A` must be upper triangular, which determines `Y` from `X_a` […]. They then have
dimension `d_model (d_model − 1)/2`. So `K(θ)` is larger than for the residual network by
`d_model (d_model − 1)/2`, respectively `0`, while the network has `d_model²`, respectively
`d_model (d_model + 1)/2`, more parameters. In both cases the functional dimension is larger by
`d_model (d_model + 1)/2`."

`OneBlock/LearnedSkipTriangular.lean` has the definitions (`upperTriangular`, `triSkips`,
`funDimLearnedTri`), the statement that at an invertible upper triangular skip the triangular
family has the functional dimension of the full family (`funDimLearnedTri_eq_funDimLearned`), and
the values for tanh, GELU, SwiGLU and GeGLU blocks of width at least `d`. Here:

* once for all continuously differentiable blocks, at one parameter: if `E` and `D` have rank `d`,
  the upper triangular skip is invertible and Step 4 holds (`NoSymmetricPart`,
  `OneBlock/LearnedSkipGain.lean`), the network with the upper triangular learned skip has the
  functional dimension of the residual network at the same weights plus `d (d + 1)/2`;
* for an attention block: the same at one parameter (some token sees a token, `S ≠ 0`), and for
  `d_in, d_out ≥ d ≥ 2`, at least one head, heads of width `1 ≤ d_h ≤ d` and a token that sees
  itself and another token: at almost every `(θ, A)`, `A` upper triangular, the functional
  dimension is `P + d (d + 1)/2 − d (d − 1)/2 − 2 H d_h²` (the equality condition: the network has
  `P + d (d + 1)/2` parameters and its symmetries have dimension `d (d − 1)/2 + 2 H d_h²`), which is
  `d (d + 1)/2` more than the residual network at almost every `θ'`.

ReLU, ReLU² and ReGLU blocks: `OneBlock/LearnedSkipTriangularRescale.lean`. Not stated: `ε = 0`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [LinearOrder d] [Fintype dIn] [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)] {ε : ℝ}

/-- **Theorem B.1 (iii) for the upper triangular skip, at one parameter, for a continuously
differentiable block (`ε > 0`):** if `E` and `D` have rank `d`, the upper triangular skip
`A = R 0` is invertible and Step 4 holds at `θ` (`NoSymmetricPart` at all inputs), the network
with the upper triangular learned skip has at `(θ, A)` the functional dimension of the residual
network at `θ` plus `d (d + 1)/2`. -/
theorem funDimLearnedTri_eq_funDim_residual_add_of_noSymmetricPart {A : Arch T d 1} {ε : ℝ}
    (hε : 0 < ε) (hA : A.χ = rmsNorm ε) (hf : ContDiff ℝ 1 (A.f 0)) (θ : Params A dIn dOut)
    (R : Fin 1 → upperTriangular d) (hE : θ.E.rank = Fintype.card d)
    (hD : θ.D.rank = Fintype.card d) (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    (hX : NoSymmetricPart A ε θ Set.univ) :
    funDimLearnedTri A (θ, R)
      = funDim A 1 θ + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the block is differentiable (`Fin 1` has the one block `0`)
  have hf' : ∀ ℓ, Differentiable ℝ (A.f ℓ) := fun ℓ => by
    obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
    exact hf.differentiable one_ne_zero
  -- at the invertible triangular skip the triangular family has the value of the full family,
  -- and the full family has the residual value plus `d (d + 1)/2`
  rw [funDimLearnedTri_eq_funDimLearned hε hA hf' θ R hR]
  exact funDimLearned_eq_funDim_residual_add_of_noSymmetricPart hε hA hf θ _ hE hD hR hX

/-- **Theorem B.1 (iii) for an attention block with an upper triangular learned skip, at one
parameter (`ε > 0`):** if `E` and `D` have rank `d`, some token sees a token,
`S = ∑_i W_{V,i} W_{O,i}` is not `0` and the upper triangular skip is invertible, the functional
dimension is that of the residual network at the same weights plus `d (d + 1)/2`. -/
theorem funDimLearnedTri_attention_rmsNorm_eq_residual_add (hε : 0 < ε)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hsees : ∃ t s, sees t s) (hS : ∑ i, headValueModel θ 0 i ≠ 0)
    (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det) :
    funDimLearnedTri (Arch.attention sees (rmsNorm ε) H dh) (θ, R)
      = funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the attention block is analytic, hence `C¹`; Step 4 is `noSymmetricPart_attention_rmsNorm`
  have hf : ContDiff ℝ 1 ((Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).f 0) :=
    (analyticOnNhd_f_attention (d := d) sees (rmsNorm ε) H dh 0).contDiff
  exact funDimLearnedTri_eq_funDim_residual_add_of_noSymmetricPart hε rfl hf θ R hE hD hR
    (noSymmetricPart_attention_rmsNorm hε θ hE hsees hS)

omit [Fintype T] [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper (copy of the private `ae_fst_lsa` of `OneBlock/LearnedSkipAttention.lean`): a condition
on the weights that holds at almost every `θ` holds at almost every `(θ, v)`. -/
private theorem ae_fst_lts {A : Arch T d 1} {V : Type*} [NormedAddCommGroup V]
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

omit [Fintype T] [Nonempty T] [LinearOrder d] in
/-- Helper (copy of the private `rank_eq_of_isUnit_det_rows_lsa`): a matrix with `d` columns has
rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_rows_lts {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

omit [Nonempty T] [LinearOrder d] in
/-- Helper (copy of the private `ae_rank_E_D_lsa`): at generic weights `E` and `D` have rank `d`,
when `d_in ≥ d` and `d_out ≥ d`. -/
private theorem ae_rank_E_D_lts {A : Arch T d 1} (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)),
      θ.E.rank = Fintype.card d ∧ θ.D.rank = Fintype.card d := by
  -- `d` rows of `E` and `d` columns of `D`, invertible at generic weights
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hdOut
  filter_upwards [ae_isUnit_det_submatrix Measure.addHaar] with θ hθ
  exact ⟨rank_eq_of_isUnit_det_rows_lts θ.E ρ (hθ.2.2.1 ρ),
    rank_eq_card_of_isUnit_det θ.D c (hθ.2.1 c)⟩

omit [Nonempty T] [LinearOrder d] in
/-- Helper (copy of the private `ae_isUnit_det_lsa`): if a square matrix that depends linearly on
a point of `E` is the identity at one point, it is invertible at almost every point. -/
private theorem ae_isUnit_det_lts {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

omit [Nonempty T] [DecidableEq d] [LinearOrder d] in
/-- Helper (copy of the private `ae_sumValue_ne_zero_lsa`): at generic weights
`S = ∑_i W_{V,i} W_{O,i} ≠ 0`, when there is a head of width at least `1`: its entry `(a, a)` is
a polynomial in the weights, equal to `H d_h` at the weights whose reads and writes have all
entries `1`. -/
private theorem ae_sumValue_ne_zero_lts [Nonempty (H 0)] [Nonempty d]
    (hdh0 : 0 < Fintype.card (dh 0)) :
    ∀ᵐ θ ∂(Measure.addHaar :
      Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)),
      ∑ i, headValueModel θ 0 i ≠ 0 := by
  obtain ⟨a⟩ := ‹Nonempty d›
  -- the entry `(a, a)` of `S`, `∑_{i,k} W_read(a, (i, V k)) W_write((i, k), a)`, is analytic
  have hg : AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut =>
        (∑ i, headValueModel θ 0 i) a a) Set.univ := by
    simp only [Matrix.sum_apply, headValueModel, Matrix.mul_apply, Matrix.submatrix_apply, id]
    exact Finset.analyticOnNhd_fun_sum _ fun i _ => Finset.analyticOnNhd_fun_sum _ fun k _ =>
      (analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ a (i, Sum.inr (Sum.inr k))).comp
        (Params.linRead (A := Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh)
          (dIn := dIn) (dOut := dOut) 0))).mul
      (analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ (i, k) a).comp
        (Params.linWrite (A := Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh)
          (dIn := dIn) (dOut := dOut) 0)))
  -- it is `H d_h ≠ 0` at the weights with all entries `1`
  have hne : ∃ θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut,
      (∑ i, headValueModel θ 0 i) a a ≠ 0 := by
    refine ⟨⟨0, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, 0⟩, ?_⟩
    simp only [Matrix.sum_apply, headValueModel, Matrix.mul_apply, Matrix.submatrix_apply, id,
      Matrix.of_apply, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (Nat.cast_ne_zero.2 hdh0.ne')
  filter_upwards [ae_ne_zero_of_analytic Measure.addHaar hg hne] with θ hθ hS
  exact hθ (by rw [hS]; rfl)

/-- **Theorem B.1 (iii) of the skips paper for one attention block with an upper triangular
learned skip, `ε > 0`:** for `d_in, d_out ≥ d ≥ 2`, at least one head, heads of width
`1 ≤ d_h ≤ d` and a token that sees itself and another token, at almost every `(θ, A)`, `A` upper
triangular, the functional dimension is `P + d (d + 1)/2 − d (d − 1)/2 − 2 H d_h²`, with `P` the
number of weights without the skip. -/
theorem ae_funDimLearnedTri_attention_rmsNorm (hε : 0 < ε) [Nonempty (H 0)]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.attention sees (rmsNorm ε) H dh) p
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  classical
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have hBt : BorelSpace (Fin 1 → upperTriangular d) := inferInstance
  have hBp : BorelSpace (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut
      × (Fin 1 → upperTriangular d)) := Prod.borelSpace
  -- at almost every `θ`: `E` and `D` of rank `d`, `S ≠ 0`, and the value of the residual network
  have hθ := ((ae_rank_E_D_lts (A := Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh)
    hdIn hdOut).and (ae_sumValue_ne_zero_lts (hdh0 0))).and
    (ae_funDim_attention_residual_rmsNorm hε Measure.addHaar hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2
      hs1)
  -- at almost every `(θ, A)`, moreover the triangular skip `A_0` is invertible: its determinant
  -- is a polynomial in the entries, `1` at `A_0 = 1`
  have hdet : ∀ᵐ p ∂μ, IsUnit (p.2 0 : Matrix d d ℝ).det :=
    ae_isUnit_det_lts hBp μ (by assumption)
      ((upperTriangular d).subtype
        ∘ₗ (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => upperTriangular d) 0)
        ∘ₗ (LinearMap.snd ℝ _ (Fin 1 → upperTriangular d)))
      (0, fun _ => ⟨1, Matrix.blockTriangular_one⟩) rfl
  filter_upwards [ae_fst_lts hBt μ (by assumption) hθ, hdet] with p hp hp'
  obtain ⟨⟨⟨hE, hD⟩, hS⟩, hres⟩ := hp
  -- `fd = fd_res + d (d + 1)/2` and `fd_res + d (d − 1)/2 + 2 ∑ H d_h² = P`
  have h := funDimLearnedTri_attention_rmsNorm_eq_residual_add hε p.1 hE hD ⟨t₂, t₂, hs2⟩ hS p.2
    hp'
  rw [Prod.mk.eta] at h
  rw [h]
  generalize Fintype.card d * (Fintype.card d + 1) / 2 = y
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = x at hres ⊢
  omega

/-- **Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly
`d (d + 1)/2`", for one attention block with an upper triangular learned skip, `ε > 0`:** at
almost every `(θ, A)`, `A` upper triangular, and almost every `θ'`. -/
theorem ae_funDimLearnedTri_attention_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (H 0)]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearnedTri (Arch.attention sees (rmsNorm ε) H dh) p
      = funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- `fd + d (d − 1)/2 + s = P + d (d + 1)/2` and `fd₁ + d (d − 1)/2 + s = P`
  filter_upwards [ae_funDimLearnedTri_attention_rmsNorm hε μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2
    hs1] with p hp
  filter_upwards [ae_funDim_attention_residual_rmsNorm hε ν hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2
    hs1] with θ' hθ'
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at hp hθ'
  generalize Fintype.card d * (Fintype.card d + 1) / 2 = b at hp ⊢
  omega

end Skips
