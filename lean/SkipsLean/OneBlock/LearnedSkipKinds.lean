import SkipsLean.OneBlock.LearnedSkipZero
import SkipsLean.OneBlock.LearnedSkipBound
import SkipsLean.Depth.TanhRMS
import SkipsLean.Depth.GeluGatedTheorem
import SkipsLean.Residual.DepthMlpRMS
import SkipsLean.Residual.DepthGatedRMS
import SkipsLean.Symmetry.InsideBlocksKinds
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-!
# One block with a full learned skip under pre-RMSNorm: tanh, GELU, SwiGLU and GeGLU blocks

Paper (skips paper): Theorem 4.6 (ii): "A learned skip raises it by exactly
`d_model (d_model + 1)/2` more than an identity skip." Theorem B.1 (iii): "Let the network be
pre-RMSNorm without biases, with a learned skip `A`, full or upper triangular. For generic
parameters and `ε > 0`, its functional dimension exceeds that of the residual network of part (ii)
by exactly `d_model (d_model + 1)/2`, and it satisfies the equality condition."

Here for one tanh, GELU, SwiGLU or GeGLU block of width at least `d` (the Scope of the paper),
with a full learned skip `A` (all `d × d` matrices), `d_in, d_out ≥ d ≥ 2`, `ε > 0`: at almost
every `(θ, A)` the functional dimension is `P + d² − d (d − 1) − s`, where `P` counts the weights
without the skip (the equality condition: the network has `P + d²` parameters, and its symmetries
have dimension `d (d − 1) + s`); and it exceeds the functional dimension `P − d (d − 1)/2 − s` of
the residual network at generic weights by `d (d + 1)/2`. The definitions and the route (the upper
bound from the two orthogonal changes of basis; the lower bound at the skip `A = 0` from the value
`P − d (d − 1) − s` of the skipless network, `Depth/TanhRMS.lean`, `Depth/GeluGatedTheorem.lean`;
the generic value is the largest) are in `OneBlock/LearnedSkip.lean`. Not stated here: the upper
triangular skip (`OneBlock/LearnedSkipTriangular.lean`; any width:
`OneBlock/LearnedSkipTriangularNarrow.lean`); ReLU, ReLU², ReGLU and attention blocks (for them the
skipless value under pre-RMSNorm is not proved, and the route of the paper's Part (iii) is taken:
`OneBlock/LearnedSkipRescale.lean`, `OneBlock/LearnedSkipReGLU.lean`,
`OneBlock/LearnedSkipAttention.lean`); blocks narrower than `d`
(`OneBlock/LearnedSkipNarrowMlp.lean`, `OneBlock/LearnedSkipNarrowGated.lean`); `ε = 0`
(`OneBlock/LearnedSkipRMSZeroBound.lean`, `OneBlock/LearnedSkipRMSZeroBoundKinds.lean`).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)] {ε : ℝ}

omit [DecidableEq d] in
/-- Helper: the skips `Fin 1 → Matrix d d ℝ` carry the Borel σ-algebra of their norm topology
(the instance of Mathlib is stated for the entrywise topology of `Matrix`, the same topology). -/
private theorem borelSpace_skips_lsk : BorelSpace (Fin 1 → Matrix d d ℝ) :=
  inferInstanceAs (BorelSpace (Fin 1 → d → d → ℝ))

omit [Fintype T] [DecidableEq d] in
/-- Helper: a condition on the weights that holds at almost every `θ` holds at almost every
`(θ, v)`: the preimage of a null set under the onto linear map `(θ, v) ↦ θ` is a null set. -/
private theorem ae_fst_lsk {A : Arch T d 1} {V : Type*} [NormedAddCommGroup V]
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

omit [DecidableEq d] in
/-- Helper: the full skips of one block form a space of dimension `d²`. -/
private theorem finrank_skips_lsk :
    Module.finrank ℝ (Fin 1 → Matrix d d ℝ) = Fintype.card d ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_matrix, sq]

omit [Fintype T] in
/-- Helper (the private `rank_eq_of_isUnit_det_submatrix` of `Generic/Params.lean`): a matrix with
`d` columns has rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_rows_lsk {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- Helper: at generic weights `E` and `D` have rank `d`, when `d_in ≥ d` and `d_out ≥ d`. -/
private theorem ae_rank_E_D_lsk {A : Arch T d 1} (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)),
      θ.E.rank = Fintype.card d ∧ θ.D.rank = Fintype.card d := by
  -- `d` rows of `E` and `d` columns of `D`, invertible at generic weights
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hdOut
  filter_upwards [ae_isUnit_det_submatrix Measure.addHaar] with θ hθ
  exact ⟨rank_eq_of_isUnit_det_rows_lsk θ.E ρ (hθ.2.2.1 ρ),
    rank_eq_card_of_isUnit_det θ.D c (hθ.2.1 c)⟩

/-- Helper (the common part of the four kinds): for one real-analytic block under pre-RMSNorm
(`ε > 0`), `d_in, d_out ≥ d`, if the skipless network has `fd + k = P` at generic weights with
`k = d (d − 1) + s`, and the bound `fd + (d (d − 1) + s) ≤ P + d²` of the full learned skip holds
at generic `(θ, A)`, then it is an equality there. -/
private theorem ae_funDimLearned_of_skipless_lsk [Nonempty T] {A : Arch T d 1} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))) [hμ : μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    {k s : ℕ} (h0 : ∀ᵐ θ ∂(Measure.addHaar : Measure (Params A dIn dOut)),
      funDim A 0 θ + k = Module.finrank ℝ (Params A dIn dOut))
    (hub : ∀ᵐ p ∂μ, funDimLearned A p + (Fintype.card d * (Fintype.card d - 1) + s)
      ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2)
    (hk : k = Fintype.card d * (Fintype.card d - 1) + s) :
    ∀ᵐ p ∂μ, funDimLearned A p + (Fintype.card d * (Fintype.card d - 1) + s)
      = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
  -- a weight `θ₀` with the skipless value and `E`, `D` of rank `d`
  obtain ⟨θ₀, hθ₀, hE, hD⟩ := (h0.and (ae_rank_E_D_lsk hdIn hdOut)).exists
  -- at the skip `0`: `fd(θ₀, 0) ≥ fd₀(θ₀) + d²`
  have hz := funDim_add_finrank_le_funDimSkips_zero hε hA hf
    (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (fun _ _ h => h) θ₀ hE hD
  rw [finrank_skips_lsk] at hz
  change _ ≤ funDimLearned A (θ₀, 0) at hz
  -- generic `(θ, A)` have at least this functional dimension
  have hχ : AnalyticOnNhd ℝ A.χ Set.univ := by rw [hA]; exact analyticOnNhd_rmsNorm hε
  have hge := @ae_funDimSkips_ge _ _ _ _ _ _ _ _ _ _ _ _ _ _ borelSpace_skips_lsk A
    (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) hf hχ μ hμ (θ₀, 0)
  filter_upwards [hge, hub] with p h1 h2
  change funDimLearned A (θ₀, 0) ≤ funDimLearned A p at h1
  generalize Fintype.card d * (Fintype.card d - 1) = x at *
  omega

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `d (d − 1)` is even, so two halves of it make it whole (`L + 1 = 2` changes of basis
of `d (d − 1)/2` dimensions each in the skipless network of one block). -/
private theorem two_mul_half_lsk (n : ℕ) : (1 + 1) * (n * (n - 1) / 2) = n * (n - 1) := by
  have h := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  generalize n * (n - 1) = x at h ⊢
  omega

/-- Helper: `d (d + 1)/2 + d (d − 1)/2 = d²` (both products are even). -/
private theorem half_add_half_lsk (n : ℕ) : n * (n + 1) / 2 + n * (n - 1) / 2 = n ^ 2 := by
  have h1 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  have h3 : n * (n + 1) + n * (n - 1) = 2 * n ^ 2 := by
    cases n with
    | zero => rfl
    | succ m => rw [Nat.add_sub_cancel]; ring
  generalize n * (n + 1) = y at h1 h3 ⊢
  generalize n * (n - 1) = x at h2 h3 ⊢
  generalize n ^ 2 = q at h3 ⊢
  omega

/-- Helper (the upper bound with no symmetries inside the block): at generic `(θ, A)`,
`fd + d (d − 1) ≤ P + d²` (`funDimLearned_add_le_rmsNorm` with `U = 0`, `E` and `D` of rank `d`). -/
private theorem ae_upper_bot_lsk {A : Arch T d 1} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))) [hμ : μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned A p + (Fintype.card d * (Fintype.card d - 1) + 0)
      ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
  have hf' : ∀ ℓ, Differentiable ℝ (A.f ℓ) :=
    fun ℓ => differentiableOn_univ.1 (hf ℓ).differentiableOn
  filter_upwards [ae_fst_lsk borelSpace_skips_lsk μ hμ (ae_rank_E_D_lsk hdIn hdOut)] with p hp
  have h := funDimLearned_add_le_rmsNorm hε hA hf' p hp.1 hp.2 ⊥ bot_le
  rwa [finrank_bot] at h

/-- Helper: the numbers of the rescalings of the hidden units form a space of dimension `s`, the
number of hidden units (the private `finrank_hidFun` of `Residual/UpperBoundSymmetries.lean`). -/
private theorem finrank_hidFun_lsk :
    Module.finrank ℝ (∀ ℓ, hid ℓ → ℝ) = ∑ ℓ, Fintype.card (hid ℓ) := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card]

/-- Helper: `α ↦ rescaleDir θ α` is linear (the private `valueRescaleLin` of
`Residual/UpperBoundSymmetries.lean`). -/
private noncomputable def valueRescaleLin_lsk {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  toFun := rescaleDir θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext a j
      cases j with
      | inl i => simp [rescaleDir]
      | inr i =>
        simp only [rescaleDir, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply,
          Sum.elim_inr]
        ring
    · intro ℓ
      ext i a
      simp [rescaleDir, add_mul]
    · simp [rescaleDir]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext a j
      cases j <;> simp [rescaleDir, mul_assoc]
    · intro ℓ
      ext i a
      simp [rescaleDir, mul_assoc]
    · simp [rescaleDir]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if no value column of the read vanishes, `α ↦ rescaleDir θ α` is injective: the value
column `e_i` moves by `-α_i e_i` (the private `valueRescaleLin_injective` of
`Residual/UpperBoundSymmetries.lean`). -/
private theorem valueRescaleLin_injective_lsk {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0) :
    Function.Injective (valueRescaleLin_lsk θ) := by
  intro α α' h
  have h' : rescaleDir θ α = rescaleDir θ α' := h
  funext ℓ i
  -- an entry `a` with `e_i a ≠ 0`
  obtain ⟨a, ha⟩ := Function.ne_iff.mp (hv ℓ i)
  have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h') a) (Sum.inr i)
  change -(α ℓ i) * θ.read ℓ a (Sum.inr i) = -(α' ℓ i) * θ.read ℓ a (Sum.inr i) at hr
  exact neg_inj.mp (mul_right_cancel₀ ha hr)

/-- Helper (the upper bound for a gated block): at generic `(θ, A)`,
`fd + (d (d − 1) + s) ≤ P + d²`, with `U` the rescalings of the values of the hidden units, of
dimension `s` where no value column of the read vanishes. -/
private theorem ae_upper_gated_lsk [Nonempty d] {σ : ℝ → ℝ} (hε : 0 < ε)
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ))) [hμ : μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.gated σ (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  have hf : ∀ ℓ, Differentiable ℝ ((Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid).f ℓ) :=
    fun ℓ => differentiableOn_univ.1 (analyticOnNhd_f_gated hσ ℓ).differentiableOn
  have hv := ae_value_ne_zero (σ := σ) (χ := rmsNorm ε) (hid := hid) (T := T) (d := d)
    (dIn := dIn) (dOut := dOut) Measure.addHaar
  filter_upwards [ae_fst_lsk borelSpace_skips_lsk μ hμ (ae_rank_E_D_lsk hdIn hdOut),
    ae_fst_lsk borelSpace_skips_lsk μ hμ hv] with p hp hp'
  -- the rescalings of the values are symmetries inside the block
  have hU : LinearMap.range (valueRescaleLin_lsk p.1)
      ≤ Submodule.span ℝ {η | InsideBlocks (Arch.gated σ (rmsNorm ε) hid) p.1 η} := by
    rintro _ ⟨α, rfl⟩
    exact Submodule.subset_span (insideBlocks_rescaleDir p.1 α)
  have h := funDimLearned_add_le_rmsNorm hε rfl hf p hp.1 hp.2 _ hU
  rwa [LinearMap.finrank_range_of_inj (valueRescaleLin_injective_lsk p.1 hp'),
    finrank_hidFun_lsk] at h

omit [Fintype T] in
/-- Helper (the form `…_eq_residual_add`): from the value `fd + (d (d − 1) + s) = P + d²` with the
learned skip and the value `fd₁ + (d (d − 1)/2 + s) = P` of the residual network, the difference
is `d² − d (d − 1)/2 = d (d + 1)/2`. -/
private theorem ae_eq_residual_add_lsk {A : Arch T d 1}
    (μ : Measure (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))) (ν : Measure (Params A dIn dOut))
    {k₁ k₂ s : ℕ}
    (hval : ∀ᵐ p ∂μ, funDimLearned A p + k₁
      = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2)
    (hres : ∀ᵐ θ' ∂ν, funDim A 1 θ' + k₂ = Module.finrank ℝ (Params A dIn dOut))
    (hk₁ : k₁ = Fintype.card d * (Fintype.card d - 1) + s)
    (hk₂ : k₂ = Fintype.card d * (Fintype.card d - 1) / 2 + s) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearned A p
      = funDim A 1 θ' + Fintype.card d * (Fintype.card d + 1) / 2 := by
  have h := half_add_half_lsk (Fintype.card d)
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  filter_upwards [hval] with p hp
  filter_upwards [hres] with θ' hθ'
  generalize Fintype.card d * (Fintype.card d + 1) = y at h ⊢
  generalize Fintype.card d * (Fintype.card d - 1) = x at h h2 hk₁ hk₂
  generalize Fintype.card d ^ 2 = q at h hp
  omega

/-- **Theorem B.1 (iii) of the skips paper for one tanh block with a full learned skip, `ε > 0`:**
at almost every `(θ, A)` the functional dimension is `P + d² − d (d − 1)`. -/
theorem ae_funDimLearned_tanh_rmsNorm [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp Real.tanh (rmsNorm ε) hid) p
        + Fintype.card d * (Fintype.card d - 1)
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  have hf : ∀ ℓ, AnalyticOnNhd ℝ
      ((Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_tanh ℓ
  -- the skipless value at generic weights, and the upper bound with `U = 0`
  have h := ae_funDimLearned_of_skipless_lsk hε rfl hf μ hdIn hdOut
    (ae_funDim_tanh_skipless_rmsNorm hε Measure.addHaar hd hdIn hdOut hhid)
    (ae_upper_bot_lsk hε rfl hf μ hdIn hdOut) ((two_mul_half_lsk _).trans (add_zero _).symm)
  simpa only [add_zero] using h

/-- **Theorem 4.6 (ii) of the skips paper, "A learned skip raises it by exactly `d (d + 1)/2` more
than an identity skip", for one tanh block, `ε > 0`:** at almost every `(θ, A)` and almost every
`θ'`, the network with the full learned skip `A` has `d (d + 1)/2` more functional dimension than
the residual network at `θ'`. -/
theorem ae_funDimLearned_tanh_rmsNorm_eq_residual_add [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearned (Arch.mlp Real.tanh (rmsNorm ε) hid) p
      = funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  exact ae_eq_residual_add_lsk μ ν (ae_funDimLearned_tanh_rmsNorm hε μ hd hdIn hdOut hhid)
    (ae_funDim_tanh_residual_rmsNorm hε ν hd hdIn hdOut) (add_zero _).symm (add_zero _).symm

/-- **Theorem B.1 (iii) of the skips paper for one GELU block with a full learned skip, `ε > 0`:**
at almost every `(θ, A)` the functional dimension is `P + d² − d (d − 1)`. -/
theorem ae_funDimLearned_gelu_rmsNorm [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.mlp gelu (rmsNorm ε) hid) p
        + Fintype.card d * (Fintype.card d - 1)
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  have hf : ∀ ℓ, AnalyticOnNhd ℝ
      ((Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_gelu ℓ
  -- the skipless value at generic weights, and the upper bound with `U = 0`
  have h := ae_funDimLearned_of_skipless_lsk hε rfl hf μ hdIn hdOut
    (ae_funDim_gelu_skipless_rmsNorm hε Measure.addHaar hd hdIn hdOut hhid)
    (ae_upper_bot_lsk hε rfl hf μ hdIn hdOut) ((two_mul_half_lsk _).trans (add_zero _).symm)
  simpa only [add_zero] using h

/-- **Theorem 4.6 (ii) of the skips paper, "A learned skip raises it by exactly `d (d + 1)/2` more
than an identity skip", for one GELU block, `ε > 0`:** at almost every `(θ, A)` and almost every
`θ'`, the network with the full learned skip `A` has `d (d + 1)/2` more functional dimension than
the residual network at `θ'`. -/
theorem ae_funDimLearned_gelu_rmsNorm_eq_residual_add [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearned (Arch.mlp gelu (rmsNorm ε) hid) p
      = funDim (Arch.mlp gelu (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  exact ae_eq_residual_add_lsk μ ν (ae_funDimLearned_gelu_rmsNorm hε μ hd hdIn hdOut hhid)
    (ae_funDim_gelu_residual_rmsNorm hε ν hd hdIn hdOut) (add_zero _).symm (add_zero _).symm

/-- **Theorem B.1 (iii) of the skips paper for one SwiGLU block with a full learned skip, `ε > 0`:**
at almost every `(θ, A)` the functional dimension is `P + d² − d (d − 1) − d_hidden`. -/
theorem ae_funDimLearned_swiglu_rmsNorm [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.gated silu (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have hf : ∀ ℓ, AnalyticOnNhd ℝ
      ((Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_gated analyticOnNhd_silu ℓ
  -- the skipless value at generic weights, and the upper bound with the rescalings
  exact ae_funDimLearned_of_skipless_lsk hε rfl hf μ hdIn hdOut
    (ae_funDim_swiglu_skipless_rmsNorm hε Measure.addHaar hd hdIn hdOut hhid)
    (ae_upper_gated_lsk hε analyticOnNhd_silu μ hdIn hdOut)
    (congrArg (· + _) (two_mul_half_lsk _))

/-- **Theorem 4.6 (ii) of the skips paper, "A learned skip raises it by exactly `d (d + 1)/2` more
than an identity skip", for one SwiGLU block, `ε > 0`:** at almost every `(θ, A)` and almost every
`θ'`, the network with the full learned skip `A` has `d (d + 1)/2` more functional dimension than
the residual network at `θ'`. -/
theorem ae_funDimLearned_swiglu_rmsNorm_eq_residual_add [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearned (Arch.gated silu (rmsNorm ε) hid) p
      = funDim (Arch.gated silu (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  exact ae_eq_residual_add_lsk μ ν (ae_funDimLearned_swiglu_rmsNorm hε μ hd hdIn hdOut hhid)
    (ae_funDim_swiglu_residual_rmsNorm hε ν hd hdIn hdOut) rfl rfl

/-- **Theorem B.1 (iii) of the skips paper for one GeGLU block with a full learned skip, `ε > 0`:**
at almost every `(θ, A)` the functional dimension is `P + d² − d (d − 1) − d_hidden`. -/
theorem ae_funDimLearned_geglu_rmsNorm [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ p ∂μ, funDimLearned (Arch.gated gelu (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d ^ 2 := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have hf : ∀ ℓ, AnalyticOnNhd ℝ
      ((Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_gated analyticOnNhd_gelu ℓ
  -- the skipless value at generic weights, and the upper bound with the rescalings
  exact ae_funDimLearned_of_skipless_lsk hε rfl hf μ hdIn hdOut
    (ae_funDim_geglu_skipless_rmsNorm hε Measure.addHaar hd hdIn hdOut hhid)
    (ae_upper_gated_lsk hε analyticOnNhd_gelu μ hdIn hdOut)
    (congrArg (· + _) (two_mul_half_lsk _))

/-- **Theorem 4.6 (ii) of the skips paper, "A learned skip raises it by exactly `d (d + 1)/2` more
than an identity skip", for one GeGLU block, `ε > 0`:** at almost every `(θ, A)` and almost every
`θ'`, the network with the full learned skip `A` has `d (d + 1)/2` more functional dimension than
the residual network at `θ'`. -/
theorem ae_funDimLearned_geglu_rmsNorm_eq_residual_add [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → Matrix d d ℝ)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearned (Arch.gated gelu (rmsNorm ε) hid) p
      = funDim (Arch.gated gelu (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  exact ae_eq_residual_add_lsk μ ν (ae_funDimLearned_geglu_rmsNorm hε μ hd hdIn hdOut hhid)
    (ae_funDim_geglu_residual_rmsNorm hε ν hd hdIn hdOut) rfl rfl

end Skips
