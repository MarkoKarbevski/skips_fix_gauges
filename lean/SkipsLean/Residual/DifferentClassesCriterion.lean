import SkipsLean.Dimension.RankCriterion
import SkipsLean.Dimension.GenericRank
import SkipsLean.Residual.PointwiseLimit

/-!
# Two families of networks whose ranks differ compute different functions

Paper (skips paper): Lemma A.26 (A rank criterion), for two families of networks, as it is applied
in the proofs of Theorem A.28 (ii), (iii) and (iv). The family `F` is the networks of an
architecture `A` with stream matrices `S` (in the applications: residual networks), the family `G`
the networks of an architecture `A'` with stream matrices `S'` (skipless networks of the same or
of other widths), with the same inputs and outputs. Both have real-analytic blocks.

Hypotheses, as in the proof of Lemma A.26: the Jacobian of the outputs of `G` on every batch has
rank at most `r₀` at every parameter, and the functional dimension of `F` at one parameter `θ₀`
exceeds `r₀` ("at some `θ₀` the Jacobian of `θ ↦ (F_θ(x))_{x ∈ X}` has rank greater than `P' - k`
on some finite batch `X`"). Conclusions:

(i) "For almost every `θ`, no `η` satisfies `F_θ = G_η`."
(ii) "for almost every `θ` there is a `δ > 0` such that every `η` has `‖F_θ(x) - G_η(x)‖ ≥ δ` at
some `x ∈ X`", given the property of definable sets for the outputs of `G` on a batch; and then
`F_θ` is not a pointwise limit of the family `G` (Definition A.29).

Sard's theorem and the property of definable sets are hypotheses from the literature
(`Literature/Sard.lean`, `Literature/OMinimal.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d d' dIn dOut : Type*} {L L' : ℕ} [Fintype T] [Fintype d] [Fintype d']
  [Fintype dIn] [Fintype dOut]

/-- Helper: the outputs of a network with real-analytic blocks on a batch are real-analytic in the
parameters (one input at a time, `analyticOnNhd_eval_params`). -/
private theorem analyticOnNhd_evalBatch_dcc (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) :
    AnalyticOnNhd ℝ (evalBatch A S X : Params A dIn dOut → Fin n → Matrix T dOut ℝ) Set.univ :=
  AnalyticOnNhd.pi fun i => analyticOnNhd_eval_params A S hf hχ (X i)

/-- **Lemma A.26 (i) of the skips paper on one batch, for two families of networks, given
Sard's theorem:** there is a finite batch `X` such that for almost every `θ` the outputs of `F_θ`
on `X` are not the outputs on `X` of any network of the family `G`. -/
theorem exists_batch_ae_notMem_range_of_jacobianRank_lt
    (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (A' : Arch T d' L') (S' : Fin L' → Matrix d' d' ℝ)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params A' dIn dOut) (Fin r → ℝ))
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (hf' : ∀ ℓ, AnalyticOnNhd ℝ (A'.f ℓ) Set.univ) (hχ' : AnalyticOnNhd ℝ A'.χ Set.univ)
    (r₀ : ℕ)
    (hr₀ : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ) (η : Params A' dIn dOut),
      jacobianRank A' S' X η ≤ r₀)
    (θ₀ : Params A dIn dOut) (hθ₀ : r₀ < funDim A S θ₀)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), ∀ᵐ θ ∂μ,
      evalBatch A S X θ ∉ Set.range (evalBatch (dOut := dOut) A' S' X) := by
  -- a batch `X` on which the rank of the Jacobian of `F` at `θ₀` is `fd(θ₀) > r₀`
  obtain ⟨n, X, hX⟩ := exists_jacobianRank_eq_funDim (S := S) θ₀
  refine ⟨n, X, ?_⟩
  -- the rank criterion for `F = evalBatch A S X` and `G = evalBatch A' S' X`
  exact ae_notMem_range_of_rank_lt hSard (evalBatch A S X) (evalBatch A' S' X)
    (analyticOnNhd_evalBatch_dcc A S hf hχ X) (analyticOnNhd_evalBatch_dcc A' S' hf' hχ' X) r₀
    (fun η => hr₀ n X η) θ₀ (lt_of_lt_of_eq hθ₀ hX.symm) μ

/-- **Lemma A.26 (i) of the skips paper for two families of networks, given Sard's theorem:** "For
almost every `θ`, no `η` satisfies `F_θ = G_η`." -/
theorem ae_forall_eval_ne_of_jacobianRank_lt
    (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (A' : Arch T d' L') (S' : Fin L' → Matrix d' d' ℝ)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params A' dIn dOut) (Fin r → ℝ))
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (hf' : ∀ ℓ, AnalyticOnNhd ℝ (A'.f ℓ) Set.univ) (hχ' : AnalyticOnNhd ℝ A'.χ Set.univ)
    (r₀ : ℕ)
    (hr₀ : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ) (η : Params A' dIn dOut),
      jacobianRank A' S' X η ≤ r₀)
    (θ₀ : Params A dIn dOut) (hθ₀ : r₀ < funDim A S θ₀)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ η : Params A' dIn dOut, eval A S θ ≠ eval A' S' η := by
  obtain ⟨n, X, h⟩ := exists_batch_ae_notMem_range_of_jacobianRank_lt A S A' S' hSard hf hχ hf'
    hχ' r₀ hr₀ θ₀ hθ₀ μ
  filter_upwards [h] with θ hθ η heq
  -- if `F_θ = G_η`, the outputs on the batch agree, so they are in the range of `G` on `X`
  refine hθ ⟨η, funext fun i => ?_⟩
  show eval A' S' η (X i) = eval A S θ (X i)
  rw [heq]

/-- Helper: if the sup norm of an element of a finite product is at least `δ > 0`, then some
coordinate has norm at least `δ`. -/
private theorem exists_le_norm_apply_dcc {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] {δ : ℝ} (hδ : 0 < δ) {y : ∀ i, E i} (h : δ ≤ ‖y‖) :
    ∃ i, δ ≤ ‖y i‖ := by
  by_contra hne
  push Not at hne
  exact absurd ((pi_norm_lt_iff hδ).2 hne) (not_lt.2 h)

/-- **Lemma A.26 (ii) of the skips paper for two families of networks, given Sard's theorem and
the property of definable sets:** there is a finite batch `X` such that "for almost every `θ`
there is a `δ > 0` such that every `η` has `‖F_θ(x) - G_η(x)‖ ≥ δ` at some `x ∈ X`". -/
theorem exists_batch_ae_exists_pos_le_norm_sub_of_jacobianRank_lt
    (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (A' : Arch T d' L') (S' : Fin L' → Matrix d' d' ℝ)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params A' dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut) A' S' X)))
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (hf' : ∀ ℓ, AnalyticOnNhd ℝ (A'.f ℓ) Set.univ) (hχ' : AnalyticOnNhd ℝ A'.χ Set.univ)
    (r₀ : ℕ)
    (hr₀ : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ) (η : Params A' dIn dOut),
      jacobianRank A' S' X η ≤ r₀)
    (θ₀ : Params A dIn dOut) (hθ₀ : r₀ < funDim A S θ₀)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), ∀ᵐ θ ∂μ, ∃ δ : ℝ, 0 < δ ∧
      ∀ η : Params A' dIn dOut, ∃ i, δ ≤ ‖eval A S θ (X i) - eval A' S' η (X i)‖ := by
  -- a batch `X` on which the rank of the Jacobian of `F` at `θ₀` is `fd(θ₀) > r₀`
  obtain ⟨n, X, hX⟩ := exists_jacobianRank_eq_funDim (S := S) θ₀
  refine ⟨n, X, ?_⟩
  -- the rank criterion: for almost every `θ`, `F_θ` on `X` is outside the closure of the range
  have h := ae_notMem_closure_range_of_rank_lt hSard (evalBatch A S X) (evalBatch A' S' X)
    (analyticOnNhd_evalBatch_dcc A S hf hχ X) (analyticOnNhd_evalBatch_dcc A' S' hf' hχ' X)
    (hOmin n X) r₀ (fun η => hr₀ n X η) θ₀ (lt_of_lt_of_eq hθ₀ hX.symm) μ
  filter_upwards [h] with θ hθ
  -- a positive distance `δ` to every output of `G` on `X`
  obtain ⟨δ, hδ, hS⟩ := exists_pos_le_norm_sub_of_notMem_closure hθ
  refine ⟨δ, hδ, fun η => ?_⟩
  -- the norm on the batch is the largest norm of an output: some input `X i` attains `δ`
  exact exists_le_norm_apply_dcc hδ (hS _ ⟨η, rfl⟩)

/-- **Theorem A.28 (iv) of the skips paper for two families of networks, given Sard's theorem and
the property of definable sets:** for almost every `θ`, the network `F_θ` is not a pointwise limit
(Definition A.29) of the family `G`. -/
theorem ae_not_isPointwiseLimit_of_jacobianRank_lt
    (A : Arch T d L) (S : Fin L → Matrix d d ℝ) (A' : Arch T d' L') (S' : Fin L' → Matrix d' d' ℝ)
    (hSard : ∀ r : ℕ, SardCriticalValues (Params A' dIn dOut) (Fin r → ℝ))
    (hOmin : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      ClosureNullOfNull (Set.range (evalBatch (dOut := dOut) A' S' X)))
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (hf' : ∀ ℓ, AnalyticOnNhd ℝ (A'.f ℓ) Set.univ) (hχ' : AnalyticOnNhd ℝ A'.χ Set.univ)
    (r₀ : ℕ)
    (hr₀ : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ) (η : Params A' dIn dOut),
      jacobianRank A' S' X η ≤ r₀)
    (θ₀ : Params A dIn dOut) (hθ₀ : r₀ < funDim A S θ₀)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ¬ IsPointwiseLimit
      (Set.range (eval A' S' : Params A' dIn dOut → Matrix T dIn ℝ → Matrix T dOut ℝ))
      (eval A S θ) := by
  obtain ⟨n, X, h⟩ := exists_batch_ae_exists_pos_le_norm_sub_of_jacobianRank_lt A S A' S' hSard
    hOmin hf hχ hf' hχ' r₀ hr₀ θ₀ hθ₀ μ
  filter_upwards [h] with θ hθ
  obtain ⟨δ, hδ, hη⟩ := hθ
  -- every network of `G` is `δ`-far from `F_θ` at some input of the batch
  refine not_isPointwiseLimit_of_exists_pos X hδ ?_
  rintro _ ⟨η, rfl⟩
  obtain ⟨i, hi⟩ := hη η
  exact ⟨i, by rw [norm_sub_rev]; exact hi⟩

end Skips
