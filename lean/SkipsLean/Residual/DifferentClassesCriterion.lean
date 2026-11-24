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

variable {T d d' dIn dOut : Type*} {L L' : ℕ} [Fintype T] [Fintype d] [DecidableEq d]
  [Fintype d'] [DecidableEq d'] [Fintype dIn] [Fintype dOut]

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end Skips
