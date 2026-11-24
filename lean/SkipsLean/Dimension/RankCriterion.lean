import SkipsLean.Literature.Sard
import SkipsLean.Literature.OMinimal
import SkipsLean.Dimension.SubmersionNull

/-!
# A rank criterion

Paper (skips paper): Lemma A.26 (A rank criterion), without networks. Two parametrized families
are given by their outputs on a finite batch, `F : P → Y` and `G : P' → Y`, real-analytic in the
parameters. In the paper the rank of the Jacobian of `G` is at most `r₀ = P' - k` at every
parameter because a Lie group acts on the parameters of `G` with orbits of dimension at least `k`
(at generic parameters, then everywhere, the rank being lower semicontinuous); here the bound
`rank DG ≤ r₀` at every point is the hypothesis. The rank of the Jacobian of `F` exceeds `r₀` at
one parameter `θ₀`.

(i) For almost every `θ`, `F θ` is not an output of the family `G`.
(ii) If the set of outputs of `G` has the property of definable sets used in the paper
(`ClosureNullOfNull`), then for almost every `θ`, `F θ` is not in the closure of the outputs of
`G`: some `δ > 0` separates it from all of them.

The Lean route follows the paper's proof, without the constant rank theorem: at a `θ` where the
Jacobian of `F` has its largest rank `r*`, a linear `π : Y → ℝ^{r*}` is chosen with `π ∘ DF(θ)`
onto; `π ∘ F` is a submersion near `θ`; `π ∘ G` has rank less than `r*` everywhere, "so all its
values are critical, and by Sard's theorem its image has measure zero"; the preimage of this image
under `π ∘ F` has measure zero near `θ` (`Dimension/SubmersionNull.lean`); countably many
neighbourhoods cover the set where the rank is `r*`, whose complement has measure zero (analytic
minors). Sard's theorem is a hypothesis from the literature (`Literature/Sard.lean`).
-/

namespace Skips

open MeasureTheory

variable {P P' Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P] [NormedAddCommGroup P'] [NormedSpace ℝ P']
  [FiniteDimensional ℝ P'] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- **Lemma A.26 (i) of the skips paper, without networks, given Sard's theorem:** if the
Jacobian of `G` has rank at most `r₀` at every parameter and the Jacobian of `F` has rank greater
than `r₀` at one parameter, then for almost every `θ` the output `F θ` is not an output of `G`. -/
theorem ae_notMem_range_of_rank_lt (hSard : ∀ r : ℕ, SardCriticalValues P' (Fin r → ℝ))
    (F : P → Y) (G : P' → Y) (hF : AnalyticOnNhd ℝ F Set.univ) (hG : AnalyticOnNhd ℝ G Set.univ)
    (r₀ : ℕ)
    (hGr : ∀ η, Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap) ≤ r₀)
    (θ₀ : P) (hθ₀ : r₀ < Module.finrank ℝ (LinearMap.range (fderiv ℝ F θ₀).toLinearMap))
    (μ : Measure P) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, F θ ∉ Set.range G := by
  sorry

/-- **Lemma A.26 (ii) of the skips paper, without networks, given Sard's theorem and the
property of definable sets:** under the same hypotheses, if the set of outputs of `G` satisfies
`ClosureNullOfNull`, then for almost every `θ` the output `F θ` is not in the closure of the set of
outputs of `G`. -/
theorem ae_notMem_closure_range_of_rank_lt (hSard : ∀ r : ℕ, SardCriticalValues P' (Fin r → ℝ))
    (F : P → Y) (G : P' → Y) (hF : AnalyticOnNhd ℝ F Set.univ) (hG : AnalyticOnNhd ℝ G Set.univ)
    (hcl : ClosureNullOfNull (Set.range G)) (r₀ : ℕ)
    (hGr : ∀ η, Module.finrank ℝ (LinearMap.range (fderiv ℝ G η).toLinearMap) ≤ r₀)
    (θ₀ : P) (hθ₀ : r₀ < Module.finrank ℝ (LinearMap.range (fderiv ℝ F θ₀).toLinearMap))
    (μ : Measure P) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, F θ ∉ closure (Set.range G) := by
  sorry

/-- The conclusion of Lemma A.26 (ii) in the paper's words: a point outside the closure of a set
has a positive distance `δ` to every point of the set. -/
theorem exists_pos_le_norm_sub_of_notMem_closure {y : Y} {S : Set Y} (h : y ∉ closure S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ S, δ ≤ ‖y - z‖ := by
  sorry

end Skips
