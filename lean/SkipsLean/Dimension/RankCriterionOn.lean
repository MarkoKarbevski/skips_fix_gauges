import SkipsLean.Dimension.RankCriterion

/-!
# A rank criterion on an open set, against countably many maps

Paper (absorb paper): proof of Proposition 4.7, Step 4: "By the constant rank theorem, after
shrinking `V`, `F_Z` maps `V` onto an embedded manifold `Y` of dimension `r`, and a linear
projection `pr` onto `ℝ^r` maps `Y` diffeomorphically onto an open set. Let
`n < L d_model² / (2 d_model − 1)`, so that every map `F'^π_Z` of a skipless network with `n` more
units has rank less than `r`. Then all values of `pr ∘ F'^π_Z` are critical, and by Sard's theorem
its image is a null set of `ℝ^r`. If the residual network with weights `θ ∈ V` equals a skipless
network with weights `η`, then `F_Z(θ) = F'^π_Z(η)` for the pattern `π` of `η`, so `pr(F_Z(θ))`
lies in this null set. As `pr ∘ F_Z` is a submersion on `V`, such `θ` form a null set. There are
finitely many `n` below the bound, finitely many choices of widths with `n` more units and
finitely many patterns on `Z`".

This is Lemma A.26 (i) of the skips paper (`ae_notMem_range_of_rank_lt`,
`Dimension/RankCriterion.lean`) in a local form: the map `F` is continuously differentiable on an
open set `U` only, the maps `G i` are countably many real-analytic maps on spaces that may
differ, and the conclusion holds at almost every point of `U`. Sard's theorem is the hypothesis
from the literature `SardCriticalValues` (`Literature/Sard.lean`). No constant rank theorem is
used: near a point of `U`, a linear `π` onto `ℝ^r` makes `π ∘ F` a submersion
(`measure_inter_preimage_eq_zero_of_surjective_fderiv`, `Dimension/SubmersionNull.lean`).
-/

namespace Skips

open MeasureTheory

variable {P Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y]

/-- **Proof of Proposition 4.7 of the absorb paper, Step 4, without networks, given Sard's
theorem:** let `F` be continuously differentiable on the open set `U`, with a Jacobian of rank
greater than `r₀` at every point of `U`, and let `G i`, for `i` in a countable set, be
real-analytic maps whose Jacobians have rank at most `r₀` everywhere. Then for almost every
`θ ∈ U` the value `F θ` is a value of no `G i`. -/
theorem ae_notMem_iUnion_range_of_rank_lt_on {ι : Type*} [Countable ι] {P' : ι → Type*}
    [∀ i, NormedAddCommGroup (P' i)] [∀ i, NormedSpace ℝ (P' i)]
    [∀ i, FiniteDimensional ℝ (P' i)]
    (hSard : ∀ (i : ι) (r : ℕ), SardCriticalValues (P' i) (Fin r → ℝ))
    (F : P → Y) (U : Set P) (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U)
    (G : ∀ i, P' i → Y) (hG : ∀ i, AnalyticOnNhd ℝ (G i) Set.univ) (r₀ : ℕ)
    (hGr : ∀ i η, Module.finrank ℝ (LinearMap.range (fderiv ℝ (G i) η).toLinearMap) ≤ r₀)
    (hFr : ∀ θ ∈ U, r₀ < Module.finrank ℝ (LinearMap.range (fderiv ℝ F θ).toLinearMap))
    (μ : Measure P) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, θ ∈ U → ∀ i, F θ ∉ Set.range (G i) := by
  sorry

end Skips
