import SkipsLean.Generic.AnalyticZeroSetOn
import SkipsLean.Dimension.GenericRank

/-!
# From the rank at one parameter to generic parameters, on a connected open set

Paper (dimension paper): Appendix D.7, "The parts together", the case (0): "By Proposition D.4
there is a finite batch `X*`, with `xE ≠ 0` for all its inputs, on which the Jacobian at `θ*` has
the rank (13). By (R2), `θ* ∈ O_{X*}`. The sum of the squares of the minors of this size of the
Jacobian of `F_{X*}` is real-analytic on the connected open set `O_{X*}` and does not vanish at
`θ*`, so its zero set has measure zero, and so has the complement of `O_{X*}` (Lemma D.20). Hence
the rank on `X*` is at least (13) at almost every parameter."

Stated here for any map `G` that is real-analytic on a connected open set `U` whose complement has
measure zero: at almost every point the rank of the derivative of `G` is at least its rank at any
given point of `U`; and for the outputs of a network on a batch. (`Dimension/GenericRank.lean` has
the case `U` the whole space.)
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut]

/-- **The generic rank on a connected open set:** let `G` be real-analytic on a connected open set
`U` whose complement has measure zero. Then at almost every `x` the rank of the derivative of `G`
is at least its rank at `x₀ ∈ U`. -/
theorem ae_finrank_range_fderiv_ge_of_isPreconnected
    {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set X} (hU : IsOpen U) (hUc : IsPreconnected U) (hUnull : μ Uᶜ = 0)
    {G : X → F} (hG : AnalyticOnNhd ℝ G U) {x₀ : X} (hx₀ : x₀ ∈ U) :
    ∀ᵐ x ∂μ, Module.finrank ℝ (LinearMap.range (fderiv ℝ G x₀).toLinearMap) ≤
      Module.finrank ℝ (LinearMap.range (fderiv ℝ G x).toLinearMap) := by
  sorry

/-- **Appendix D.7, the case (0), "Hence the rank on `X*` is at least (13) at almost every
parameter":** if the outputs of a network on the batch `X` are real-analytic on a connected open
set `U` of parameters whose complement has measure zero, then at almost every parameter the rank
of the Jacobian on `X` is at least its rank at `θ₀ ∈ U`. -/
theorem ae_jacobianRank_ge_of_isPreconnected (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) {U : Set (Params A dIn dOut)} (hU : IsOpen U)
    (hUc : IsPreconnected U) (hUnull : μ Uᶜ = 0)
    (hG : AnalyticOnNhd ℝ (evalBatch A S X : Params A dIn dOut → Fin n → Matrix T dOut ℝ) U)
    {θ₀ : Params A dIn dOut} (hθ₀ : θ₀ ∈ U) :
    ∀ᵐ θ ∂μ, jacobianRank A S X θ₀ ≤ jacobianRank A S X θ := by
  sorry

end Skips
