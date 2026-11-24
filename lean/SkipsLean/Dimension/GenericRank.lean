import SkipsLean.Dimension.Functional
import SkipsLean.Generic.Params
import SkipsLean.Network.Analytic

/-!
# From the rank at one parameter to generic parameters

Paper (dimension): Appendix D.7, "The parts together", the paragraph on GELU blocks in the case (+)
and gated blocks in the cases (n) and (+). "By Proposition D.4, the Jacobian at `θ†` has the rank
(13) on some finite batch `X`. In the cases (n) and (+) the outputs on `X` are real-analytic in
`θ ∈ ℝ^P`, and so are the minors of the Jacobian. A minor of the size (13) does not vanish at `θ†`,
so it vanishes only on a set of measure zero. At generic parameters the Jacobian on `X` therefore
has at least the rank (13)".

Stated here for every network whose fixed maps `f_ℓ` and `χ` are real-analytic (the cases (n),
`χ = id`, and (+), `χ` RMSNorm with `ε > 0`), for all stream matrices (with or without skips), and
for every batch and every parameter `θ₀`: at generic parameters the rank of the Jacobian on the
batch is at least its rank at `θ₀`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [Fintype dIn] [Fintype dOut]

/-- The output of a network with real-analytic maps `f_ℓ` and `χ` at a fixed input is a
real-analytic function of the parameters, for all stream matrices. -/
theorem analyticOnNhd_eval_params (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (x : Matrix T dIn ℝ) :
    AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => eval A S θ x) Set.univ := by
  sorry

/-- **The generic rank is the largest rank** (Appendix D.7). For a network with real-analytic maps
`f_ℓ` and `χ`, a batch `X` and a parameter `θ₀`: at generic parameters the Jacobian on `X` has at
least the rank that it has at `θ₀`. -/
theorem ae_jacobianRank_ge (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (θ₀ : Params A dIn dOut) :
    ∀ᵐ θ ∂μ, jacobianRank A S X θ₀ ≤ jacobianRank A S X θ := by
  sorry

/-- At generic parameters the functional dimension is at least the rank of the Jacobian on any
batch at any one parameter. -/
theorem ae_jacobianRank_le_funDim (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (θ₀ : Params A dIn dOut) :
    ∀ᵐ θ ∂μ, jacobianRank A S X θ₀ ≤ funDim A S θ := by
  sorry

/-- At generic parameters the functional dimension is at least the functional dimension at any one
parameter: `fd(θ₀) ≤ fd(θ)` for almost every `θ`. -/
theorem ae_funDim_ge (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] (θ₀ : Params A dIn dOut) :
    ∀ᵐ θ ∂μ, funDim A S θ₀ ≤ funDim A S θ := by
  sorry

end Skips
