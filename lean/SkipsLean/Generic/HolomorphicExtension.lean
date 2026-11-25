import SkipsLean.Imports
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Normed

/-!
# A real-analytic map extends to a holomorphic map on a complex neighbourhood

Paper (dimension paper), proof of Lemma D.10: "So `𝓑_{>k}(t (h° + u))` is a real-analytic function
of `(1/t, u)` near `(0, 0)`. It extends to a holomorphic and bounded function on a complex
neighborhood of `(0, 0)`, which gives `ϱ` and `t_0`."

This is a known fact (the power series of the map at the point, with complex arguments).
Mathlib does not have it at the pinned version (searched for `complexif`, for `ofReal` with
`AnalyticAt`, and for `baseChange` under `Analysis/Analytic`; it has the converse, the restriction
of a holomorphic map to the reals, `AnalyticAt.re_ofReal`), so it is proved here, for maps between
spaces of real tuples:

* `exists_analyticOnNhd_complex_extension`: a map `f : ℝ^ι → ℝ^κ` that is real-analytic at `x`
  agrees on a ball around `x` with a map `g : ℂ^ι → ℂ^κ` that is holomorphic on the ball of the
  same radius around `x`;
* `exists_holomorphic_extension_real_param`: the step of the paper, for a map `F(s, h)` of a real
  number and a real matrix that is real-analytic at `(0, H)`: there are `ϱ, s₀ > 0` and a bound
  `C` such that for every real `s` with `|s| ≤ s₀` the map `u ↦ F(s, H + u)` extends to a
  holomorphic map on the complex matrices `u` with `|u_{τ j}| ≤ ϱ` for all entries, bounded by `C`
  there. ("Holomorphic on" a closed set is `AnalyticOnNhd ℂ`: holomorphic near each of its
  points.)
-/

namespace Skips

open scoped Matrix.Norms.Elementwise Topology

/-- **A real-analytic map extends to a holomorphic map:** if `f : ℝ^ι → ℝ^κ` is real-analytic at
`x`, there are a radius `r > 0` and a map `g : ℂ^ι → ℂ^κ`, holomorphic on the ball of radius `r`
around `x`, with `g(y) = f(y)` at the real points `y` of the ball of radius `r` around `x`. -/
theorem exists_analyticOnNhd_complex_extension {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : (ι → ℝ) → (κ → ℝ)} {x : ι → ℝ} (hf : AnalyticAt ℝ f x) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : (ι → ℂ) → (κ → ℂ),
      AnalyticOnNhd ℂ g (Metric.ball (fun i => (x i : ℂ)) r)
      ∧ ∀ y ∈ Metric.ball x r, g (fun i => (y i : ℂ)) = fun j => (f y j : ℂ) := by
  sorry

/-- **Proof of Lemma D.10, "It extends to a holomorphic and bounded function on a complex
neighborhood of `(0, 0)`, which gives `ϱ` and `t_0`":** if `F(s, h)` is real-analytic at
`(0, H)`, there are `ϱ, s₀ > 0` and `C` such that, for every real `s` with `|s| ≤ s₀`, the map
`u ↦ F(s, H + u)` extends to a holomorphic map on the complex matrices `u` with
`|u_{τ j}| ≤ ϱ`, bounded by `C`. -/
theorem exists_holomorphic_extension_real_param {T d T' d' : Type*} [Fintype T] [Fintype d]
    [Fintype T'] [Fintype d'] {F : ℝ × Matrix T d ℝ → Matrix T' d' ℝ} {H : Matrix T d ℝ}
    (hF : AnalyticAt ℝ F (0, H)) :
    ∃ ϱ : ℝ, 0 < ϱ ∧ ∃ s₀ : ℝ, 0 < s₀ ∧ ∃ C : ℝ, ∀ s : ℝ, |s| ≤ s₀ →
      ∃ G : Matrix T d ℂ → Matrix T' d' ℂ,
        AnalyticOnNhd ℂ G {u | ∀ τ j, ‖u τ j‖ ≤ ϱ}
        ∧ (∀ u : Matrix T d ℝ, (∀ τ j, |u τ j| ≤ ϱ) →
            G (u.map fun a : ℝ => (a : ℂ)) = (F (s, H + u)).map fun a : ℝ => (a : ℂ))
        ∧ ∀ u : Matrix T d ℂ, (∀ τ j, ‖u τ j‖ ≤ ϱ) → ‖G u‖ ≤ C := by
  sorry

end Skips
