import SkipsLean.Residual.SmallParameter
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The rank of a Jacobian along a small parameter, for a map that is smooth near one point

Paper (skips paper): proof of Lemma A.30 (ReLU-type blocks with small writes): "We follow the
proof of Lemma A.27 […]. With the writes `τ V_ℓ`, the pre-activations of block `ℓ` are
`h_{ℓ−1} W_read^ℓ` with `h_{ℓ−1} = x E + O(τ)`. So for `|τ|` below some `τ_0 > 0`, which depends
on the parameters and on the batch, every pre-activation on the batch has the sign of its limit.
The outputs on the batch are then polynomial in the parameters and in `τ`, the Jacobian on the
batch, with its read columns divided by `τ`, tends to `J_0`, and by lower semicontinuity it has
rank at least `P − d_model² − s` for all small `τ ≠ 0`."

So the step "The rank" of Lemma A.27 (`Residual/SmallParameter.lean`,
`eventually_finrank_le_of_small_parameter`) is used for a map `G τ θ` that is twice continuously
differentiable only near `(0, θ)`. This file states that form. The hypotheses and the conclusion
are those of `eventually_finrank_le_of_small_parameter`; they involve `G` only near `(0, θ)`.
-/

namespace Skips

open Filter Topology

variable {P Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

omit [FiniteDimensional ℝ Y] in
/-- A cutoff: a map `G̃` that is `C²` everywhere and equals `G` on `(−δ, δ) × ball θ δ`. -/
private theorem exists_cutoff_spo (G : ℝ → P → Y) (θ : P)
    (U : Set (ℝ × P)) (hU : U ∈ 𝓝 ((0 : ℝ), θ))
    (hG : ContDiffOn ℝ 2 (fun p : ℝ × P => G p.1 p.2) U) :
    ∃ G' : ℝ → P → Y, ∃ δ > 0, ContDiff ℝ 2 (fun p : ℝ × P => G' p.1 p.2) ∧
      ∀ τ θ', |τ| < δ → dist θ' θ < δ → G' τ θ' = G τ θ' := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  set c : ℝ × P := ((0 : ℝ), θ)
  -- the bump: `1` on the closed ball of radius `r / 4`, `0` outside the ball of radius `r / 2`
  let φ : ContDiffBump c := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨fun τ θ' => φ (τ, θ') • G τ θ', r / 4, by positivity, ?_, ?_⟩
  · -- smooth on the ball of radius `r` (inside `U`), and zero outside the closed ball `r / 2`
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : dist p c < r
    · have h1 : ContDiffOn ℝ 2 (fun p : ℝ × P => φ p • G p.1 p.2) (Metric.ball c r) :=
        (φ.contDiff.contDiffOn).smul (hG.mono hrU)
      exact h1.contDiffAt (Metric.isOpen_ball.mem_nhds hp)
    · push Not at hp
      have h2 : (fun _ : ℝ × P => (0 : Y)) =ᶠ[𝓝 p] (fun q : ℝ × P => φ (q.1, q.2) • G q.1 q.2) := by
        have hopen : IsOpen {q : ℝ × P | r / 2 < dist q c} :=
          isOpen_lt continuous_const (continuous_id.dist continuous_const)
        filter_upwards [hopen.mem_nhds (show r / 2 < dist p c by linarith)] with q hq
        have hq' : φ (q.1, q.2) = 0 := φ.zero_of_le_dist (le_of_lt hq)
        rw [hq', zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq h2.symm
  · intro τ θ' hτ hθ'
    have hmem : ((τ, θ') : ℝ × P) ∈ Metric.closedBall c φ.rIn := by
      rw [Metric.mem_closedBall, Prod.dist_eq]
      simp only [c, Real.dist_eq, sub_zero]
      exact max_le hτ.le hθ'.le
    show φ (τ, θ') • G τ θ' = G τ θ'
    rw [φ.one_of_mem_closedBall hmem, one_smul]

/-- **Proof of Lemma A.27, "The rank", as the proof of Lemma A.30 uses it:** the statement of
`eventually_finrank_le_of_small_parameter` for a map `G` that is twice continuously differentiable
on a neighborhood `U` of `(0, θ)`. -/
theorem eventually_finrank_le_of_small_parameter_of_contDiffOn (G : ℝ → P → Y) (θ : P)
    (U : Set (ℝ × P)) (hU : U ∈ 𝓝 ((0 : ℝ), θ))
    (hG : ContDiffOn ℝ 2 (fun p : ℝ × P => G p.1 p.2) U) (π : P →L[ℝ] P)
    (h0 : ∀ η, fderiv ℝ (G 0) θ (π η) = 0) (V : Submodule ℝ P)
    (hV : ∀ η, fderiv ℝ (G 0) θ (η - π η)
        + fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ (π η) = 0 → η ∈ V) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      Module.finrank ℝ P
        ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ (G τ) θ).toLinearMap)
          + Module.finrank ℝ V := by
  -- the cutoff `G'`, smooth everywhere and equal to `G` near `(0, θ)`
  obtain ⟨G', δ, hδ, hG', hGG'⟩ := exists_cutoff_spo G θ U hU hG
  -- for `|τ| < δ`, the derivatives in `θ` at `θ` agree
  have hD : ∀ τ : ℝ, |τ| < δ → fderiv ℝ (G' τ) θ = fderiv ℝ (G τ) θ := by
    intro τ hτ
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [Metric.ball_mem_nhds θ hδ] with θ' hθ'
    exact hGG' τ θ' hτ hθ'
  -- the derivatives in `τ` at `0` agree near `θ`, so do their derivatives in `θ`
  have hT : fderiv ℝ (fun θ' => deriv (fun τ => G' τ θ') 0) θ
      = fderiv ℝ (fun θ' => deriv (fun τ => G τ θ') 0) θ := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [Metric.ball_mem_nhds θ hδ] with θ' hθ'
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with τ hτ
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hτ
    exact hGG' τ θ' hτ hθ'
  have hD0 := hD 0 (by rw [abs_zero]; exact hδ)
  have h0' : ∀ η, fderiv ℝ (G' 0) θ (π η) = 0 := by
    intro η; rw [hD0]; exact h0 η
  have hV' : ∀ η, fderiv ℝ (G' 0) θ (η - π η)
      + fderiv ℝ (fun θ' => deriv (fun τ => G' τ θ') 0) θ (π η) = 0 → η ∈ V := by
    intro η; rw [hD0, hT]; exact hV η
  -- the global statement for `G'`, and `fderiv ℝ (G' τ) θ = fderiv ℝ (G τ) θ` for small `τ`
  filter_upwards [eventually_finrank_le_of_small_parameter G' hG' π θ h0' V hV',
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hδ)] with τ hτ hτδ
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hτδ
  rwa [← hD τ hτδ]

end Skips
