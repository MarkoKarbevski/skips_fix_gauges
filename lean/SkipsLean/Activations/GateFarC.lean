import SkipsLean.Activations.GateFar
import SkipsLean.Activations.MillsCExpansion

/-!
# A gate far from zero, at complex arguments

Paper (dimension): proof of Lemma D.11, "One gate. Let `z ∈ ℂ` with `Re z ≥ 2` and
`|Im z| ≤ ½ Re z`, so that `Re(z²) ≥ ¾ (Re z)²` and `|z| ≤ 2 Re z`. For GELU, by Lemma D.8,
`σ(z) − z = −φ(z) z mr(z)` and `|z mr(z)| ≤ |z|/Re z ≤ 2`, so `|σ(z) − z| ≤ e^{−(3/8)(Re z)²}`.
For SiLU, `σ(z) − z = −z/(1 + e^z)` and `|1 + e^z| ≥ ½ e^{Re z}`, so
`|σ(z) − z| ≤ 4 Re z e^{−Re z}`. Both gates are holomorphic at `z` and at `−z`, and
`σ(−z) = σ(z) − z`. So there is a number `κ_1 > 0` such that, for large `Re z`,
`|σ(z) − z| ≤ e^{−κ_1 (Re z)^p}` and `|σ(−z)| ≤ e^{−κ_1 (Re z)^p}`. (31)"

`GateFarC σ p` is (31) for a gate `σ` on the reals: `σ` has an extension to complex arguments
that is holomorphic at `z` and at `−z` and satisfies the two bounds, for all `z` in the sector
`|Im z| ≤ ½ Re z` with `Re z ≥ R`. It holds for GELU with `p = 2` (the extension `geluC` of
`Activations/MillsC.lean`) and for SiLU with `p = 1` (the extension `z/(1 + e^{−z})`). It is not
a notion of the paper; `GateFar` (`Activations/GateFar.lean`) is its twin on the reals.
-/

namespace Skips

/-- **Equation (31):** the gate `σ` has an extension `σc` to complex arguments such that, for a
number `R` and a number `κ > 0`, at every `z` with `Re z ≥ R` and `|Im z| ≤ ½ Re z`, `σc` is
holomorphic at `z` and at `−z`, `|σc(z) − z| ≤ e^{−κ (Re z)^p}` and `|σc(−z)| ≤ e^{−κ (Re z)^p}`. -/
def GateFarC (σ : ℝ → ℝ) (p : ℕ) : Prop :=
  ∃ σc : ℂ → ℂ, (∀ x : ℝ, σc (x : ℂ) = ((σ x : ℝ) : ℂ)) ∧ ∃ R κ : ℝ, 0 < κ ∧
    ∀ z : ℂ, R ≤ z.re → |z.im| ≤ z.re / 2 →
      AnalyticAt ℂ σc z ∧ AnalyticAt ℂ σc (-z) ∧
        ‖σc z - z‖ ≤ Real.exp (-(κ * z.re ^ p)) ∧ ‖σc (-z)‖ ≤ Real.exp (-(κ * z.re ^ p))

/-- **Equation (31) for GELU,** with `p = 2`. -/
theorem gateFarC_gelu : GateFarC gelu 2 := by
  sorry

/-- **Equation (31) for SiLU,** with `p = 1`. -/
theorem gateFarC_silu : GateFarC silu 1 := by
  sorry

end Skips
