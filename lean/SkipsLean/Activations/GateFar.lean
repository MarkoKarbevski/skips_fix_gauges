import SkipsLean.Activations.FarFromZero
import SkipsLean.Activations.Analytic

/-!
# A gate far from zero: what the proofs on rays use of GELU and SiLU

Paper (dimension): Appendix D.5, "A gate on a ray", equations (24) and (25), and the proof of
Lemma D.12, "One small factor".

The proofs on rays use the gate `σ` of a gated block (GELU for GeGLU, SiLU for SwiGLU) only through
a few properties, with `δ(y) = y − σ(y)`, `δ'(y) = 1 − σ'(y)` and `p = 2` for GELU, `p = 1` for
SiLU:

* `σ` is real-analytic with the derivative `σ'`;
* (24): `σ(−y) = −δ(y)` and `σ'(−y) = δ'(y)`;
* (25): for `y ≥ 2`, `e^{−y^p/p}/6 ≤ δ(y) ≤ y e^{−y^p/p}` and `|δ'(y)| ≤ 4 y δ(y)`;
* `y |δ'(y)| / δ(y) → ∞` as `y → ∞`. (For GELU, `δ'(y)/δ(y) = (mr(y) − y)/(y mr(y))` and
  `y mr(y) ≤ 1`; for SiLU, `y δ'(y)/δ(y) = 1 − y + δ(y)`: both are in "One small factor".)

`GateFar σ σ' p` collects them, so that the statements on rays are written once for both gates. It
is not a notion of the paper.
-/

namespace Skips

open Filter Topology

/-- What the proofs on rays use of a gate `σ` with the derivative `σ'` and the exponent `p`:
(24), (25) and `y |δ'(y)| / δ(y) → ∞`, for `δ(y) = y − σ(y)`. -/
structure GateFar (σ σ' : ℝ → ℝ) (p : ℕ) : Prop where
  one_le : 1 ≤ p
  analytic : AnalyticOnNhd ℝ σ Set.univ
  hasDerivAt : ∀ z, HasDerivAt σ (σ' z) z
  /-- equation (24) -/
  neg : ∀ y, σ (-y) = -(y - σ y) ∧ σ' (-y) = 1 - σ' y
  /-- equation (25) -/
  gap : ∀ y, 2 ≤ y →
    1 / 6 * Real.exp (-(y ^ p / (p : ℝ))) ≤ y - σ y ∧
      y - σ y ≤ y * Real.exp (-(y ^ p / (p : ℝ))) ∧ |1 - σ' y| ≤ 4 * y * (y - σ y)
  ratio : Tendsto (fun y : ℝ => y * |1 - σ' y| / (y - σ y)) atTop atTop

/-- SiLU, the gate of SwiGLU, with `p = 1`. -/
theorem gateFar_silu : GateFar silu siluDeriv 1 := by
  sorry

/-- GELU, the gate of GeGLU, with `p = 2`. -/
theorem gateFar_gelu : GateFar gelu geluDeriv 2 := by
  sorry

end Skips
