import SkipsLean.Dimension.GenericRank
import SkipsLean.Generic.Params

/-!
# Skipless networks: the bound of Theorem 4.2 at every parameter

Paper (skips paper): proof of Theorem A.28 (iii), "its changes of basis at `h_0, …, h_L` have
orbits of dimension `(L + 1) d_model²` at generic parameters (Lemma A.18)", with the proof of
Lemma A.26, "the rank is lower semicontinuous, so the bound holds at every `η`". For a skipless
network of real-analytic blocks whose writes have at least `d` rows (MLP blocks of at least `d`
hidden units), the Jacobian of the outputs on every batch has rank at most `P - (L + 1) d²` at
EVERY parameter; under pre-RMSNorm with `ε > 0`, at most `P - (L + 1) d (d - 1)/2`.

The bounds on the functional dimension at generic parameters are `ae_funDim_add_le_skipless` and
`ae_funDim_add_le_skipless_rmsNorm` (`Generic/Params.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {A : Arch T d L}

/-- **The bound of Theorem 4.2 without skips at every parameter, on every batch, without
normalization:** for real-analytic blocks whose writes have at least `d` rows and `d_in ≥ d`, the
Jacobian of the outputs of a skipless network on a batch has rank at most `P - (L + 1) d²` at
every parameter. -/
theorem jacobianRank_add_le_skipless_all (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) (θ : Params A dIn dOut) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank A 0 X θ + (L + 1) * Fintype.card d ^ 2
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **The same under pre-RMSNorm with `ε > 0`:** the Jacobian of the outputs of a skipless network
on a batch has rank at most `P - (L + 1) d (d - 1)/2` at every parameter. -/
theorem jacobianRank_add_le_skipless_all_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) (θ : Params A dIn dOut) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank A 0 X θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end Skips
