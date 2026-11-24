import SkipsLean.Depth.DomainZero
import SkipsLean.Generic.ConnectedCompl

/-!
# The domain of the case (0) is connected

Paper (dimension paper): Appendix D.6, Lemma D.20 (The domain), "`O_X` is open and connected".

Its proof: "The complement of `O^0` is a finite union of subspaces of codimension `d_model ≥ 2`.
Let `ℓ ≥ 1` and `x ∈ X`. On `O^{ℓ−1}`, `h_ℓ = w̃_ℓ W_write^ℓ` with
`w̃_ℓ = σ(N(h_{ℓ−1}) W_read^ℓ)`, and `h_{ℓ−1}` does not depend on the weights of block `ℓ`. For tanh
and GELU, `σ(z) = 0` only at `z = 0`. So `w̃_ℓ = 0` exactly where `N(h_{ℓ−1}) W_read^ℓ = 0`, a
closed submanifold of `O^{ℓ−1}` of codimension at least `d_model ≥ 2`, because the derivative with
respect to `W_read^ℓ` is onto. Where `w̃_ℓ ≠ 0`, the derivative of `h_ℓ` with respect to `W_write^ℓ`
is onto `ℝ^{1×d_model}`, so there the parameters with `h_ℓ = 0` form a closed submanifold of
codimension `d_model ≥ 2`. Removing finitely many closed submanifolds of codimension at least two,
one after the other, from a connected open set leaves a connected open set".

`hiddenNonzero σ hid X k` (`Depth/DomainZero.lean`) is the paper's `O^k`. One removal is
`isPreconnected_diff_zeroSet_of_surjective` (`Generic/ConnectedCompl.lean`); the codimensions here
are the number of hidden units of the block (at least two) and `d ≥ 2`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

/-- **Lemma D.20, "`O_X` is connected", the sets `O^k`:** let `σ` be real-analytic and vanish
exactly at `0`, `d ≥ 2`, every block with at least two hidden units, and no row of an input of the
batch zero. Then every `O^k` is preconnected. -/
theorem isPreconnected_hiddenNonzero (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hσ0 : ∀ z : ℝ, σ z = 0 ↔ z = 0) (hd : 2 ≤ Fintype.card d)
    (hhid : ∀ ℓ, 2 ≤ Fintype.card (hid ℓ)) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i t, X i t ≠ 0) (k : Fin (L + 1)) :
    IsPreconnected (hiddenNonzero σ hid X k :
      Set (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)) := by
  sorry

/-- **Lemma D.20 of the dimension paper, "`O_X` is open and connected":** under the same
hypotheses `O_X = O^L` is connected (preconnected, and not empty: its complement has measure
zero). -/
theorem isConnected_hiddenNonzero (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hσ0 : ∀ z : ℝ, σ z = 0 ↔ z = 0) (hd : 2 ≤ Fintype.card d)
    (hhid : ∀ ℓ, 2 ≤ Fintype.card (hid ℓ)) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i t, X i t ≠ 0) :
    IsConnected (hiddenNonzero σ hid X (Fin.last L) :
      Set (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)) := by
  sorry

end Skips
