import SkipsLean.Depth.HiddenZero
import SkipsLean.Dimension.SubmersionNull
import SkipsLean.Dimension.Functional
import SkipsLean.Generic.Params

/-!
# The domain of the case (0): open, with a complement of measure zero, and the outputs analytic

Paper (dimension paper): Appendix D.6, Lemma D.20 (The domain). "In the case (0), let `X` be a
finite batch of nonzero inputs, and let `O_X ⊂ ℝ^P` be the set of parameters at which the hidden
states `h_0, …, h_L` of the network are nonzero for every `x ∈ X`. Then `O_X` is open and
connected, its complement has measure zero, and the outputs `F_X` on the batch are real-analytic
on `O_X`."

Its proof: "Let `O^0` be the set of parameters with `xE ≠ 0` for all `x ∈ X`, and for `ℓ ≥ 1` let
`O^ℓ` be the set of parameters in `O^{ℓ−1}` with `h_ℓ ≠ 0` for all `x ∈ X`. […] For tanh and GELU,
`σ(z) = 0` only at `z = 0`. […] Removing finitely many closed submanifolds of codimension at least
two, one after the other, from a connected open set leaves a connected open set and removes a set
of measure zero."

Stated here for networks of MLP blocks under pre-RMSNorm with `ε = 0` whose activation `σ` is
real-analytic and vanishes exactly at `0` (tanh and GELU are of this kind). `hiddenNonzero σ hid X k`
is the paper's `O^k`: no row of `h_0, …, h_k` vanishes at any input of the batch (a hidden state
has the rows `T`), and `O_X` is `O^L`. "Nonzero inputs": no row of an input vanishes. This file has
"open", "its complement has measure zero" and "the outputs are real-analytic"; "connected" is
`Depth/DomainZeroConnected.lean`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

/-- **The sets `O^k` of the proof of Lemma D.20:** the parameters at which no row of the hidden
states `h_0, …, h_k` vanishes, at every input of the batch `X`. The paper's `O_X` is `O^L`,
`hiddenNonzero σ hid X (Fin.last L)`. -/
def hiddenNonzero (σ : ℝ → ℝ) (hid : Fin L → Type) [∀ ℓ, Fintype (hid ℓ)] {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) (k : Fin (L + 1)) :
    Set (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :=
  {θ | ∀ (i : Fin n) (j : Fin (L + 1)), j ≤ k →
    ∀ t, hidden (Arch.mlp σ (rmsNorm 0) hid) 0 θ (X i) j t ≠ 0}

/-- **Lemma D.20, "`O_X` is open":** for a real-analytic `σ`, every `O^k` is open. -/
theorem isOpen_hiddenNonzero (hσa : AnalyticOnNhd ℝ σ Set.univ) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) (k : Fin (L + 1)) :
    IsOpen (hiddenNonzero σ hid X k :
      Set (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)) := by
  sorry

/-- **Lemma D.20, "its complement has measure zero":** let `σ` be real-analytic and vanish exactly
at `0`, `d ≥ 2`, every block with at least two hidden units, and no row of an input of the batch
zero. Then the complement of every `O^k` has measure zero. -/
theorem measure_compl_hiddenNonzero (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hσ0 : ∀ z : ℝ, σ z = 0 ↔ z = 0) (hd : 2 ≤ Fintype.card d)
    (hhid : ∀ ℓ, 2 ≤ Fintype.card (hid ℓ)) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i t, X i t ≠ 0)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (k : Fin (L + 1)) :
    μ (hiddenNonzero σ hid X k)ᶜ = 0 := by
  sorry

/-- **Lemma D.20, "the outputs `F_X` on the batch are real-analytic on `O_X`":** for a
real-analytic `σ`, the outputs on the batch `X` are real-analytic on `O^L`. -/
theorem analyticOnNhd_evalBatch_hiddenNonzero (hσa : AnalyticOnNhd ℝ σ Set.univ) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) :
    AnalyticOnNhd ℝ
      (evalBatch (Arch.mlp σ (rmsNorm 0) hid) 0 X :
        Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut →
          Fin n → Matrix T dOut ℝ)
      (hiddenNonzero σ hid X (Fin.last L)) := by
  sorry

end Skips
