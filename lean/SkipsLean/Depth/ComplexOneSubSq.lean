import SkipsLean.Depth.SuffixRows
import SkipsLean.Depth.ComplexBlockIdentity

/-!
# Lemma D.17 for a complex row `b`

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), Lemma D.17 (A change of the reads moves
the output). "In the case (0), let `θ` be regular with (S1) for block `k + 1`, let
`V = W_write^{k+1}` have the rows `a_1, …, a_q`, and let `b ∈ ℂ^{1×q}`. If

  `𝐃𝓑_{>k+1}(w̃V) (((1 − w̃²) ⊙ b) V) = 0`

for all `w̃` in a nonempty open subset of `ℝ^{1×q}`, where `1 − w̃²` is the row with the entries
`1 − w̃_j²`, then `b = 0`."

Its proof begins: "At real `w̃` the derivative is a real linear map, so the real and the imaginary
part of `b` satisfy the hypothesis: let `b` be real." The case of a real `b` is
`eq_zero_of_fderiv_suffix_one_sub_sq_zero` (`Depth/StepZeroValues.lean`).

Here `𝐃𝓑_{>k+1}` at the complex direction `((1 − w̃²) ⊙ b) V` is the complex derivative of
`suffixC σC` (`Depth/ComplexSuffix.lean`), for a map `σC` that extends the activation and a cone
`C_κ` on which `𝓑_{>k+1}` is holomorphic. The paper's rows `w̃` and `b` are rows `hid k → ℝ` and
`hid k → ℂ`, and the hidden state has the same row `w̃V` at every token. Numbering as in
`Depth/StepTanh.lean`: the block is `k : Fin L`, the paper's block `k + 1`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {σC : ℂ → ℂ}

/-- **Lemma D.17 of the dimension paper (a change of the reads moves the output).** In the case
(0), let the blocks be real-analytic MLP blocks whose activation is extended by `σC`, `d ≥ 2`, `θ`
regular, any two rows of the write `V` of block `k` linearly independent (S1), and `𝓑_{>k+1}`
holomorphic on a cone `C_κ`. For a complex row `b`: if `𝐃𝓑(w̃ V)(((1 − w̃²) ⊙ b) V) = 0` for all
real rows `w̃` in a nonempty open set, then `b = 0`. -/
theorem eq_zero_of_fderiv_suffixC_one_sub_sq [Nonempty T] (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hσ : ∀ x : ℝ, σC (x : ℂ) = ((σ x : ℝ) : ℂ))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d) (k : Fin L)
    (hS1 : ∀ i j : hid k, i ≠ j → ∀ a c : ℝ, a • θ.write k i + c • θ.write k j = 0 →
      a = 0 ∧ c = 0)
    {κ : ℝ} (hκ : 0 < κ) (hhol : HolomorphicOnCone σC θ k.succ κ)
    (b : hid k → ℂ) (O : Set (hid k → ℝ)) (hO : IsOpen O) (hne : O.Nonempty)
    (h : ∀ r ∈ O,
      fderiv ℂ (fun h' : Matrix T d ℂ => suffixC σC θ.toC k.succ h')
        ((Matrix.of fun (_ : T) (j : hid k) => (r j : ℂ)) * θ.toC.2.1 k)
        ((Matrix.of fun (_ : T) (j : hid k) => (1 - (r j : ℂ) ^ 2) * b j) * θ.toC.2.1 k) = 0) :
    b = 0 := by
  sorry

end Skips
