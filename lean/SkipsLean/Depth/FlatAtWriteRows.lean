import SkipsLean.Depth.SuffixRows

/-!
# From an open set of rows to all hidden states: the last part of the step on the path

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), proof of Lemma D.18, part (c):
"`𝐃𝓑(w̃V)(w̃ η_V) + 𝐃_θ𝓑(w̃V) η' = 0` for real `w̃` near `s̄`. The left side is real-analytic on the
rows `w̃ ∈ ℝ^{1×q}` with `w̃V ≠ 0`. These form a connected set, the complement of a subspace of
codimension `d_model ≥ 2`, so the identity holds on all of it."

Here `V` is the write of block `k : Fin L` (the paper's block `k + 1`), `𝓑 = 𝓑_{>k+1}` is
`suffix … k.succ`, and a hidden state has the rows `T`. The hypothesis is the identity at the
hidden states with the same row `w̃V` at every token, for `w̃` in a nonempty open set of rows; the
conclusion is the identity at every `w` such that `wV` has no zero row, the hypothesis of Lemma D.3
(`suffixFlatZero_of_flat_at_write`, `Depth/SuffixZeroClaim.lean`). The passage from one row to all
tokens is `Depth/SuffixRows.lean`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

/-- **Proof of Lemma D.18, part (c):** in the case (0), for real-analytic MLP blocks, `d ≥ 2` and
regular `θ`: if `𝐃𝓑(w̃V)(w̃ η_V) + 𝐃_θ𝓑(w̃V) η = 0` for all rows `w̃` in a nonempty open set (the
same row at every token), then `𝐃𝓑(wV)(w η_V) + 𝐃_θ𝓑(wV) η = 0` for every `w` such that `wV` has
no zero row. -/
theorem flat_at_write_of_isOpen_rows [Nonempty T] (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d) (k : Fin L)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (O : Set (hid k → ℝ)) (hO : IsOpen O) (hne : O.Nonempty)
    (h : ∀ r ∈ O,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k.succ h')
          ((Matrix.of fun (_ : T) => r) * θ.write k) ((Matrix.of fun (_ : T) => r) * η.write k)
        + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
            suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k.succ
              ((Matrix.of fun (_ : T) => r) * θ.write k)) θ η = 0) :
    ∀ w : Matrix T (hid k) ℝ, (∀ t, (w * θ.write k) t ≠ 0) →
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k.succ h')
          (w * θ.write k) (w * η.write k)
        + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
            suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k.succ (w * θ.write k)) θ η = 0 := by
  sorry

end Skips
