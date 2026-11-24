import SkipsLean.Depth.FlatAtWriteRows

/-!
# From an open set of rows to all hidden states, at any matrix of rank `d`

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), proof of Lemma D.19, Step 1: "The right
side is real-analytic and homogeneous of degree `0` in the row `n ≠ 0`, and it vanishes for `ξ` in
the open set `P`, hence for all `n ≠ 0`. With `h = n W V`, which takes every value by (P1), this is
(16) for `k + 1`"; and proof of Lemma D.18, part (c): "The left side is real-analytic on the rows
`w̃ ∈ ℝ^{1×q}` with `w̃V ≠ 0`. These form a connected set, the complement of a subspace of
codimension `d_model ≥ 2`, so the identity holds on all of it."

`Depth/FlatAtWriteRows.lean` has this for the write `V` of a block and `η_V` (part (c) of
Lemma D.18). Here it is stated for any matrix `M` of rank `d` and any `η_M`, and for the network
after any hidden state: Step 1 of Lemma D.19 uses `M = W V` and `η_M = Z W V + η_W V + W η_V`.
The conclusion is the hypothesis of Lemma D.3 (`suffixFlatZero_of_flat_at_write`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}

/-- **From an open set of rows to all hidden states:** in the case (0), for real-analytic MLP
blocks, `d ≥ 2`, regular `θ` and a matrix `M` of rank `d`: if
`𝐃𝓑_{>j}(rM)(r η_M) + 𝐃_θ𝓑_{>j}(rM) η = 0` for the rows `r` of a nonempty open set (the same row
at every token), then the identity holds at every `w` such that `wM` has no zero row. -/
theorem flat_at_matrix_of_isOpen_rows [Nonempty T] (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d)
    (j : Fin (L + 1)) {m : Type*} [Fintype m] (M : Matrix m d ℝ)
    (hM : M.rank = Fintype.card d) (ηM : Matrix m d ℝ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (O : Set (m → ℝ)) (hO : IsOpen O) (hne : O.Nonempty)
    (h : ∀ r ∈ O,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ j h')
          ((Matrix.of fun (_ : T) => r) * M) ((Matrix.of fun (_ : T) => r) * ηM)
        + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
            suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' j
              ((Matrix.of fun (_ : T) => r) * M)) θ η = 0) :
    ∀ w : Matrix T m ℝ, (∀ t, (w * M) t ≠ 0) →
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ j h')
          (w * M) (w * ηM)
        + fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
            suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' j (w * M)) θ η = 0 := by
  sorry

end Skips
