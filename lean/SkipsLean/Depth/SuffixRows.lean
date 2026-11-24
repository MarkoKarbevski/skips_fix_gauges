import SkipsLean.Depth.SuffixZeroDeriv

/-!
# The network after a hidden state acts on every token alone

Paper (dimension paper): Appendix D takes inputs of one token, since an MLP block acts on each
token separately. Here a hidden state has the rows `T`. For MLP blocks under pre-RMSNorm, row `t` of
`𝓑_{>k}(h)` depends only on row `t` of `h`, and in the case (0) so do the rows of the derivatives
`𝐃𝓑_{>k}(h) v` and `𝐃_θ𝓑_{>k}(h) η`.

These statements carry an identity that is known at the hidden states whose rows are all equal
(the paper's one token) to every hidden state without a zero row. They are used in the step for
`tanh` on the path (Lemma D.18), where the path of Appendix D.6 is taken with the same row at every
token.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {ε : ℝ}

/-- **An MLP block acts on each token separately:** for MLP blocks under pre-RMSNorm (any `ε`), row
`t` of `𝓑_{>k}(h)` is row `t` of `𝓑_{>k}` at the hidden state whose rows all equal row `t` of
`h`. -/
theorem suffix_mlp_rmsNorm_row
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) (k : Fin (L + 1))
    (h : Matrix T d ℝ) (t : T) :
    suffix (Arch.mlp σ (rmsNorm ε) hid) 0 θ k h t
      = suffix (Arch.mlp σ (rmsNorm ε) hid) 0 θ k (Matrix.of fun _ => h t) t := by
  sorry

/-- **The derivative in `h`, token by token, case (0):** for real-analytic MLP blocks and regular
`θ`, at `h` without a zero row, row `t` of `𝐃𝓑_{>k}(h) v` is row `t` of the same derivative at the
hidden state whose rows all equal row `t` of `h`, along the direction whose rows all equal row `t`
of `v`. -/
theorem fderiv_suffix_zero_row (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (k : Fin (L + 1))
    (h v : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) (t : T) :
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k h') h v t
      = fderiv ℝ (fun h' : Matrix T d ℝ => suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ k h')
          (Matrix.of fun _ => h t) (Matrix.of fun _ => v t) t := by
  sorry

/-- **The derivative in the weights, token by token, case (0):** under the same hypotheses, row
`t` of `𝐃_θ𝓑_{>k}(h) η` is row `t` of the same derivative at the hidden state whose rows all equal
row `t` of `h`. -/
theorem fderiv_param_suffix_zero_row (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : RegularZero (Arch.mlp σ (rmsNorm 0) hid) θ) (k : Fin (L + 1))
    (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (t : T) :
    fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k h) θ η t
      = fderiv ℝ (fun θ' : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
          suffix (Arch.mlp σ (rmsNorm 0) hid) 0 θ' k (Matrix.of fun _ => h t)) θ η t := by
  sorry

end Skips
