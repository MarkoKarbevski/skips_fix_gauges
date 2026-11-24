import SkipsLean.Residual.OneChangeOfBasis
import SkipsLean.Dimension.UpperBoundResidualRMSNormZero

/-!
# One change of basis is left in a residual network, under pre-RMSNorm with `ε = 0`

Paper (skips paper), Theorem A.5 (iii): "One change of basis is left. Let `d_model ≥ 2`, and let
every block be nonzero for some value of its parameters. […] The map `T_G` of the embedding, the
reads, the writes and the readout preserves the function of every residual network if and only if
`G_0 = G_1 = ⋯ = G_L ∈ 𝒢`. Under RMSNorm with `ε = 0`, the same holds for
`G_ℓ = c_ℓ Q_ℓ ∈ CO(d_model)`, with `c_ℓ > 0` and `Q_ℓ` orthogonal, when `T_G` multiplies the reads
and the readout by `Q_{ℓ−1}^⊤` and `Q_L^⊤` in place of `G_{ℓ−1}^{−1}` and `G_L^{−1}`."
Theorem A.17 (i) has the same claim: "For `ε = 0`, the changes of basis in `𝒢` at the hidden
states […] preserve that of every residual network only if they agree at all hidden states."

Its proof, "Part (iii) under RMSNorm with `ε = 0`": "Fix a token, and an input and reads at which
the row of `f(N_ε(h) W_read^ℓ)` of this token is nonzero. As the write varies, the row `b` of this
token takes every value. So, with `u = h + b`, the row `c_ℓ u R + (c h − c_ℓ h R)` is a positive
multiple of `u` for every `u ≠ 0`. Large `u` give `R = I`. Then `(c − c_ℓ) h` is parallel to
every `u`, so `c_ℓ = c`."

Here, for arbitrary maps `f_ℓ`: the map `T_G` is `θ.cob G Q` (the embedding and the writes times
`G_ℓ`, the reads and the readout times `Q_ℓ⁻¹ = Q_ℓ^⊤`), with `G_ℓ = c_ℓ Q_ℓ`. The twin for
`ε > 0` is `eval_cob_residual_rmsNorm_iff` (`Residual/OneChangeOfBasis.lean`). The hypothesis on
the blocks is the one that the proof uses: for every block there are an input, an embedding, a
read and a token at which the row of `x E` and the row of the block are both nonzero. (The
paper's "nonzero for some value of its parameters" is this for the blocks of the paper; for an
arbitrary map `f_ℓ` whose output is nonzero only at tokens with a zero row of `x E`, the scale
`c_ℓ` would not be determined.) Lean's `rmsNorm 0` maps a zero row to `0`; both directions hold
with it.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn]
variable {A : Arch T d L}

/-- **Theorem A.5 (iii) of the skips paper under RMSNorm with `ε = 0`, "only if" (also the last
clause of Theorem A.17 (i)):** let `d ≥ 2`, let every block have an input, an embedding, a read
and a token at which the row of `x E` and the row of the block are nonzero, and let
`G_ℓ = c_ℓ Q_ℓ` with `c_ℓ > 0` and `Q_ℓ` orthogonal. If `θ.cob G Q` has the same function as `θ`
for every residual network `θ`, then `G_0 = G_1 = ⋯ = G_L`. -/
theorem cob_eq_of_eval_cob_residual_rmsNorm_zero [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ) (t : T),
      (x * E) t ≠ 0 ∧ A.f ℓ (rmsNorm 0 (x * E) * W) t ≠ 0)
    (G Q : Fin (L + 1) → GL d ℝ) (c : Fin (L + 1) → ℝ) (hc : ∀ ℓ, 0 < c ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ))
    (h : ∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ),
      eval A 1 (θ.cob G Q) x = eval A 1 θ x) :
    ∀ ℓ, G ℓ = G 0 := by
  sorry

/-- **Theorem A.5 (iii) of the skips paper under RMSNorm with `ε = 0`:** under the hypotheses of
`cob_eq_of_eval_cob_residual_rmsNorm_zero`, the map `θ ↦ θ.cob G Q` with `G_ℓ = c_ℓ Q_ℓ`
preserves the function of every residual network if and only if `G_0 = G_1 = ⋯ = G_L`. -/
theorem eval_cob_residual_rmsNorm_zero_iff [Nonempty T] [Nonempty dIn] [Nonempty dOut]
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (hne : ∀ ℓ, ∃ (x : Matrix T dIn ℝ) (E : Matrix dIn d ℝ) (W : Matrix d (A.r ℓ) ℝ) (t : T),
      (x * E) t ≠ 0 ∧ A.f ℓ (rmsNorm 0 (x * E) * W) t ≠ 0)
    (G Q : Fin (L + 1) → GL d ℝ) (c : Fin (L + 1) → ℝ) (hc : ∀ ℓ, 0 < c ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ)) :
    (∀ (θ : Params A dIn dOut) (x : Matrix T dIn ℝ), eval A 1 (θ.cob G Q) x = eval A 1 θ x)
      ↔ ∀ ℓ, G ℓ = G 0 := by
  sorry

end Skips
