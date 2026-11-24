import SkipsLean.Depth.SuffixZeroClaim

/-!
# The converse of the claim `(D_k)` in the case `ε = 0`

Paper (dimension paper): Appendix D.3, after the forms (17) to (19): "Conversely, every
`Z = Z_k ∈ 𝔤` and `η` of the form (17), or (19) for gated blocks, satisfy (16): it is the
derivative at `τ = 0` of the identity `𝓑_{>k}(h exp(τ Z_k)) = 𝓑_{>k}(h)`, in which the left side
is taken at the weights moved by the symmetries with `G_ℓ = exp(τ Z_ℓ)`"; in the case (0) the form
is (18): `Z = Y_k + β_k I`, reads `−Y_{ℓ−1} W_read^ℓ`, writes `W_write^ℓ (Y_ℓ + β_ℓ I)`, `−Y_L D`,
with antisymmetric `Y_ℓ` (the symmetries are `G_ℓ = c_ℓ Q_ℓ`, and `N(hG) = N(h)Q`).

The proof of Lemma D.19 uses it in "Step 3: subtracting a symmetry": "The pair `Y_k + β_k I` and
`(−Y_k W, V (Y_{k+1} + β_{k+1} I), η')` is of the form (18), so it satisfies (16) for `k`."

Stated here for real-analytic blocks of any kind under pre-RMSNorm with `ε = 0` and regular `θ`:
the direction `cobDir θ Y + scaleDir θ β` is of the form (18) for every `k` (its entries at `E`
and at the blocks before `h_k` play no role in (16)), and it satisfies (16) for `k` with
`Z = Y_k + β_k I`, when `Y_ℓ` is antisymmetric for `ℓ ≥ k`. (`Depth/SuffixFlatConverse.lean` has
the case of gated blocks without normalization.)
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L) (θ : Params A dIn dOut)

/-- **"Conversely, every `Z = Z_k ∈ 𝔤` and `η` of the form (18) satisfy (16)", the case (0):** for
real-analytic blocks under pre-RMSNorm with `ε = 0` and regular `θ`, if `Y_ℓ` is antisymmetric for
every `ℓ ≥ k`, then `Z = Y_k + β_k I` and `η = cobDir θ Y + scaleDir θ β` satisfy (16) for `k`. -/
theorem suffixFlatZero_cobDir_add_scaleDir (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ) (k : Fin (L + 1))
    (Y : Fin (L + 1) → Matrix d d ℝ) (hY : ∀ ℓ, k ≤ ℓ → Y ℓ ∈ antisymmetric d)
    (β : Fin (L + 1) → ℝ) :
    SuffixFlatZero A θ k (Y k + β k • (1 : Matrix d d ℝ)) (cobDir θ Y + scaleDir θ β) := by
  sorry

end Skips
