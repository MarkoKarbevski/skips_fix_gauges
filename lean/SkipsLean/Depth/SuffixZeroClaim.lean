import SkipsLean.Depth.SuffixZeroDeriv
import SkipsLean.Dimension.UpperBoundRMSNormZero

/-!
# The case (0): a direction at a write, and the claim gives the rank

Paper (dimension paper): Appendix D.3 in the case (0), pre-RMSNorm with `ε = 0`.

Lemma D.3 (A direction at a write): "Let `θ` be regular, `0 ≤ k ≤ L`, and let `A` be a matrix with
`d` columns and rank `d`. Let `η_A` be a matrix of the size of `A` and `η` a direction of the
weights of the blocks `k + 1, …, L` and of `D`. If `𝐃𝓑_{>k}(wA)(w η_A) + 𝐃_θ𝓑_{>k}(wA) η = 0` for
all rows `w`, with `wA ≠ 0` in the case (0), then `η_A = AZ` for a `d × d` matrix `Z`, and (16)
holds."

Proposition D.4 (The claim gives the rank): "Let `θ` be regular […] and let `(D_0)` hold at `θ`.
Then the directions `η` with `𝐃_θ F(θ, x) η = 0` for all `x`, with `xE ≠ 0` in the case (0), are
the directions `η^Z` of (11) […], and the Jacobian of the network has the rank (13) on some finite
batch of such inputs." In the case (0) the directions of the symmetries are
`cobDir θ Y + scaleDir θ β` with antisymmetric `Y_0, …, Y_L` and numbers `β_0, …, β_L`
(`Dimension/UpperBoundRMSNormZero.lean`), and the rank is `P − (L + 1)(d(d−1)/2 + 1)`.

A hidden state has the rows `T`; "`≠ 0`" is "no row vanishes". The Lean `flat` and `funDim` use
every input: at an input where the output is not differentiable in the parameters Lean takes the
derivative to be `0`, which asks nothing of a direction.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L) (θ : Params A dIn dOut)

/-- **Lemma D.3 of the dimension paper (a direction at a write), the case (0):** let the blocks be
real-analytic, `d ≥ 2`, `θ` regular, and `M` a matrix with `d` columns and rank `d`. If
`𝐃𝓑_{>k}(wM)(w η_M) + 𝐃_θ𝓑_{>k}(wM) η = 0` for all `w` such that `wM` has no zero row, then
`η_M = M Z` for a matrix `Z`, and the identity (16) holds for `k`, `Z` and `η`. -/
theorem suffixFlatZero_of_flat_at_write [Nonempty T] (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ)
    (hd : 2 ≤ Fintype.card d) (k : Fin (L + 1))
    {m : Type*} [Fintype m] (M : Matrix m d ℝ) (hM : M.rank = Fintype.card d)
    (ηM : Matrix m d ℝ) (η : Params A dIn dOut)
    (h : ∀ w : Matrix T m ℝ, (∀ t, (w * M) t ≠ 0) →
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (w * M) (w * ηM)
        + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k (w * M)) θ η = 0) :
    ∃ Z : Matrix d d ℝ, ηM = M * Z ∧ SuffixFlatZero A θ k Z η := by
  sorry

/-- **Proposition D.4 of the dimension paper, the case (0), the flat directions:** for
real-analytic blocks under pre-RMSNorm with `ε = 0`, `d ≥ 2`, regular `θ` and `(D_0)`, every flat
direction is a direction of the symmetries: `η = cobDir θ Y + scaleDir θ β` with antisymmetric
`Y_0, …, Y_L` and numbers `β_0, …, β_L`. -/
theorem flat_le_cobDir_add_scaleDir_of_claimZero [Nonempty T] (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ)
    (hd : 2 ≤ Fintype.card d) (h0 : ClaimZero A θ 0)
    (η : Params A dIn dOut) (hη : η ∈ flat A 0 θ) :
    ∃ (Y : Fin (L + 1) → Matrix d d ℝ) (β : Fin (L + 1) → ℝ),
      (∀ ℓ, Y ℓ ∈ antisymmetric d) ∧ η = cobDir θ Y + scaleDir θ β := by
  sorry

/-- **Proposition D.4 of the dimension paper, the case (0), the rank:** for real-analytic blocks
under pre-RMSNorm with `ε = 0`, `d ≥ 2`, regular `θ` and `(D_0)`, the functional dimension is
`P − (L + 1)(d(d−1)/2 + 1)`. -/
theorem funDim_of_claimZero [Nonempty T] (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ)
    (hd : 2 ≤ Fintype.card d) (h0 : ClaimZero A θ 0) :
    funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
      = Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end Skips
