import SkipsLean.Residual.SmallWritesNorm
import SkipsLean.Depth.SuffixRMS

/-!
# Small writes under pre-RMSNorm: the final normalization, large inputs, the skip

Paper (skips paper): proof of Lemma A.27, paragraph "Under pre-RMSNorm", for `ε > 0`. With
`h = x E`, `n = N_ε(h)` and the limit

  `(J_0 η)(x) = 𝐃N_ε(h) (x η_E + D_θ g(n) η) D + N_ε(h) η_D`

(`smallWritesLimitNorm`, `Residual/SmallWritesNorm.lean`), "this is the equation of the proof of
Theorem B.1 (ii) with `h_1 = x E` and `D_θ h_1 η = x η_E + D_θ g(n) η`, and its Steps 1 to 5 go
through with three changes. In Step 2, `D_θ g(n) η` is bounded, since `‖n_t‖ < √d` for every
token `t`. In Step 3, the direction `η^Y` has the entries `E Y` at `E` and `-Y D` at `D` and no
others, since `𝐃N_ε(h)(h Y) = N_ε(h) Y` for antisymmetric `Y`."

This file states Steps 1 to 3 for a direction `η` that is flat for `J_0`: there is an
antisymmetric `Y` with `η_E = E Y` and `η_D = -Y D`, and `D_θ g(n) η = 0` at every
`n = N_ε(x E)`. Step 4 starts there (`Residual/DepthMlpRMS.lean`, `Residual/DepthGatedRMS.lean`).
The steps do not depend on the kind of block: the maps `f_ℓ` are arbitrary continuously
differentiable maps.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]

/-- **Proof of Lemma A.27 under pre-RMSNorm (`ε > 0`), Steps 1 to 3:** let `E` and `D` have rank
`d`, and let `η` be flat for the limit `J_0`. Then there is an antisymmetric `Y` with
`η_E = E Y` and `η_D = -Y D`, and the derivative of the wide block
`n ↦ ∑_ℓ f_ℓ(n W_read^ℓ) W_write^ℓ` along the entries of `η` at the reads and the writes
vanishes at every `n = N_ε(x E)`. -/
theorem exists_antisymm_of_smallWritesLimitNorm_rmsNorm {A : Arch T d L} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, ContDiff ℝ 1 (A.f ℓ)) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (η : Params A dIn dOut) (hη : ∀ x, smallWritesLimitNorm A θ η x = 0) :
    ∃ Y : Matrix d d ℝ, Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D) ∧
      ∀ x : Matrix T dIn ℝ,
        ∑ ℓ, (fderiv ℝ (A.f ℓ) (rmsNorm ε (x * θ.E) * θ.read ℓ)
                (rmsNorm ε (x * θ.E) * η.read ℓ) * θ.write ℓ
              + A.f ℓ (rmsNorm ε (x * θ.E) * θ.read ℓ) * η.write ℓ) = 0 := by
  sorry

end Skips
