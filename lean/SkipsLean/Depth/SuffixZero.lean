import SkipsLean.Depth.SuffixRMS

/-!
# The claim `(D_k)` in the case (0): pre-RMSNorm with `ε = 0`

Paper (dimension paper): Appendix D.3 in the case (0). "For `k = 0, …, L` and a row `h`, with
`h ≠ 0` in the case (0), let `𝓑_{>k}(h)` be the output of the network when its hidden state `h_k`
is set to `h`." The identity (16) is asked "for all rows `h`, with `h ≠ 0` in the case (0)", and
Claim `(D_k)` reads, in the case (0) (equation (18)): "with `Z_ℓ = Y_ℓ + β_ℓ I` for antisymmetric
matrices `Y_k, …, Y_L` and numbers `β_k, …, β_L`,

`Z = Y_k + β_k I`, `η = ((−Y_{ℓ−1} W_read^ℓ, W_write^ℓ (Y_ℓ + β_ℓ I))_{ℓ=k+1}^L, −Y_L D)`."

Lemma D.5 (The readout), the case (0): "Here (16) is `𝐃N(h)(hZ) D + N(h) η_D = 0`. Multiplying by
`‖h‖³/√d` gives `‖h‖² h (ZD + η_D) = ⟨hZ, h⟩ hD` for all rows `h`. […] `Z = Y_L + βI` with `Y_L`
antisymmetric, and `η_D = −Y_L D`."

In Lean a hidden state has the rows `T` (tokens), and "`h ≠ 0`" is "no row of `h` vanishes". The
Lean `rmsNorm 0` maps a zero row to `0`; where a row vanishes it is not differentiable, and nothing
is claimed there.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-! ### RMSNorm with `ε = 0` away from the zero rows -/

/-- RMSNorm with `ε = 0` is real-analytic at every matrix without a zero row. -/
theorem analyticAt_rmsNorm_zero (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) :
    AnalyticAt ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h := by
  sorry

/-- **The derivative of RMSNorm with `ε = 0`** at a matrix `h` without a zero row: on every row,
`𝐃N(h) u = u/ρ − ⟨h, u⟩ h/(d ρ³)` with `ρ = ‖h‖/√d` (the formula of the case `ε > 0` with
`ε = 0`). -/
theorem fderiv_rmsNorm_zero_apply (h U : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) :
    fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h U
      = Matrix.of fun t =>
          (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ • U t
            - ((h t ⬝ᵥ U t) / (Fintype.card d : ℝ)
                * (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ ^ 3) • h t := by
  sorry

/-- **Equation (15) of the dimension paper for the normalization:** RMSNorm with `ε = 0` does not
change along `h`: `𝐃N(h) h = 0` at every matrix `h` without a zero row. -/
theorem fderiv_rmsNorm_zero_self (h : Matrix T d ℝ) (hh : ∀ t, h t ≠ 0) :
    fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h h = 0 := by
  sorry

variable (A : Arch T d L) (θ : Params A dIn dOut)

/-! ### The identity (16) and the claim in the case (0) -/

/-- The identity (16) of the paper for `k`, `Z` and `η` in the case (0):
`𝐃𝓑_{>k}(h) (h Z) + 𝐃_θ 𝓑_{>k}(h) η = 0` for all `h` without a zero row. -/
def SuffixFlatZero (k : Fin (L + 1)) (Z : Matrix d d ℝ) (η : Params A dIn dOut) : Prop :=
  ∀ h : Matrix T d ℝ, (∀ t, h t ≠ 0) →
    fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h (h * Z)
      + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k h) θ η = 0

/-- **Claim `(D_k)` in the case (0)** (equation (18)), for blocks without symmetries inside: every
`Z` and `η` that satisfy the identity (16) for `k` come from the symmetries at the hidden states
`h_k, …, h_L`: `Z = Y_k + β_k I` with antisymmetric `Y_k, …, Y_L` and numbers `β_k, …, β_L`, the
reads move by `−Y_{ℓ−1} W_read^ℓ`, the writes by `W_write^ℓ (Y_ℓ + β_ℓ I)` and `D` by `−Y_L D`. -/
def ClaimZero (k : Fin (L + 1)) : Prop :=
  ∀ (Z : Matrix d d ℝ) (η : Params A dIn dOut), SuffixFlatZero A θ k Z η →
    ∃ (Y : Fin (L + 1) → Matrix d d ℝ) (β : Fin (L + 1) → ℝ),
      (∀ ℓ, k ≤ ℓ → Y ℓ ∈ antisymmetric d) ∧ Z = Y k + β k • (1 : Matrix d d ℝ) ∧
      (∀ ℓ : Fin L, k ≤ ℓ.castSucc →
        η.read ℓ = -(Y ℓ.castSucc * θ.read ℓ) ∧
        η.write ℓ = θ.write ℓ * (Y ℓ.succ + β ℓ.succ • (1 : Matrix d d ℝ))) ∧
      η.D = -(Y (Fin.last L) * θ.D)

/-- **Lemma D.5 of the dimension paper (the readout), the case (0):** if `D` has rank `d ≥ 2`,
then `(D_L)` holds under pre-RMSNorm with `ε = 0`. -/
theorem claimZero_last [Nonempty T] (hχ : A.χ = rmsNorm 0) (hD : θ.D.rank = Fintype.card d)
    (hd : 2 ≤ Fintype.card d) : ClaimZero A θ (Fin.last L) := by
  sorry

end Skips
