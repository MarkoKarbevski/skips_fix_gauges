import SkipsLean.Depth.Suffix
import SkipsLean.Dimension.UpperBoundRMSNorm

/-!
# The claim `(D_k)` under pre-RMSNorm with `ε > 0`

Paper (dimension paper): Appendix D.3 ("The claim, and the reduction to one step"), in the case (+):
`χ = N_ε` with `ε > 0`, the group of the changes of basis is `O(d)`, and its Lie algebra `𝔤` is the
set of the antisymmetric matrices.

The identity (16) is the one of the case (n) (`SuffixFlat`, which is stated for any `χ`). Claim
`(D_k)` now says: if `Z` and `η` satisfy (16) for `k`, then `Z` is antisymmetric, and there are
antisymmetric `Z_k = Z, Z_{k+1}, …, Z_L` with

  `η_read^ℓ = - Z_{ℓ-1} W_read^ℓ`,  `η_write^ℓ = W_write^ℓ Z_ℓ`  (`ℓ = k+1, …, L`),  `η_D = - Z_L D`.

"Regular" is as in the case (n) (`Regular`: (R1), and (R3) for the blocks as maps of their inputs).
Stated here: Lemma D.2, Lemma D.3, Proposition D.4 and Lemma D.5 in the case (+), and that the
network after a hidden state is real-analytic for a real-analytic `χ`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L) (θ : Params A dIn dOut) {ε : ℝ}

omit [DecidableEq d] in
/-- RMSNorm with `ε > 0` is real-analytic. -/
theorem analyticOnNhd_rmsNorm (hε : 0 < ε) :
    AnalyticOnNhd ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) Set.univ := by
  sorry

/-- For a real-analytic `χ` and real-analytic blocks, the network after a hidden state is
real-analytic in the weights and the hidden state together. -/
theorem analyticOnNhd_suffix_prod_of_analytic (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (k : Fin (L + 1)) :
    AnalyticOnNhd ℝ
      (fun p : Params A dIn dOut × Matrix T d ℝ => suffix A 0 p.1 k p.2) Set.univ := by
  sorry

/-- For a real-analytic `χ` and real-analytic blocks, `𝓑_{>k}` is real-analytic in the hidden
state. -/
theorem analyticOnNhd_suffix_of_analytic (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (k : Fin (L + 1)) :
    AnalyticOnNhd ℝ (fun h : Matrix T d ℝ => suffix A 0 θ k h) Set.univ := by
  sorry

/-- **Claim `(D_k)` in the case (+),** for blocks without symmetries inside: every `Z` and `η` that
satisfy the identity (16) for `k` come from changes of basis `Z_k = Z, Z_{k+1}, …, Z_L` at the
hidden states `h_k, …, h_L`, all antisymmetric. -/
def ClaimRMS (k : Fin (L + 1)) : Prop :=
  ∀ (Z : Matrix d d ℝ) (η : Params A dIn dOut), SuffixFlat A θ k Z η →
    ∃ X : Fin (L + 1) → Matrix d d ℝ, X k = Z ∧ (∀ ℓ, k ≤ ℓ → X ℓ ∈ antisymmetric d) ∧
      (∀ ℓ : Fin L, k ≤ ℓ.castSucc →
        η.read ℓ = -(X ℓ.castSucc * θ.read ℓ) ∧ η.write ℓ = θ.write ℓ * X ℓ.succ) ∧
      η.D = -(X (Fin.last L) * θ.D)

/-- **Lemma D.2, case (+):** for a regular `θ` and analytic blocks there is, for every `k`, an open
dense set of hidden states `h` at which the derivative of `𝓑_{>k}` is injective. (`N_ε` is a
diffeomorphism of the rows onto the ball `‖n‖² < d`.) -/
theorem exists_open_dense_injective_fderiv_suffix_rmsNorm (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (k : Fin (L + 1)) :
    ∃ U : Set (Matrix T d ℝ), IsOpen U ∧ Dense U ∧
      ∀ h ∈ U, Function.Injective (fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') h) := by
  sorry

/-- **Lemma D.3, case (+) (a direction at a write).** Let `θ` be regular, and let `M` be a matrix
with `d` columns and rank `d`. If `𝐃𝓑_{>k}(w M) (w η_M) + 𝐃_θ 𝓑_{>k}(w M) η = 0` for all `w`, then
`η_M = M Z` for a `d × d` matrix `Z`, and the identity (16) holds for `k`, `Z` and `η`. -/
theorem suffixFlat_of_flat_at_write_rmsNorm [Nonempty T] (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (k : Fin (L + 1))
    {m : Type*} [Fintype m] (M : Matrix m d ℝ) (hM : M.rank = Fintype.card d)
    (ηM : Matrix m d ℝ) (η : Params A dIn dOut)
    (h : ∀ w : Matrix T m ℝ,
      fderiv ℝ (fun h' : Matrix T d ℝ => suffix A 0 θ k h') (w * M) (w * ηM)
        + fderiv ℝ (fun θ' : Params A dIn dOut => suffix A 0 θ' k (w * M)) θ η = 0) :
    ∃ Z : Matrix d d ℝ, ηM = M * Z ∧ SuffixFlat A θ k Z η := by
  sorry

/-- **Lemma D.5, case (+):** if `D` has rank `d`, then `(D_L)` holds. (The identity (16) for `L` is
`(n Z - ⟨n Z, n⟩ n / d) D + n η_D = 0` for the rows `n` of the ball; its part of degree `1` gives
`η_D = - Z D`, and its part of degree `3` gives that `Z` is antisymmetric.) -/
theorem claimRMS_last [Nonempty T] (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hD : θ.D.rank = Fintype.card d) : ClaimRMS A θ (Fin.last L) := by
  sorry

/-- **Proposition D.4, case (+), first part:** if `θ` is regular and `(D_0)` holds at `θ`, every
flat direction is the direction of antisymmetric changes of basis at the hidden states. -/
theorem flat_le_range_cobDir_of_claimRMS [Nonempty T] (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (h0 : ClaimRMS A θ 0)
    (η : Params A dIn dOut) (hη : η ∈ flat A 0 θ) :
    ∃ X : Fin (L + 1) → Matrix d d ℝ, (∀ ℓ, X ℓ ∈ antisymmetric d) ∧ η = cobDir θ X := by
  sorry

/-- **Proposition D.4, case (+):** if `θ` is regular and `(D_0)` holds at `θ`, the functional
dimension at `θ` is `P - (L + 1) d (d - 1) / 2`. -/
theorem funDim_of_claimRMS [Nonempty T] (hε : 0 < ε) (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : Regular A θ) (h0 : ClaimRMS A θ 0) :
    funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end Skips
