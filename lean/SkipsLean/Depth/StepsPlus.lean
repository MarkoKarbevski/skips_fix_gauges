import SkipsLean.Depth.Frozen
import SkipsLean.Depth.SuffixGated
import SkipsLean.Depth.StepTanhRMS

/-!
# Lemma D.12, steps 1 to 3, under pre-RMSNorm

Paper (dimension): Appendix D.5, proof of Lemma D.12, from equation (38) to the end, in the case
(+). "Step 1: the gates. By (26), `ż^g(n)` is a polynomial in `n` that vanishes on the open set
`C_k`, so it vanishes for all `n`. […] In the case (+) its part of degree 3 is
`⟨n Z, n⟩ n W_g = 0`, so `Z` is antisymmetric, as `W_g ≠ 0`, and its part of degree 1 gives
`η_g = −Z W_g`. In both cases `Z ∈ 𝔤`, and in a gated block `ż^v(n) = n (Z W_v + η_v)`."
"Step 2: the values and the write" gives, by Lemmas D.3 and D.2, a matrix `Z'` and a diagonal
matrix `Δ_{k+1}` (`Δ_{k+1} = 0` in a GELU block) with `η_V = Δ_{k+1} V + V Z'`,
`η_v = −Z W_v − W_v Δ_{k+1}`, and the identity (16) for `k+1` with `Z'`. "Step 3: the rest. In the
case (+), `𝓑^∞ = 𝓑_{>k+1}`, and the second part of (39) is (16) for `k+1`, with `Z'` and `η'`. By
`(D_{k+1})`, `Z' ∈ 𝔤` and `η'` is of the form (19), or (17) for GELU blocks, with `Z_{k+1} = Z'`.
With Steps 1 and 2 this is (19), or (17), for `k`."

Stated here: the conclusion of `(D_k)` for one pair `Z`, `η`, from (38), for gated blocks with a
real-analytic gate (the claim `ClaimGated (antisymmetric d)`) and for MLP blocks with a
real-analytic activation (the claim `ClaimRMS`; the GELU blocks of the paper). (38) is the
hypothesis: for gated blocks `ż^g(n) = 0` and the identity with `writeLHS` at `v = w̃ ⊙ ι(n)`,
`vdot = w̃ ⊙ ż^v(n)`, for all `n` with rows in `C_k`; for MLP blocks `ż(n) = 0` for these `n` and
the identity at `v = w̃`, `vdot = 0`. Here `ż(n) = (n Z − ⟨n Z, n⟩ n / d) W_read + n η_read`
(`tangentRMS`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ : ℝ → ℝ} {ε : ℝ}

/-- **Lemma D.12, steps 1 to 3, gated blocks, case (+).** Let `θ` be good for the cones and
regular, and let `(D_{k+1})` hold. If (38) holds for `Z` and `η`, then `Z` is antisymmetric and `η`
is of the form (19) for `k` with `Z_k = Z`. -/
theorem claimGated_castSucc_of_flat_rmsNorm [Nonempty T] (hε : 0 < ε)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (hreg : Regular (Arch.gated σ (rmsNorm ε) hid) θ) (k : Fin L)
    (hk : ClaimGated (antisymmetric d) θ k.succ) (Z : Matrix d d ℝ)
    (η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (h38 : ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) →
      (∀ t j, (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inl j) = 0) ∧
      ∀ w : Matrix T (hid k) ℝ,
        writeLHS (Arch.gated σ (rmsNorm ε) hid) θ k η
          (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
          (Matrix.of fun t j =>
            w t j * (tangentRMS Z n * θ.read k + n * η.read k) t (Sum.inr j)) = 0) :
    ∃ (X : Fin (L + 1) → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      X k.castSucc = Z ∧ (∀ ℓ, k.castSucc ≤ ℓ → X ℓ ∈ antisymmetric d) ∧
      (∀ ℓ : Fin L, k.castSucc ≤ ℓ.castSucc →
        η.read ℓ = -(X ℓ.castSucc * θ.read ℓ) + (rescaleDir θ α).read ℓ ∧
        η.write ℓ = θ.write ℓ * X ℓ.succ + (rescaleDir θ α).write ℓ) ∧
      η.D = -(X (Fin.last L) * θ.D) := by
  sorry

/-- **Lemma D.12, steps 1 to 3, MLP blocks, case (+).** Let `θ` be good for the cones and regular,
and let `(D_{k+1})` hold. If (38) holds for `Z` and `η`, then `Z` is antisymmetric and `η` is of
the form (17) for `k` with `Z_k = Z`. -/
theorem claimRMS_castSucc_of_flat_rmsNorm [Nonempty T] (hε : 0 < ε)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)}
    {θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut}
    (hθ : GoodForConesMlp C A θ) (hreg : Regular (Arch.mlp σ (rmsNorm ε) hid) θ) (k : Fin L)
    (hk : ClaimRMS (Arch.mlp σ (rmsNorm ε) hid) θ k.succ) (Z : Matrix d d ℝ)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hz : ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) →
      tangentRMS Z n * θ.read k + n * η.read k = 0)
    (hw : ∀ w : Matrix T (hid k) ℝ, writeLHS (Arch.mlp σ (rmsNorm ε) hid) θ k η w 0 = 0) :
    ∃ X : Fin (L + 1) → Matrix d d ℝ, X k.castSucc = Z ∧
      (∀ ℓ, k.castSucc ≤ ℓ → X ℓ ∈ antisymmetric d) ∧
      (∀ ℓ : Fin L, k.castSucc ≤ ℓ.castSucc →
        η.read ℓ = -(X ℓ.castSucc * θ.read ℓ) ∧ η.write ℓ = θ.write ℓ * X ℓ.succ) ∧
      η.D = -(X (Fin.last L) * θ.D) := by
  sorry

end Skips
