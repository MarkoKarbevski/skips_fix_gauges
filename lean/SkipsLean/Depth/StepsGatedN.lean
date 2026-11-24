import SkipsLean.Depth.Frozen
import SkipsLean.Depth.SuffixFlatConverse

/-!
# Lemma D.12, steps 1 to 3, for gated blocks without normalization

Paper (dimension): Appendix D.5, proof of Lemma D.12, from equation (38) to the end, in the case
(n). After the induction on the exponents, "for all `n ∈ C_k` and all rows `w̃ ∈ ℝ^{1×q}`, with
`ŵ = w̃ ⊙ ι(n)`,

  `ż^g(n) = 0`,   `𝐃𝓑^∞(ŵ V) ((w̃ ⊙ ż^v(n)) V + ŵ η_V) + 𝐃_θ 𝓑^∞(ŵ V) η' = 0`   (38)",

where `𝓑^∞` is the frozen network in the case (n). "Step 1: the gates" gives `η_g = −Z W_g`;
"Step 2: the values and the write" gives a diagonal matrix `Δ_{k+1}` and a matrix `Z'` with
`η_V = Δ_{k+1} V + V Z'` and `η_v = −Z W_v − W_v Δ_{k+1}` (Lemmas D.3 and D.2 for the frozen
network); "Step 3: the rest", in the case (n), subtracts the direction `η♭` of the form (19) built
from `Z`, `Δ_{k+1}`, `Z'`, which satisfies (16) by the converse of the claim, and applies
`(D_{k+1})` to what is left, after extending an identity from the values of `g_{k+1}` to all rows
by (R3).

Stated here: the conclusion of `(D_k)` for one pair `Z`, `η` that satisfies (16) for `k`, from
(38). In Lean, (38) is the two hypotheses `hgate` (its first part holds on an open set of `n` and
is linear in `n`, so it says `Z W_g + η_g = 0`) and `hfro`; the second part is written with
`writeLHS` for the frozen network at `v = w̃ ⊙ ι(n)`, `vdot = w̃ ⊙ ż^v(n)`. The gate `σ` is any
real-analytic function: these steps do not look at it.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **Lemma D.12, steps 1 to 3, case (n).** Let `θ` be good for the cones and regular, and let
`(D_{k+1})` hold. If `Z` and `η` satisfy (16) for `k` and (38) holds for them with the frozen
network, then `η` is of the form (19) for `k` with `Z_k = Z`. -/
theorem claimGated_castSucc_of_frozen [Nonempty T] (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) {C : Fin (L + 1) → Set (d → ℝ)}
    {A : ∀ ℓ, Finset (hid ℓ)} {θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : GoodForConesGated C A θ) (hreg : Regular (Arch.gated σ id hid) θ) (k : Fin L)
    (hk : ClaimGated ⊤ θ k.succ) (Z : Matrix d d ℝ)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hflat : SuffixFlat (Arch.gated σ id hid) θ k.castSucc Z η)
    (hgate : ∀ i j, (Z * θ.read k + η.read k) i (Sum.inl j) = 0)
    (hfro : ∀ n : Matrix T d ℝ, (∀ t, n t ∈ C k.castSucc) → ∀ w : Matrix T (hid k) ℝ,
      writeLHS (Arch.frozen A) (θ.toFrozen A) k (η.toFrozen A)
        (Matrix.of fun t j => w t j * (n * θ.read k) t (Sum.inr j))
        (Matrix.of fun t j => w t j * (n * (Z * θ.read k + η.read k)) t (Sum.inr j)) = 0) :
    ∃ (X : Fin (L + 1) → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      X k.castSucc = Z ∧ (∀ ℓ, k.castSucc ≤ ℓ → X ℓ ∈ (⊤ : Submodule ℝ (Matrix d d ℝ))) ∧
      (∀ ℓ : Fin L, k.castSucc ≤ ℓ.castSucc →
        η.read ℓ = -(X ℓ.castSucc * θ.read ℓ) + (rescaleDir θ α).read ℓ ∧
        η.write ℓ = θ.write ℓ * X ℓ.succ + (rescaleDir θ α).write ℓ) ∧
      η.D = -(X (Fin.last L) * θ.D) := by
  sorry

end Skips
