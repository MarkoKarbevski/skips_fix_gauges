import SkipsLean.Depth.SuffixGated

/-!
# The converse of the claim `(D_k)`, for gated blocks without normalization

Paper (dimension): Appendix D.3, after equation (19). "Conversely, every `Z = Z_k ∈ 𝔤` and `η` of
the form (17), or (19) for gated blocks, satisfy (16): it is the derivative at `τ = 0` of the
identity `𝓑_{>k}(h exp(τ Z_k)) = 𝓑_{>k}(h)`, in which the left side is taken at the weights moved
by the symmetries with `G_ℓ = exp(τ Z_ℓ)`" and by the rescalings.

Stated here for gated blocks in the case (n), where `𝔤` contains every matrix: the direction
`cobDir θ X + rescaleDir θ α` is of the form (19) for every `k`, with `Z_ℓ = X ℓ` and
`Δ_ℓ = diag(α ℓ)`, and it satisfies (16) for `k` with `Z = X k`. (Its entries at `E` and at the
blocks before `k+1` play no role in (16).) The proof of Lemma D.12 uses this in the case (n). The
case (+) and the form (17) are not stated here.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **The converse of the claim, gated blocks, case (n):** the directions of the form (19),
`cobDir θ X + rescaleDir θ α`, satisfy the identity (16) for every `k`, with `Z = X k`. -/
theorem suffixFlat_cobDir_add_rescaleDir (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (k : Fin (L + 1))
    (X : Fin (L + 1) → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ) :
    SuffixFlat (Arch.gated σ id hid) θ k (X k) (cobDir θ X + rescaleDir θ α) := by
  sorry

end Skips
