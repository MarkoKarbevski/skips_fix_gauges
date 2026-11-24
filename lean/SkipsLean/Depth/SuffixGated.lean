import SkipsLean.Depth.SuffixRMS
import SkipsLean.Dimension.Rescaling
import SkipsLean.Activations.Analytic

/-!
# Claim `(D_k)` for gated blocks, and what it gives

Paper (dimension): Appendix D.3. "Claim `(D_k)`, for `k = 0, …, L`. Let `Z` be a `d × d` matrix
and `η` a direction of the weights of the blocks `k+1, …, L` and of `D`. If (16) holds, then
`Z ∈ 𝔤`, and with `Z_k = Z` there are `Z_{k+1}, …, Z_L ∈ 𝔤` such that … For gated blocks there
are, in addition, diagonal matrices `Δ_{k+1}, …, Δ_L`, with `Δ_ℓ` of size `q_ℓ`, such that

  `η = ({-Z_{ℓ-1} W_g^ℓ, -Z_{ℓ-1} W_v^ℓ - W_v^ℓ Δ_ℓ, Δ_ℓ W_write^ℓ + W_write^ℓ Z_ℓ}_{ℓ=k+1}^L, -Z_L D)`  (19)."

Here `𝔤` is the space of all matrices in the case (n) (no normalization) and the space of
antisymmetric matrices in the case (+) (pre-RMSNorm with `ε > 0`); gated blocks are not treated in
the case (0). The diagonal matrix `Δ_ℓ` is the function `α ℓ : hid ℓ → ℝ` of its diagonal entries,
and the three terms with `Δ_ℓ` in (19) are the entries of `rescaleDir θ α`
(`Dimension/Rescaling.lean`): `0` at the gate columns, `-α_i` times the value column of unit `i`,
`α_i` times its write row.

Stated here, for the cases (n) and (+): the claim (`ClaimGated`); Lemma D.5 for gated blocks
(`(D_L)` holds); Proposition D.4 for gated blocks ("Let `θ` be regular, with no vanishing value
column if the blocks are gated, and let `(D_0)` hold at `θ`. Then the directions `η` with
`D_θ F(θ, x) η = 0` for all `x` … are the directions … `η^{Z,Δ}` of (12) for gated blocks, and the
Jacobian of the network has the rank (13) on some finite batch"), where the rank (13) is
`P - (L + 1) dim G - s` with `s = ∑_ℓ q_ℓ`.

For GELU blocks in the case (+) the claim has the form (17) of tanh blocks, and `ClaimRMS`,
`claimRMS_last`, `funDim_of_claimRMS` of `Depth/SuffixRMS.lean` apply as they are.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- **Claim `(D_k)` for gated blocks,** with the changes of basis in the subspace `g` of matrices
(all matrices in the case (n), the antisymmetric ones in the case (+)): every `Z` and `η` that
satisfy the identity (16) for `k` come from changes of basis `Z_k = Z, Z_{k+1}, …, Z_L ∈ g` at the
hidden states `h_k, …, h_L` and from rescalings of the values of the hidden units of the blocks
after `h_k`, as in (19). -/
def ClaimGated (g : Submodule ℝ (Matrix d d ℝ))
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (k : Fin (L + 1)) : Prop :=
  ∀ (Z : Matrix d d ℝ) (η : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut),
    SuffixFlat (Arch.gated σ χ hid) θ k Z η →
    ∃ (X : Fin (L + 1) → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      X k = Z ∧ (∀ ℓ, k ≤ ℓ → X ℓ ∈ g) ∧
      (∀ ℓ : Fin L, k ≤ ℓ.castSucc →
        η.read ℓ = -(X ℓ.castSucc * θ.read ℓ) + (rescaleDir θ α).read ℓ ∧
        η.write ℓ = θ.write ℓ * X ℓ.succ + (rescaleDir θ α).write ℓ) ∧
      η.D = -(X (Fin.last L) * θ.D)

/-! ### Lemma D.5 for gated blocks: `(D_L)` -/

/-- **Lemma D.5, gated blocks, case (n):** `(D_L)` holds. -/
theorem claimGated_last [Nonempty T]
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    ClaimGated ⊤ θ (Fin.last L) := by
  sorry

/-- **Lemma D.5, gated blocks, case (+):** if `D` has rank `d`, then `(D_L)` holds. -/
theorem claimGated_last_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hD : θ.D.rank = Fintype.card d) :
    ClaimGated (antisymmetric d) θ (Fin.last L) := by
  sorry

/-! ### Proposition D.4 for gated blocks -/

/-- **Proposition D.4, gated blocks, case (n), first part:** if `θ` is regular and `(D_0)` holds
at `θ`, every flat direction is the sum of the direction of changes of basis at the hidden states
and of the direction of rescalings of the values (`η^{Z,Δ}` of the paper). -/
theorem flat_le_cobDir_add_rescaleDir_of_claimGated [Nonempty T]
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hθ : Regular (Arch.gated σ id hid) θ) (h0 : ClaimGated ⊤ θ 0)
    (η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flat (Arch.gated σ id hid) 0 θ) :
    ∃ (X : Fin (L + 1) → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      η = cobDir θ X + rescaleDir θ α := by
  sorry

/-- **Proposition D.4, gated blocks, case (n):** if `θ` is regular, no value column of a read
vanishes and `(D_0)` holds at `θ`, the functional dimension at `θ` is
`P - (L + 1) d² - ∑ d_hidden`. -/
theorem funDim_of_claimGated [Nonempty T] (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hθ : Regular (Arch.gated σ id hid) θ)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) (h0 : ClaimGated ⊤ θ 0) :
    funDim (Arch.gated σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Proposition D.4, gated blocks, case (+), first part:** if `θ` is regular and `(D_0)` holds
at `θ`, every flat direction is the sum of the direction of antisymmetric changes of basis at the
hidden states and of the direction of rescalings of the values. -/
theorem flat_le_cobDir_add_rescaleDir_of_claimGated_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : Regular (Arch.gated σ (rmsNorm ε) hid) θ) (h0 : ClaimGated (antisymmetric d) θ 0)
    (η : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hη : η ∈ flat (Arch.gated σ (rmsNorm ε) hid) 0 θ) :
    ∃ (X : Fin (L + 1) → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ),
      (∀ ℓ, X ℓ ∈ antisymmetric d) ∧ η = cobDir θ X + rescaleDir θ α := by
  sorry

/-- **Proposition D.4, gated blocks, case (+):** if `θ` is regular, no value column of a read
vanishes and `(D_0)` holds at `θ`, the functional dimension at `θ` is
`P - (L + 1) d (d - 1) / 2 - ∑ d_hidden`. -/
theorem funDim_of_claimGated_rmsNorm [Nonempty T] {ε : ℝ} (hε : 0 < ε)
    (hσ : AnalyticOnNhd ℝ σ Set.univ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hθ : Regular (Arch.gated σ (rmsNorm ε) hid) θ)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0)
    (h0 : ClaimGated (antisymmetric d) θ 0) :
    funDim (Arch.gated σ (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

end Skips
