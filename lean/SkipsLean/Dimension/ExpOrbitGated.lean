import SkipsLean.Dimension.ExpOrbit
import SkipsLean.Dimension.RescaleAction

/-!
# Gated blocks: the changes of basis and the rescalings near the identity, as one map

Paper (dimension paper): Appendix B, proof of Proposition 4.6: "The changes of basis of
Proposition 3.2, the rescalings and the changes of basis inside the heads form a Lie group of
dimension `k`, which acts smoothly. It acts locally freely at `θ`, so the map that sends an element
of the group to the image of `θ` under it is an immersion near the identity".

For a network of gated blocks the group is that of the changes of basis and of the rescalings of
the values of the hidden units. In the chart `(m, α) ↦ (exp m_ℓ, e^{α_{ℓ,i}})` at the identity, the
map that sends an element of the group to the image of `θ` is
`cobExpRescale θ (m, α) = (θ.rescale (e^α)).cob (exp m) (exp m)`: the value column of hidden unit
`i` of block `ℓ` is divided by `e^{α_{ℓ,i}}`, its write row is multiplied by `e^{α_{ℓ,i}}`, and
then the change of basis `exp m_ℓ` is made at the hidden state `h_ℓ`.

Stated here: the map passes through `θ` at `0`, and it is strictly differentiable at `0` with the
derivative `(m, α) ↦ cobDir θ m + rescaleDir θ α` (`Dimension/UpperBound.lean`,
`Dimension/Rescaling.lean`), for any gate `σ` and any map `χ`. Used for local identifiability of
networks of gated blocks, with and without skip connections
(`Dimension/LocalIdentifiabilityGated.lean`, `Residual/LocalIdentifiabilityGated.lean`).
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- The parameters `(θ.rescale (e^α)).cob (exp m) (exp m)` of a gated network: the rescaling of
the value of hidden unit `i` of block `ℓ` by `e^{α ℓ i}`, then the change of basis `exp m_ℓ` at the
hidden state `h_ℓ`. -/
noncomputable def cobExpRescale (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ)) :
    Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut :=
  cobExp (θ.rescale fun ℓ i => Real.exp (p.2 ℓ i)) p.1

variable (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)

/-- At `(m, α) = 0` the map gives `θ`. -/
theorem cobExpRescale_zero : cobExpRescale θ 0 = θ := by
  sorry

/-- The map `(m, α) ↦ (θ.rescale (e^α)).cob (exp m) (exp m)` is strictly differentiable at `0`,
with the derivative `(m, α) ↦ cobDir θ m + rescaleDir θ α`. -/
theorem hasStrictFDerivAt_cobExpRescale :
    ∃ Φ' : ((Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ)) →L[ℝ]
        Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut,
      HasStrictFDerivAt (cobExpRescale θ) Φ' 0 ∧ ∀ p, Φ' p = cobDir θ p.1 + rescaleDir θ p.2 := by
  sorry

end Skips
