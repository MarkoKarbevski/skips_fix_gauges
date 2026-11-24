import SkipsLean.Dimension.ExpOrbit
import SkipsLean.Symmetry.AttentionHeads

/-!
# The orbit of the symmetries of an attention network through `θ`

Paper (dimension paper): Appendix B, proof of Lemma B.1: "In an attention block, the changes of
basis inside the heads map `W_{Q,i} ↦ W_{Q,i} K_i` and `W_{V,i} ↦ W_{V,i} K'_i`" (with
`W_{K,i} ↦ W_{K,i} K_i^{-⊤}` and `W_{O,i} ↦ K'^{-1}_i W_{O,i}`); proof of Proposition 4.6: "The
changes of basis of Proposition 3.2, the rescalings and the changes of basis inside the heads form
a Lie group of dimension `k`, which acts smoothly. It acts locally freely at `θ`, so the map that
sends an element of the group to the image of `θ` under it is an immersion near the identity".

Here the orbit map for attention networks, as `Dimension/ExpOrbitGated.lean` has it for gated
blocks: `cobExpHeads θ (m, Γ, Γ')` applies the changes of basis `exp Γ_{ℓ,i}` between the queries
and keys and `exp Γ'_{ℓ,i}` between the values and outputs of every head, then the changes of
basis `exp m_ℓ` at the hidden states. It passes through `θ` at `0` and is strictly differentiable
there, with the derivative `cobDir θ m + headDirQK θ Γ + headDirVO θ Γ'`.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees] {χ : Matrix T d ℝ → Matrix T d ℝ}
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-- The parameters `((θ.headsQK (exp Γ)).headsVO (exp Γ')).cob (exp m) (exp m)` of an attention
network: the changes of basis `exp Γ_{ℓ,i}` and `exp Γ'_{ℓ,i}` inside head `i` of block `ℓ`, then
the change of basis `exp m_ℓ` at the hidden state `h_ℓ`. -/
noncomputable def cobExpHeads (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) :
    Params (Arch.attention sees χ H dh) dIn dOut :=
  cobExp ((θ.headsQK fun ℓ i => expGL (p.2.1 ℓ i)).headsVO fun ℓ i => expGL (p.2.2 ℓ i)) p.1

variable (θ : Params (Arch.attention sees χ H dh) dIn dOut)

/-- The orbit map passes through `θ` at `0`. -/
theorem cobExpHeads_zero : cobExpHeads θ 0 = θ := by
  sorry

/-- The orbit map `(m, Γ, Γ') ↦ cobExpHeads θ (m, Γ, Γ')` is strictly differentiable at `0`, with
the derivative `(m, Γ, Γ') ↦ cobDir θ m + headDirQK θ Γ + headDirVO θ Γ'`. -/
theorem hasStrictFDerivAt_cobExpHeads :
    ∃ Φ' : ((Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
          × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) →L[ℝ]
        Params (Arch.attention sees χ H dh) dIn dOut,
      HasStrictFDerivAt (cobExpHeads θ) Φ' 0
        ∧ ∀ p, Φ' p = cobDir θ p.1 + headDirQK θ p.2.1 + headDirVO θ p.2.2 := by
  sorry

end Skips
