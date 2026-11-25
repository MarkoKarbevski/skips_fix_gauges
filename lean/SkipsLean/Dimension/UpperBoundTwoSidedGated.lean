import SkipsLean.Dimension.UpperBoundTwoSided

/-!
# Locally free action when one block is narrower than `d`, from both ends: gated blocks

Paper (skips paper), Lemma A.18 (Locally free action) and Remark A.19; see the header of
`Dimension/UpperBoundTwoSided.lean`, which has this form for the changes of basis alone and for
ReLU and ReLU² blocks. Here the twins for gated blocks: with the rescalings of the values (any
gate), and with the rescalings of values and gates (ReGLU). For a block `m`: `E` and the writes
of the blocks before `m` have rank `d`, and no rescaled read column of a block up to `m`
vanishes; `D` has rank `d`, and for the blocks after `m` no write row vanishes and

* with the rescalings of the values: the read has rank `d`;
* with both rescalings: the gate and value columns of the read are in general position (any `d`
  of them linearly independent, more than `d` of them), as in the form with the readout
  (`cobDir_add_rescaleDir_add_rescaleDirGate_injective_of_rank_D`).

Nothing is asked of the write of block `m`. Numeric check:
`ai_notes/locally_free_one_narrow_block_gated_check_2026-11-25.py`. Used for S Proposition A.35
for ReGLU blocks (`Depth/InactiveGateTwoSided.lean`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- **Lemma A.18 from both ends, gated blocks with the rescalings of the values, in
infinitesimal form.** If `E` and `D` have rank `d`, every write of a block before block `m` and
every read of a block after block `m` has rank `d`, no value column of a read of a block up to
`m` and no write row of a block after `m` vanishes, the direction
`cobDir θ X + rescaleDir θ α` determines `X` and `α`. -/
theorem cobDir_add_rescaleDir_injective_of_rank_E_D
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (m : Fin L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hr : ∀ ℓ, m < ℓ → (θ.read ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (ha : ∀ ℓ, m < ℓ → ∀ i, (fun a => θ.write ℓ i a) ≠ 0) :
    Function.Injective fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
      cobDir θ p.1 + rescaleDir θ p.2 := by
  sorry

/-- **Lemma A.18 from both ends, ReGLU blocks, in infinitesimal form.** If `E` and `D` have rank
`d`, every write of a block before block `m` has rank `d`, no gate column and no value column of
a read of a block up to `m` vanishes, and for every block after `m` no write row vanishes and the
gate and value columns of its read are in general position (any `d` of them linearly
independent, more than `d` of them), the direction
`cobDir θ X + rescaleDir θ α + rescaleDirGate k θ β` determines `X`, `α` and `β`. -/
theorem cobDir_add_rescaleDir_add_rescaleDirGate_injective_of_rank_E_D (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (m : Fin L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0)
    (ha : ∀ ℓ, m < ℓ → ∀ i, (fun a => θ.write ℓ i a) ≠ 0)
    (hgp : ∀ ℓ, m < ℓ → ∀ S : Finset (hid ℓ ⊕ hid ℓ), S.card ≤ Fintype.card d →
      LinearIndependent ℝ fun j : S => (θ.read ℓ)ᵀ j)
    (hcard : ∀ ℓ, m < ℓ → Fintype.card d < Fintype.card (hid ℓ ⊕ hid ℓ)) :
    Function.Injective
      fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
        cobDir θ p.1 + rescaleDir θ p.2.1 + rescaleDirGate k θ p.2.2 := by
  sorry

end Skips
