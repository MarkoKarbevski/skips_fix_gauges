import SkipsLean.Dimension.UpperBoundReadoutInside

/-!
# Locally free action when one block is narrower than `d`: from both ends

Paper (skips paper), Lemma A.18 (Locally free action): "If the embedding has rank `d_model` and
every block has width at least `d_model`, then at generic parameters the changes of basis and the
symmetries inside blocks act locally freely. The same holds if the readout has rank `d_model` and
every block has width at least `d_model`." Remark A.19: "The width condition is needed: at a
hidden state of a skipless network that is written and read at rank `m < d_model`, the changes
of basis that fix the parameters form a family of dimension `(d_model − m)²`".

The proofs of Proposition A.33 (ii) and of Proposition A.35 use the lemma for the network without
a dead unit ("The other columns are those of the network without this unit, whose symmetries are
the changes of basis of its `L + 1` hidden states and `s − 1` rescalings"). When the block of the
dead unit has exactly `d_model` hidden units, that network has one block of width `d_model − 1`,
to which neither sentence of the lemma applies as stated. The two inductions of its proof
together still give the conclusion, when both the embedding and the readout have rank `d`: the
changes of basis at the hidden states up to the one that the narrow block reads are fixed from
the embedding, and those from the one that it writes on are fixed from the readout. Nothing is
asked of the write of the narrow block. (Two adjacent blocks narrower than `d` are not covered,
as Remark A.19 says: `ai_notes/locally_free_one_narrow_block_check_2026-11-25.py`.)

Here this form, in infinitesimal form, for a block `m`: `E` and the writes of the blocks before
`m` have rank `d`, `D` and the reads of the blocks after `m` have rank `d`. For ReLU and ReLU²
blocks with the rescalings: no read column of a block up to `m` and no write row of a block after
`m` vanishes, and `k ≠ 0`. For `m` the last block and `m` the first block these are close to the
forms with the embedding and with the readout (`cobDir_injective`,
`cobDir_injective_of_rank_D` and their twins), which do not ask the rank of the other end.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- **Lemma A.18 from both ends, the changes of basis, in infinitesimal form** (any kind of
block). If `E` and `D` have rank `d`, every write of a block before block `m` has rank `d` and
every read of a block after block `m` has rank `d`, the direction `cobDir θ X` determines `X`. -/
theorem cobDir_injective_of_rank_E_D {A : Arch T d L} (θ : Params A dIn dOut) (m : Fin L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hr : ∀ ℓ, m < ℓ → (θ.read ℓ).rank = Fintype.card d) :
    Function.Injective (cobDir θ) := by
  sorry

/-- **Lemma A.18 from both ends, ReLU and ReLU² blocks, in infinitesimal form.** For `k ≠ 0`: if
`E` and `D` have rank `d`, every write of a block before block `m` and every read of a block
after block `m` has rank `d`, no read column of a block up to `m` and no write row of a block
after `m` vanishes, the direction `cobDir θ X + rescaleDirMlp k θ α` determines `X` and `α`. -/
theorem cobDir_add_rescaleDirMlp_injective_of_rank_E_D (k : ℕ) (hk : k ≠ 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (m : Fin L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hr : ∀ ℓ, m < ℓ → (θ.read ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a i) ≠ 0)
    (ha : ∀ ℓ, m < ℓ → ∀ i, (fun a => θ.write ℓ i a) ≠ 0) :
    Function.Injective fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
      cobDir θ p.1 + rescaleDirMlp k θ p.2 := by
  sorry

end Skips
