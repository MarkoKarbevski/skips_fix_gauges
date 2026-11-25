import SkipsLean.Dimension.RescalingGate
import SkipsLean.Dimension.UpperBoundRMSNormZero
import SkipsLean.Dimension.UpperBoundReadout
import SkipsLean.Basic.EigenvectorsGeneralPosition

/-!
# Locally free action, the form with the readout: the symmetries inside blocks

Paper (skips paper), Lemma A.18 (Locally free action): "The same holds if the readout has rank
`d_model` and every block has width at least `d_model`." Its proof: "The second statement follows
by the mirror induction from the readout, `D ↦ G_L^{-1} D`: rescalings act freely on the rows of
a generic write, except that for ReGLU a row fixes only the product `cc′` of the gate and value
scales of its unit; each read, of rank `d_model` and with generic columns, then forces
`G_{ℓ−1} = I` and the remaining scales to be 1. With RMSNorm the changes of basis lie in
`CO(d_model)` or `O(d_model)`, and the argument is unchanged."

`Dimension/UpperBoundReadout.lean` has this sentence in infinitesimal form for the changes of
basis alone (`cobDir_injective_of_rank_D`). Here the same form with the symmetries inside blocks:
the twins of `cobDir_add_rescaleDir_injective` (gated blocks, the rescaling of the values),
`cobDir_add_rescaleDirMlp_injective` (ReLU and ReLU² blocks), of
`cobDir_add_rescaleDir_add_rescaleDirGate_injective` (ReGLU blocks) and of
`cobDir_add_scaleDir_injective` (`ε = 0`: the scaling of each hidden state), which ask `E` and
the writes of rank `d`. Each asks instead: `D` of rank `d`, every read of rank `d`, no row of a
write zero.

* For ReLU and ReLU² blocks the degree `k` is not `0` (the write row of a hidden unit moves by
  `−k α_i a_i`).
* For ReGLU blocks a write row gives only `α_i − k β_i`, and the read gives the rest when its
  columns are in general position: any `d` of the `2 d_hidden` gate and value columns are
  linearly independent, and there are more than `d` of them (so the read has rank `d`; at generic
  parameters this holds when the block has width at least `d ≥ 1`). Rank `d` alone is not enough:
  for `d = 2` and one block with two hidden units, gate columns `e_1, e_2`, value columns
  `e_2, e_1` and `E = 0`, the direction of `X_0 = diag(1, −1)`, `α = β = (1, −1)`, `X_1 = 0` is
  `0` (`ai_notes/locally_free_readout_check_2026-11-25.py`).
* For `ε = 0` the statement asks `E ≠ 0` and every write nonzero, and nothing of the matrices
  `Y_ℓ` (the twin with the embedding asks them antisymmetric).

The statements for the group ("only the identity fixes `θ`") are in
`Symmetry/LocallyFreeEmbedding.lean` and `Symmetry/LocallyFreeReadout.lean`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- **Lemma A.18, second sentence, for gated blocks, in infinitesimal form.** If `D` and every
read have rank `d` and no row of a write vanishes, the direction `cobDir θ X + rescaleDir θ α`
determines `X` and `α`. -/
theorem cobDir_add_rescaleDir_injective_of_rank_D
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hD : θ.D.rank = Fintype.card d) (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0) :
    Function.Injective fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
      cobDir θ p.1 + rescaleDir θ p.2 := by
  sorry

/-- **Lemma A.18, second sentence, for ReLU and ReLU² blocks, in infinitesimal form.** For
`k ≠ 0`: if `D` and every read have rank `d` and no row of a write vanishes, the direction
`cobDir θ X + rescaleDirMlp k θ α` determines `X` and `α`. -/
theorem cobDir_add_rescaleDirMlp_injective_of_rank_D (k : ℕ) (hk : k ≠ 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (hD : θ.D.rank = Fintype.card d) (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0) :
    Function.Injective fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
      cobDir θ p.1 + rescaleDirMlp k θ p.2 := by
  sorry

/-- **Lemma A.18, second sentence, for ReGLU blocks, in infinitesimal form.** If `D` has rank
`d`, no row of a write vanishes, and the gate and value columns of every read are in general
position (any `d` of them are linearly independent, and there are more than `d`), the direction
`cobDir θ X + rescaleDir θ α + rescaleDirGate k θ β` determines `X`, `α` and `β`. -/
theorem cobDir_add_rescaleDir_add_rescaleDirGate_injective_of_rank_D (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hD : θ.D.rank = Fintype.card d) (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0)
    (hgp : ∀ ℓ (S : Finset (hid ℓ ⊕ hid ℓ)), S.card ≤ Fintype.card d →
      LinearIndependent ℝ fun j : S => (θ.read ℓ)ᵀ j)
    (hcard : ∀ ℓ, Fintype.card d < Fintype.card (hid ℓ ⊕ hid ℓ)) :
    Function.Injective
      fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
        cobDir θ p.1 + rescaleDir θ p.2.1 + rescaleDirGate k θ p.2.2 := by
  sorry

/-- **Lemma A.18, second sentence, for `ε = 0`, in infinitesimal form** (any kind of block). If
`D` and every read have rank `d`, and `E` and every write are not zero, the direction
`cobDir θ Y + scaleDir θ β` determines the matrices `Y_0, …, Y_L` and the numbers
`β_0, …, β_L`. -/
theorem cobDir_add_scaleDir_injective_of_rank_D {A : Arch T d L} (θ : Params A dIn dOut)
    (hD : θ.D.rank = Fintype.card d) (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (hE : θ.E ≠ 0) (hw : ∀ ℓ, θ.write ℓ ≠ 0) :
    Function.Injective fun p : (Fin (L + 1) → Matrix d d ℝ) × (Fin (L + 1) → ℝ) =>
      cobDir θ p.1 + scaleDir θ p.2 := by
  sorry

end Skips
