import SkipsLean.Absorb.PatternMaps
import SkipsLean.Dimension.RankCriterionOn
import SkipsLean.Residual.DepthRescale

/-!
# Full residual ReLU networks and a lower bound from counting dimensions

Paper (absorb paper): Proposition 4.7 (A lower bound from counting dimensions) and the paragraph
before it. "Let the residual network have `P` weights and `s` hidden units. […] So on any finite
set of inputs, the Jacobian of the outputs with respect to the weights has rank at most
`P − d_model² − s` […]. We call a residual ReLU network full if this rank is reached on some
finite set of inputs at which no unit has argument `0`: its only redundancy is then these
symmetries." The proposition: "Consider ReLU networks of `L` blocks without normalization. The
full residual networks form an open set of weights. For almost every full residual network, every
skipless network of `L` blocks with the same `d_model` that equals it has, in total, at least
`L d_model² / (2 d_model − 1)` more hidden units." After it: "Full networks exist: every network
with generic weights is full once all its writes are scaled by a small enough factor."

Stated here for the residual network with the hidden units `hid ℓ` (any widths) and
`d_in ≥ d ≥ 1`:

* `IsFull θ`: a finite batch on which no unit has argument `0` at `θ` and on which the Jacobian
  has rank `P − d² − s`.
* On a batch on which no unit has argument `0` at `θ`, the Jacobian has rank at most
  `P − d² − s`, at every `θ`.
* The full networks form an open set.
* The proposition, in the setting of the main text (every block of the skipless network has at
  least `d` hidden units, Section 2): for almost every `θ`, if `θ` is full then no skipless ReLU
  network of `L` blocks with the widths `m ℓ ≥ d` equals it when
  `(2d − 1) ∑_ℓ m ℓ < (2d − 1) ∑_ℓ d_hidden^ℓ + L d²`, that is, with fewer than
  `L d² / (2d − 1)` more hidden units in total. Sard's theorem is a hypothesis from the
  literature (`Literature/Sard.lean`), as in the proof of the paper.
* Full networks exist (Lemma A.30 of the skips paper, `Residual/DepthRescale.lean`): for generic
  `θ` and all small `τ ≠ 0`, `θ_τ` is full.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **A full residual ReLU network:** the rank `P − d² − s` of the Jacobian is reached on some
finite batch of inputs at which no unit has argument `0`. -/
def IsFull (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) : Prop :=
  ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
    (∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
      (hidden (Arch.mlp relu id hid) 1 θ (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) ∧
    jacobianRank (Arch.mlp relu id hid) 1 X θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)

/-- **"On any finite set of inputs, the Jacobian […] has rank at most `P − d² − s`", at every
parameter:** for `d_in ≥ d ≥ 1`, on a batch on which no unit has argument `0` at `θ`. -/
theorem jacobianRank_add_le_residual_relu_of_ne_zero [Nonempty d]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ (i : Fin n) (ℓ : Fin L) (t : T) (j : hid ℓ),
      (hidden (Arch.mlp relu id hid) 1 θ (X i) ℓ.castSucc * θ.read ℓ) t j ≠ 0) :
    jacobianRank (Arch.mlp relu id hid) 1 X θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Proposition 4.7, first sentence:** for `d_in ≥ d ≥ 1`, the full residual ReLU networks form
an open set of weights. -/
theorem isOpen_setOf_isFull [Nonempty d] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    IsOpen {θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut | IsFull θ} := by
  sorry

/-- **Proposition 4.7, second sentence, given Sard's theorem:** for `d_in ≥ d ≥ 1`, for almost
every residual ReLU network `θ` of `L` blocks: if `θ` is full, no skipless ReLU network of `L`
blocks with the same `d` and at least `d` hidden units in every block equals it unless it has, in
total, at least `L d² / (2d − 1)` more hidden units. -/
theorem ae_isFull_imp_eval_ne_skipless_relu [Nonempty d]
    (hSard : ∀ (m : Fin L → ℕ) (r : ℕ), SardCriticalValues
      (Params (Arch.mlp (T := T) (d := d) relu id (fun ℓ => Fin (m ℓ))) dIn dOut) (Fin r → ℝ))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, IsFull θ → ∀ m : Fin L → ℕ, (∀ ℓ, Fintype.card d ≤ m ℓ) →
      (2 * Fintype.card d - 1) * ∑ ℓ, m ℓ
          < (2 * Fintype.card d - 1) * ∑ ℓ, Fintype.card (hid ℓ) + L * Fintype.card d ^ 2 →
      ∀ η : Params (Arch.mlp (T := T) (d := d) relu id (fun ℓ => Fin (m ℓ))) dIn dOut,
        eval (Arch.mlp relu id hid) 1 θ ≠ eval (Arch.mlp relu id (fun ℓ => Fin (m ℓ))) 0 η := by
  sorry

/-- **"Full networks exist: every network with generic weights is full once all its writes are
scaled by a small enough factor":** with `d_in, d_out ≥ d ≥ 2` and blocks of any widths, for
generic `θ` and all small `τ ≠ 0`, the network `θ_τ` is full. -/
theorem ae_eventually_isFull_smallWrites
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ), IsFull (θ.smallWrites τ) := by
  sorry

end Skips
