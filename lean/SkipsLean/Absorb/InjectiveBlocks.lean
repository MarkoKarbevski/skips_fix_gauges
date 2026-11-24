import SkipsLean.Absorb.FirstBlock
import SkipsLean.Residual.Folding

/-!
# Injective residual blocks: every block of an equal skipless network has `2 d` units

Paper (absorb paper): Proposition 4.6 (Injective blocks: `2 d_model` units in every block): "Let
`σ` be ReLU or GELU, without normalization, and let `E` and `D` have rank `d_model`. Suppose that
every block of the residual network is injective on tokens when `σ` is replaced by ReLU:
`x + B_ℓ(x) ≠ x' + B_ℓ(x')` for all tokens `x ≠ x'`. Then every skipless network of `σ` blocks,
of any depth and with the same `d_model`, that equals the residual network has at least
`2 d_model` hidden units in every block." After it: "The condition holds when every block has
`‖W_read‖ ‖W_write‖ < 1`, in spectral norm".

Its proof (Appendix A.1). "GELU reduces to ReLU: if a residual GELU network equals a skipless one,
the two ReLU networks with the same weights are equal". Step 1: the residual network is injective
in `x E`. Step 2: every skipless block is injective; it uses "A continuous, positively
homogeneous, injective map `ψ` of `ℝ^{1×d_model}` to itself is onto: […] by invariance of domain
it is open". Step 3: an injective block has `2 d_model` units: "Fix `u` off the hyperplanes […]
Injectivity makes this matrix invertible, so `|S| ≥ d_model` at `u` and at `−u`. The active sets
at `u` and `−u` are disjoint".

Stated here with the block maps on one row: `blockMapRes θ ℓ` (`Residual/Folding.lean`,
`h ↦ h + σ(h W_read^ℓ) W_write^ℓ`) for the residual network, and `vanillaBlock`
(`Absorb/Block.lean`) for one skipless block. Invariance of domain is the hypothesis from the
literature `InvarianceOfDomain d` (`Literature/InvarianceOfDomain.lean`). The skipless network
has any number `L'` of blocks and any widths `hid'`, the same `d`, `d_in`, `d_out` and tokens.

* Step 2, the topological fact: under invariance of domain, a continuous, positively homogeneous,
  injective map of `ℝ^d` to itself is onto.
* Step 3: an injective ReLU block of `ℝ^d` to itself has at least `2 d` hidden units.
* The proposition for ReLU and for GELU, and with the condition `‖W_read‖ ‖W_write‖ < 1` (the
  spectral norms as Lipschitz constants in the Euclidean norm, as in
  `not_folds_of_norm_mul_norm_lt_one`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T dIn dOut : Type*} {d : Type} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Proof of Proposition 4.6, Step 2, the topological fact, under invariance of domain:** a
continuous, positively homogeneous, injective map of `ℝ^d` to itself is onto. -/
theorem surjective_of_injective_of_posHomogeneous (hinv : InvarianceOfDomain d)
    (ψ : (d → ℝ) → (d → ℝ)) (hc : Continuous ψ)
    (hh : ∀ (c : ℝ) (u : d → ℝ), 0 < c → ψ (c • u) = c • ψ u) (hi : Function.Injective ψ) :
    Function.Surjective ψ := by
  sorry

/-- **Proof of Proposition 4.6, Step 3:** a ReLU block `h ↦ ReLU(h W_read) W_write` of `ℝ^d` to
itself that is injective has at least `2 d` hidden units. -/
theorem two_mul_card_le_of_injective_vanillaBlock_relu {m : Type*} [Fintype m]
    (Wr : Matrix d m ℝ) (Ww : Matrix m d ℝ)
    (hi : Function.Injective (vanillaBlock relu Wr Ww)) :
    2 * Fintype.card d ≤ Fintype.card m := by
  sorry

/-- **Proposition 4.6 for ReLU, under invariance of domain:** let `E` and `D` have rank `d` and
let every block of the residual ReLU network be injective on rows. Then every skipless ReLU
network with the same `d`, of any depth and any widths, that equals the residual network has at
least `2 d` hidden units in every block. -/
theorem two_mul_card_le_of_eval_eq_skipless_relu [Nonempty T] (hinv : InvarianceOfDomain d)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hinj : ∀ ℓ, Function.Injective (blockMapRes θ ℓ))
    {L' : ℕ} (hid' : Fin L' → Type) [∀ ℓ, Fintype (hid' ℓ)]
    (θ' : Params (Arch.mlp (T := T) (d := d) relu id hid') dIn dOut)
    (heq : ∀ X : Matrix T dIn ℝ,
      eval (Arch.mlp relu id hid') 0 θ' X = eval (Arch.mlp relu id hid) 1 θ X) :
    ∀ ℓ : Fin L', 2 * Fintype.card d ≤ Fintype.card (hid' ℓ) := by
  sorry

/-- **Proposition 4.6 for GELU, under invariance of domain:** let `E` and `D` have rank `d` and
let every block of the residual network be injective on rows when GELU is replaced by ReLU. Then
every skipless GELU network with the same `d`, of any depth and any widths, that equals the
residual GELU network has at least `2 d` hidden units in every block. -/
theorem two_mul_card_le_of_eval_eq_skipless_gelu [Nonempty T] (hinv : InvarianceOfDomain d)
    (θ : Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hinj : ∀ ℓ, Function.Injective (blockMapRes (θ.withActivation relu) ℓ))
    {L' : ℕ} (hid' : Fin L' → Type) [∀ ℓ, Fintype (hid' ℓ)]
    (θ' : Params (Arch.mlp (T := T) (d := d) gelu id hid') dIn dOut)
    (heq : ∀ X : Matrix T dIn ℝ,
      eval (Arch.mlp gelu id hid') 0 θ' X = eval (Arch.mlp gelu id hid) 1 θ X) :
    ∀ ℓ : Fin L', 2 * Fintype.card d ≤ Fintype.card (hid' ℓ) := by
  sorry

/-- **Proposition 4.6 for ReLU with the condition `‖W_read‖ ‖W_write‖ < 1`, under invariance of
domain:** if `E` and `D` have rank `d` and every block of the residual ReLU network has Lipschitz
constants `a ℓ` of its read and `b ℓ` of its write, in the Euclidean norm, with
`a ℓ * b ℓ < 1`, every skipless ReLU network with the same `d` that equals it has at least `2 d`
hidden units in every block. -/
theorem two_mul_card_le_of_eval_eq_skipless_relu_of_norm_lt_one [Nonempty T]
    (hinv : InvarianceOfDomain d)
    (θ : Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) (a b : Fin L → ℝ)
    (ha : ∀ ℓ (v : d → ℝ),
      Real.sqrt ((v ᵥ* θ.read ℓ) ⬝ᵥ (v ᵥ* θ.read ℓ)) ≤ a ℓ * Real.sqrt (v ⬝ᵥ v))
    (hb : ∀ ℓ (u : hid ℓ → ℝ),
      Real.sqrt ((u ᵥ* θ.write ℓ) ⬝ᵥ (u ᵥ* θ.write ℓ)) ≤ b ℓ * Real.sqrt (u ⬝ᵥ u))
    (hab : ∀ ℓ, a ℓ * b ℓ < 1)
    {L' : ℕ} (hid' : Fin L' → Type) [∀ ℓ, Fintype (hid' ℓ)]
    (θ' : Params (Arch.mlp (T := T) (d := d) relu id hid') dIn dOut)
    (heq : ∀ X : Matrix T dIn ℝ,
      eval (Arch.mlp relu id hid') 0 θ' X = eval (Arch.mlp relu id hid) 1 θ X) :
    ∀ ℓ : Fin L', 2 * Fintype.card d ≤ Fintype.card (hid' ℓ) := by
  sorry

/-- **Proposition 4.6 for GELU with the condition `‖W_read‖ ‖W_write‖ < 1`, under invariance of
domain.** -/
theorem two_mul_card_le_of_eval_eq_skipless_gelu_of_norm_lt_one [Nonempty T]
    (hinv : InvarianceOfDomain d)
    (θ : Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) (a b : Fin L → ℝ)
    (ha : ∀ ℓ (v : d → ℝ),
      Real.sqrt ((v ᵥ* θ.read ℓ) ⬝ᵥ (v ᵥ* θ.read ℓ)) ≤ a ℓ * Real.sqrt (v ⬝ᵥ v))
    (hb : ∀ ℓ (u : hid ℓ → ℝ),
      Real.sqrt ((u ᵥ* θ.write ℓ) ⬝ᵥ (u ᵥ* θ.write ℓ)) ≤ b ℓ * Real.sqrt (u ⬝ᵥ u))
    (hab : ∀ ℓ, a ℓ * b ℓ < 1)
    {L' : ℕ} (hid' : Fin L' → Type) [∀ ℓ, Fintype (hid' ℓ)]
    (θ' : Params (Arch.mlp (T := T) (d := d) gelu id hid') dIn dOut)
    (heq : ∀ X : Matrix T dIn ℝ,
      eval (Arch.mlp gelu id hid') 0 θ' X = eval (Arch.mlp gelu id hid) 1 θ X) :
    ∀ ℓ : Fin L', 2 * Fintype.card d ≤ Fintype.card (hid' ℓ) := by
  sorry

end Skips
