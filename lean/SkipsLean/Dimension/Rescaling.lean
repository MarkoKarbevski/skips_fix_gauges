import SkipsLean.Network.Blocks
import SkipsLean.Dimension.UpperBound

/-!
# Gated blocks: the rescalings inside the blocks, and the upper bound with them

Paper (dimension paper): Appendix B, "The symmetries inside the blocks", and Theorem 4.3 for gated
blocks without normalization.

In a gated block the value column `e_i` of hidden unit `i` and its write row `a_i` can be rescaled,
`(e_i, a_i) ↦ (e_i / λ, λ a_i)` with `λ ≠ 0`, without changing the map of the block. With
`λ = e^{τ α}` this moves the parameters, to first order in `τ`, in the direction `rescaleDir θ α`:
the value columns of the read of block `ℓ` change by `-α_{ℓ,i} e_i`, the write rows by
`α_{ℓ,i} a_i`, and nothing else changes.

These directions are flat. Together with the directions `cobDir θ X` of the changes of basis they
span a space of dimension `(L + 1) d² + s`, where `s` is the number of hidden units of the network,
when `E` and the writes have rank `d` and no value column of a read vanishes (Lemma B.1). So the
functional dimension is at most `P - (L + 1) d² - s`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- The direction of the rescalings of the values of the hidden units of a gated network: the
rescaling `λ = e^{τ α ℓ i}` of hidden unit `i` of block `ℓ`, to first order in `τ`. -/
def rescaleDir (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (α : ∀ ℓ, hid ℓ → ℝ) : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut where
  E := 0
  read ℓ := Matrix.of fun k j => Sum.elim (fun _ => 0) (fun i => -(α ℓ i) * θ.read ℓ k (Sum.inr i)) j
  write ℓ := Matrix.of fun i k => α ℓ i * θ.write ℓ i k
  D := 0

variable (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)

/-- The rescalings of the values preserve the function: with every value column of the read of
block `ℓ` divided by `c ℓ i ≠ 0` and the write row of the same hidden unit multiplied by `c ℓ i`,
the network computes the same function. -/
theorem eval_rescale (c : ∀ ℓ, hid ℓ → ℝ) (hc : ∀ ℓ i, c ℓ i ≠ 0)
    (θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ'.E = θ.E) (hD : θ'.D = θ.D)
    (hg : ∀ ℓ k i, θ'.read ℓ k (Sum.inl i) = θ.read ℓ k (Sum.inl i))
    (hv : ∀ ℓ k i, θ'.read ℓ k (Sum.inr i) = (c ℓ i)⁻¹ * θ.read ℓ k (Sum.inr i))
    (hw : ∀ ℓ i k, θ'.write ℓ i k = c ℓ i * θ.write ℓ i k)
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (Arch.gated σ id hid) S θ' x = eval (Arch.gated σ id hid) S θ x := by
  -- the hidden states of `θ'` and `θ` agree, by induction along the network
  have hh : ∀ ℓ : Fin (L + 1),
      hidden (Arch.gated σ id hid) S θ' x ℓ = hidden (Arch.gated σ id hid) S θ x ℓ := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => rw [hidden_zero, hidden_zero, hE]
    | succ ℓ ih =>
      -- the stream term `h S_ℓ` is the same; compare the outputs of block `ℓ`
      rw [hidden_succ, hidden_succ, ih]
      congr 1
      set h := hidden (Arch.gated σ id hid) S θ x ℓ.castSucc
      -- the gates are the same, and the values are divided by `c ℓ i`
      have hz : ∀ t i, (h * θ'.read ℓ) t (Sum.inl i) = (h * θ.read ℓ) t (Sum.inl i) := by
        intro t i
        simp only [Matrix.mul_apply, hg]
      have hu : ∀ t i,
          (h * θ'.read ℓ) t (Sum.inr i) = (c ℓ i)⁻¹ * (h * θ.read ℓ) t (Sum.inr i) := by
        intro t i
        rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hv]
        ring
      -- so hidden unit `i` contributes `σ(z_i) (w_i / c) (c a_i) = σ(z_i) w_i a_i`
      ext t k
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show σ ((h * θ'.read ℓ) t (Sum.inl i)) * (h * θ'.read ℓ) t (Sum.inr i) * θ'.write ℓ i k =
        σ ((h * θ.read ℓ) t (Sum.inl i)) * (h * θ.read ℓ) t (Sum.inr i) * θ.write ℓ i k
      rw [hz, hu, hw]
      field_simp [hc ℓ i]
  -- hence the outputs agree
  rw [eval, eval, hh, hD]

/-- The directions of the rescalings are flat. -/
theorem rescaleDir_mem_flat (hσ : Differentiable ℝ σ) (α : ∀ ℓ, hid ℓ → ℝ) :
    rescaleDir θ α ∈ flat (Arch.gated σ id hid) 0 θ := by
  sorry

/-- **Lemma B.1 for gated blocks.** If `E` and every write have rank `d` and no value column of a
read vanishes, the direction `cobDir θ X + rescaleDir θ α` determines `X` and `α`. -/
theorem cobDir_add_rescaleDir_injective (hE : θ.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) :
    Function.Injective fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
      cobDir θ p.1 + rescaleDir θ p.2 := by
  sorry

/-- **Theorem 4.3 for gated blocks, without normalization,** under the conditions of its proof:
the functional dimension is at most `P - (L + 1) d² - s`, with `s` the number of hidden units of
the network. -/
theorem funDim_add_le_skipless_gated (hσ : Differentiable ℝ σ)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.gated σ id hid) 0 θ + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

end Skips
