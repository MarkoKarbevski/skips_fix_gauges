import SkipsLean.Depth.SuffixGated
import SkipsLean.Depth.BlockIdentityGated

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

/-- Helper: the direction at the hidden state after a gated block whose values are rescaled. If
`ż^g = 0` and `ż^v_{t j} = −a_j z^v_{t j}`, then `(w̃' ⊙ ż^g ⊙ z^v + w̃ ⊙ ż^v) V + ŵ (V Y + diag(a) V)
= (ŵ V) Y` with `ŵ = w̃ ⊙ z^v`: the rescaling of the values cancels the rescaling of the write. -/
private theorem dir_rescale_eq {m n p : Type*} [Fintype n] [Fintype p]
    (V : Matrix n p ℝ) (Y : Matrix p p ℝ) (a : n → ℝ) (w w' : Matrix m n ℝ)
    (z zdot : Matrix m (n ⊕ n) ℝ) (h1 : ∀ t j, zdot t (Sum.inl j) = 0)
    (h2 : ∀ t j, zdot t (Sum.inr j) = -(a j) * z t (Sum.inr j)) :
    (Matrix.of fun t j => w' t j * zdot t (Sum.inl j) * z t (Sum.inr j)
        + w t j * zdot t (Sum.inr j)) * V
      + (Matrix.of fun t j => w t j * z t (Sum.inr j))
        * (V * Y + Matrix.of fun i c => a i * V i c)
      = ((Matrix.of fun t j => w t j * z t (Sum.inr j)) * V) * Y := by
  -- `−(ŵ diag(a)) V + ŵ (diag(a) V) = 0`, entrywise
  have h0 : (Matrix.of fun t j => w' t j * zdot t (Sum.inl j) * z t (Sum.inr j)
        + w t j * zdot t (Sum.inr j)) * V
      + (Matrix.of fun t j => w t j * z t (Sum.inr j)) * (Matrix.of fun i c => a i * V i c)
      = 0 := by
    ext t c
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply, h1, h2,
      ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun j _ => by ring
  -- what is left is `ŵ (V Y) = (ŵ V) Y`
  rw [Matrix.mul_add, ← Matrix.mul_assoc, add_left_comm, h0, add_zero]

omit [Fintype T] [DecidableEq d] in
/-- Helper: if the direction `(w̃' ⊙ ż^g ⊙ z^v + w̃ ⊙ ż^v) V + ŵ η_V` at the hidden state after
block `ℓ` is `(ŵ V) Y`, and (16) holds after block `ℓ` with `Y` and `η`, then `𝓛 = 0`. -/
private theorem blockLHSGated_eq_zero_of
    (θ η : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (ℓ : Fin L)
    (Y : Matrix d d ℝ) (w w' : Matrix T (hid ℓ) ℝ) (z zdot : Matrix T (hid ℓ ⊕ hid ℓ) ℝ)
    (hdir : (Matrix.of fun t j => w' t j * zdot t (Sum.inl j) * z t (Sum.inr j)
          + w t j * zdot t (Sum.inr j)) * θ.write ℓ
        + (Matrix.of fun t j => w t j * z t (Sum.inr j)) * η.write ℓ
        = ((Matrix.of fun t j => w t j * z t (Sum.inr j)) * θ.write ℓ) * Y)
    (hY : SuffixFlat (Arch.gated σ id hid) θ ℓ.succ Y η) :
    blockLHSGated θ ℓ η w w' z zdot = 0 := by
  unfold blockLHSGated
  rw [hdir]
  exact hY _

/-- **The converse of the claim, gated blocks, case (n):** the directions of the form (19),
`cobDir θ X + rescaleDir θ α`, satisfy the identity (16) for every `k`, with `Z = X k`. -/
theorem suffixFlat_cobDir_add_rescaleDir (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (k : Fin (L + 1))
    (X : Fin (L + 1) → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ) :
    SuffixFlat (Arch.gated σ id hid) θ k (X k) (cobDir θ X + rescaleDir θ α) := by
  induction k using Fin.reverseInduction with
  | last =>
    -- `𝓑_{>L}(h) = h D`: the left side is `(h X_L) D + h η_D = h X_L D − h X_L D = 0`
    intro h
    calc _ = h * X (Fin.last L) * θ.D + h * (cobDir θ X + rescaleDir θ α).D :=
          congrArg₂ (· + ·)
            (fderiv_suffix_last (Arch.gated (T := T) (d := d) σ id hid) θ rfl h
              (h * X (Fin.last L)))
            (fderiv_params_suffix_last (Arch.gated (T := T) (d := d) σ id hid) θ rfl h
              (cobDir θ X + rescaleDir θ α))
      _ = 0 := by
          show h * X (Fin.last L) * θ.D + h * (-(X (Fin.last L) * θ.D) + 0) = 0
          rw [add_zero, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel]
  | cast ℓ ih =>
    -- by the chain rule through block `ℓ` (equation (28)), it suffices that `𝓛 = 0` at every `n`
    refine (suffixFlat_castSucc_iff_gated hσ θ ℓ (X ℓ.castSucc) _).2 fun n => ?_
    -- `Z W + η_read = (rescaleDir θ α).read ℓ`: the change of basis cancels
    have hr : X ℓ.castSucc * θ.read ℓ + (cobDir θ X + rescaleDir θ α).read ℓ
        = (rescaleDir θ α).read ℓ := by
      rw [Params.add_read]
      exact add_neg_cancel_left _ _
    rw [hr]
    -- so `ż^g = 0` and `ż^v_{t j} = −α_j z^v_{t j}`, and the direction after the block is
    -- `(ŵ V) X_{ℓ+1}`; then `𝓛 = 0` is (16) after block `ℓ`, the induction hypothesis
    refine blockLHSGated_eq_zero_of θ _ ℓ (X ℓ.succ) _ _ _ _ ?_ ih
    exact dir_rescale_eq (θ.write ℓ) (X ℓ.succ) (α ℓ) _ _ _ _
      (fun t j => Finset.sum_eq_zero fun c _ => mul_zero (n t c))
      (fun t j => by
        rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        show n t c * (-(α ℓ j) * θ.read ℓ c (Sum.inr j))
          = -(α ℓ j) * (n t c * θ.read ℓ c (Sum.inr j))
        ring)

end Skips
