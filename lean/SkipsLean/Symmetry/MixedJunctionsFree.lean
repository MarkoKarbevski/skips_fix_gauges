import SkipsLean.Symmetry.MixedJunctions

/-!
# Networks of mixed blocks: the copies of the groups act independently

Paper (skips paper), Proposition A.1 (iii) (One group per junction): "The maps of (i) and (ii)
commute when they act at different junctions. A skipless network therefore carries one copy of
`𝒢` per hidden state, and a network of mixed blocks one more copy of `GL(d_model)` per block."

`Symmetry/MixedJunctions.lean` has the maps `T_{G,K}` (`θ.cobMixed G Q K`), their invariance, and
that they compose as the product group with one factor per junction and commute. Here: the
factors are independent. At a parameter whose embedding has rank `d_model` and whose identity
units have invertible reads `U_ℓ` and writes `V_ℓ`, the element `(G, K)` of the product group is
determined by `T_{G,K}(θ)`: the action is free at `θ`, so no factor acts through another
(`cobMixed_injective`); in particular only the identity fixes `θ` (`cobMixed_eq_self_iff`).
The matrices `Q_ℓ` that multiply the reads through a normalization play no part: they are
determined by the `G_ℓ` in each case of normalization.
-/

namespace Skips

open Matrix

variable {T : Type*} {d : Type} {dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d]
  [Fintype dIn]
variable {A : Arch T d L}

/-- **Proposition A.1 (iii), the copies act independently:** if `E` has rank `d` and all `U_ℓ`
and `V_ℓ` are invertible, then `T_{G,K}(θ) = T_{G',K'}(θ)` only for `G = G'` and `K = K'`. -/
theorem cobMixed_injective (θ : Params A.mixed dIn dOut) (hE : θ.E.rank = Fintype.card d)
    (hU : ∀ ℓ, IsUnit (θ.mixU ℓ)) (hV : ∀ ℓ, IsUnit (θ.mixV ℓ))
    {G Q G' Q' : Fin (L + 1) → GL d ℝ} {K K' : Fin L → GL d ℝ}
    (h : θ.cobMixed G Q K = θ.cobMixed G' Q' K') : G = G' ∧ K = K' := by
  sorry

omit [Fintype dIn] in
/-- Helper: the identity of the product group acts as the identity. -/
private theorem cobMixed_one_mjf (θ : Params A.mixed dIn dOut) : θ.cobMixed 1 1 1 = θ := by
  rw [cobMixed_one_one]
  unfold Params.mixK
  simp only [Pi.one_apply, inv_one, Units.val_one, Matrix.mul_one, Matrix.one_mul]
  exact Params.mix_unmix θ

/-- **Proposition A.1 (iii), only the identity fixes `θ`:** if `E` has rank `d` and all `U_ℓ`
and `V_ℓ` are invertible, then `T_{G,K}(θ) = θ`, with the reads through the normalization
multiplied as the others (`Q = G`), exactly when all `G_ℓ` and `K_ℓ` are the identity. -/
theorem cobMixed_eq_self_iff (θ : Params A.mixed dIn dOut) (hE : θ.E.rank = Fintype.card d)
    (hU : ∀ ℓ, IsUnit (θ.mixU ℓ)) (hV : ∀ ℓ, IsUnit (θ.mixV ℓ))
    (G : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ) :
    θ.cobMixed G G K = θ ↔ G = 1 ∧ K = 1 := by
  constructor
  · intro h
    have h' : θ.cobMixed G G K = θ.cobMixed 1 1 1 := by rw [h, cobMixed_one_mjf]
    exact cobMixed_injective θ hE hU hV h'
  · rintro ⟨rfl, rfl⟩
    exact cobMixed_one_mjf θ

end Skips
