import SkipsLean.Symmetry.FiniteSymmetriesCompose

/-!
# Changes of basis at different hidden states commute

Paper (skips paper), Proposition A.1 (iii): "One group per junction. The maps of (i) and (ii)
commute when they act at different junctions. A skipless network therefore carries one copy of
`G` per hidden state, and a network of mixed blocks one more copy of `GL(d_model)` per block."

Here, for the maps of (ii) (`Params.cob θ G K`: the writes of the hidden state `h_ℓ` are
multiplied by `G_ℓ`, its reads by `K_ℓ⁻¹`; `K = G` without normalization and for `ε > 0`, and
`G_ℓ = c_ℓ Q_ℓ`, `K_ℓ = Q_ℓ` for `ε = 0`):

* `cob_comm_of_commute`: two such maps commute when their matrices commute at every hidden state;
* `cob_mulSingle_comm`: in particular when they act at different hidden states.

The dimension of the group that a skipless network carries ("one copy of `G` per hidden state")
is `Symmetry/CobGroup.lean`. The maps of (i) are for mixed blocks, which the library does not
have.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d]

/-- **Two changes of basis commute when their matrices commute at every hidden state.** -/
theorem cob_comm_of_commute {A : Arch T d L} (θ : Params A dIn dOut)
    (G K G' K' : Fin (L + 1) → GL d ℝ) (hG : ∀ ℓ, Commute (G ℓ) (G' ℓ))
    (hK : ∀ ℓ, Commute (K ℓ) (K' ℓ)) :
    (θ.cob G K).cob G' K' = (θ.cob G' K').cob G K := by
  rw [cob_cob, cob_cob]
  congr 1
  · funext ℓ
    exact (hG ℓ).eq
  · funext ℓ
    exact (hK ℓ).eq

/-- **Proposition A.1 (iii) of the skips paper, "The maps of (i) and (ii) commute when they act
at different junctions", for the maps of (ii):** a change of basis at the hidden state `h_ℓ`
(the matrices `g` on its writes and `k⁻¹` on its reads) and one at another hidden state `h_ℓ'`
commute. -/
theorem cob_mulSingle_comm {A : Arch T d L} (θ : Params A dIn dOut) {ℓ ℓ' : Fin (L + 1)}
    (h : ℓ ≠ ℓ') (g k g' k' : GL d ℝ) :
    (θ.cob (Pi.mulSingle ℓ g) (Pi.mulSingle ℓ k)).cob (Pi.mulSingle ℓ' g') (Pi.mulSingle ℓ' k')
      = (θ.cob (Pi.mulSingle ℓ' g') (Pi.mulSingle ℓ' k')).cob
          (Pi.mulSingle ℓ g) (Pi.mulSingle ℓ k) := by
  -- at every hidden state one of the two matrices is the identity
  have key : ∀ (a b : GL d ℝ) (m : Fin (L + 1)),
      Commute ((Pi.mulSingle ℓ a : Fin (L + 1) → GL d ℝ) m)
        ((Pi.mulSingle ℓ' b : Fin (L + 1) → GL d ℝ) m) := by
    intro a b m
    by_cases hm : m = ℓ
    · rw [hm, Pi.mulSingle_eq_of_ne h]
      exact Commute.one_right _
    · rw [Pi.mulSingle_eq_of_ne hm]
      exact Commute.one_left _
  exact cob_comm_of_commute θ _ _ _ _ (key g g') (key k k')

end Skips
