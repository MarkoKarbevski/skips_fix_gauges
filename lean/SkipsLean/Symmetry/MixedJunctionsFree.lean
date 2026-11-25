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

omit [DecidableEq d] in
/-- A matrix `M` of full column rank can be cancelled on the left: `M X = M Y` gives `X = Y` (a
copy of the private `mul_left_cancel_of_rank` of `Dimension/UpperBoundRMSNorm.lean`). -/
private theorem mul_left_cancel_of_rank_mjf {m : Type*} [Fintype m] {M : Matrix m d ℝ}
    (hM : M.rank = Fintype.card d) {X Y : Matrix d d ℝ} (h : M * X = M * Y) : X = Y := by
  classical
  -- `v ↦ v M` is onto, so some `B` has `B M = 1`.
  obtain ⟨B, hB⟩ : ∃ B : Matrix d m ℝ, B * M = 1 := by
    have hs := (Matrix.vecMul_surjective_iff_rank_eq_card (M := M)).2 hM
    choose v hv using fun i : d => hs (Pi.single i 1)
    have hv' : ∀ i, v i ᵥ* M = Pi.single i 1 := hv
    refine ⟨Matrix.of v, ?_⟩
    ext i j
    rw [Matrix.mul_apply_eq_vecMul, show (Matrix.of v) i = v i from rfl, hv',
      Matrix.one_eq_pi_single]
  calc X = B * M * X := by rw [hB, Matrix.one_mul]
    _ = B * M * Y := by rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc]
    _ = Y := by rw [hB, Matrix.one_mul]

/-- **Proposition A.1 (iii), the copies act independently:** if `E` has rank `d` and all `U_ℓ`
and `V_ℓ` are invertible, then `T_{G,K}(θ) = T_{G',K'}(θ)` only for `G = G'` and `K = K'`. -/
theorem cobMixed_injective (θ : Params A.mixed dIn dOut) (hE : θ.E.rank = Fintype.card d)
    (hU : ∀ ℓ, IsUnit (θ.mixU ℓ)) (hV : ∀ ℓ, IsUnit (θ.mixV ℓ))
    {G Q G' Q' : Fin (L + 1) → GL d ℝ} {K K' : Fin L → GL d ℝ}
    (h : θ.cobMixed G Q K = θ.cobMixed G' Q' K') : G = G' ∧ K = K' := by
  -- the embeddings: `E G_0 = E G'_0`
  have hE0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E * (G' 0 : Matrix d d ℝ) := congrArg Params.E h
  -- the identity units: `G_{ℓ-1}⁻¹ U_ℓ K_ℓ = G'_{ℓ-1}⁻¹ U_ℓ K'_ℓ`, `K_ℓ⁻¹ V_ℓ G_ℓ = K'_ℓ⁻¹ V_ℓ G'_ℓ`
  have hUe := congrArg Params.mixU h
  have hVe := congrArg Params.mixV h
  simp only [Params.cobMixed, Params.mixU_mix, Params.mixV_mix] at hUe hVe
  -- `K_ℓ = K'_ℓ` once `G_{ℓ-1} = G'_{ℓ-1}`, since `U_ℓ` is invertible
  have hK : ∀ ℓ : Fin L, G ℓ.castSucc = G' ℓ.castSucc → K ℓ = K' ℓ := by
    intro ℓ hc
    have e := congrFun hUe ℓ
    rw [hc, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_right_inj] at e
    exact Units.ext ((hU ℓ).mul_left_cancel e)
  -- `G_ℓ = G'_ℓ` once `K_ℓ = K'_ℓ`, since `V_ℓ` is invertible
  have hGs : ∀ ℓ : Fin L, K ℓ = K' ℓ → G ℓ.succ = G' ℓ.succ := by
    intro ℓ hk
    have e := congrFun hVe ℓ
    rw [hk, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_right_inj] at e
    exact Units.ext ((hV ℓ).mul_left_cancel e)
  -- `G_k = G'_k` by induction on `k`, starting from `E` of rank `d`
  have hG : ∀ k, G k = G' k := by
    intro k
    induction k using Fin.induction with
    | zero => exact Units.ext (mul_left_cancel_of_rank_mjf hE hE0)
    | succ ℓ ih => exact hGs ℓ (hK ℓ ih)
  exact ⟨funext hG, funext fun ℓ => hK ℓ (hG _)⟩

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
