import SkipsLean.Dimension.UpperBound

/-!
# Locally free action of the changes of basis: the form with the readout

Paper (skips paper), Lemma A.18 (Locally free action): "If the embedding has rank `d_model` and
every block has width at least `d_model`, then at generic parameters the changes of basis and the
symmetries inside blocks act locally freely. The same holds if the readout has rank `d_model` and
every block has width at least `d_model`." (The dimension paper, Lemma B.1, has the first
sentence.)

`cobDir_injective` (`Dimension/UpperBound.lean`) is the infinitesimal form of the first sentence
for the changes of basis: if `E` and every write have rank `d`, the direction `cobDir θ X`
determines `X`. Here the second sentence in the same form: if `D` and every read have rank `d`
(at generic parameters every read of a block of width at least `d` has rank `d`), the direction
determines `X`: `X_L` from the entry `−X_L D` at the readout, and `X_ℓ`, `ℓ < L`, from the entry
`−X_ℓ W_read^{ℓ+1}` at the read of the next block.

The form with the readout for the symmetries inside blocks is in
`Dimension/UpperBoundReadoutInside.lean`; the statements on the group ("only the identity fixes
`θ`") are in `Symmetry/LocallyFreeEmbedding.lean` and `Symmetry/LocallyFreeReadout.lean`.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {A : Arch T d L}

/-- Helper: a matrix `M` of rank equal to its number of rows cancels on the right,
`X M = Y M → X = Y` (`v ↦ v M` is injective by rank–nullity for `Mᵀ`). -/
private theorem mul_right_cancel_of_rank_ubd {m n k : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ} (h : X * M = Y * M) :
    X = Y := by
  -- `w ↦ Mᵀ w` is injective: `rank Mᵀ + dim ker Mᵀ = card m`
  have hinj : Function.Injective Mᵀ.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker Mᵀ.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [← Matrix.rank_transpose, Matrix.rank] at hM
    omega
  -- compare `X` and `Y` row by row
  ext i j
  have hrow : Mᵀ.mulVecLin (fun l => X i l) = Mᵀ.mulVecLin (fun l => Y i l) := by
    funext p
    have := congrFun (congrFun h i) p
    show (Mᵀ *ᵥ fun l => X i l) p = (Mᵀ *ᵥ fun l => Y i l) p
    rw [Matrix.mulVec_transpose, Matrix.mulVec_transpose]
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this
  exact congrFun (hinj hrow) j

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- **Lemma A.18 of the skips paper, "The same holds if the readout has rank `d_model` and every
block has width at least `d_model`", for the changes of basis, in infinitesimal form.** If `D`
and every read have rank `d`, the direction `cobDir θ X` determines `X`. -/
theorem cobDir_injective_of_rank_D (θ : Params A dIn dOut) (hD : θ.D.rank = Fintype.card d)
    (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d) :
    Function.Injective (cobDir θ) := by
  intro X Y h
  funext ℓ
  induction ℓ using Fin.lastCases with
  | last =>
    -- the readout component: `X_L D = Y_L D`, and `D` has rank `d`
    have h0 : -(X (Fin.last L) * θ.D) = -(Y (Fin.last L) * θ.D) := congrArg Params.D h
    exact mul_right_cancel_of_rank_ubd θ.D hD (neg_injective h0)
  | cast ℓ =>
    -- the read component of block `ℓ + 1`: `X_ℓ W_read = Y_ℓ W_read`
    have h1 : -(X ℓ.castSucc * θ.read ℓ) = -(Y ℓ.castSucc * θ.read ℓ) :=
      congrArg (fun η => η.read ℓ) h
    exact mul_right_cancel_of_rank_ubd (θ.read ℓ) (hr ℓ) (neg_injective h1)

end Skips
