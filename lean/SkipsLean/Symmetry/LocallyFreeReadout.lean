import SkipsLean.Symmetry.LocallyFreeEmbedding
import SkipsLean.Basic.EigenvectorsGeneralPosition

/-!
# Locally free action: only the identity fixes the parameters (the form with the readout)

Paper (skips paper), Lemma A.18 (Locally free action): "The same holds if the readout has rank
`d_model` and every block has width at least `d_model`." Its proof: "The second statement follows
by the mirror induction from the readout, `D ↦ G_L^{-1} D`: rescalings act freely on the rows of
a generic write, except that for ReGLU a row fixes only the product `cc′` of the gate and value
scales of its unit; each read, of rank `d_model` and with generic columns, then forces
`G_{ℓ−1} = I` and the remaining scales to be 1. With RMSNorm the changes of basis lie in
`CO(d_model)` or `O(d_model)`, and the argument is unchanged."

The twins of the statements of `Symmetry/LocallyFreeEmbedding.lean`, for the group: **if changes
of basis and rescalings fix `θ`, they are the identity**, at every `θ` whose readout and reads
have rank `d` and whose write rows are not zero (at generic parameters: `d_out ≥ d` and blocks of
width at least `d`).

* `cob_eq_self_of_rank_D`: any kind of block, `θ.cob G K = θ` (writes multiplied by `G`, reads by
  `K⁻¹`): `K = 1`.
* `cob_rescaleMlp_eq_self_of_rank_D`: ReLU and ReLU² blocks, degree `k ≠ 0`, positive rescalings
  (a write row is divided by `c^k`, so `c^k = 1`; for even `k` the write row does not tell `c`
  from `−c`).
* `cob_rescale_eq_self_of_rank_D`: gated blocks with any gate, any numbers `c`.
* `cob_rescale_rescaleGate_eq_self_of_rank_D`: ReGLU blocks, positive rescalings `c` of the
  gates; the gate and value columns of every read in general position (any `d` of them linearly
  independent, more than `d` of them), the form in which "generic columns" is used:
  `Basic/EigenvectorsGeneralPosition.lean`. Rank `d` alone is not enough (the example in the
  header of `Dimension/UpperBoundReadoutInside.lean`).
* `cob_rmsNorm_zero_eq_self_of_rank_D`: `ε = 0`, `G_ℓ = c_ℓ Q_ℓ` on the writes and `Q_ℓ⁻¹` on the
  reads; asks `E ≠ 0` and every write nonzero. Nothing is asked of `c` and `Q` beyond
  `G_ℓ = c_ℓ Q_ℓ`.

Not stated: `ε = 0` together with rescalings inside blocks.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- Helper (the private `mul_right_cancel_of_rank_ubd` of `Dimension/UpperBoundReadout.lean`): a
matrix `M` of rank equal to its number of rows cancels on the right, `X M = Y M → X = Y`. -/
private theorem mul_right_cancel_of_rank_lfr {m n k : Type*} [Fintype m] [Fintype n]
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

omit [Fintype T] [Fintype dIn] in
/-- **Lemma A.18, second sentence, for the changes of basis.** If `D` and every read have rank
`d` and the changes of basis fix `θ` (`θ.cob G K = θ`: the writes are multiplied by `G`, the
reads by `K⁻¹`), then `K = 1`. -/
theorem cob_eq_self_of_rank_D {A : Arch T d L} (θ : Params A dIn dOut)
    (G K : Fin (L + 1) → GL d ℝ) (hD : θ.D.rank = Fintype.card d)
    (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d) (h : θ.cob G K = θ) : K = 1 := by
  funext ℓ
  -- it suffices that the inverse is the identity
  have key : ((K ℓ)⁻¹ : GL d ℝ) = 1 := by
    apply Units.ext
    induction ℓ using Fin.lastCases with
    | last =>
      -- the readout: `K_L⁻¹ D = D`, and `D` has rank `d`
      have h0 : (↑(K (Fin.last L))⁻¹ : Matrix d d ℝ) * θ.D = (1 : Matrix d d ℝ) * θ.D := by
        rw [Matrix.one_mul]
        exact congrArg Params.D h
      exact mul_right_cancel_of_rank_lfr θ.D hD h0
    | cast ℓ =>
      -- the read of block `ℓ + 1`: `K_ℓ⁻¹ W = W`, and `W` has rank `d`
      have h1 : (↑(K ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ
          = (1 : Matrix d d ℝ) * θ.read ℓ := by
        rw [Matrix.one_mul]
        exact congrArg (fun η => η.read ℓ) h
      exact mul_right_cancel_of_rank_lfr (θ.read ℓ) (hr ℓ) h1
  exact inv_eq_one.mp key

/-- **Lemma A.18, second sentence, for ReLU and ReLU² blocks.** For `k ≠ 0`: if `D` and every
read have rank `d`, no row of a write vanishes, and the changes of basis `G` with positive
rescalings `c` of the hidden units fix `θ`, then `G = 1` and `c = 1`. -/
theorem cob_rescaleMlp_eq_self_of_rank_D (k : ℕ) (hk : k ≠ 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (G : Fin (L + 1) → GL d ℝ)
    (c : ∀ ℓ, hid ℓ → ℝ) (hc : ∀ ℓ i, 0 < c ℓ i) (hD : θ.D.rank = Fintype.card d)
    (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0)
    (h : (θ.cob G G).rescaleMlp k c = θ) : G = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  sorry

/-- **Lemma A.18, second sentence, for gated blocks with any gate.** If `D` and every read have
rank `d`, no row of a write vanishes, and the changes of basis `G` with the rescalings `c` of
the values fix `θ`, then `G = 1` and `c = 1`. -/
theorem cob_rescale_eq_self_of_rank_D
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (G : Fin (L + 1) → GL d ℝ)
    (c : ∀ ℓ, hid ℓ → ℝ) (hD : θ.D.rank = Fintype.card d)
    (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0)
    (h : (θ.cob G G).rescale c = θ) : G = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  sorry

/-- **Lemma A.18, second sentence, for ReGLU blocks.** If `D` has rank `d`, no row of a write
vanishes, the gate and value columns of every read are in general position (any `d` of them are
linearly independent, and there are more than `d`), and the changes of basis `G` with the
rescalings `c'` of the values and positive rescalings `c` of the gates fix `θ`, then `G = 1`,
`c = 1` and `c' = 1`. -/
theorem cob_rescale_rescaleGate_eq_self_of_rank_D (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (G : Fin (L + 1) → GL d ℝ)
    (c c' : ∀ ℓ, hid ℓ → ℝ) (hc : ∀ ℓ i, 0 < c ℓ i) (hD : θ.D.rank = Fintype.card d)
    (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0)
    (hgp : ∀ ℓ (S : Finset (hid ℓ ⊕ hid ℓ)), S.card ≤ Fintype.card d →
      LinearIndependent ℝ fun j : S => (θ.read ℓ)ᵀ j)
    (hcard : ∀ ℓ, Fintype.card d < Fintype.card (hid ℓ ⊕ hid ℓ))
    (h : ((θ.cob G G).rescale c').rescaleGate k c = θ) :
    G = 1 ∧ (∀ ℓ i, c ℓ i = 1) ∧ ∀ ℓ i, c' ℓ i = 1 := by
  sorry

/-- **Lemma A.18, second sentence, under pre-RMSNorm with `ε = 0`.** The change of basis
`G_ℓ = c_ℓ Q_ℓ` multiplies the writes by `G_ℓ` and the reads by `Q_ℓ⁻¹`. If `D` and every read
have rank `d`, `E` and every write are not zero, and these changes of basis fix `θ`, then
`c_ℓ = 1` and `Q_ℓ = 1` for every `ℓ`. -/
theorem cob_rmsNorm_zero_eq_self_of_rank_D {A : Arch T d L} (θ : Params A dIn dOut)
    (G Q : Fin (L + 1) → GL d ℝ) (c : Fin (L + 1) → ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ))
    (hD : θ.D.rank = Fintype.card d) (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (hE : θ.E ≠ 0) (hw : ∀ ℓ, θ.write ℓ ≠ 0)
    (h : θ.cob G Q = θ) : (∀ ℓ, c ℓ = 1) ∧ Q = 1 := by
  sorry

end Skips
