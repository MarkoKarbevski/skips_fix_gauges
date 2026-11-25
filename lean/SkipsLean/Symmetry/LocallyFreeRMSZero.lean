import SkipsLean.Symmetry.LocallyFreeReadout
import SkipsLean.Symmetry.LocallyFreeAttention

/-!
# Locally free action under pre-RMSNorm with `ε = 0`, with the symmetries inside blocks

Paper (skips paper), Lemma A.18 (Locally free action): "Consider an MLP network, skipless or
residual, without normalization or with pre-RMSNorm, […] and the symmetries inside blocks of
Section 4.1." Its proof: "With RMSNorm the changes of basis lie in `CO(d_model)` or
`O(d_model)`, and the argument is unchanged." (The dimension paper, Lemma B.1: "Without
normalization or under pre-RMSNorm".)

For `ε > 0` the changes of basis are the orthogonal ones among `θ.cob G G`, and the statements of
`Symmetry/LocallyFreeEmbedding.lean`, `Symmetry/LocallyFreeReadout.lean` and
`Symmetry/LocallyFreeAttention.lean` apply. For `ε = 0` the change of basis `G_ℓ = s_ℓ Q_ℓ`,
`s_ℓ > 0`, `Q_ℓ` orthogonal, multiplies the writes by `G_ℓ` and the reads by `Q_ℓ⁻¹`
(`eval_cob_rmsNorm_zero`): this is `θ.cob G Q`, and those files have it for the changes of basis
alone. Here **`ε = 0` together with the symmetries inside blocks**: if such changes of basis and
symmetries inside the blocks fix `θ`, then `s_ℓ = 1`, `Q_ℓ = 1` and the symmetries inside the
blocks are the identity.

* With the embedding (`E` and the writes of rank `d ≥ 1`): ReLU and ReLU² blocks, gated blocks,
  ReGLU blocks, attention blocks. `E G_0 = E` gives `s_0 Q_0 = 1`, so `s_0 = 1` and `Q_0 = 1`;
  then the read and the write of each block, as without normalization.
* With the readout (`D` and the reads of rank `d ≥ 1`, `E ≠ 0`, no write row zero, the rescaled
  read columns not zero): ReLU and ReLU² blocks, gated blocks, ReGLU blocks. Here a rescaled read
  column is an eigenvector of the orthogonal matrix `Q_{ℓ−1}⁻¹` with a positive eigenvalue, which
  is therefore `1`; so the read columns need not be in general position (for ReGLU blocks without
  normalization they must be: `Symmetry/LocallyFreeReadout.lean`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- Helper (the private `mul_left_cancel_of_rank` of `Dimension/UpperBound.lean`): a matrix `M`
of rank equal to its number of columns cancels on the left, `M X = M Y → X = Y`. -/
private theorem mul_left_cancel_of_rank_lfz {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
    (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ} (h : M * X = M * Y) : X = Y := by
  -- `v ↦ M v` is injective: `rank M + dim ker M = card n`
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [Matrix.rank] at hM
    omega
  -- compare `X` and `Y` column by column
  ext i j
  have hcol : M.mulVecLin (fun l => X l j) = M.mulVecLin (fun l => Y l j) := by
    funext p
    have := congrFun (congrFun h p) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  exact congrFun (hinj hcol) i

/-- Helper (the private `mul_right_cancel_of_rank_ubd` of `Dimension/UpperBoundReadout.lean`): a
matrix `M` of rank equal to its number of rows cancels on the right, `X M = Y M → X = Y`. -/
private theorem mul_right_cancel_of_rank_lfz {m n k : Type*} [Fintype m] [Fintype n]
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

/-- Helper (the argument inside `cob_rmsNorm_zero_eq_self_of_rank_E`): if `s Q = 1` with `Q`
orthogonal and `s > 0`, then `s = 1` and `Q = 1`. -/
private theorem eq_one_of_smul_eq_one_lfz [Nonempty d] (Q : GL d ℝ)
    (hQ : (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) {s : ℝ} (hs : 0 < s)
    (h : s • (Q : Matrix d d ℝ) = 1) : s = 1 ∧ Q = 1 := by
  -- `(s Q)(s Q)ᵀ = s² 1`, and `s Q = 1`: `s² = 1`
  have hQQ := (Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ
  have h2 : (s • (Q : Matrix d d ℝ)) * (s • (Q : Matrix d d ℝ))ᵀ
      = (s * s) • (1 : Matrix d d ℝ) := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hQQ]
  rw [h, Matrix.transpose_one, Matrix.one_mul] at h2
  obtain ⟨x⟩ := (inferInstance : Nonempty d)
  have h3 := congrFun (congrFun h2 x) x
  rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h3
  -- so `s = 1`, and then `Q = 1`
  have hs1 : s = 1 := by nlinarith
  refine ⟨hs1, Units.ext ?_⟩
  rw [hs1, one_smul] at h
  exact h

/-- Helper: a positive eigenvalue of `Q⁻¹`, `Q` orthogonal, is `1`: if `Q⁻¹ w = r w` with `w ≠ 0`
and `r > 0`, then `r = 1` (`Q⁻¹ = Qᵀ` keeps the length, so `r² = 1`). -/
private theorem eq_one_of_orthogonal_mulVec_lfz (Q : GL d ℝ)
    (hQ : (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) {w : d → ℝ} {r : ℝ}
    (hw : (↑Q⁻¹ : Matrix d d ℝ) *ᵥ w = r • w) (h0 : w ≠ 0) (hr : 0 < r) : r = 1 := by
  have hQQ := (Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ
  have hQQ' := (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hQ
  -- `Q⁻¹ = Qᵀ`
  have hinv : (↑Q⁻¹ : Matrix d d ℝ) = (Q : Matrix d d ℝ)ᵀ := by
    calc (↑Q⁻¹ : Matrix d d ℝ) = ((Q : Matrix d d ℝ)ᵀ * (Q : Matrix d d ℝ)) * ↑Q⁻¹ := by
          rw [hQQ', Matrix.one_mul]
      _ = (Q : Matrix d d ℝ)ᵀ * ((Q : Matrix d d ℝ) * ↑Q⁻¹) := Matrix.mul_assoc _ _ _
      _ = (Q : Matrix d d ℝ)ᵀ := by rw [Units.mul_inv, Matrix.mul_one]
  -- `Qᵀ` keeps the length: `(r w) ⬝ (r w) = w ⬝ w`
  have hlen : (r • w) ⬝ᵥ (r • w) = w ⬝ᵥ w := by
    rw [← hw, hinv, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hQQ,
      Matrix.one_mulVec]
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc] at hlen
  -- `w ⬝ w ≠ 0`, so `r² = 1`, and `r > 0`
  have hne : w ⬝ᵥ w ≠ 0 := fun h1 => h0 (dotProduct_self_eq_zero.mp h1)
  have hrr : r * r = 1 := mul_right_cancel₀ hne (hlen.trans (one_mul _).symm)
  nlinarith

/-- Helper (the private `eq_one_of_mul_smul_one_lfr` of `Symmetry/LocallyFreeReadout.lean`): if
`X (r 1) = X` and `X ≠ 0`, then `r = 1`. -/
private theorem eq_one_of_mul_smul_one_lfz {m : Type*} (X : Matrix m d ℝ) (hX : X ≠ 0) {r : ℝ}
    (h : X * (r • (1 : Matrix d d ℝ)) = X) : r = 1 := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hX
  obtain ⟨q, hpq⟩ := Function.ne_iff.mp hp
  have h1 := congrFun (congrFun h p) q
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul] at h1
  exact mul_right_cancel₀ hpq (h1.trans (one_mul _).symm)

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Lemma A.18, first sentence, `ε = 0`, ReLU and ReLU² blocks.** Let `G_ℓ = s_ℓ Q_ℓ` with
`s_ℓ > 0` and `Q_ℓ` orthogonal. If `E` and every write have rank `d ≥ 1`, no column of a read
vanishes, and these changes of basis with the rescalings `c` of the hidden units fix `θ`, then
`s = 1`, `Q = 1` and `c = 1`. -/
theorem cob_rmsNorm_zero_rescaleMlp_eq_self_of_rank_E [Nonempty d] (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (s : Fin (L + 1) → ℝ) (c : ∀ ℓ, hid ℓ → ℝ) (hs : ∀ ℓ, 0 < s ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hcol : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0)
    (h : (θ.cob G Q).rescaleMlp k c = θ) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  -- `G_ℓ = 1` gives `s_ℓ = 1` and `Q_ℓ = 1`
  have hGQ : ∀ ℓ, G ℓ = 1 → s ℓ = 1 ∧ Q ℓ = 1 := fun ℓ h1 =>
    eq_one_of_smul_eq_one_lfz (Q ℓ) (hQ ℓ) (hs ℓ) (by rw [← hG ℓ, h1, Units.val_one])
  -- the embedding: `E G_0 = E`, and `E` has rank `d`
  have h0 : G 0 = 1 := by
    have hE0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E * (1 : Matrix d d ℝ) := by
      rw [Matrix.mul_one]
      have h1 := congrArg Params.E h
      exact h1
    exact Units.ext (mul_left_cancel_of_rank_lfz θ.E hE hE0)
  -- block `ℓ`: if `G_{ℓ-1} = 1`, then `Q_{ℓ-1} = 1`, `c_ℓ = 1` and `G_ℓ = 1`
  have key : ∀ ℓ : Fin L, G ℓ.castSucc = 1 → (∀ i, c ℓ i = 1) ∧ G ℓ.succ = 1 := by
    intro ℓ hℓ
    have hQℓ : Q ℓ.castSucc = 1 := (hGQ _ hℓ).2
    -- the read column `i` becomes `c_i w_i`, and `w_i ≠ 0`
    have hc : ∀ i, c ℓ i = 1 := by
      intro i
      obtain ⟨a, ha⟩ := Function.ne_iff.mp (hcol ℓ i)
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) i
      change c ℓ i * ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a i = θ.read ℓ a i at hr
      rw [hQℓ, inv_one, Units.val_one, Matrix.one_mul] at hr
      exact mul_right_cancel₀ ha (hr.trans (one_mul _).symm)
    refine ⟨hc, Units.ext ?_⟩
    -- the write becomes `(1 ^ k)⁻¹ W G_ℓ = W G_ℓ`, and `W` has rank `d`
    refine mul_left_cancel_of_rank_lfz (θ.write ℓ) (hw ℓ) ?_
    rw [Units.val_one, Matrix.mul_one]
    ext i a
    have hr := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
    change (c ℓ i ^ k)⁻¹ * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) i a = θ.write ℓ i a at hr
    rw [hc i, one_pow, inv_one, one_mul] at hr
    exact hr
  -- by induction along the network
  have hG1 : ∀ ℓ : Fin (L + 1), G ℓ = 1 := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => exact h0
    | succ ℓ ih => exact (key ℓ ih).2
  exact ⟨fun ℓ => (hGQ ℓ (hG1 ℓ)).1, funext fun ℓ => (hGQ ℓ (hG1 ℓ)).2,
    fun ℓ => (key ℓ (hG1 ℓ.castSucc)).1⟩

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Lemma A.18, first sentence, `ε = 0`, gated blocks with any gate.** Let `G_ℓ = s_ℓ Q_ℓ`
with `s_ℓ > 0` and `Q_ℓ` orthogonal. If `E` and every write have rank `d ≥ 1`, no value column
of a read vanishes, and these changes of basis with the rescalings `c` of the values fix `θ`,
then `s = 1`, `Q = 1` and `c = 1`. -/
theorem cob_rmsNorm_zero_rescale_eq_self_of_rank_E [Nonempty d]
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (s : Fin (L + 1) → ℝ) (c : ∀ ℓ, hid ℓ → ℝ) (hs : ∀ ℓ, 0 < s ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (h : (θ.cob G Q).rescale c = θ) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  -- `G_ℓ = 1` gives `s_ℓ = 1` and `Q_ℓ = 1`
  have hGQ : ∀ ℓ, G ℓ = 1 → s ℓ = 1 ∧ Q ℓ = 1 := fun ℓ h1 =>
    eq_one_of_smul_eq_one_lfz (Q ℓ) (hQ ℓ) (hs ℓ) (by rw [← hG ℓ, h1, Units.val_one])
  -- the embedding: `E G_0 = E`, and `E` has rank `d`
  have h0 : G 0 = 1 := by
    have hE0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E * (1 : Matrix d d ℝ) := by
      rw [Matrix.mul_one]
      have h1 := congrArg Params.E h
      exact h1
    exact Units.ext (mul_left_cancel_of_rank_lfz θ.E hE hE0)
  -- block `ℓ`: if `G_{ℓ-1} = 1`, then `Q_{ℓ-1} = 1`, `c_ℓ = 1` and `G_ℓ = 1`
  have key : ∀ ℓ : Fin L, G ℓ.castSucc = 1 → (∀ i, c ℓ i = 1) ∧ G ℓ.succ = 1 := by
    intro ℓ hℓ
    have hQℓ : Q ℓ.castSucc = 1 := (hGQ _ hℓ).2
    -- the value column `i` becomes `c_i⁻¹ e_i`, and `e_i ≠ 0`
    have hc : ∀ i, c ℓ i = 1 := by
      intro i
      obtain ⟨a, ha⟩ := Function.ne_iff.mp (hv ℓ i)
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inr i)
      change (c ℓ i)⁻¹ * ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inr i)
        = θ.read ℓ a (Sum.inr i) at hr
      rw [hQℓ, inv_one, Units.val_one, Matrix.one_mul] at hr
      exact inv_eq_one.mp (mul_right_cancel₀ ha (hr.trans (one_mul _).symm))
    refine ⟨hc, Units.ext ?_⟩
    -- the write becomes `1 · W G_ℓ = W G_ℓ`, and `W` has rank `d`
    refine mul_left_cancel_of_rank_lfz (θ.write ℓ) (hw ℓ) ?_
    rw [Units.val_one, Matrix.mul_one]
    ext i a
    have hr := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
    change c ℓ i * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) i a = θ.write ℓ i a at hr
    rw [hc i, one_mul] at hr
    exact hr
  -- by induction along the network
  have hG1 : ∀ ℓ : Fin (L + 1), G ℓ = 1 := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => exact h0
    | succ ℓ ih => exact (key ℓ ih).2
  exact ⟨fun ℓ => (hGQ ℓ (hG1 ℓ)).1, funext fun ℓ => (hGQ ℓ (hG1 ℓ)).2,
    fun ℓ => (key ℓ (hG1 ℓ.castSucc)).1⟩

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Lemma A.18, first sentence, `ε = 0`, ReGLU blocks.** Let `G_ℓ = s_ℓ Q_ℓ` with `s_ℓ > 0`
and `Q_ℓ` orthogonal. If `E` and every write have rank `d ≥ 1`, no gate column and no value
column of a read vanishes, and these changes of basis with the rescalings `c'` of the values and
`c` of the gates fix `θ`, then `s = 1`, `Q = 1`, `c = 1` and `c' = 1`. -/
theorem cob_rmsNorm_zero_rescale_rescaleGate_eq_self_of_rank_E [Nonempty d] (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (s : Fin (L + 1) → ℝ) (c c' : ∀ ℓ, hid ℓ → ℝ) (hs : ∀ ℓ, 0 < s ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0)
    (h : ((θ.cob G Q).rescale c').rescaleGate k c = θ) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ (∀ ℓ i, c ℓ i = 1) ∧ ∀ ℓ i, c' ℓ i = 1 := by
  -- `G_ℓ = 1` gives `s_ℓ = 1` and `Q_ℓ = 1`
  have hGQ : ∀ ℓ, G ℓ = 1 → s ℓ = 1 ∧ Q ℓ = 1 := fun ℓ h1 =>
    eq_one_of_smul_eq_one_lfz (Q ℓ) (hQ ℓ) (hs ℓ) (by rw [← hG ℓ, h1, Units.val_one])
  -- the embedding: `E G_0 = E`, and `E` has rank `d`
  have h0 : G 0 = 1 := by
    have hE0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E * (1 : Matrix d d ℝ) := by
      rw [Matrix.mul_one]
      have h1 := congrArg Params.E h
      exact h1
    exact Units.ext (mul_left_cancel_of_rank_lfz θ.E hE hE0)
  -- block `ℓ`: if `G_{ℓ-1} = 1`, then `Q_{ℓ-1} = 1`, `c_ℓ = 1`, `c'_ℓ = 1` and `G_ℓ = 1`
  have key : ∀ ℓ : Fin L, G ℓ.castSucc = 1 →
      (∀ i, c ℓ i = 1) ∧ (∀ i, c' ℓ i = 1) ∧ G ℓ.succ = 1 := by
    intro ℓ hℓ
    have hQℓ : Q ℓ.castSucc = 1 := (hGQ _ hℓ).2
    -- the gate column `i` becomes `c_i g_i`, and `g_i ≠ 0`
    have hc : ∀ i, c ℓ i = 1 := by
      intro i
      obtain ⟨a, ha⟩ := Function.ne_iff.mp (hg ℓ i)
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inl i)
      change c ℓ i * ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inl i)
        = θ.read ℓ a (Sum.inl i) at hr
      rw [hQℓ, inv_one, Units.val_one, Matrix.one_mul] at hr
      exact mul_right_cancel₀ ha (hr.trans (one_mul _).symm)
    -- the value column `i` becomes `c'_i⁻¹ e_i`, and `e_i ≠ 0`
    have hc' : ∀ i, c' ℓ i = 1 := by
      intro i
      obtain ⟨a, ha⟩ := Function.ne_iff.mp (hv ℓ i)
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inr i)
      change (c' ℓ i)⁻¹ * ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inr i)
        = θ.read ℓ a (Sum.inr i) at hr
      rw [hQℓ, inv_one, Units.val_one, Matrix.one_mul] at hr
      exact inv_eq_one.mp (mul_right_cancel₀ ha (hr.trans (one_mul _).symm))
    refine ⟨hc, hc', Units.ext ?_⟩
    -- the write becomes `(1 ^ k)⁻¹ (1 · W G_ℓ) = W G_ℓ`, and `W` has rank `d`
    refine mul_left_cancel_of_rank_lfz (θ.write ℓ) (hw ℓ) ?_
    rw [Units.val_one, Matrix.mul_one]
    ext i a
    have hr := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
    change (c ℓ i ^ k)⁻¹ * (c' ℓ i * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) i a)
      = θ.write ℓ i a at hr
    rw [hc i, hc' i, one_pow, inv_one, one_mul, one_mul] at hr
    exact hr
  -- by induction along the network
  have hG1 : ∀ ℓ : Fin (L + 1), G ℓ = 1 := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => exact h0
    | succ ℓ ih => exact (key ℓ ih).2.2
  exact ⟨fun ℓ => (hGQ ℓ (hG1 ℓ)).1, funext fun ℓ => (hGQ ℓ (hG1 ℓ)).2,
    fun ℓ => (key ℓ (hG1 ℓ.castSucc)).1, fun ℓ => (key ℓ (hG1 ℓ.castSucc)).2.1⟩

omit [Fintype T] [Fintype dIn] in
/-- **Lemma A.18, second sentence, `ε = 0`, ReLU and ReLU² blocks.** Let `G_ℓ = s_ℓ Q_ℓ` with
`Q_ℓ` orthogonal (the proof does not use `s_ℓ > 0`, and the statement does not ask it). If `D`
and every read have rank `d ≥ 1`, `E ≠ 0`, no column of a read and no row of a write vanishes,
and these changes of basis with positive rescalings `c` of the hidden units fix `θ`, then
`s = 1`, `Q = 1` and `c = 1`. -/
theorem cob_rmsNorm_zero_rescaleMlp_eq_self_of_rank_D [Nonempty d] (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (s : Fin (L + 1) → ℝ) (c : ∀ ℓ, hid ℓ → ℝ) (hc : ∀ ℓ i, 0 < c ℓ i)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hD : θ.D.rank = Fintype.card d) (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (hE : θ.E ≠ 0) (hcol : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0)
    (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0)
    (h : (θ.cob G Q).rescaleMlp k c = θ) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  -- the readout: `Q_L⁻¹ D = D`, and `D` has rank `d`
  have hL : Q (Fin.last L) = 1 := by
    have hD0 : (↑(Q (Fin.last L))⁻¹ : Matrix d d ℝ) * θ.D = (1 : Matrix d d ℝ) * θ.D := by
      rw [Matrix.one_mul]
      have h1 := congrArg Params.D h
      exact h1
    exact inv_eq_one.mp (Units.ext (mul_right_cancel_of_rank_lfz θ.D hD hD0))
  -- block `ℓ`: if `Q_ℓ = 1`, then `c_ℓ = 1`, `s_ℓ = 1` and `Q_{ℓ-1} = 1`
  have key : ∀ ℓ : Fin L, Q ℓ.succ = 1 →
      (∀ i, c ℓ i = 1) ∧ s ℓ.succ = 1 ∧ Q ℓ.castSucc = 1 := by
    intro ℓ hℓ
    have hGs : (G ℓ.succ : Matrix d d ℝ) = s ℓ.succ • (1 : Matrix d d ℝ) := by
      rw [hG, hℓ, Units.val_one]
    -- the write row `i` becomes `(c_i ^ k)⁻¹ s a_i`, and `a_i ≠ 0`: `(c_i ^ k)⁻¹ s = 1`
    have hsc : ∀ i, (c ℓ i ^ k)⁻¹ * s ℓ.succ = 1 := by
      intro i
      obtain ⟨a, hwa⟩ := Function.ne_iff.mp (ha ℓ i)
      have hr' := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
      change (c ℓ i ^ k)⁻¹ * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) i a = θ.write ℓ i a at hr'
      rw [hGs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul,
        ← mul_assoc] at hr'
      exact mul_right_cancel₀ hwa (hr'.trans (one_mul _).symm)
    -- the read column `i` becomes `c_i K w_i` with `K = Q_{ℓ-1}⁻¹`: `K w_i = c_i⁻¹ w_i`, so
    -- `c_i⁻¹ = 1`
    have hc1 : ∀ i, c ℓ i = 1 := by
      intro i
      have hK : (↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) *ᵥ (fun a => θ.read ℓ a i)
          = (c ℓ i)⁻¹ • (fun a => θ.read ℓ a i) := by
        funext a
        have hr' := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) i
        change c ℓ i * ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a i = θ.read ℓ a i at hr'
        show ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a i = (c ℓ i)⁻¹ * θ.read ℓ a i
        rw [← hr', ← mul_assoc, inv_mul_cancel₀ (hc ℓ i).ne', one_mul]
      exact inv_eq_one.mp (eq_one_of_orthogonal_mulVec_lfz (Q ℓ.castSucc) (hQ _) hK (hcol ℓ i)
        (inv_pos.mpr (hc ℓ i)))
    -- there is a hidden unit: the read has rank `d ≥ 1`
    obtain ⟨i₀⟩ : Nonempty (hid ℓ) := by
      have h1 := Matrix.rank_le_card_width (θ.read ℓ)
      rw [hr ℓ] at h1
      exact Fintype.card_pos_iff.mp (lt_of_lt_of_le Fintype.card_pos h1)
    have hs1 : s ℓ.succ = 1 := by
      have h1 := hsc i₀
      rw [hc1 i₀, one_pow, inv_one, one_mul] at h1
      exact h1
    refine ⟨hc1, hs1, inv_eq_one.mp (Units.ext ?_)⟩
    -- the read becomes `Q_{ℓ-1}⁻¹ W`, and `W` has rank `d`
    refine mul_right_cancel_of_rank_lfz (θ.read ℓ) (hr ℓ) ?_
    rw [Units.val_one, Matrix.one_mul]
    ext a i
    have hr' := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) i
    change c ℓ i * ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a i = θ.read ℓ a i at hr'
    rw [hc1 i, one_mul] at hr'
    exact hr'
  -- by the mirror induction, from the readout down
  have hQ1 : ∀ ℓ : Fin (L + 1), Q ℓ = 1 := by
    intro ℓ
    induction ℓ using Fin.reverseInduction with
    | last => exact hL
    | cast ℓ ih => exact (key ℓ ih).2.2
  -- the embedding: `s_0 E = E`, and `E ≠ 0`
  have hs0 : s 0 = 1 := by
    have h1 := congrArg Params.E h
    change θ.E * (G 0 : Matrix d d ℝ) = θ.E at h1
    rw [hG 0, hQ1 0, Units.val_one] at h1
    exact eq_one_of_mul_smul_one_lfz θ.E hE h1
  refine ⟨fun ℓ => ?_, funext hQ1, fun ℓ => (key ℓ (hQ1 ℓ.succ)).1⟩
  cases ℓ using Fin.cases with
  | zero => exact hs0
  | succ ℓ => exact (key ℓ (hQ1 ℓ.succ)).2.1

omit [Fintype T] [Fintype dIn] in
/-- **Lemma A.18, second sentence, `ε = 0`, gated blocks with any gate.** Let `G_ℓ = s_ℓ Q_ℓ`
with `s_ℓ > 0` and `Q_ℓ` orthogonal. If `D` and every read have rank `d ≥ 1`, `E ≠ 0`, no value
column of a read and no row of a write vanishes, and these changes of basis with the rescalings
`c` of the values fix `θ`, then `s = 1`, `Q = 1` and `c = 1`. -/
theorem cob_rmsNorm_zero_rescale_eq_self_of_rank_D [Nonempty d]
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (s : Fin (L + 1) → ℝ) (c : ∀ ℓ, hid ℓ → ℝ) (hs : ∀ ℓ, 0 < s ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hD : θ.D.rank = Fintype.card d) (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (hE : θ.E ≠ 0) (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0)
    (h : (θ.cob G Q).rescale c = θ) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  -- the readout: `Q_L⁻¹ D = D`, and `D` has rank `d`
  have hL : Q (Fin.last L) = 1 := by
    have hD0 : (↑(Q (Fin.last L))⁻¹ : Matrix d d ℝ) * θ.D = (1 : Matrix d d ℝ) * θ.D := by
      rw [Matrix.one_mul]
      have h1 := congrArg Params.D h
      exact h1
    exact inv_eq_one.mp (Units.ext (mul_right_cancel_of_rank_lfz θ.D hD hD0))
  -- block `ℓ`: if `Q_ℓ = 1`, then `c_ℓ = 1`, `s_ℓ = 1` and `Q_{ℓ-1} = 1`
  have key : ∀ ℓ : Fin L, Q ℓ.succ = 1 →
      (∀ i, c ℓ i = 1) ∧ s ℓ.succ = 1 ∧ Q ℓ.castSucc = 1 := by
    intro ℓ hℓ
    have hGs : (G ℓ.succ : Matrix d d ℝ) = s ℓ.succ • (1 : Matrix d d ℝ) := by
      rw [hG, hℓ, Units.val_one]
    -- the write row `i` becomes `c_i s a_i`, and `a_i ≠ 0`: `c_i s = 1`, so `c_i = s⁻¹ > 0`
    have hcs : ∀ i, c ℓ i * s ℓ.succ = 1 := by
      intro i
      obtain ⟨a, hwa⟩ := Function.ne_iff.mp (ha ℓ i)
      have hr' := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
      change c ℓ i * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) i a = θ.write ℓ i a at hr'
      rw [hGs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul,
        ← mul_assoc] at hr'
      exact mul_right_cancel₀ hwa (hr'.trans (one_mul _).symm)
    have hpos : ∀ i, 0 < c ℓ i := fun i => by
      rw [eq_inv_of_mul_eq_one_left (hcs i)]
      exact inv_pos.mpr (hs _)
    -- the value column `i` becomes `c_i⁻¹ K e_i` with `K = Q_{ℓ-1}⁻¹`: `K e_i = c_i e_i`, so
    -- `c_i = 1`
    have hc1 : ∀ i, c ℓ i = 1 := by
      intro i
      have hK : (↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) *ᵥ (fun a => θ.read ℓ a (Sum.inr i))
          = c ℓ i • (fun a => θ.read ℓ a (Sum.inr i)) := by
        funext a
        have hr' := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inr i)
        change (c ℓ i)⁻¹ * ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inr i)
          = θ.read ℓ a (Sum.inr i) at hr'
        show ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inr i)
          = c ℓ i * θ.read ℓ a (Sum.inr i)
        rw [← hr', ← mul_assoc, mul_inv_cancel₀ (hpos i).ne', one_mul]
      exact eq_one_of_orthogonal_mulVec_lfz (Q ℓ.castSucc) (hQ _) hK (hv ℓ i) (hpos i)
    -- there is a hidden unit: the read has rank `d ≥ 1`
    obtain ⟨i₀⟩ : Nonempty (hid ℓ) := by
      have h1 := Matrix.rank_le_card_width (θ.read ℓ)
      rw [hr ℓ] at h1
      obtain ⟨j⟩ := Fintype.card_pos_iff.mp (lt_of_lt_of_le Fintype.card_pos h1)
      rcases j with i | i <;> exact ⟨i⟩
    have hs1 : s ℓ.succ = 1 := by
      have h1 := hcs i₀
      rw [hc1 i₀, one_mul] at h1
      exact h1
    refine ⟨hc1, hs1, inv_eq_one.mp (Units.ext ?_)⟩
    -- the read becomes `Q_{ℓ-1}⁻¹ W`, and `W` has rank `d`
    refine mul_right_cancel_of_rank_lfz (θ.read ℓ) (hr ℓ) ?_
    rw [Units.val_one, Matrix.one_mul]
    ext a j
    have hr' := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) j
    rcases j with i | i
    · exact hr'
    · change (c ℓ i)⁻¹ * ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inr i)
        = θ.read ℓ a (Sum.inr i) at hr'
      rw [hc1 i, inv_one, one_mul] at hr'
      exact hr'
  -- by the mirror induction, from the readout down
  have hQ1 : ∀ ℓ : Fin (L + 1), Q ℓ = 1 := by
    intro ℓ
    induction ℓ using Fin.reverseInduction with
    | last => exact hL
    | cast ℓ ih => exact (key ℓ ih).2.2
  -- the embedding: `s_0 E = E`, and `E ≠ 0`
  have hs0 : s 0 = 1 := by
    have h1 := congrArg Params.E h
    change θ.E * (G 0 : Matrix d d ℝ) = θ.E at h1
    rw [hG 0, hQ1 0, Units.val_one] at h1
    exact eq_one_of_mul_smul_one_lfz θ.E hE h1
  refine ⟨fun ℓ => ?_, funext hQ1, fun ℓ => (key ℓ (hQ1 ℓ.succ)).1⟩
  cases ℓ using Fin.cases with
  | zero => exact hs0
  | succ ℓ => exact (key ℓ (hQ1 ℓ.succ)).2.1

omit [Fintype T] [Fintype dIn] in
/-- **Lemma A.18, second sentence, `ε = 0`, ReGLU blocks.** Let `G_ℓ = s_ℓ Q_ℓ` with `s_ℓ > 0`
and `Q_ℓ` orthogonal. If `D` and every read have rank `d ≥ 1`, `E ≠ 0`, no gate column and no
value column of a read and no row of a write vanishes, and these changes of basis with the
rescalings `c'` of the values and positive rescalings `c` of the gates fix `θ`, then `s = 1`,
`Q = 1`, `c = 1` and `c' = 1`. -/
theorem cob_rmsNorm_zero_rescale_rescaleGate_eq_self_of_rank_D [Nonempty d] (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (s : Fin (L + 1) → ℝ) (c c' : ∀ ℓ, hid ℓ → ℝ) (hs : ∀ ℓ, 0 < s ℓ) (hc : ∀ ℓ i, 0 < c ℓ i)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hD : θ.D.rank = Fintype.card d) (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (hE : θ.E ≠ 0) (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0)
    (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0)
    (h : ((θ.cob G Q).rescale c').rescaleGate k c = θ) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ (∀ ℓ i, c ℓ i = 1) ∧ ∀ ℓ i, c' ℓ i = 1 := by
  -- the readout: `Q_L⁻¹ D = D`, and `D` has rank `d`
  have hL : Q (Fin.last L) = 1 := by
    have hD0 : (↑(Q (Fin.last L))⁻¹ : Matrix d d ℝ) * θ.D = (1 : Matrix d d ℝ) * θ.D := by
      rw [Matrix.one_mul]
      have h1 := congrArg Params.D h
      exact h1
    exact inv_eq_one.mp (Units.ext (mul_right_cancel_of_rank_lfz θ.D hD hD0))
  -- block `ℓ`: if `Q_ℓ = 1`, then `c_ℓ = 1`, `c'_ℓ = 1`, `s_ℓ = 1` and `Q_{ℓ-1} = 1`
  have key : ∀ ℓ : Fin L, Q ℓ.succ = 1 →
      (∀ i, c ℓ i = 1) ∧ (∀ i, c' ℓ i = 1) ∧ s ℓ.succ = 1 ∧ Q ℓ.castSucc = 1 := by
    intro ℓ hℓ
    have hGs : (G ℓ.succ : Matrix d d ℝ) = s ℓ.succ • (1 : Matrix d d ℝ) := by
      rw [hG, hℓ, Units.val_one]
    -- the write row `i` becomes `(c_i ^ k)⁻¹ c'_i s a_i`, and `a_i ≠ 0`
    have hcs : ∀ i, (c ℓ i ^ k)⁻¹ * c' ℓ i * s ℓ.succ = 1 := by
      intro i
      obtain ⟨a, hwa⟩ := Function.ne_iff.mp (ha ℓ i)
      have hr' := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
      change (c ℓ i ^ k)⁻¹ * (c' ℓ i * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) i a)
        = θ.write ℓ i a at hr'
      rw [hGs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul,
        ← mul_assoc, ← mul_assoc] at hr'
      exact mul_right_cancel₀ hwa (hr'.trans (one_mul _).symm)
    -- the gate column `i` becomes `c_i K g_i` with `K = Q_{ℓ-1}⁻¹`: `K g_i = c_i⁻¹ g_i`, so
    -- `c_i⁻¹ = 1`
    have hc1 : ∀ i, c ℓ i = 1 := by
      intro i
      have hK : (↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) *ᵥ (fun a => θ.read ℓ a (Sum.inl i))
          = (c ℓ i)⁻¹ • (fun a => θ.read ℓ a (Sum.inl i)) := by
        funext a
        have hr' := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inl i)
        change c ℓ i * ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inl i)
          = θ.read ℓ a (Sum.inl i) at hr'
        show ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inl i)
          = (c ℓ i)⁻¹ * θ.read ℓ a (Sum.inl i)
        rw [← hr', ← mul_assoc, inv_mul_cancel₀ (hc ℓ i).ne', one_mul]
      exact inv_eq_one.mp (eq_one_of_orthogonal_mulVec_lfz (Q ℓ.castSucc) (hQ _) hK (hg ℓ i)
        (inv_pos.mpr (hc ℓ i)))
    -- so `c'_i s = 1`, and `c'_i = s⁻¹ > 0`
    have hcs' : ∀ i, c' ℓ i * s ℓ.succ = 1 := fun i => by
      have h1 := hcs i
      rw [hc1 i, one_pow, inv_one, one_mul] at h1
      exact h1
    have hpos : ∀ i, 0 < c' ℓ i := fun i => by
      rw [eq_inv_of_mul_eq_one_left (hcs' i)]
      exact inv_pos.mpr (hs _)
    -- the value column `i` becomes `c'_i⁻¹ K e_i`: `K e_i = c'_i e_i`, so `c'_i = 1`
    have hc'1 : ∀ i, c' ℓ i = 1 := by
      intro i
      have hK : (↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) *ᵥ (fun a => θ.read ℓ a (Sum.inr i))
          = c' ℓ i • (fun a => θ.read ℓ a (Sum.inr i)) := by
        funext a
        have hr' := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inr i)
        change (c' ℓ i)⁻¹ * ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inr i)
          = θ.read ℓ a (Sum.inr i) at hr'
        show ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inr i)
          = c' ℓ i * θ.read ℓ a (Sum.inr i)
        rw [← hr', ← mul_assoc, mul_inv_cancel₀ (hpos i).ne', one_mul]
      exact eq_one_of_orthogonal_mulVec_lfz (Q ℓ.castSucc) (hQ _) hK (hv ℓ i) (hpos i)
    -- there is a hidden unit: the read has rank `d ≥ 1`
    obtain ⟨i₀⟩ : Nonempty (hid ℓ) := by
      have h1 := Matrix.rank_le_card_width (θ.read ℓ)
      rw [hr ℓ] at h1
      obtain ⟨j⟩ := Fintype.card_pos_iff.mp (lt_of_lt_of_le Fintype.card_pos h1)
      rcases j with i | i <;> exact ⟨i⟩
    have hs1 : s ℓ.succ = 1 := by
      have h1 := hcs' i₀
      rw [hc'1 i₀, one_mul] at h1
      exact h1
    refine ⟨hc1, hc'1, hs1, inv_eq_one.mp (Units.ext ?_)⟩
    -- the read becomes `Q_{ℓ-1}⁻¹ W`, and `W` has rank `d`
    refine mul_right_cancel_of_rank_lfz (θ.read ℓ) (hr ℓ) ?_
    rw [Units.val_one, Matrix.one_mul]
    ext a j
    have hr' := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) j
    rcases j with i | i
    · change c ℓ i * ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inl i)
        = θ.read ℓ a (Sum.inl i) at hr'
      rw [hc1 i, one_mul] at hr'
      exact hr'
    · change (c' ℓ i)⁻¹ * ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inr i)
        = θ.read ℓ a (Sum.inr i) at hr'
      rw [hc'1 i, inv_one, one_mul] at hr'
      exact hr'
  -- by the mirror induction, from the readout down
  have hQ1 : ∀ ℓ : Fin (L + 1), Q ℓ = 1 := by
    intro ℓ
    induction ℓ using Fin.reverseInduction with
    | last => exact hL
    | cast ℓ ih => exact (key ℓ ih).2.2.2
  -- the embedding: `s_0 E = E`, and `E ≠ 0`
  have hs0 : s 0 = 1 := by
    have h1 := congrArg Params.E h
    change θ.E * (G 0 : Matrix d d ℝ) = θ.E at h1
    rw [hG 0, hQ1 0, Units.val_one] at h1
    exact eq_one_of_mul_smul_one_lfz θ.E hE h1
  refine ⟨fun ℓ => ?_, funext hQ1, fun ℓ => (key ℓ (hQ1 ℓ.succ)).1,
    fun ℓ => (key ℓ (hQ1 ℓ.succ)).2.1⟩
  cases ℓ using Fin.cases with
  | zero => exact hs0
  | succ ℓ => exact (key ℓ (hQ1 ℓ.succ)).2.2.1

variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

omit [Fintype dIn] [Fintype dOut] in
/-- **Lemma A.18, third sentence, `ε = 0`, attention blocks.** Let `G_ℓ = s_ℓ Q_ℓ` with
`s_ℓ > 0` and `Q_ℓ` orthogonal. If `E` and every write have rank `d ≥ 1`, the query matrix and
the value matrix of every head have rank `d_h`, and these changes of basis with the changes of
basis `K`, `K'` inside the heads fix `θ`, then `s = 1`, `Q = 1`, `K = 1` and `K' = 1`. -/
theorem cob_rmsNorm_zero_headsQK_headsVO_eq_self_of_rank_E [Nonempty d]
    (θ : Params (Arch.attention sees χ H dh) dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (s : Fin (L + 1) → ℝ) (K K' : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (hs : ∀ ℓ, 0 < s ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = s ℓ • (Q ℓ : Matrix d d ℝ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQr : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hVr : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (h : ((θ.cob G Q).headsQK K).headsVO K' = θ) :
    (∀ ℓ, s ℓ = 1) ∧ Q = 1 ∧ K = 1 ∧ K' = 1 := by
  -- `G_ℓ = 1` gives `s_ℓ = 1` and `Q_ℓ = 1`
  have hGQ : ∀ ℓ, G ℓ = 1 → s ℓ = 1 ∧ Q ℓ = 1 := fun ℓ h1 =>
    eq_one_of_smul_eq_one_lfz (Q ℓ) (hQ ℓ) (hs ℓ) (by rw [← hG ℓ, h1, Units.val_one])
  -- the embedding: `E G_0 = E`, and `E` has rank `d`
  have h0 : G 0 = 1 := by
    have hE0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E * (1 : Matrix d d ℝ) := by
      rw [Matrix.mul_one]
      have h1 := congrArg Params.E h
      exact h1
    exact Units.ext (mul_left_cancel_of_rank_lfz θ.E hE hE0)
  -- block `ℓ`: if `G_{ℓ-1} = 1`, then `Q_{ℓ-1} = 1`, `K_ℓ = 1`, `K'_ℓ = 1` and `G_ℓ = 1`
  have key : ∀ ℓ : Fin L, G ℓ.castSucc = 1 →
      (∀ i, K ℓ i = 1) ∧ (∀ i, K' ℓ i = 1) ∧ G ℓ.succ = 1 := by
    intro ℓ hℓ
    have hQℓ : Q ℓ.castSucc = 1 := (hGQ _ hℓ).2
    -- the query matrix of head `i` becomes `W_{Q,i} K_i`, and `W_{Q,i}` has rank `d_h`
    have hK : ∀ i, K ℓ i = 1 := by
      intro i
      apply Units.ext
      refine mul_left_cancel_of_rank_lfz _ (hQr ℓ i) ?_
      rw [Units.val_one, Matrix.mul_one]
      ext a k
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (i, Sum.inl k)
      change ∑ k', ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (i, Sum.inl k')
          * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) k' k = θ.read ℓ a (i, Sum.inl k) at hr
      rw [hQℓ, inv_one, Units.val_one, Matrix.one_mul] at hr
      exact hr
    -- the value matrix of head `i` becomes `W_{V,i} K'_i`, and `W_{V,i}` has rank `d_h`
    have hK' : ∀ i, K' ℓ i = 1 := by
      intro i
      apply Units.ext
      refine mul_left_cancel_of_rank_lfz _ (hVr ℓ i) ?_
      rw [Units.val_one, Matrix.mul_one]
      ext a k
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (i, Sum.inr (Sum.inr k))
      change ∑ k', ((↑(Q ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (i, Sum.inr (Sum.inr k'))
          * (K' ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) k' k = θ.read ℓ a (i, Sum.inr (Sum.inr k)) at hr
      rw [hQℓ, inv_one, Units.val_one, Matrix.one_mul] at hr
      exact hr
    refine ⟨hK, hK', Units.ext ?_⟩
    -- the write becomes `(K'_i⁻¹ (W G_ℓ)_i)_i = W G_ℓ`, and `W` has rank `d`
    refine mul_left_cancel_of_rank_lfz (θ.write ℓ) (hw ℓ) ?_
    rw [Units.val_one, Matrix.mul_one]
    ext ⟨i, k⟩ b
    have hr := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) (i, k)) b
    change ((↑(K' ℓ i)⁻¹ : Matrix (dh ℓ) (dh ℓ) ℝ)
        * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)).submatrix (fun k' : dh ℓ => (i, k')) id) k b
      = θ.write ℓ (i, k) b at hr
    rw [hK' i, inv_one, Units.val_one, Matrix.one_mul] at hr
    exact hr
  -- by induction along the network
  have hG1 : ∀ ℓ : Fin (L + 1), G ℓ = 1 := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => exact h0
    | succ ℓ ih => exact (key ℓ ih).2.2
  exact ⟨fun ℓ => (hGQ ℓ (hG1 ℓ)).1, funext fun ℓ => (hGQ ℓ (hG1 ℓ)).2,
    funext fun ℓ => funext fun i => (key ℓ (hG1 ℓ.castSucc)).1 i,
    funext fun ℓ => funext fun i => (key ℓ (hG1 ℓ.castSucc)).2.1 i⟩

end Skips
