import SkipsLean.Dimension.RescaleAction
import SkipsLean.Dimension.RescaleActionHomogeneous
import SkipsLean.Symmetry.Normalized

/-!
# Locally free action: only the identity fixes the parameters (the form with the embedding)

Paper (skips paper), Lemma A.18 (Locally free action): "Consider an MLP network, skipless or
residual, without normalization or with pre-RMSNorm, with vanilla MLP blocks with tanh, GELU,
ReLU or ReLU² activations, or with gated blocks with any gate, and the symmetries inside blocks of
Section 4.1. If the embedding has rank `d_model` and every block has width at least `d_model`,
then at generic parameters the changes of basis and the symmetries inside blocks act locally
freely." (The dimension paper, Lemma B.1, has the same sentence.) The proof: "Permutations and
sign flips are isolated, so it suffices to consider changes of basis and rescalings close to the
identity. Let changes of basis `G_0, …, G_L` and positive rescalings `c_ℓ` of hidden units (for
ReLU and ReLU²), of gates and values (for ReGLU) or of values (for the other gated blocks) fix a
generic `θ`; for tanh and GELU there are no `c_ℓ`. The embedding transforms as `E ↦ E G_0`, and
`E` has rank `d_model`, so `G_0 = I`. Suppose `G_{ℓ−1} = I`. The read of block `ℓ` then
transforms as `W_read^ℓ ↦ W_read^ℓ diag(c_ℓ)`, with entries 1 on the columns that are not
rescaled, and no column of a generic `W_read^ℓ` vanishes, so `c_ℓ = 1`. The write then transforms
as `W_write^ℓ ↦ W_write^ℓ G_ℓ`, and `W_write^ℓ` has rank `d_model` because the block has width at
least `d_model`, so `G_ℓ = I`. By induction only the identity fixes `θ`. In a residual network the
`G_ℓ` are equal (Theorem A.5(iii)) and the same argument applies. […] With RMSNorm the changes of
basis lie in `CO(d_model)` or `O(d_model)`, and the argument is unchanged."

The library had this lemma in infinitesimal form (the directions of the symmetries determine
their matrices and numbers: `cobDir_injective` and its twins). Here the statement of the proof,
for the group: **if changes of basis and rescalings fix `θ`, they are the identity**, at every
`θ` whose embedding and writes have rank `d` and whose rescaled read columns are not zero (at
generic parameters: `d_in ≥ d` and blocks of width at least `d`).

* `cob_eq_self_of_rank_E`: any kind of block, the changes of basis `θ.cob G K` (writes multiplied
  by `G`, reads by `K⁻¹`): `G = 1`. With `K = G` this is the lemma without normalization and, for
  orthogonal `G`, with pre-RMSNorm, `ε > 0`; `G` constant is a residual network.
* `cob_rescaleMlp_eq_self_of_rank_E`: ReLU and ReLU² blocks (any degree `k`), with the
  rescalings of the hidden units.
* `cob_rescale_eq_self_of_rank_E`: gated blocks with any gate, with the rescalings of the values.
* `cob_rescale_rescaleGate_eq_self_of_rank_E`: ReGLU blocks, with the rescalings of the values
  and of the gates.
* `cob_rmsNorm_zero_eq_self_of_rank_E`: pre-RMSNorm with `ε = 0`, where `G_ℓ = c_ℓ Q_ℓ` multiplies
  the writes and `Q_ℓ⁻¹` the reads (`eval_cob_rmsNorm_zero`): `c_ℓ = 1` and `Q_ℓ = 1`.

Lean asks nothing of the numbers `c` (the paper: positive rescalings): a read column that is
fixed and not zero gives `c = 1`. Not stated: `ε = 0` together with rescalings inside blocks.
The form with the readout is in `Symmetry/LocallyFreeReadout.lean`, attention blocks in
`Symmetry/LocallyFreeAttention.lean`.
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
private theorem mul_left_cancel_of_rank_lfe {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Lemma A.18, first sentence, for the changes of basis.** If `E` and every write have rank
`d` and the changes of basis fix `θ` (`θ.cob G K = θ`: the writes are multiplied by `G`, the
reads by `K⁻¹`), then `G = 1`. -/
theorem cob_eq_self_of_rank_E {A : Arch T d L} (θ : Params A dIn dOut)
    (G K : Fin (L + 1) → GL d ℝ) (hE : θ.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) (h : θ.cob G K = θ) : G = 1 := by
  funext ℓ
  apply Units.ext
  cases ℓ using Fin.cases with
  | zero =>
    -- the embedding: `E G_0 = E`, and `E` has rank `d`
    have h0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E * (1 : Matrix d d ℝ) := by
      rw [Matrix.mul_one]
      exact congrArg Params.E h
    exact mul_left_cancel_of_rank_lfe θ.E hE h0
  | succ ℓ =>
    -- the write of block `ℓ + 1`: `W G_{ℓ+1} = W`, and `W` has rank `d`
    have h1 : θ.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.write ℓ * (1 : Matrix d d ℝ) := by
      rw [Matrix.mul_one]
      exact congrArg (fun η => η.write ℓ) h
    exact mul_left_cancel_of_rank_lfe (θ.write ℓ) (hw ℓ) h1

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Lemma A.18, first sentence, for ReLU and ReLU² blocks.** If `E` and every write have rank
`d`, no column of a read vanishes, and the changes of basis `G` with the rescalings `c` of the
hidden units fix `θ`, then `G = 1` and `c = 1`. -/
theorem cob_rescaleMlp_eq_self_of_rank_E (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (G : Fin (L + 1) → GL d ℝ)
    (c : ∀ ℓ, hid ℓ → ℝ) (hE : θ.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hcol : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0)
    (h : (θ.cob G G).rescaleMlp k c = θ) : G = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  -- the embedding: `E G_0 = E`, and `E` has rank `d`
  have h0 : G 0 = 1 := by
    have hE0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E * (1 : Matrix d d ℝ) := by
      rw [Matrix.mul_one]
      have h1 := congrArg Params.E h
      exact h1
    exact Units.ext (mul_left_cancel_of_rank_lfe θ.E hE hE0)
  -- block `ℓ`: if `G_{ℓ-1} = 1`, then `c_ℓ = 1` and `G_ℓ = 1`
  have key : ∀ ℓ : Fin L, G ℓ.castSucc = 1 → (∀ i, c ℓ i = 1) ∧ G ℓ.succ = 1 := by
    intro ℓ hℓ
    -- the read column `i` becomes `c_i w_i`, and `w_i ≠ 0`
    have hc : ∀ i, c ℓ i = 1 := by
      intro i
      obtain ⟨a, ha⟩ := Function.ne_iff.mp (hcol ℓ i)
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) i
      change c ℓ i * ((↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a i = θ.read ℓ a i at hr
      rw [hℓ, inv_one, Units.val_one, Matrix.one_mul] at hr
      exact mul_right_cancel₀ ha (hr.trans (one_mul _).symm)
    refine ⟨hc, Units.ext ?_⟩
    -- the write becomes `(1 ^ k)⁻¹ W G_ℓ = W G_ℓ`, and `W` has rank `d`
    refine mul_left_cancel_of_rank_lfe (θ.write ℓ) (hw ℓ) ?_
    rw [Units.val_one, Matrix.mul_one]
    ext i a
    have hr := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
    change (c ℓ i ^ k)⁻¹ * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) i a = θ.write ℓ i a at hr
    rw [hc i, one_pow, inv_one, one_mul] at hr
    exact hr
  -- by induction along the network
  have hG : ∀ ℓ : Fin (L + 1), G ℓ = 1 := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => exact h0
    | succ ℓ ih => exact (key ℓ ih).2
  exact ⟨funext hG, fun ℓ => (key ℓ (hG ℓ.castSucc)).1⟩

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Lemma A.18, first sentence, for gated blocks with any gate.** If `E` and every write have
rank `d`, no value column of a read vanishes, and the changes of basis `G` with the rescalings
`c` of the values fix `θ`, then `G = 1` and `c = 1`. -/
theorem cob_rescale_eq_self_of_rank_E
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (G : Fin (L + 1) → GL d ℝ)
    (c : ∀ ℓ, hid ℓ → ℝ) (hE : θ.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (h : (θ.cob G G).rescale c = θ) : G = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  -- the embedding: `E G_0 = E`, and `E` has rank `d`
  have h0 : G 0 = 1 := by
    have hE0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E * (1 : Matrix d d ℝ) := by
      rw [Matrix.mul_one]
      have h1 := congrArg Params.E h
      exact h1
    exact Units.ext (mul_left_cancel_of_rank_lfe θ.E hE hE0)
  -- block `ℓ`: if `G_{ℓ-1} = 1`, then `c_ℓ = 1` and `G_ℓ = 1`
  have key : ∀ ℓ : Fin L, G ℓ.castSucc = 1 → (∀ i, c ℓ i = 1) ∧ G ℓ.succ = 1 := by
    intro ℓ hℓ
    -- the value column `i` becomes `c_i⁻¹ e_i`, and `e_i ≠ 0`
    have hc : ∀ i, c ℓ i = 1 := by
      intro i
      obtain ⟨a, ha⟩ := Function.ne_iff.mp (hv ℓ i)
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inr i)
      change (c ℓ i)⁻¹ * ((↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inr i)
        = θ.read ℓ a (Sum.inr i) at hr
      rw [hℓ, inv_one, Units.val_one, Matrix.one_mul] at hr
      exact inv_eq_one.mp (mul_right_cancel₀ ha (hr.trans (one_mul _).symm))
    refine ⟨hc, Units.ext ?_⟩
    -- the write becomes `1 · W G_ℓ = W G_ℓ`, and `W` has rank `d`
    refine mul_left_cancel_of_rank_lfe (θ.write ℓ) (hw ℓ) ?_
    rw [Units.val_one, Matrix.mul_one]
    ext i a
    have hr := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
    change c ℓ i * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) i a = θ.write ℓ i a at hr
    rw [hc i, one_mul] at hr
    exact hr
  -- by induction along the network
  have hG : ∀ ℓ : Fin (L + 1), G ℓ = 1 := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => exact h0
    | succ ℓ ih => exact (key ℓ ih).2
  exact ⟨funext hG, fun ℓ => (key ℓ (hG ℓ.castSucc)).1⟩

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Lemma A.18, first sentence, for ReGLU blocks.** If `E` and every write have rank `d`, no
gate column and no value column of a read vanishes, and the changes of basis `G` with the
rescalings `c'` of the values and `c` of the gates fix `θ`, then `G = 1`, `c = 1` and
`c' = 1`. -/
theorem cob_rescale_rescaleGate_eq_self_of_rank_E (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (G : Fin (L + 1) → GL d ℝ)
    (c c' : ∀ ℓ, hid ℓ → ℝ) (hE : θ.E.rank = Fintype.card d)
    (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0)
    (h : ((θ.cob G G).rescale c').rescaleGate k c = θ) :
    G = 1 ∧ (∀ ℓ i, c ℓ i = 1) ∧ ∀ ℓ i, c' ℓ i = 1 := by
  -- the embedding: `E G_0 = E`, and `E` has rank `d`
  have h0 : G 0 = 1 := by
    have hE0 : θ.E * (G 0 : Matrix d d ℝ) = θ.E * (1 : Matrix d d ℝ) := by
      rw [Matrix.mul_one]
      have h1 := congrArg Params.E h
      exact h1
    exact Units.ext (mul_left_cancel_of_rank_lfe θ.E hE hE0)
  -- block `ℓ`: if `G_{ℓ-1} = 1`, then `c_ℓ = 1`, `c'_ℓ = 1` and `G_ℓ = 1`
  have key : ∀ ℓ : Fin L, G ℓ.castSucc = 1 →
      (∀ i, c ℓ i = 1) ∧ (∀ i, c' ℓ i = 1) ∧ G ℓ.succ = 1 := by
    intro ℓ hℓ
    -- the gate column `i` becomes `c_i g_i`, and `g_i ≠ 0`
    have hc : ∀ i, c ℓ i = 1 := by
      intro i
      obtain ⟨a, ha⟩ := Function.ne_iff.mp (hg ℓ i)
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inl i)
      change c ℓ i * ((↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inl i)
        = θ.read ℓ a (Sum.inl i) at hr
      rw [hℓ, inv_one, Units.val_one, Matrix.one_mul] at hr
      exact mul_right_cancel₀ ha (hr.trans (one_mul _).symm)
    -- the value column `i` becomes `c'_i⁻¹ e_i`, and `e_i ≠ 0`
    have hc' : ∀ i, c' ℓ i = 1 := by
      intro i
      obtain ⟨a, ha⟩ := Function.ne_iff.mp (hv ℓ i)
      have hr := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inr i)
      change (c' ℓ i)⁻¹ * ((↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inr i)
        = θ.read ℓ a (Sum.inr i) at hr
      rw [hℓ, inv_one, Units.val_one, Matrix.one_mul] at hr
      exact inv_eq_one.mp (mul_right_cancel₀ ha (hr.trans (one_mul _).symm))
    refine ⟨hc, hc', Units.ext ?_⟩
    -- the write becomes `(1 ^ k)⁻¹ (1 · W G_ℓ) = W G_ℓ`, and `W` has rank `d`
    refine mul_left_cancel_of_rank_lfe (θ.write ℓ) (hw ℓ) ?_
    rw [Units.val_one, Matrix.mul_one]
    ext i a
    have hr := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
    change (c ℓ i ^ k)⁻¹ * (c' ℓ i * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) i a)
      = θ.write ℓ i a at hr
    rw [hc i, hc' i, one_pow, inv_one, one_mul, one_mul] at hr
    exact hr
  -- by induction along the network
  have hG : ∀ ℓ : Fin (L + 1), G ℓ = 1 := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero => exact h0
    | succ ℓ ih => exact (key ℓ ih).2.2
  exact ⟨funext hG, fun ℓ => (key ℓ (hG ℓ.castSucc)).1,
    fun ℓ => (key ℓ (hG ℓ.castSucc)).2.1⟩

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Lemma A.18, first sentence, under pre-RMSNorm with `ε = 0`** ("With RMSNorm the changes of
basis lie in `CO(d_model)` or `O(d_model)`, and the argument is unchanged"). The change of basis
`G_ℓ = c_ℓ Q_ℓ`, `c_ℓ > 0`, `Q_ℓ` orthogonal, multiplies the writes by `G_ℓ` and the reads by
`Q_ℓ⁻¹`. If `E` and every write have rank `d ≥ 1` and these changes of basis fix `θ`, then
`c_ℓ = 1` and `Q_ℓ = 1` for every `ℓ`. -/
theorem cob_rmsNorm_zero_eq_self_of_rank_E [Nonempty d] {A : Arch T d L} (θ : Params A dIn dOut)
    (G Q : Fin (L + 1) → GL d ℝ) (c : Fin (L + 1) → ℝ) (hc : ∀ ℓ, 0 < c ℓ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (hG : ∀ ℓ, (G ℓ : Matrix d d ℝ) = c ℓ • (Q ℓ : Matrix d d ℝ))
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (h : θ.cob G Q = θ) : (∀ ℓ, c ℓ = 1) ∧ Q = 1 := by
  -- the changes of basis are the identity: `G = 1`
  have hG1 := cob_eq_self_of_rank_E θ G Q hE hw h
  -- so `c_ℓ Q_ℓ = 1`, and `Q_ℓ` is orthogonal: `c_ℓ² = 1`, `c_ℓ = 1`
  have key : ∀ ℓ, c ℓ = 1 ∧ (Q ℓ : Matrix d d ℝ) = 1 := by
    intro ℓ
    have h1 : c ℓ • (Q ℓ : Matrix d d ℝ) = 1 := by
      rw [← hG ℓ, hG1]
      rfl
    have hQQ := (Matrix.mem_orthogonalGroup_iff d ℝ).mp (hQ ℓ)
    have h2 : (c ℓ • (Q ℓ : Matrix d d ℝ)) * (c ℓ • (Q ℓ : Matrix d d ℝ))ᵀ
        = (c ℓ * c ℓ) • (1 : Matrix d d ℝ) := by
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
    rw [h1, Matrix.transpose_one, Matrix.one_mul] at h2
    obtain ⟨x⟩ := (inferInstance : Nonempty d)
    have h3 := congrFun (congrFun h2 x) x
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h3
    have hc1 : c ℓ = 1 := by nlinarith [hc ℓ]
    refine ⟨hc1, ?_⟩
    rw [hc1, one_smul] at h1
    exact h1
  exact ⟨fun ℓ => (key ℓ).1, funext fun ℓ => Units.ext (key ℓ).2⟩

end Skips
