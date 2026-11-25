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

omit [Fintype T] [Fintype dIn] in
/-- **Lemma A.18, second sentence, for ReLU and ReLU² blocks.** For `k ≠ 0`: if `D` and every
read have rank `d`, no row of a write vanishes, and the changes of basis `G` with positive
rescalings `c` of the hidden units fix `θ`, then `G = 1` and `c = 1`. -/
theorem cob_rescaleMlp_eq_self_of_rank_D (k : ℕ) (hk : k ≠ 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (G : Fin (L + 1) → GL d ℝ)
    (c : ∀ ℓ, hid ℓ → ℝ) (hc : ∀ ℓ i, 0 < c ℓ i) (hD : θ.D.rank = Fintype.card d)
    (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0)
    (h : (θ.cob G G).rescaleMlp k c = θ) : G = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  -- the readout: `G_L⁻¹ D = D`, and `D` has rank `d`
  have hL : G (Fin.last L) = 1 := by
    have hD0 : (↑(G (Fin.last L))⁻¹ : Matrix d d ℝ) * θ.D = (1 : Matrix d d ℝ) * θ.D := by
      rw [Matrix.one_mul]
      have h1 := congrArg Params.D h
      exact h1
    exact inv_eq_one.mp (Units.ext (mul_right_cancel_of_rank_lfr θ.D hD hD0))
  -- block `ℓ`: if `G_ℓ = 1`, then `c_ℓ = 1` and `G_{ℓ-1} = 1`
  have key : ∀ ℓ : Fin L, G ℓ.succ = 1 → (∀ i, c ℓ i = 1) ∧ G ℓ.castSucc = 1 := by
    intro ℓ hℓ
    -- the write row `i` becomes `(c_i ^ k)⁻¹ a_i`, and `a_i ≠ 0`: `c_i ^ k = 1`, `c_i = 1`
    have hc1 : ∀ i, c ℓ i = 1 := by
      intro i
      obtain ⟨a, hwa⟩ := Function.ne_iff.mp (ha ℓ i)
      have hr' := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
      change (c ℓ i ^ k)⁻¹ * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) i a = θ.write ℓ i a at hr'
      rw [hℓ, Units.val_one, Matrix.mul_one] at hr'
      have hk1 : c ℓ i ^ k = 1 :=
        inv_eq_one.mp (mul_right_cancel₀ hwa (hr'.trans (one_mul _).symm))
      exact (pow_eq_one_iff_of_nonneg (hc ℓ i).le hk).mp hk1
    refine ⟨hc1, inv_eq_one.mp (Units.ext ?_)⟩
    -- the read becomes `G_{ℓ-1}⁻¹ W`, and `W` has rank `d`
    refine mul_right_cancel_of_rank_lfr (θ.read ℓ) (hr ℓ) ?_
    rw [Units.val_one, Matrix.one_mul]
    ext a i
    have hr' := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) i
    change c ℓ i * ((↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a i = θ.read ℓ a i at hr'
    rw [hc1 i, one_mul] at hr'
    exact hr'
  -- by the mirror induction, from the readout down
  have hG : ∀ ℓ : Fin (L + 1), G ℓ = 1 := by
    intro ℓ
    induction ℓ using Fin.reverseInduction with
    | last => exact hL
    | cast ℓ ih => exact (key ℓ ih).2
  exact ⟨funext hG, fun ℓ => (key ℓ (hG ℓ.succ)).1⟩

omit [Fintype T] [Fintype dIn] in
/-- **Lemma A.18, second sentence, for gated blocks with any gate.** If `D` and every read have
rank `d`, no row of a write vanishes, and the changes of basis `G` with the rescalings `c` of
the values fix `θ`, then `G = 1` and `c = 1`. -/
theorem cob_rescale_eq_self_of_rank_D
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (G : Fin (L + 1) → GL d ℝ)
    (c : ∀ ℓ, hid ℓ → ℝ) (hD : θ.D.rank = Fintype.card d)
    (hr : ∀ ℓ, (θ.read ℓ).rank = Fintype.card d)
    (ha : ∀ ℓ i, (fun a => θ.write ℓ i a) ≠ 0)
    (h : (θ.cob G G).rescale c = θ) : G = 1 ∧ ∀ ℓ i, c ℓ i = 1 := by
  -- the readout: `G_L⁻¹ D = D`, and `D` has rank `d`
  have hL : G (Fin.last L) = 1 := by
    have hD0 : (↑(G (Fin.last L))⁻¹ : Matrix d d ℝ) * θ.D = (1 : Matrix d d ℝ) * θ.D := by
      rw [Matrix.one_mul]
      have h1 := congrArg Params.D h
      exact h1
    exact inv_eq_one.mp (Units.ext (mul_right_cancel_of_rank_lfr θ.D hD hD0))
  -- block `ℓ`: if `G_ℓ = 1`, then `c_ℓ = 1` and `G_{ℓ-1} = 1`
  have key : ∀ ℓ : Fin L, G ℓ.succ = 1 → (∀ i, c ℓ i = 1) ∧ G ℓ.castSucc = 1 := by
    intro ℓ hℓ
    -- the write row `i` becomes `c_i a_i`, and `a_i ≠ 0`
    have hc1 : ∀ i, c ℓ i = 1 := by
      intro i
      obtain ⟨a, hwa⟩ := Function.ne_iff.mp (ha ℓ i)
      have hr' := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
      change c ℓ i * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) i a = θ.write ℓ i a at hr'
      rw [hℓ, Units.val_one, Matrix.mul_one] at hr'
      exact mul_right_cancel₀ hwa (hr'.trans (one_mul _).symm)
    refine ⟨hc1, inv_eq_one.mp (Units.ext ?_)⟩
    -- the read becomes `G_{ℓ-1}⁻¹ W`, and `W` has rank `d`
    refine mul_right_cancel_of_rank_lfr (θ.read ℓ) (hr ℓ) ?_
    rw [Units.val_one, Matrix.one_mul]
    ext a j
    have hr' := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) j
    rcases j with i | i
    · exact hr'
    · change (c ℓ i)⁻¹ * ((↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inr i)
        = θ.read ℓ a (Sum.inr i) at hr'
      rw [hc1 i, inv_one, one_mul] at hr'
      exact hr'
  -- by the mirror induction, from the readout down
  have hG : ∀ ℓ : Fin (L + 1), G ℓ = 1 := by
    intro ℓ
    induction ℓ using Fin.reverseInduction with
    | last => exact hL
    | cast ℓ ih => exact (key ℓ ih).2
  exact ⟨funext hG, fun ℓ => (key ℓ (hG ℓ.succ)).1⟩

/-- Helper: if `M = μ 1` and `M v = r v` with `v ≠ 0`, then `μ = r`. -/
private theorem eq_of_smul_one_mulVec_lfr {M : Matrix d d ℝ} {μ r : ℝ} {v : d → ℝ}
    (hM : M = μ • (1 : Matrix d d ℝ)) (hv : M *ᵥ v = r • v) (h0 : v ≠ 0) : μ = r := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp h0
  have h1 := congrFun hv a
  rw [hM, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  exact mul_right_cancel₀ ha h1

omit [Fintype T] [Fintype dIn] in
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
  -- the readout: `G_L⁻¹ D = D`, and `D` has rank `d`
  have hL : G (Fin.last L) = 1 := by
    have hD0 : (↑(G (Fin.last L))⁻¹ : Matrix d d ℝ) * θ.D = (1 : Matrix d d ℝ) * θ.D := by
      rw [Matrix.one_mul]
      have h1 := congrArg Params.D h
      exact h1
    exact inv_eq_one.mp (Units.ext (mul_right_cancel_of_rank_lfr θ.D hD hD0))
  -- block `ℓ`: if `G_ℓ = 1`, then `c_ℓ = 1`, `c'_ℓ = 1` and `G_{ℓ-1} = 1`
  have key : ∀ ℓ : Fin L, G ℓ.succ = 1 →
      (∀ i, c ℓ i = 1) ∧ (∀ i, c' ℓ i = 1) ∧ G ℓ.castSucc = 1 := by
    intro ℓ hℓ
    -- the write row `i` becomes `(c_i ^ k)⁻¹ c'_i a_i`, and `a_i ≠ 0`: `c'_i = c_i ^ k`
    have hcc : ∀ i, c' ℓ i = c ℓ i ^ k := by
      intro i
      obtain ⟨a, hwa⟩ := Function.ne_iff.mp (ha ℓ i)
      have hr' := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
      change (c ℓ i ^ k)⁻¹ * (c' ℓ i * (θ.write ℓ * (G ℓ.succ : Matrix d d ℝ)) i a)
        = θ.write ℓ i a at hr'
      rw [hℓ, Units.val_one, Matrix.mul_one, ← mul_assoc] at hr'
      have h1 : (c ℓ i ^ k)⁻¹ * c' ℓ i = 1 := mul_right_cancel₀ hwa (hr'.trans (one_mul _).symm)
      have hpow : c ℓ i ^ k ≠ 0 := pow_ne_zero _ (hc ℓ i).ne'
      calc c' ℓ i = c ℓ i ^ k * ((c ℓ i ^ k)⁻¹ * c' ℓ i) := by
            rw [← mul_assoc, mul_inv_cancel₀ hpow, one_mul]
        _ = c ℓ i ^ k := by rw [h1, mul_one]
    -- with `K = G_{ℓ-1}⁻¹`: `K g_i = c_i⁻¹ g_i` (the gate column becomes `c_i K g_i`)
    have hgate : ∀ i, (↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) *ᵥ (θ.read ℓ)ᵀ (Sum.inl i)
        = (c ℓ i)⁻¹ • (θ.read ℓ)ᵀ (Sum.inl i) := by
      intro i
      funext a
      have hr' := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inl i)
      change c ℓ i * ((↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inl i)
        = θ.read ℓ a (Sum.inl i) at hr'
      show ((↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inl i)
        = (c ℓ i)⁻¹ * θ.read ℓ a (Sum.inl i)
      rw [← hr', ← mul_assoc, inv_mul_cancel₀ (hc ℓ i).ne', one_mul]
    -- and `K e_i = c'_i e_i` (the value column becomes `c'_i⁻¹ K e_i`)
    have hval : ∀ i, (↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) *ᵥ (θ.read ℓ)ᵀ (Sum.inr i)
        = c' ℓ i • (θ.read ℓ)ᵀ (Sum.inr i) := by
      intro i
      funext a
      have hr' := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inr i)
      change (c' ℓ i)⁻¹ * ((↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inr i)
        = θ.read ℓ a (Sum.inr i) at hr'
      show ((↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) * θ.read ℓ) a (Sum.inr i)
        = c' ℓ i * θ.read ℓ a (Sum.inr i)
      have hne : c' ℓ i ≠ 0 := by
        rw [hcc i]
        exact pow_ne_zero _ (hc ℓ i).ne'
      rw [← hr', ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    -- every column is an eigenvector of `K`, so `K = μ 1`
    obtain ⟨μ, hμ⟩ := eq_smul_one_of_eigenvectors_generalPosition (fun j => (θ.read ℓ)ᵀ j)
      (hgp ℓ) (hcard ℓ) (↑(G ℓ.castSucc)⁻¹ : Matrix d d ℝ) (by
        rintro (i | i)
        · exact ⟨_, hgate i⟩
        · exact ⟨_, hval i⟩)
    -- there is a hidden unit (`card d < 2 |hid ℓ|`), and its write row is not zero, so `d ≠ ∅`
    obtain ⟨i₀⟩ : Nonempty (hid ℓ) := by
      obtain ⟨j⟩ := Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt (hcard ℓ))
      rcases j with i | i <;> exact ⟨i⟩
    have hd1 : 1 ≤ Fintype.card d := by
      obtain ⟨a, -⟩ := Function.ne_iff.mp (ha ℓ i₀)
      exact Fintype.card_pos_iff.mpr ⟨a⟩
    -- so every column is not zero (a single column is linearly independent)
    have hne : ∀ j, (θ.read ℓ)ᵀ j ≠ 0 := by
      intro j
      have hli := hgp ℓ {j} (by rw [Finset.card_singleton]; exact hd1)
      exact hli.ne_zero ⟨j, Finset.mem_singleton_self j⟩
    -- `μ = c_i⁻¹` and `μ = c_i ^ k`, so `c_i ^ (k + 1) = 1`, `c_i = 1`
    have hc1 : ∀ i, c ℓ i = 1 := by
      intro i
      have h1 := eq_of_smul_one_mulVec_lfr hμ (hgate i) (hne _)
      have h2 := eq_of_smul_one_mulVec_lfr hμ (hval i) (hne _)
      rw [hcc i] at h2
      have h3 : c ℓ i ^ (k + 1) = 1 := by
        rw [pow_succ, ← h2, h1, inv_mul_cancel₀ (hc ℓ i).ne']
      exact (pow_eq_one_iff_of_nonneg (hc ℓ i).le (Nat.succ_ne_zero k)).mp h3
    have hc'1 : ∀ i, c' ℓ i = 1 := fun i => by rw [hcc i, hc1 i, one_pow]
    refine ⟨hc1, hc'1, inv_eq_one.mp (Units.ext ?_)⟩
    -- `μ = c_{i₀}⁻¹ = 1`, so `K = 1`
    have hμ1 : μ = 1 := by
      rw [eq_of_smul_one_mulVec_lfr hμ (hgate i₀) (hne _), hc1 i₀, inv_one]
    rw [hμ, hμ1, one_smul, Units.val_one]
  -- by the mirror induction, from the readout down
  have hG : ∀ ℓ : Fin (L + 1), G ℓ = 1 := by
    intro ℓ
    induction ℓ using Fin.reverseInduction with
    | last => exact hL
    | cast ℓ ih => exact (key ℓ ih).2.2
  exact ⟨funext hG, fun ℓ => (key ℓ (hG ℓ.succ)).1, fun ℓ => (key ℓ (hG ℓ.succ)).2.1⟩

/-- Helper: if `X (r 1) = X` and `X ≠ 0`, then `r = 1`. -/
private theorem eq_one_of_mul_smul_one_lfr {m : Type*} (X : Matrix m d ℝ) (hX : X ≠ 0) {r : ℝ}
    (h : X * (r • (1 : Matrix d d ℝ)) = X) : r = 1 := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hX
  obtain ⟨q, hpq⟩ := Function.ne_iff.mp hp
  have h1 := congrFun (congrFun h p) q
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul] at h1
  exact mul_right_cancel₀ hpq (h1.trans (one_mul _).symm)

omit [Fintype T] [Fintype dIn] in
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
  -- the changes of basis of the reads are the identity: `Q = 1`, so `G_ℓ = c_ℓ 1`
  have hQ1 := cob_eq_self_of_rank_D θ G Q hD hr h
  have hG' : ∀ ℓ, (G ℓ : Matrix d d ℝ) = c ℓ • (1 : Matrix d d ℝ) := by
    intro ℓ
    rw [hG ℓ, hQ1]
    rfl
  refine ⟨fun ℓ => ?_, hQ1⟩
  cases ℓ using Fin.cases with
  | zero =>
    -- the embedding: `c_0 E = E`, and `E ≠ 0`
    have h1 : θ.E * (G 0 : Matrix d d ℝ) = θ.E := congrArg Params.E h
    rw [hG' 0] at h1
    exact eq_one_of_mul_smul_one_lfr θ.E hE h1
  | succ ℓ =>
    -- the write of block `ℓ + 1`: `c_{ℓ+1} W = W`, and `W ≠ 0`
    have h1 : θ.write ℓ * (G ℓ.succ : Matrix d d ℝ) = θ.write ℓ :=
      congrArg (fun η => η.write ℓ) h
    rw [hG' ℓ.succ] at h1
    exact eq_one_of_mul_smul_one_lfr (θ.write ℓ) (hw ℓ) h1

end Skips
