import SkipsLean.Dimension.UpperBoundReadoutInside

/-!
# Locally free action when one block is narrower than `d`: from both ends

Paper (skips paper), Lemma A.18 (Locally free action): "If the embedding has rank `d_model` and
every block has width at least `d_model`, then at generic parameters the changes of basis and the
symmetries inside blocks act locally freely. The same holds if the readout has rank `d_model` and
every block has width at least `d_model`." Remark A.19: "The width condition is needed: at a
hidden state of a skipless network that is written and read at rank `m < d_model`, the changes
of basis that fix the parameters form a family of dimension `(d_model − m)²`".

The proof of Proposition A.35 uses the lemma for the network without
a dead unit ("The other columns are those of the network without this unit, whose symmetries are
the changes of basis of its `L + 1` hidden states and `s − 1` rescalings"). When the block of the
dead unit has exactly `d_model` hidden units, that network has one block of width `d_model − 1`,
to which neither sentence of the lemma applies as stated. The two inductions of its proof
together still give the conclusion, when both the embedding and the readout have rank `d`: the
changes of basis at the hidden states up to the one that the narrow block reads are fixed from
the embedding, and those from the one that it writes on are fixed from the readout. Nothing is
asked of the write of the narrow block. (Two adjacent blocks narrower than `d` are not covered,
as Remark A.19 says: `ai_notes/locally_free_one_narrow_block_check_2026-11-25.py`.) The proof of
Proposition A.33 (ii), for a residual network, does not need this form: there one change of basis
acts on all hidden states, and the embedding of rank `d` fixes it (`Residual/DeadUnits.lean`).

Here this form, in infinitesimal form, for a block `m`: `E` and the writes of the blocks before
`m` have rank `d`, `D` and the reads of the blocks after `m` have rank `d`. For ReLU and ReLU²
blocks with the rescalings: no read column of a block up to `m` and no write row of a block after
`m` vanishes, and `k ≠ 0`. For `m` the last block and `m` the first block these are close to the
forms with the embedding and with the readout (`cobDir_injective`,
`cobDir_injective_of_rank_D` and their twins), which do not ask the rank of the other end.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- Helper (the private `mul_left_cancel_of_rank` of `UpperBound.lean`): a matrix `M` of rank
equal to its number of columns cancels on the left, `M X = M Y → X = Y` (its kernel is `0` by
rank–nullity). -/
private theorem mul_left_cancel_of_rank_ubts {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

/-- Helper (the private `mul_right_cancel_of_rank_ubd` of `UpperBoundReadout.lean`): a matrix `M`
of rank equal to its number of rows cancels on the right, `X M = Y M → X = Y` (`v ↦ v M` is
injective by rank–nullity for `Mᵀ`). -/
private theorem mul_right_cancel_of_rank_ubts {m n k : Type*} [Fintype m] [Fintype n]
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
/-- **Lemma A.18 from both ends, the changes of basis, in infinitesimal form** (any kind of
block). If `E` and `D` have rank `d`, every write of a block before block `m` has rank `d` and
every read of a block after block `m` has rank `d`, the direction `cobDir θ X` determines `X`. -/
theorem cobDir_injective_of_rank_E_D {A : Arch T d L} (θ : Params A dIn dOut) (m : Fin L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hr : ∀ ℓ, m < ℓ → (θ.read ℓ).rank = Fintype.card d) :
    Function.Injective (cobDir θ) := by
  intro X Y h
  funext l
  rcases le_or_gt l m.castSucc with hl | hl
  · -- a hidden state up to the one that block `m` reads: from the embedding side
    induction l using Fin.cases with
    | zero =>
      -- the embedding component: `E X_0 = E Y_0`, and `E` has rank `d`
      have h0 : θ.E * X 0 = θ.E * Y 0 := congrArg Params.E h
      exact mul_left_cancel_of_rank_ubts θ.E hE h0
    | succ ℓ =>
      -- the write component of block `ℓ < m`: `W_write X_{ℓ+1} = W_write Y_{ℓ+1}`
      have h1 : θ.write ℓ * X ℓ.succ = θ.write ℓ * Y ℓ.succ :=
        congrArg (fun η => η.write ℓ) h
      exact mul_left_cancel_of_rank_ubts (θ.write ℓ) (hw ℓ (Fin.succ_le_castSucc_iff.1 hl)) h1
  · -- a hidden state from the one that block `m` writes on: from the readout side
    induction l using Fin.lastCases with
    | last =>
      -- the readout component: `X_L D = Y_L D`, and `D` has rank `d`
      have h0 : -(X (Fin.last L) * θ.D) = -(Y (Fin.last L) * θ.D) := congrArg Params.D h
      exact mul_right_cancel_of_rank_ubts θ.D hD (neg_injective h0)
    | cast ℓ =>
      -- the read component of block `ℓ > m`: `X_ℓ W_read = Y_ℓ W_read`
      have h1 : -(X ℓ.castSucc * θ.read ℓ) = -(Y ℓ.castSucc * θ.read ℓ) :=
        congrArg (fun η => η.read ℓ) h
      exact mul_right_cancel_of_rank_ubts (θ.read ℓ)
        (hr ℓ (Fin.castSucc_lt_castSucc_iff.1 hl)) (neg_injective h1)

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- **Lemma A.18 from both ends, ReLU and ReLU² blocks, in infinitesimal form.** For `k ≠ 0`: if
`E` and `D` have rank `d`, every write of a block before block `m` and every read of a block
after block `m` has rank `d`, no read column of a block up to `m` and no write row of a block
after `m` vanishes, the direction `cobDir θ X + rescaleDirMlp k θ α` determines `X` and `α`. -/
theorem cobDir_add_rescaleDirMlp_injective_of_rank_E_D (k : ℕ) (hk : k ≠ 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (m : Fin L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hr : ∀ ℓ, m < ℓ → (θ.read ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a i) ≠ 0)
    (ha : ∀ ℓ, m < ℓ → ∀ i, (fun a => θ.write ℓ i a) ≠ 0) :
    Function.Injective fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
      cobDir θ p.1 + rescaleDirMlp k θ p.2 := by
  rintro ⟨X, α⟩ ⟨X', α'⟩ h
  -- the read of block `ℓ` moves by `-X_{ℓ-1} W_read + W_read diag(α_ℓ)`
  have hrd : ∀ ℓ, -(X ℓ.castSucc * θ.read ℓ) + Matrix.of (fun a i => α ℓ i * θ.read ℓ a i) =
      -(X' ℓ.castSucc * θ.read ℓ) + Matrix.of (fun a i => α' ℓ i * θ.read ℓ a i) :=
    fun ℓ => congrArg (fun η => η.read ℓ) h
  -- the write of block `ℓ` moves by `W_write X_ℓ - k diag(α_ℓ) W_write`
  have hwr : ∀ ℓ, θ.write ℓ * X ℓ.succ
        + Matrix.of (fun i a => -((k : ℝ) * α ℓ i) * θ.write ℓ i a) =
      θ.write ℓ * X' ℓ.succ + Matrix.of (fun i a => -((k : ℝ) * α' ℓ i) * θ.write ℓ i a) :=
    fun ℓ => congrArg (fun η => η.write ℓ) h
  -- a block up to `m`: if `X_{ℓ-1} = X'_{ℓ-1}`, an entry `a` with `c_i a ≠ 0` of the read column
  -- of hidden unit `i` gives `α_i = α'_i`
  have hαr : ∀ ℓ, ℓ ≤ m → X ℓ.castSucc = X' ℓ.castSucc → α ℓ = α' ℓ := by
    intro ℓ hℓ hX
    funext i
    obtain ⟨a, ha'⟩ := Function.ne_iff.mp (hc ℓ hℓ i)
    have e := congrFun (congrFun (hrd ℓ) a) i
    change -(X ℓ.castSucc * θ.read ℓ) a i + α ℓ i * θ.read ℓ a i =
      -(X' ℓ.castSucc * θ.read ℓ) a i + α' ℓ i * θ.read ℓ a i at e
    rw [hX, add_right_inj] at e
    exact mul_right_cancel₀ ha' e
  -- a block before `m`: if `α_ℓ = α'_ℓ`, the write of rank `d` gives `X_ℓ = X'_ℓ`
  have hXw : ∀ ℓ, ℓ < m → α ℓ = α' ℓ → X ℓ.succ = X' ℓ.succ := by
    intro ℓ hℓ hα
    have e := hwr ℓ
    rw [hα, add_left_inj] at e
    exact mul_left_cancel_of_rank_ubts (θ.write ℓ) (hw ℓ hℓ) e
  -- a block after `m`: if `X_ℓ = X'_ℓ`, an entry `a` with `a_i a ≠ 0` of the write row of hidden
  -- unit `i` gives `k α_i = k α'_i`, and `k ≠ 0`
  have hαw : ∀ ℓ, m < ℓ → X ℓ.succ = X' ℓ.succ → α ℓ = α' ℓ := by
    intro ℓ hℓ hX
    have e := hwr ℓ
    rw [hX, add_right_inj] at e
    funext i
    obtain ⟨a, ha'⟩ := Function.ne_iff.mp (ha ℓ hℓ i)
    have hia : -((k : ℝ) * α ℓ i) * θ.write ℓ i a = -((k : ℝ) * α' ℓ i) * θ.write ℓ i a :=
      congrFun (congrFun e i) a
    exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hk) (neg_inj.mp (mul_right_cancel₀ ha' hia))
  -- a block after `m`: if `α_ℓ = α'_ℓ`, the read of rank `d` gives `X_{ℓ-1} = X'_{ℓ-1}`
  have hXr : ∀ ℓ, m < ℓ → α ℓ = α' ℓ → X ℓ.castSucc = X' ℓ.castSucc := by
    intro ℓ hℓ hα
    have e := hrd ℓ
    rw [hα, add_left_inj] at e
    exact mul_right_cancel_of_rank_ubts (θ.read ℓ) (hr ℓ hℓ) (neg_injective e)
  -- from the embedding, by induction along the network: `X_j = X'_j` for `j` up to the hidden
  -- state that block `m` reads
  have hfw : ∀ l : Fin (L + 1), l ≤ m.castSucc → X l = X' l := by
    intro l
    induction l using Fin.induction with
    | zero =>
      intro _
      -- the embedding component: `E X_0 = E X'_0` (the rescalings leave `E` alone)
      have h0 : θ.E * X 0 + 0 = θ.E * X' 0 + 0 := congrArg Params.E h
      rw [add_zero, add_zero] at h0
      exact mul_left_cancel_of_rank_ubts θ.E hE h0
    | succ ℓ ih =>
      intro hl
      have hℓ : ℓ < m := Fin.succ_le_castSucc_iff.1 hl
      exact hXw ℓ hℓ (hαr ℓ hℓ.le (ih (Fin.castSucc_le_castSucc_iff.2 hℓ.le)))
  -- from the readout, by induction down the network: `X_j = X'_j` for `j` from the hidden state
  -- that block `m` writes on
  have hbw : ∀ l : Fin (L + 1), m.succ ≤ l → X l = X' l := by
    intro l
    induction l using Fin.reverseInduction with
    | last =>
      intro _
      -- the readout component: `X_L D = X'_L D` (the rescalings leave `D` alone)
      have h0 : -(X (Fin.last L) * θ.D) + 0 = -(X' (Fin.last L) * θ.D) + 0 :=
        congrArg Params.D h
      rw [add_zero, add_zero] at h0
      exact mul_right_cancel_of_rank_ubts θ.D hD (neg_injective h0)
    | cast ℓ ih =>
      intro hl
      have hℓ : m < ℓ := Fin.succ_le_castSucc_iff.1 hl
      exact hXr ℓ hℓ (hαw ℓ hℓ (ih (Fin.succ_le_succ_iff.2 hℓ.le)))
  -- every hidden state is on one of the two sides; the write of block `m` is not used
  have hX : ∀ l, X l = X' l := by
    intro l
    rcases le_or_gt l m.castSucc with hl | hl
    · exact hfw l hl
    · exact hbw l (Fin.castSucc_lt_iff_succ_le.1 hl)
  -- then `α_ℓ` from the read for `ℓ ≤ m`, from the write for `ℓ > m`
  refine Prod.ext (funext hX) (funext fun ℓ => ?_)
  rcases le_or_gt ℓ m with hℓ | hℓ
  · exact hαr ℓ hℓ (hX _)
  · exact hαw ℓ hℓ (hX _)

end Skips
