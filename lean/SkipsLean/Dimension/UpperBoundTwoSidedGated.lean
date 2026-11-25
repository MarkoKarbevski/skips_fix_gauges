import SkipsLean.Dimension.UpperBoundTwoSided

/-!
# Locally free action when one block is narrower than `d`, from both ends: gated blocks

Paper (skips paper), Lemma A.18 (Locally free action) and Remark A.19; see the header of
`Dimension/UpperBoundTwoSided.lean`, which has this form for the changes of basis alone and for
ReLU and ReLU² blocks. Here the twins for gated blocks: with the rescalings of the values (any
gate), and with the rescalings of values and gates (ReGLU). For a block `m`: `E` and the writes
of the blocks before `m` have rank `d`, and no rescaled read column of a block up to `m`
vanishes; `D` has rank `d`, and for the blocks after `m` no write row vanishes and

* with the rescalings of the values: the read has rank `d`;
* with both rescalings: the gate and value columns of the read are in general position (any `d`
  of them linearly independent, more than `d` of them), as in the form with the readout
  (`cobDir_add_rescaleDir_add_rescaleDirGate_injective_of_rank_D`).

Nothing is asked of the write of block `m`. Numeric check:
`ai_notes/locally_free_one_narrow_block_gated_check_2026-11-25.py`. Used for S Proposition A.35
for ReGLU blocks (`Depth/InactiveGateTwoSided.lean`).
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
private theorem mul_left_cancel_of_rank_ubtg {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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
private theorem mul_right_cancel_of_rank_ubtg {m n k : Type*} [Fintype m] [Fintype n]
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
/-- **Lemma A.18 from both ends, gated blocks with the rescalings of the values, in
infinitesimal form.** If `E` and `D` have rank `d`, every write of a block before block `m` and
every read of a block after block `m` has rank `d`, no value column of a read of a block up to
`m` and no write row of a block after `m` vanishes, the direction
`cobDir θ X + rescaleDir θ α` determines `X` and `α`. -/
theorem cobDir_add_rescaleDir_injective_of_rank_E_D
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (m : Fin L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hr : ∀ ℓ, m < ℓ → (θ.read ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (ha : ∀ ℓ, m < ℓ → ∀ i, (fun a => θ.write ℓ i a) ≠ 0) :
    Function.Injective fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
      cobDir θ p.1 + rescaleDir θ p.2 := by
  rintro ⟨X, α⟩ ⟨X', α'⟩ h
  -- the read of block `ℓ` moves by `-X_{ℓ-1} W_read`, plus `-α_i e_i` on the value columns
  have hrd : ∀ ℓ, -(X ℓ.castSucc * θ.read ℓ) + Matrix.of (fun a j =>
        Sum.elim (fun _ => 0) (fun i => -(α ℓ i) * θ.read ℓ a (Sum.inr i)) j) =
      -(X' ℓ.castSucc * θ.read ℓ) + Matrix.of (fun a j =>
        Sum.elim (fun _ => 0) (fun i => -(α' ℓ i) * θ.read ℓ a (Sum.inr i)) j) :=
    fun ℓ => congrArg (fun η => η.read ℓ) h
  -- the write of block `ℓ` moves by `W_write X_ℓ + diag(α_ℓ) W_write`
  have hwr : ∀ ℓ, θ.write ℓ * X ℓ.succ + Matrix.of (fun i a => α ℓ i * θ.write ℓ i a) =
      θ.write ℓ * X' ℓ.succ + Matrix.of (fun i a => α' ℓ i * θ.write ℓ i a) :=
    fun ℓ => congrArg (fun η => η.write ℓ) h
  -- a block up to `m`: if `X_{ℓ-1} = X'_{ℓ-1}`, an entry `a` with `e_i a ≠ 0` of the value column
  -- of hidden unit `i` gives `α_i = α'_i`
  have hαr : ∀ ℓ, ℓ ≤ m → X ℓ.castSucc = X' ℓ.castSucc → α ℓ = α' ℓ := by
    intro ℓ hℓ hX
    funext i
    obtain ⟨a, ha'⟩ := Function.ne_iff.mp (hv ℓ hℓ i)
    have e := congrFun (congrFun (hrd ℓ) a) (Sum.inr i)
    change -(X ℓ.castSucc * θ.read ℓ) a (Sum.inr i) + -(α ℓ i) * θ.read ℓ a (Sum.inr i) =
      -(X' ℓ.castSucc * θ.read ℓ) a (Sum.inr i) + -(α' ℓ i) * θ.read ℓ a (Sum.inr i) at e
    rw [hX, add_right_inj] at e
    exact neg_inj.mp (mul_right_cancel₀ ha' e)
  -- a block before `m`: if `α_ℓ = α'_ℓ`, the write of rank `d` gives `X_ℓ = X'_ℓ`
  have hXw : ∀ ℓ, ℓ < m → α ℓ = α' ℓ → X ℓ.succ = X' ℓ.succ := by
    intro ℓ hℓ hα
    have e := hwr ℓ
    rw [hα, add_left_inj] at e
    exact mul_left_cancel_of_rank_ubtg (θ.write ℓ) (hw ℓ hℓ) e
  -- a block after `m`: if `X_ℓ = X'_ℓ`, an entry `a` with `a_i a ≠ 0` of the write row of hidden
  -- unit `i` gives `α_i = α'_i`
  have hαw : ∀ ℓ, m < ℓ → X ℓ.succ = X' ℓ.succ → α ℓ = α' ℓ := by
    intro ℓ hℓ hX
    have e := hwr ℓ
    rw [hX, add_right_inj] at e
    funext i
    obtain ⟨a, ha'⟩ := Function.ne_iff.mp (ha ℓ hℓ i)
    have hia : α ℓ i * θ.write ℓ i a = α' ℓ i * θ.write ℓ i a := congrFun (congrFun e i) a
    exact mul_right_cancel₀ ha' hia
  -- a block after `m`: if `α_ℓ = α'_ℓ`, the read of rank `d` gives `X_{ℓ-1} = X'_{ℓ-1}`
  have hXr : ∀ ℓ, m < ℓ → α ℓ = α' ℓ → X ℓ.castSucc = X' ℓ.castSucc := by
    intro ℓ hℓ hα
    have e := hrd ℓ
    rw [hα, add_left_inj] at e
    exact mul_right_cancel_of_rank_ubtg (θ.read ℓ) (hr ℓ hℓ) (neg_injective e)
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
      exact mul_left_cancel_of_rank_ubtg θ.E hE h0
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
      exact mul_right_cancel_of_rank_ubtg θ.D hD (neg_injective h0)
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

/-- Helper (the private `exists_ne_zero_col_uri` of `UpperBoundReadoutInside.lean`): columns in
general position, `d ≥ 1`: no column is zero (a single column is linearly independent). -/
private theorem exists_ne_zero_col_ubtg {m q : Type*} [Fintype m] (R : Matrix m q ℝ)
    (hgp : ∀ S : Finset q, S.card ≤ Fintype.card m → LinearIndependent ℝ fun j : S => Rᵀ j)
    (hm : 0 < Fintype.card m) (j : q) : ∃ a, R a j ≠ 0 := by
  have h := (hgp {j} (by rw [Finset.card_singleton]; omega)).ne_zero
    ⟨j, Finset.mem_singleton_self j⟩
  obtain ⟨a, ha⟩ := Function.ne_iff.mp h
  exact ⟨a, ha⟩

omit [Fintype T] [Fintype dIn] in
/-- **Lemma A.18 from both ends, ReGLU blocks, in infinitesimal form.** If `E` and `D` have rank
`d`, every write of a block before block `m` has rank `d`, no gate column and no value column of
a read of a block up to `m` vanishes, and for every block after `m` no write row vanishes and the
gate and value columns of its read are in general position (any `d` of them linearly
independent, more than `d` of them), the direction
`cobDir θ X + rescaleDir θ α + rescaleDirGate k θ β` determines `X`, `α` and `β`. -/
theorem cobDir_add_rescaleDir_add_rescaleDirGate_injective_of_rank_E_D (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (m : Fin L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0)
    (ha : ∀ ℓ, m < ℓ → ∀ i, (fun a => θ.write ℓ i a) ≠ 0)
    (hgp : ∀ ℓ, m < ℓ → ∀ S : Finset (hid ℓ ⊕ hid ℓ), S.card ≤ Fintype.card d →
      LinearIndependent ℝ fun j : S => (θ.read ℓ)ᵀ j)
    (hcard : ∀ ℓ, m < ℓ → Fintype.card d < Fintype.card (hid ℓ ⊕ hid ℓ)) :
    Function.Injective
      fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
        cobDir θ p.1 + rescaleDir θ p.2.1 + rescaleDirGate k θ p.2.2 := by
  rintro ⟨X, α, β⟩ ⟨X', α', β'⟩ h
  -- the read of block `ℓ` moves by `-X_{ℓ-1} W_read`, plus `-α_i e_i` on the value columns and
  -- `β_i g_i` on the gate columns
  have hrd : ∀ ℓ, -(X ℓ.castSucc * θ.read ℓ) + Matrix.of (fun a j =>
          Sum.elim (fun _ => 0) (fun i => -(α ℓ i) * θ.read ℓ a (Sum.inr i)) j)
        + Matrix.of (fun a j => Sum.elim (fun i => β ℓ i * θ.read ℓ a (Sum.inl i))
          (fun _ => 0) j) =
      -(X' ℓ.castSucc * θ.read ℓ) + Matrix.of (fun a j =>
          Sum.elim (fun _ => 0) (fun i => -(α' ℓ i) * θ.read ℓ a (Sum.inr i)) j)
        + Matrix.of (fun a j => Sum.elim (fun i => β' ℓ i * θ.read ℓ a (Sum.inl i))
          (fun _ => 0) j) :=
    fun ℓ => congrArg (fun η => η.read ℓ) h
  -- the write of block `ℓ` moves by `W_write X_ℓ + diag(α_ℓ - k β_ℓ) W_write`
  have hwr : ∀ ℓ, θ.write ℓ * X ℓ.succ + Matrix.of (fun i a => α ℓ i * θ.write ℓ i a)
        + Matrix.of (fun i a => -((k : ℝ) * β ℓ i) * θ.write ℓ i a) =
      θ.write ℓ * X' ℓ.succ + Matrix.of (fun i a => α' ℓ i * θ.write ℓ i a)
        + Matrix.of (fun i a => -((k : ℝ) * β' ℓ i) * θ.write ℓ i a) :=
    fun ℓ => congrArg (fun η => η.write ℓ) h
  -- a block up to `m`: if `X_{ℓ-1} = X'_{ℓ-1}`, an entry `a` with `g_i a ≠ 0` of the gate column
  -- of hidden unit `i` gives `β_i = β'_i`
  have hβr : ∀ ℓ, ℓ ≤ m → X ℓ.castSucc = X' ℓ.castSucc → β ℓ = β' ℓ := by
    intro ℓ hℓ hX
    funext i
    obtain ⟨a, ha'⟩ := Function.ne_iff.mp (hg ℓ hℓ i)
    have e := congrFun (congrFun (hrd ℓ) a) (Sum.inl i)
    change -(X ℓ.castSucc * θ.read ℓ) a (Sum.inl i) + 0 + β ℓ i * θ.read ℓ a (Sum.inl i) =
      -(X' ℓ.castSucc * θ.read ℓ) a (Sum.inl i) + 0 + β' ℓ i * θ.read ℓ a (Sum.inl i) at e
    rw [hX, add_right_inj] at e
    exact mul_right_cancel₀ ha' e
  -- and an entry `a` with `e_i a ≠ 0` of the value column gives `α_i = α'_i`
  have hαr : ∀ ℓ, ℓ ≤ m → X ℓ.castSucc = X' ℓ.castSucc → α ℓ = α' ℓ := by
    intro ℓ hℓ hX
    funext i
    obtain ⟨a, ha'⟩ := Function.ne_iff.mp (hv ℓ hℓ i)
    have e := congrFun (congrFun (hrd ℓ) a) (Sum.inr i)
    change -(X ℓ.castSucc * θ.read ℓ) a (Sum.inr i) + -(α ℓ i) * θ.read ℓ a (Sum.inr i) + 0 =
      -(X' ℓ.castSucc * θ.read ℓ) a (Sum.inr i) + -(α' ℓ i) * θ.read ℓ a (Sum.inr i) + 0 at e
    rw [hX, add_left_inj, add_right_inj] at e
    exact neg_inj.mp (mul_right_cancel₀ ha' e)
  -- a block before `m`: if `α_ℓ = α'_ℓ` and `β_ℓ = β'_ℓ`, the write of rank `d` gives
  -- `X_ℓ = X'_ℓ`
  have hXw : ∀ ℓ, ℓ < m → α ℓ = α' ℓ → β ℓ = β' ℓ → X ℓ.succ = X' ℓ.succ := by
    intro ℓ hℓ hα hβ
    have e := hwr ℓ
    rw [hα, hβ, add_left_inj, add_left_inj] at e
    exact mul_left_cancel_of_rank_ubtg (θ.write ℓ) (hw ℓ hℓ) e
  -- a block after `m`: if `X_ℓ = X'_ℓ`, then `α_ℓ = α'_ℓ`, `β_ℓ = β'_ℓ` and `X_{ℓ-1} = X'_{ℓ-1}`
  have hback : ∀ ℓ, m < ℓ → X ℓ.succ = X' ℓ.succ →
      α ℓ = α' ℓ ∧ β ℓ = β' ℓ ∧ X ℓ.castSucc = X' ℓ.castSucc := by
    intro ℓ hℓm hℓ
    -- the block has a hidden unit `i₀`, and `d ≥ 1` (the write row of `i₀` is not zero)
    have hcs := hcard ℓ hℓm
    rw [Fintype.card_sum] at hcs
    obtain ⟨i₀⟩ : Nonempty (hid ℓ) := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨a₀, -⟩ := Function.ne_iff.mp (ha ℓ hℓm i₀)
    have hd : 0 < Fintype.card d := Fintype.card_pos_iff.mpr ⟨a₀⟩
    -- the first terms of the write agree; an entry `a` with `a_i a ≠ 0` gives
    -- `α_i - k β_i = α'_i - k β'_i`
    have hw' := hwr ℓ
    rw [hℓ, add_assoc, add_assoc, add_right_inj] at hw'
    have hwi : ∀ i, α ℓ i - k * β ℓ i = α' ℓ i - k * β' ℓ i := by
      intro i
      obtain ⟨a, ha'⟩ := Function.ne_iff.mp (ha ℓ hℓm i)
      have hia : α ℓ i * θ.write ℓ i a + -((k : ℝ) * β ℓ i) * θ.write ℓ i a =
          α' ℓ i * θ.write ℓ i a + -((k : ℝ) * β' ℓ i) * θ.write ℓ i a :=
        congrFun (congrFun hw' i) a
      rw [← add_mul, ← add_mul] at hia
      linear_combination mul_right_cancel₀ ha' hia
    -- the read: with `Y = X_ℓ - X'_ℓ`, `Y g_i = (β_i - β'_i) g_i` on the gate columns and
    -- `Y e_i = -(α_i - α'_i) e_i` on the value columns
    have hr' := hrd ℓ
    obtain ⟨Y, hY⟩ : ∃ Y, Y = X ℓ.castSucc - X' ℓ.castSucc := ⟨_, rfl⟩
    have hYR : ∀ a j, (Y * θ.read ℓ) a j =
        (X ℓ.castSucc * θ.read ℓ) a j - (X' ℓ.castSucc * θ.read ℓ) a j := by
      intro a j
      rw [hY, Matrix.sub_mul, Matrix.sub_apply]
    have hgate : ∀ a i, (Y * θ.read ℓ) a (Sum.inl i) =
        (β ℓ i - β' ℓ i) * θ.read ℓ a (Sum.inl i) := by
      intro a i
      have e := congrFun (congrFun hr' a) (Sum.inl i)
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, Sum.elim_inl] at e
      rw [hYR]
      linear_combination -e
    have hval : ∀ a i, (Y * θ.read ℓ) a (Sum.inr i) =
        -(α ℓ i - α' ℓ i) * θ.read ℓ a (Sum.inr i) := by
      intro a i
      have e := congrFun (congrFun hr' a) (Sum.inr i)
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, Sum.elim_inr] at e
      rw [hYR]
      linear_combination -e
    -- every column is an eigenvector of `Y`, so `Y = μ 1` (general position)
    obtain ⟨μ, hμ⟩ := eq_smul_one_of_eigenvectors_generalPosition (q := hid ℓ ⊕ hid ℓ)
      (fun j => (θ.read ℓ)ᵀ j) (hgp ℓ hℓm) (hcard ℓ hℓm) Y (by
        rintro (i | i)
        · exact ⟨β ℓ i - β' ℓ i, funext fun a => hgate a i⟩
        · exact ⟨-(α ℓ i - α' ℓ i), funext fun a => hval a i⟩)
    have hYμ : ∀ a j, (Y * θ.read ℓ) a j = μ * θ.read ℓ a j := by
      intro a j
      rw [hμ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]
    -- no column is zero, so `β_i - β'_i = μ` and `-(α_i - α'_i) = μ` for every `i`
    have hβi : ∀ i, β ℓ i - β' ℓ i = μ := by
      intro i
      obtain ⟨a, ha'⟩ := exists_ne_zero_col_ubtg (θ.read ℓ) (hgp ℓ hℓm) hd (Sum.inl i)
      exact mul_right_cancel₀ ha' ((hgate a i).symm.trans (hYμ a _))
    have hαi : ∀ i, -(α ℓ i - α' ℓ i) = μ := by
      intro i
      obtain ⟨a, ha'⟩ := exists_ne_zero_col_ubtg (θ.read ℓ) (hgp ℓ hℓm) hd (Sum.inr i)
      exact mul_right_cancel₀ ha' ((hval a i).symm.trans (hYμ a _))
    -- so `-μ = k μ` at the unit `i₀`, and `μ = 0`
    have hμ0 : μ = 0 := by
      have h1 : (1 + (k : ℝ)) * μ = 0 := by
        linear_combination -(hαi i₀) - hwi i₀ - (k : ℝ) * hβi i₀
      have h2 : (1 + (k : ℝ)) ≠ 0 := by positivity
      exact (mul_eq_zero.1 h1).resolve_left h2
    refine ⟨funext fun i => ?_, funext fun i => ?_, ?_⟩
    · have := hαi i
      linarith
    · have := hβi i
      linarith
    · rw [← sub_eq_zero, ← hY, hμ, hμ0, zero_smul]
  -- from the embedding, by induction along the network: `X_j = X'_j` for `j` up to the hidden
  -- state that block `m` reads
  have hfw : ∀ l : Fin (L + 1), l ≤ m.castSucc → X l = X' l := by
    intro l
    induction l using Fin.induction with
    | zero =>
      intro _
      -- the embedding component: `E X_0 = E X'_0` (the rescalings leave `E` alone)
      have h0 : θ.E * X 0 + 0 + 0 = θ.E * X' 0 + 0 + 0 := congrArg Params.E h
      simp only [add_zero] at h0
      exact mul_left_cancel_of_rank_ubtg θ.E hE h0
    | succ ℓ ih =>
      intro hl
      have hℓ : ℓ < m := Fin.succ_le_castSucc_iff.1 hl
      have hX := ih (Fin.castSucc_le_castSucc_iff.2 hℓ.le)
      exact hXw ℓ hℓ (hαr ℓ hℓ.le hX) (hβr ℓ hℓ.le hX)
  -- from the readout, by induction down the network: `X_j = X'_j` for `j` from the hidden state
  -- that block `m` writes on
  have hbw : ∀ l : Fin (L + 1), m.succ ≤ l → X l = X' l := by
    intro l
    induction l using Fin.reverseInduction with
    | last =>
      intro _
      -- the readout component: `X_L D = X'_L D` (the rescalings leave `D` alone)
      have h0 : -(X (Fin.last L) * θ.D) + 0 + 0 = -(X' (Fin.last L) * θ.D) + 0 + 0 :=
        congrArg Params.D h
      simp only [add_zero] at h0
      exact mul_right_cancel_of_rank_ubtg θ.D hD (neg_injective h0)
    | cast ℓ ih =>
      intro hl
      have hℓ : m < ℓ := Fin.succ_le_castSucc_iff.1 hl
      exact (hback ℓ hℓ (ih (Fin.succ_le_succ_iff.2 hℓ.le))).2.2
  -- every hidden state is on one of the two sides; the write of block `m` is not used
  have hX : ∀ l, X l = X' l := by
    intro l
    rcases le_or_gt l m.castSucc with hl | hl
    · exact hfw l hl
    · exact hbw l (Fin.castSucc_lt_iff_succ_le.1 hl)
  -- then `α_ℓ`, `β_ℓ` from the read for `ℓ ≤ m`, from the block step from the readout for `ℓ > m`
  refine Prod.ext (funext hX) (Prod.ext (funext fun ℓ => ?_) (funext fun ℓ => ?_))
  · rcases le_or_gt ℓ m with hℓ | hℓ
    · exact hαr ℓ hℓ (hX _)
    · exact (hback ℓ hℓ (hX _)).1
  · rcases le_or_gt ℓ m with hℓ | hℓ
    · exact hβr ℓ hℓ (hX _)
    · exact (hback ℓ hℓ (hX _)).2.1

end Skips
