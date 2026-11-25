import SkipsLean.Depth.InactiveUnitRelu
import SkipsLean.Dimension.UpperBoundTwoSided
import SkipsLean.Symmetry.LocallyFreeReadoutGeneric

/-!
# Dead units without skips, for blocks with at least `d` hidden units

Paper (skips paper), Proposition A.35 (Dead units without skips): "Consider skipless networks of
`L ≥ 2` ReLU, ReLU² or ReGLU blocks without normalization. There is a nonempty open set of
weights on which a unit of block 2 is dead. On it the functional dimension is at most
`P − (L + 1) d_model² − s − (2 d_model − 1)`, and at most
`P − (L + 1) d_model² − s − (3 d_model − 2)` for ReGLU, so the equality condition fails there."
The Scope of the main text has `d_hidden ≥ d_model` and `d_in, d_out ≥ d_model`.

`Depth/InactiveUnit.lean` and `Depth/InactiveUnitRelu.lean` have the proposition as the dimension
paper states it (Proposition E.1: "each with more than `d_model` hidden units"; "At almost every
point of this set"): they ask more than `d` hidden units in the block of the dead unit, because
the network without the dead unit must have writes of rank `d`. Here the proposition for ReLU and
ReLU² blocks with **at least `d` hidden units in every block**, for `d_in, d_out ≥ d ≥ 1`: the
block of the dead unit may have exactly `d` hidden units. The bound uses the locally free action
from both ends (`Dimension/UpperBoundTwoSided.lean`): nothing is asked of the write of the block
of the dead unit.

* `funDim_add_le_of_eventually_unitInactive_of_rank_E_D`: the bound at one parameter, the twin
  of `funDim_add_le_of_eventually_unitInactive`.
* `exists_isOpen_unitInactive_relu_of_le`, `exists_isOpen_unitInactive_reluSq_of_le`: the
  nonempty open set (the same set `negReadSet`) and the bound at almost every point of it.
* `not_ae_funDim_add_eq_relu_skipless_of_le`, `not_ae_funDim_add_eq_reluSq_skipless_of_le`: "so
  the equality condition fails there".

As in the twins, the network has the blocks `Fin (L + 1)` in the last four statements (at least
two blocks when `L ≥ 1`), Lean's `funDim` is at least the paper's functional dimension, and the
bound is at almost every point of the open set. The bound at every point of the open set is in
`Depth/InactiveUnitEveryPoint.lean`. ReGLU blocks with exactly `d` hidden units in the block of
the dead unit are in `Depth/InactiveGateTwoSided.lean`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ}

/-- Helper (as the private `cancel_left_of_rank_iu` of `InactiveUnit.lean`): a matrix `M` of rank
equal to its number of columns cancels on the left, `M X = M Y → X = Y`. -/
private theorem cancel_left_of_rank_iuts {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

/-- Helper (as the private `mul_right_cancel_of_rank_ubd` of `UpperBoundReadout.lean`): a matrix
`M` of rank equal to its number of rows cancels on the right, `X M = Y M → X = Y`. -/
private theorem cancel_right_of_rank_iuts {m n k : Type*} [Fintype m] [Fintype n]
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

omit [DecidableEq d] in
/-- Helper (as the private `rescaleDirMlpLin_iu` of `InactiveUnit.lean`): `α ↦ rescaleDirMlp k θ α`
is linear. -/
private noncomputable def rescaleDirMlpLin_iuts {L : ℕ} {hid : Fin L → Type}
    [∀ ℓ, Fintype (hid ℓ)] (k : ℕ) (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut where
  toFun := rescaleDirMlp k θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDirMlp]
    · intro ℓ
      ext a i
      simp only [rescaleDirMlp, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply]
      ring
    · intro ℓ
      ext i a
      simp only [rescaleDirMlp, Pi.add_apply, Params.add_write, Matrix.add_apply, Matrix.of_apply]
      ring
    · simp [rescaleDirMlp]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDirMlp]
    · intro ℓ
      ext a i
      simp only [rescaleDirMlp, Pi.smul_apply, Params.smul_read, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · intro ℓ
      ext i a
      simp only [rescaleDirMlp, Pi.smul_apply, Params.smul_write, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [rescaleDirMlp]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read of `unitDir` at a block other than `m` is `0`. -/
private theorem unitDir_read_ne_iuts {L : ℕ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
    [∀ ℓ, DecidableEq (hid ℓ)] {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δr δa : d → ℝ) {ℓ : Fin L} (hℓ : ℓ ≠ m) :
    (unitDir (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δr δa).read ℓ = 0 := by
  simp only [unitDir]
  rw [Function.update_of_ne hℓ]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write of `unitDir` at a block other than `m` is `0`. -/
private theorem unitDir_write_ne_iuts {L : ℕ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
    [∀ ℓ, DecidableEq (hid ℓ)] {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δr δa : d → ℝ) {ℓ : Fin L} (hℓ : ℓ ≠ m) :
    (unitDir (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δr δa).write ℓ = 0 := by
  simp only [unitDir]
  rw [Function.update_of_ne hℓ]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read of `unitDir` at block `m`. -/
private theorem unitDir_read_self_iuts {L : ℕ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
    [∀ ℓ, DecidableEq (hid ℓ)] {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δr δa : d → ℝ) (a : d) (i : hid m) :
    (unitDir (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δr δa).read m a i =
      if i = j then δr a else 0 := by
  simp only [unitDir, Function.update_self, Matrix.of_apply]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write of `unitDir` at block `m`. -/
private theorem unitDir_write_self_iuts {L : ℕ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
    [∀ ℓ, DecidableEq (hid ℓ)] {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δr δa : d → ℝ) (i : hid m) (a : d) :
    (unitDir (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δr δa).write m i a =
      if i = j then δa a else 0 := by
  simp only [unitDir, Function.update_self, Matrix.of_apply]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `(δr, δa) ↦ unitDir m j δr δa` is linear. -/
private noncomputable def unitDirLin_iuts {L : ℕ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
    [∀ ℓ, DecidableEq (hid ℓ)] (m : Fin L) (j : hid m) :
    ((d → ℝ) × (d → ℝ)) →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut where
  toFun p := unitDir m j p.1 p.2
  map_add' p q := by
    apply Params.ext'
    · simp [unitDir]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext a i
        simp only [Params.add_read, Matrix.add_apply, unitDir_read_self_iuts, Prod.fst_add,
          Pi.add_apply]
        split_ifs <;> simp
      · simp only [Params.add_read, unitDir_read_ne_iuts m j _ _ hℓ, add_zero]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext i a
        simp only [Params.add_write, Matrix.add_apply, unitDir_write_self_iuts, Prod.snd_add,
          Pi.add_apply]
        split_ifs <;> simp
      · simp only [Params.add_write, unitDir_write_ne_iuts m j _ _ hℓ, add_zero]
    · simp [unitDir]
  map_smul' c p := by
    apply Params.ext'
    · simp [unitDir]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext a i
        simp only [Params.smul_read, Matrix.smul_apply, unitDir_read_self_iuts, Prod.smul_fst,
          Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> simp
      · simp only [Params.smul_read, unitDir_read_ne_iuts m j _ _ hℓ, smul_zero]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext i a
        simp only [Params.smul_write, Matrix.smul_apply, unitDir_write_self_iuts, Prod.smul_snd,
          Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> simp
      · simp only [Params.smul_write, unitDir_write_ne_iuts m j _ _ hℓ, smul_zero]
    · simp [unitDir]

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- Helper (Lemma A.18 from both ends with the dead unit, in the form for directions): if
`cobDir θ X + rescaleDirMlp k θ α + unitDir m j δr δa = 0` with `α m j = 0` and `k ≠ 0`, then
`X`, `α`, `δr` and `δa` vanish, when `E` and `D` have rank `d`, the writes of the blocks before
`m` and the reads of the blocks after `m` have rank `d`, no read column of a block up to `m` and
no write row of a block after `m` vanishes. Nothing is asked of the write of block `m`. -/
private theorem eq_zero_of_dir_eq_zero_iuts {L : ℕ} {hid : Fin L → Type}
    [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)] (k : ℕ) (hk : k ≠ 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hr : ∀ ℓ, m < ℓ → (θ.read ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a i) ≠ 0)
    (ha : ∀ ℓ, m < ℓ → ∀ i, (fun a => θ.write ℓ i a) ≠ 0)
    (X : Fin (L + 1) → Matrix d d ℝ) (α : ∀ ℓ, hid ℓ → ℝ) (hαj : α m j = 0) (δr δa : d → ℝ)
    (h : cobDir θ X + (rescaleDirMlp k θ α + unitDir m j δr δa) = 0) :
    X = 0 ∧ α = 0 ∧ δr = 0 ∧ δa = 0 := by
  -- the direction of the unit, with its components
  obtain ⟨U, hU⟩ : ∃ U : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut,
      U = unitDir m j δr δa := ⟨_, rfl⟩
  rw [← hU] at h
  have hUr : ∀ ℓ, ℓ ≠ m → U.read ℓ = 0 := fun ℓ hℓ => by
    rw [hU, unitDir_read_ne_iuts m j δr δa hℓ]
  have hUw : ∀ ℓ, ℓ ≠ m → U.write ℓ = 0 := fun ℓ hℓ => by
    rw [hU, unitDir_write_ne_iuts m j δr δa hℓ]
  have hUrm : ∀ a i, U.read m a i = if i = j then δr a else 0 := fun a i => by
    rw [hU, unitDir_read_self_iuts]
  have hUwm : ∀ i a, U.write m i a = if i = j then δa a else 0 := fun i a => by
    rw [hU, unitDir_write_self_iuts]
  -- the components of the equation: `E`, `D`, the reads and the writes
  have h0 : θ.E * X 0 = θ.E * (0 : Matrix d d ℝ) := by
    have hE0 := congrArg Params.E h
    change θ.E * X 0 + (0 + U.E) = 0 at hE0
    rw [show U.E = 0 by rw [hU]; rfl, add_zero, add_zero] at hE0
    rw [hE0, Matrix.mul_zero]
  have hL : X (Fin.last L) * θ.D = (0 : Matrix d d ℝ) * θ.D := by
    have hD0 := congrArg Params.D h
    change -(X (Fin.last L) * θ.D) + (0 + U.D) = 0 at hD0
    rw [show U.D = 0 by rw [hU]; rfl, add_zero, add_zero, neg_eq_zero] at hD0
    rw [hD0, Matrix.zero_mul]
  have hrd : ∀ ℓ a i,
      -(X ℓ.castSucc * θ.read ℓ) a i + (α ℓ i * θ.read ℓ a i + U.read ℓ a i) = 0 :=
    fun ℓ a i => congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) i
  have hwr : ∀ ℓ i a, (θ.write ℓ * X ℓ.succ) i a
      + (-((k : ℝ) * α ℓ i) * θ.write ℓ i a + U.write ℓ i a) = 0 :=
    fun ℓ i a => congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
  -- a block up to `m`: if `X_{ℓ-1} = 0`, then `α_ℓ = 0`. The read column `c_i` of hidden unit `i`
  -- moves by `α_i c_i`, and by `δr` for the dead unit `j` of block `m`, where `α_j = 0`; an entry
  -- `a` with `c_i a ≠ 0` gives `α_i = 0`
  have hαr : ∀ ℓ, ℓ ≤ m → X ℓ.castSucc = 0 → α ℓ = 0 := by
    intro ℓ hℓm hℓ
    funext i
    obtain ⟨a, ha'⟩ := Function.ne_iff.mp (hc ℓ hℓm i)
    have hU0 : U.read ℓ a i = 0 ∨ α ℓ i = 0 := by
      by_cases hℓm' : ℓ = m
      · subst hℓm'
        by_cases hi : i = j
        · right
          rw [hi]
          exact hαj
        · left
          rw [hUrm, ite_eq_right hi]
      · left
        rw [hUr ℓ hℓm']
        rfl
    rcases hU0 with h' | h'
    · have h'' := hrd ℓ a i
      rw [hℓ, h', Matrix.zero_mul, Matrix.zero_apply, neg_zero, zero_add, add_zero] at h''
      exact (mul_eq_zero.mp h'').resolve_right ha'
    · exact h'
  -- a block before `m`: if `α_ℓ = 0`, then `W X_ℓ = 0`, and `W` has rank `d`
  have hXw : ∀ ℓ, ℓ < m → α ℓ = 0 → X ℓ.succ = 0 := by
    intro ℓ hℓm hα
    have hsub : θ.write ℓ * X ℓ.succ = θ.write ℓ * (0 : Matrix d d ℝ) := by
      rw [Matrix.mul_zero]
      ext i a
      have h'' := hwr ℓ i a
      rwa [hα, Pi.zero_apply, mul_zero, neg_zero, zero_mul, zero_add, hUw ℓ hℓm.ne,
        Matrix.zero_apply, add_zero] at h''
    exact cancel_left_of_rank_iuts _ (hw ℓ hℓm) hsub
  -- a block after `m`: if `X_ℓ = 0`, then `α_ℓ = 0`. The write row `a_i` of hidden unit `i` moves
  -- by `-k α_i a_i`; an entry `a` with `a_i a ≠ 0` gives `k α_i = 0`, and `k ≠ 0`
  have hαw : ∀ ℓ, m < ℓ → X ℓ.succ = 0 → α ℓ = 0 := by
    intro ℓ hℓm hℓ
    funext i
    obtain ⟨a, ha'⟩ := Function.ne_iff.mp (ha ℓ hℓm i)
    have h'' := hwr ℓ i a
    rw [hℓ, Matrix.mul_zero, Matrix.zero_apply, zero_add, hUw ℓ hℓm.ne', Matrix.zero_apply,
      add_zero, neg_mul, neg_eq_zero] at h''
    have h3 : (k : ℝ) * α ℓ i = 0 := (mul_eq_zero.mp h'').resolve_right ha'
    exact (mul_eq_zero.mp h3).resolve_left (Nat.cast_ne_zero.2 hk)
  -- a block after `m`: if `α_ℓ = 0`, then `X_{ℓ-1} W_read = 0`, and the read has rank `d`
  have hXr : ∀ ℓ, m < ℓ → α ℓ = 0 → X ℓ.castSucc = 0 := by
    intro ℓ hℓm hα
    have hsub : X ℓ.castSucc * θ.read ℓ = (0 : Matrix d d ℝ) * θ.read ℓ := by
      rw [Matrix.zero_mul]
      ext a i
      have h'' := hrd ℓ a i
      rwa [hα, Pi.zero_apply, zero_mul, zero_add, hUr ℓ hℓm.ne', Matrix.zero_apply, add_zero,
        neg_eq_zero] at h''
    exact cancel_right_of_rank_iuts (θ.read ℓ) (hr ℓ hℓm) hsub
  -- from the embedding, by induction along the network: `X_j = 0` up to the hidden state that
  -- block `m` reads
  have hfw : ∀ l : Fin (L + 1), l ≤ m.castSucc → X l = 0 := by
    intro l
    induction l using Fin.induction with
    | zero => exact fun _ => cancel_left_of_rank_iuts θ.E hE h0
    | succ ℓ ih =>
      intro hl
      have hℓ : ℓ < m := Fin.succ_le_castSucc_iff.1 hl
      exact hXw ℓ hℓ (hαr ℓ hℓ.le (ih (Fin.castSucc_le_castSucc_iff.2 hℓ.le)))
  -- from the readout, by induction down the network: `X_j = 0` from the hidden state that block
  -- `m` writes on
  have hbw : ∀ l : Fin (L + 1), m.succ ≤ l → X l = 0 := by
    intro l
    induction l using Fin.reverseInduction with
    | last => exact fun _ => cancel_right_of_rank_iuts θ.D hD hL
    | cast ℓ ih =>
      intro hl
      have hℓ : m < ℓ := Fin.succ_le_castSucc_iff.1 hl
      exact hXr ℓ hℓ (hαw ℓ hℓ (ih (Fin.succ_le_succ_iff.2 hℓ.le)))
  -- every hidden state is on one of the two sides
  have hX : ∀ l, X l = 0 := by
    intro l
    rcases le_or_gt l m.castSucc with hl | hl
    · exact hfw l hl
    · exact hbw l (Fin.castSucc_lt_iff_succ_le.1 hl)
  -- then `α_ℓ = 0` from the read for `ℓ ≤ m`, from the write for `ℓ > m`
  have hα : α = 0 := by
    funext ℓ
    rcases le_or_gt ℓ m with hℓ | hℓ
    · exact hαr ℓ hℓ (hX _)
    · exact hαw ℓ hℓ (hX _)
  refine ⟨funext hX, hα, ?_, ?_⟩
  · -- read column `j` of block `m` moves by `δr` alone
    funext a
    have h'' := hrd m a j
    rw [hX, hα, hUrm, ite_eq_left rfl] at h''
    simpa only [Pi.zero_apply, Matrix.zero_mul, Matrix.zero_apply, neg_zero, zero_mul, zero_add]
      using h''
  · -- write row `j` of block `m` moves by `δa` alone (the other rows of the write of block `m`
    -- give nothing more)
    funext a
    have h'' := hwr m j a
    rw [hX, hα, hUwm, ite_eq_left rfl] at h''
    simpa only [Pi.zero_apply, Matrix.mul_zero, Matrix.zero_apply, mul_zero, neg_zero, zero_mul,
      zero_add] using h''

/-- **Proposition A.35, the bound, at one parameter (ReLU and ReLU² blocks), with the conditions
from both ends.** Let `σ` be positively homogeneous of degree `k ≠ 0` and vanish on `z ≤ 0`, and
let hidden unit `j` of block `m` be inactive at every input at all parameters near `θ`. If `E`
and `D` have rank `d`, the writes of the blocks before `m` and the reads of the blocks after `m`
have rank `d`, no read column of a block up to `m` and no write row of a block after `m`
vanishes, then `fd(θ) ≤ P − (L+1) d² − s − (2d − 1)`, with `s` the number of hidden units. -/
theorem funDim_add_le_of_eventually_unitInactive_of_rank_E_D {L : ℕ} {hid : Fin L → Type}
    [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)] {k : ℕ} (hk : k ≠ 0)
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hθ : ∀ᶠ θ' in 𝓝 θ, UnitInactive θ' m j)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hr : ∀ ℓ, m < ℓ → (θ.read ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a i) ≠ 0)
    (ha : ∀ ℓ, m < ℓ → ∀ i, (fun a => θ.write ℓ i a) ≠ 0) :
    funDim (Arch.mlp σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) + (2 * Fintype.card d - 1))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the numbers `α` of the rescalings with `α m j = 0`: the kernel `K` of `α ↦ α m j`
  let ev : (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : hid m => ℝ) j).comp
      (LinearMap.proj (R := ℝ) (φ := fun ℓ => hid ℓ → ℝ) m)
  let K := LinearMap.ker ev
  -- the linear map `(X, α, δr, δa) ↦ cobDir θ X + rescaleDirMlp k θ α + unitDir m j δr δa`
  let Φ := (cobDirLin θ).coprod
    (((rescaleDirMlpLin_iuts k θ).comp K.subtype).coprod (unitDirLin_iuts m j))
  -- its directions are flat, since the three summands are
  have hV : LinearMap.range Φ ≤ flat (Arch.mlp σ id hid) 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply]
    exact Submodule.add_mem _ (cobDir_mem_flat_skipless' θ rfl p.1)
      (Submodule.add_mem _ (rescaleDirMlp_mem_flat hσ θ 0 _)
        (unitDir_mem_flat hσ0 θ m j hθ _ _))
  -- it is injective (Lemma A.18 from both ends, with the dead unit)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨X, ⟨α, hα⟩, δr, δa⟩ hp
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply] at hp
    obtain ⟨h1, h2, h3, h4⟩ := eq_zero_of_dir_eq_zero_iuts k hk θ m j hE hD hw hr hc ha X α
      (LinearMap.mem_ker.mp hα) δr δa hp
    exact Prod.ext h1 (Prod.ext (Subtype.ext h2) (Prod.ext h3 h4))
  -- `K` has dimension `s - 1`: `α ↦ α m j` is onto `ℝ`
  have hK : Module.finrank ℝ K + 1 = ∑ ℓ, Fintype.card (hid ℓ) := by
    have hsurj : Function.Surjective ev := fun c =>
      ⟨Function.update 0 m (Function.update 0 j c), by
        simp only [ev, LinearMap.coe_comp, LinearMap.coe_proj, Function.comp_apply,
          Function.eval, Function.update_self]⟩
    have h1 := LinearMap.finrank_range_add_finrank_ker ev
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self,
      Module.finrank_pi_fintype] at h1
    simp only [Module.finrank_fintype_fun_eq_card] at h1
    exact (add_comm _ _).trans h1
  -- `d ≥ 1`, since a read column does not vanish
  have hd : 1 ≤ Fintype.card d := by
    obtain ⟨a, -⟩ := Function.ne_iff.mp (hc m le_rfl j)
    exact Fintype.card_pos_iff.2 ⟨a⟩
  -- the domain has dimension `(L + 1) d² + (s - 1) + 2d`
  have hdim : Module.finrank ℝ ((Fin (L + 1) → Matrix d d ℝ) × (K × ((d → ℝ) × (d → ℝ)))) =
      (L + 1) * Fintype.card d ^ 2 + (Module.finrank ℝ K + (Fintype.card d + Fintype.card d)) := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, finrank_cobDomain,
      Module.finrank_fintype_fun_eq_card]
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rw [LinearMap.finrank_range_of_inj hinj, hdim] at h
  generalize (L + 1) * Fintype.card d ^ 2 = c at h ⊢
  omega

variable {L : ℕ} {hid : Fin (L + 1) → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)]

/-- Proposition A.35 for an activation `σ ≥ 0` that is positively homogeneous of degree `k ≠ 0`
and vanishes on `z ≤ 0` (ReLU and ReLU²), with at least `d` hidden units in every block. -/
private theorem exists_isOpen_unitInactive_iuts [Nonempty d] {k : ℕ} (hk : k ≠ 0)
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0) (hσnn : ∀ z : ℝ, 0 ≤ σ z)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, UnitInactive θ ℓ.succ j) ∧
      ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp σ id hid) 0 θ
          + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m) + (2 * Fintype.card d - 1))
        ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the open set: `a_k r < 0` for every hidden unit `k` of block `ℓ.castSucc`
  refine ⟨negReadSet σ id dIn dOut ℓ j, isOpen_negReadSet ℓ j, nonempty_negReadSet ℓ j,
    fun θ hθ => unitInactive_of_mem_negReadSet hσnn ℓ j hθ, ?_⟩
  -- at generic parameters `E`, `D`, the writes and the reads have rank `d`, and no read column
  -- and no write row vanishes
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_rank_D_read μ hdOut hhid,
    ae_read_col_ne_zero μ, ae_write_row_ne_zero μ] with θ h1 h2 h3 h4 hθU
  -- the unit is inactive at every input at all parameters near `θ`
  have hθ : ∀ᶠ θ' in 𝓝 θ, UnitInactive θ' ℓ.succ j :=
    Filter.mem_of_superset ((isOpen_negReadSet (σ := σ) (χ := id) ℓ j).mem_nhds hθU)
      fun _ h => unitInactive_of_mem_negReadSet hσnn ℓ j h
  -- the bound at one parameter, from both ends, for a network of `L + 1` blocks and `m = ℓ.succ`
  exact funDim_add_le_of_eventually_unitInactive_of_rank_E_D hk hσ hσ0 θ ℓ.succ j hθ h1.1 h2.1
    (fun ℓ' _ => h1.2 ℓ') (fun ℓ' _ => h2.2 ℓ') (fun ℓ' _ i => h3 ℓ' i) (fun ℓ' _ i => h4 ℓ' i)

/-- **Proposition A.35 for ReLU blocks with at least `d` hidden units:** for `d_in, d_out ≥ d ≥ 1`
and at least `d` hidden units in every block, there is a nonempty open set of weights on which
hidden unit `j` of block `ℓ.succ` is inactive at every input, and at almost every point of this
set `fd ≤ P − (L+2) d² − s − (2d − 1)`, with `s` the number of hidden units. -/
theorem exists_isOpen_unitInactive_relu_of_le [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, UnitInactive θ ℓ.succ j) ∧
      ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp relu id hid) 0 θ
          + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m) + (2 * Fintype.card d - 1))
        ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  exact exists_isOpen_unitInactive_iuts (k := 1) one_ne_zero relu_homogeneous
    (fun _ hz => max_eq_right hz) (fun _ => le_max_right _ _) μ hdIn hdOut hhid ℓ j

/-- **Proposition A.35 for ReLU² blocks with at least `d` hidden units:** the same as for ReLU
blocks. -/
theorem exists_isOpen_unitInactive_reluSq_of_le [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, UnitInactive θ ℓ.succ j) ∧
      ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp reluSq id hid) 0 θ
          + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m) + (2 * Fintype.card d - 1))
        ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  exact exists_isOpen_unitInactive_iuts (k := 2) two_ne_zero reluSq_homogeneous
    (fun _ hz => by rw [reluSq, max_eq_right hz, zero_pow two_ne_zero])
    (fun _ => sq_nonneg _) μ hdIn hdOut hhid ℓ j

/-- "So the equality condition fails there", for an activation as in
`exists_isOpen_unitInactive_iuts`, with at least `d` hidden units in every block. -/
private theorem not_ae_funDim_add_eq_iuts [Nonempty d] {k : ℕ} (hk : k ≠ 0)
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0) (hσnn : ∀ z : ℝ, 0 ≤ σ z)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) :
    ¬ ∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 0 θ
        + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  intro hae
  -- the dead unit: a hidden unit `j` of the second block (it has at least `d ≥ 1` of them)
  let ℓ : Fin L := ⟨0, hL⟩
  have hd1 : 0 < Fintype.card d := Fintype.card_pos
  have : Nonempty (hid ℓ.succ) := Fintype.card_pos_iff.mp (hd1.trans_le (hhid _))
  obtain j : hid ℓ.succ := Classical.arbitrary _
  obtain ⟨U, hUo, hUne, -, hU⟩ :=
    exists_isOpen_unitInactive_iuts hk hσ hσ0 hσnn μ hdIn hdOut hhid ℓ j
  -- at almost every point of `U` both the equality and the bound with `2d - 1 ≥ 1` would hold
  have hnull : μ U = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae, hU] with θ he hle hθU
    have := hle hθU
    omega
  -- but a nonempty open set has positive measure
  exact (hUo.measure_pos μ hUne).ne' hnull

/-- **Proposition A.35, "so the equality condition fails there", for ReLU blocks with at least
`d` hidden units:** for at least two blocks (`L ≥ 1`) and `d_in, d_out ≥ d ≥ 1`, it is not the
case that `fd = P − (L+2) d² − s` at almost every parameter. -/
theorem not_ae_funDim_add_eq_relu_skipless_of_le [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) :
    ¬ ∀ᵐ θ ∂μ, funDim (Arch.mlp relu id hid) 0 θ
        + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  exact not_ae_funDim_add_eq_iuts (k := 1) one_ne_zero relu_homogeneous
    (fun _ hz => max_eq_right hz) (fun _ => le_max_right _ _) μ hL hdIn hdOut hhid

/-- **The same for ReLU² blocks with at least `d` hidden units.** -/
theorem not_ae_funDim_add_eq_reluSq_skipless_of_le [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) :
    ¬ ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq id hid) 0 θ
        + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  exact not_ae_funDim_add_eq_iuts (k := 2) two_ne_zero reluSq_homogeneous
    (fun _ hz => by rw [reluSq, max_eq_right hz, zero_pow two_ne_zero])
    (fun _ => sq_nonneg _) μ hL hdIn hdOut hhid

end Skips
