import SkipsLean.Depth.InactiveGateReGLU
import SkipsLean.Dimension.UpperBoundTwoSidedGated
import SkipsLean.Symmetry.LocallyFreeReadoutGeneric

/-!
# Dead units without skips, ReGLU blocks with at least `d` hidden units

Paper (skips paper), Proposition A.35 (Dead units without skips): "Consider skipless networks of
`L ≥ 2` ReLU, ReLU² or ReGLU blocks without normalization. There is a nonempty open set of
weights on which a unit of block 2 is dead. On it the functional dimension is at most
`P − (L + 1) d_model² − s − (2 d_model − 1)`, and at most
`P − (L + 1) d_model² − s − (3 d_model − 2)` for ReGLU, so the equality condition fails there."

`Depth/InactiveGate.lean` and `Depth/InactiveGateReGLU.lean` have the proposition for ReGLU
blocks as the dimension paper states it (Proposition E.1, more than `d_model` hidden units in the
block of the dead unit). Here the twins for **at least `d` hidden units in every block** and
`d_in, d_out ≥ d ≥ 1`, as `Depth/InactiveUnitTwoSided.lean` for ReLU and ReLU² blocks: the bound
uses the locally free action from both ends (`Dimension/UpperBoundTwoSidedGated.lean`), and asks
nothing of the write of the block of the dead unit. For the blocks after it the gate and value
columns of the read are asked in general position, which holds at generic parameters.

As in the twins, the last two statements are for networks with the blocks `Fin (L + 1)`, Lean's
`funDim` is at least the paper's functional dimension, and the bound is at almost every point of
the open set. Not stated: the bound at every point of the open set.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ}

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (as the private `unitDirGated_read_ne_ig` of `InactiveGate.lean`): the read of
`unitDirGated` vanishes at the blocks other than `m`. -/
private theorem unitDirGated_read_ne_igts {L : ℕ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
    [∀ ℓ, DecidableEq (hid ℓ)] {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δg δe δa : d → ℝ) {ℓ : Fin L} (h : ℓ ≠ m) :
    (unitDirGated (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δg δe δa).read ℓ = 0 := by
  simp only [unitDirGated]
  rw [Function.update_of_ne h]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write of `unitDirGated` vanishes at the blocks other than `m`. -/
private theorem unitDirGated_write_ne_igts {L : ℕ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
    [∀ ℓ, DecidableEq (hid ℓ)] {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δg δe δa : d → ℝ) {ℓ : Fin L} (h : ℓ ≠ m) :
    (unitDirGated (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δg δe δa).write ℓ = 0 := by
  simp only [unitDirGated]
  rw [Function.update_of_ne h]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the gate columns of the read of `unitDirGated` at block `m`. -/
private theorem unitDirGated_gate_igts {L : ℕ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
    [∀ ℓ, DecidableEq (hid ℓ)] {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δg δe δa : d → ℝ) (a : d) (i : hid m) :
    (unitDirGated (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δg δe δa).read m a
      (Sum.inl i) = if i = j then δg a else 0 := by
  simp only [unitDirGated, Function.update_self, Matrix.of_apply, Sum.elim_inl]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the value columns of the read of `unitDirGated` at block `m`. -/
private theorem unitDirGated_value_igts {L : ℕ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
    [∀ ℓ, DecidableEq (hid ℓ)] {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δg δe δa : d → ℝ) (a : d) (i : hid m) :
    (unitDirGated (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δg δe δa).read m a
      (Sum.inr i) = if i = j then δe a else 0 := by
  simp only [unitDirGated, Function.update_self, Matrix.of_apply, Sum.elim_inr]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write rows of `unitDirGated` at block `m`. -/
private theorem unitDirGated_write_igts {L : ℕ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
    [∀ ℓ, DecidableEq (hid ℓ)] {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m)
    (δg δe δa : d → ℝ) (i : hid m) (a : d) :
    (unitDirGated (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δg δe δa).write m i a
      = if i = j then δa a else 0 := by
  simp only [unitDirGated, Function.update_self, Matrix.of_apply]

/-- Helper (as the private `cancel_left_of_rank_ig` of `InactiveGate.lean`): a matrix `M` of rank
equal to its number of columns cancels on the left, `M X = M Y → X = Y`. -/
private theorem cancel_left_of_rank_igts {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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
private theorem cancel_right_of_rank_igts {m n k : Type*} [Fintype m] [Fintype n]
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

/-- Helper (the private `exists_ne_zero_col_uri` of `UpperBoundReadoutInside.lean`): columns in
general position, `d ≥ 1`: no column is zero (a single column is linearly independent). -/
private theorem exists_ne_zero_col_igts {m q : Type*} [Fintype m] (R : Matrix m q ℝ)
    (hgp : ∀ S : Finset q, S.card ≤ Fintype.card m → LinearIndependent ℝ fun j : S => Rᵀ j)
    (hm : 0 < Fintype.card m) (j : q) : ∃ a, R a j ≠ 0 := by
  have h := (hgp {j} (by rw [Finset.card_singleton]; omega)).ne_zero
    ⟨j, Finset.mem_singleton_self j⟩
  obtain ⟨a, ha⟩ := Function.ne_iff.mp h
  exact ⟨a, ha⟩

/-- Helper: `α ↦ rescaleDir θ α` is linear (the private `rescaleDirLin_ig` of
`Depth/InactiveGate.lean`). -/
private noncomputable def rescaleDirLin_igts {L : ℕ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut where
  toFun := rescaleDir θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext a j
      cases j with
      | inl i => simp [rescaleDir]
      | inr i =>
        simp only [rescaleDir, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply,
          Sum.elim_inr]
        ring
    · intro ℓ
      ext i a
      simp [rescaleDir, add_mul]
    · simp [rescaleDir]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext a j
      cases j <;> simp [rescaleDir, mul_assoc]
    · intro ℓ
      ext i a
      simp [rescaleDir, mul_assoc]
    · simp [rescaleDir]

/-- Helper: `β ↦ rescaleDirGate k θ β` is linear (the private `rescaleDirGateLin_ig` of
`Depth/InactiveGate.lean`). -/
private noncomputable def rescaleDirGateLin_igts {L : ℕ} {hid : Fin L → Type}
    [∀ ℓ, Fintype (hid ℓ)] (k : ℕ) (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut where
  toFun := rescaleDirGate k θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDirGate]
    · intro ℓ
      ext a j
      cases j with
      | inl i =>
        simp only [rescaleDirGate, Pi.add_apply, Params.add_read, Matrix.add_apply,
          Matrix.of_apply, Sum.elim_inl]
        ring
      | inr i => simp [rescaleDirGate]
    · intro ℓ
      ext i a
      simp only [rescaleDirGate, Pi.add_apply, Params.add_write, Matrix.add_apply,
        Matrix.of_apply]
      ring
    · simp [rescaleDirGate]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDirGate]
    · intro ℓ
      ext a j
      cases j with
      | inl i =>
        simp only [rescaleDirGate, Pi.smul_apply, Params.smul_read, Matrix.smul_apply,
          Matrix.of_apply, Sum.elim_inl, smul_eq_mul, RingHom.id_apply]
        ring
      | inr i => simp [rescaleDirGate]
    · intro ℓ
      ext i a
      simp only [rescaleDirGate, Pi.smul_apply, Params.smul_write, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [rescaleDirGate]

/-- Helper: `(δg, δe, δa) ↦ unitDirGated m j δg δe δa` is linear (the private
`unitDirGatedLin_ig` of `Depth/InactiveGate.lean`). -/
private noncomputable def unitDirGatedLin_igts {L : ℕ} {hid : Fin L → Type}
    [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)] (m : Fin L) (j : hid m) :
    ((d → ℝ) × (d → ℝ) × (d → ℝ)) →ₗ[ℝ]
      Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut where
  toFun p := unitDirGated m j p.1 p.2.1 p.2.2
  map_add' p q := by
    apply Params.ext'
    · simp [unitDirGated]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext a i
        cases i with
        | inl i =>
          rw [Params.add_read, Matrix.add_apply, unitDirGated_gate_igts, unitDirGated_gate_igts,
            unitDirGated_gate_igts]
          split_ifs <;> simp
        | inr i =>
          rw [Params.add_read, Matrix.add_apply, unitDirGated_value_igts, unitDirGated_value_igts,
            unitDirGated_value_igts]
          split_ifs <;> simp
      · rw [Params.add_read, unitDirGated_read_ne_igts _ _ _ _ _ hℓ,
          unitDirGated_read_ne_igts _ _ _ _ _ hℓ, unitDirGated_read_ne_igts _ _ _ _ _ hℓ,
          add_zero]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext i a
        rw [Params.add_write, Matrix.add_apply, unitDirGated_write_igts, unitDirGated_write_igts,
          unitDirGated_write_igts]
        split_ifs <;> simp
      · rw [Params.add_write, unitDirGated_write_ne_igts _ _ _ _ _ hℓ,
          unitDirGated_write_ne_igts _ _ _ _ _ hℓ, unitDirGated_write_ne_igts _ _ _ _ _ hℓ,
          add_zero]
    · simp [unitDirGated]
  map_smul' c p := by
    apply Params.ext'
    · simp [unitDirGated]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext a i
        cases i with
        | inl i =>
          rw [Params.smul_read, Matrix.smul_apply, unitDirGated_gate_igts,
            unitDirGated_gate_igts]
          split_ifs <;> simp
        | inr i =>
          rw [Params.smul_read, Matrix.smul_apply, unitDirGated_value_igts,
            unitDirGated_value_igts]
          split_ifs <;> simp
      · rw [Params.smul_read, unitDirGated_read_ne_igts _ _ _ _ _ hℓ,
          unitDirGated_read_ne_igts _ _ _ _ _ hℓ, smul_zero]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext i a
        rw [Params.smul_write, Matrix.smul_apply, unitDirGated_write_igts,
          unitDirGated_write_igts]
        split_ifs <;> simp
      · rw [Params.smul_write, unitDirGated_write_ne_igts _ _ _ _ _ hℓ,
          unitDirGated_write_ne_igts _ _ _ _ _ hℓ, smul_zero]
    · simp [unitDirGated]

/-- Helper: the value `α m j` of a family of numbers on the hidden units, as a linear
functional (the private `evalAt_ig` of `Depth/InactiveGate.lean`). -/
private noncomputable def evalAt_igts {L : ℕ} {hid : Fin L → Type} (m : Fin L) (j : hid m) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.proj j).comp (LinearMap.proj (R := ℝ) (φ := fun ℓ => hid ℓ → ℝ) m)

/-- Helper: the families that vanish at `(m, j)` form a space of dimension `∑ d_hidden - 1`
(rank–nullity for the functional `α ↦ α m j`, which is onto). -/
private theorem finrank_ker_evalAt_igts {L : ℕ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]
    (m : Fin L) (j : hid m) :
    Module.finrank ℝ (LinearMap.ker (evalAt_igts m j)) + 1 = ∑ ℓ, Fintype.card (hid ℓ) := by
  have h := LinearMap.finrank_range_add_finrank_ker (evalAt_igts m j)
  have hr : LinearMap.range (evalAt_igts m j) = ⊤ :=
    LinearMap.range_eq_top.2 fun c => ⟨fun _ _ => c, rfl⟩
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_pi_fintype] at h
  simp only [Module.finrank_fintype_fun_eq_card] at h
  omega

omit [Fintype T] [Fintype dIn] in
/-- Helper (Lemma A.18 from both ends with the dead gated unit, in the form for directions): if
`cobDir θ X + rescaleDir θ α + rescaleDirGate k θ β + unitDirGated m j δg δe δa = 0` with
`α m j = β m j = 0`, then `X`, `α`, `β`, `δg`, `δe` and `δa` vanish, under the conditions of
`cobDir_add_rescaleDir_add_rescaleDirGate_injective_of_rank_E_D`. Nothing is asked of the write
of block `m`. -/
private theorem eq_zero_of_dir_eq_zero_igts {L : ℕ} {hid : Fin L → Type}
    [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)] (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0)
    (ha : ∀ ℓ, m < ℓ → ∀ i, (fun a => θ.write ℓ i a) ≠ 0)
    (hgp : ∀ ℓ, m < ℓ → ∀ S : Finset (hid ℓ ⊕ hid ℓ), S.card ≤ Fintype.card d →
      LinearIndependent ℝ fun j : S => (θ.read ℓ)ᵀ j)
    (hcard : ∀ ℓ, m < ℓ → Fintype.card d < Fintype.card (hid ℓ ⊕ hid ℓ))
    (X : Fin (L + 1) → Matrix d d ℝ) (α β : ∀ ℓ, hid ℓ → ℝ) (hα0 : α m j = 0)
    (hβ0 : β m j = 0) (δg δe δa : d → ℝ)
    (h : cobDir θ X + (rescaleDir θ α + (rescaleDirGate k θ β
      + unitDirGated m j δg δe δa)) = 0) :
    X = 0 ∧ α = 0 ∧ β = 0 ∧ δg = 0 ∧ δe = 0 ∧ δa = 0 := by
  -- the direction of the unit, with its components
  obtain ⟨U, hU⟩ : ∃ U : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut,
      U = unitDirGated m j δg δe δa := ⟨_, rfl⟩
  rw [← hU] at h
  have hUr : ∀ ℓ, ℓ ≠ m → U.read ℓ = 0 := fun ℓ hℓ => by
    rw [hU, unitDirGated_read_ne_igts m j δg δe δa hℓ]
  have hUw : ∀ ℓ, ℓ ≠ m → U.write ℓ = 0 := fun ℓ hℓ => by
    rw [hU, unitDirGated_write_ne_igts m j δg δe δa hℓ]
  have hUg : ∀ a i, U.read m a (Sum.inl i) = if i = j then δg a else 0 := fun a i => by
    rw [hU, unitDirGated_gate_igts]
  have hUv : ∀ a i, U.read m a (Sum.inr i) = if i = j then δe a else 0 := fun a i => by
    rw [hU, unitDirGated_value_igts]
  have hUwm : ∀ i a, U.write m i a = if i = j then δa a else 0 := fun i a => by
    rw [hU, unitDirGated_write_igts]
  -- the components of the equation: `E`, `D`, the gate and value columns, the write rows
  have hE0 : θ.E * X 0 = θ.E * (0 : Matrix d d ℝ) := by
    have h1 := congrArg Params.E h
    change θ.E * X 0 + (0 + (0 + U.E)) = 0 at h1
    rw [show U.E = 0 by rw [hU]; rfl, add_zero, add_zero, add_zero] at h1
    rw [h1, Matrix.mul_zero]
  have hL : X (Fin.last L) * θ.D = (0 : Matrix d d ℝ) * θ.D := by
    have h1 := congrArg Params.D h
    change -(X (Fin.last L) * θ.D) + (0 + (0 + U.D)) = 0 at h1
    rw [show U.D = 0 by rw [hU]; rfl, add_zero, add_zero, add_zero, neg_eq_zero] at h1
    rw [h1, Matrix.zero_mul]
  have hgate : ∀ ℓ a i, -(X ℓ.castSucc * θ.read ℓ) a (Sum.inl i)
      + β ℓ i * θ.read ℓ a (Sum.inl i) + U.read ℓ a (Sum.inl i) = 0 := by
    intro ℓ a i
    have h1 := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inl i)
    change -(X ℓ.castSucc * θ.read ℓ) a (Sum.inl i) + (0 + (β ℓ i * θ.read ℓ a (Sum.inl i)
      + U.read ℓ a (Sum.inl i))) = 0 at h1
    linarith
  have hval : ∀ ℓ a i, -(X ℓ.castSucc * θ.read ℓ) a (Sum.inr i)
      - α ℓ i * θ.read ℓ a (Sum.inr i) + U.read ℓ a (Sum.inr i) = 0 := by
    intro ℓ a i
    have h1 := congrFun (congrFun (congrArg (fun η => η.read ℓ) h) a) (Sum.inr i)
    change -(X ℓ.castSucc * θ.read ℓ) a (Sum.inr i) + (-(α ℓ i) * θ.read ℓ a (Sum.inr i)
      + (0 + U.read ℓ a (Sum.inr i))) = 0 at h1
    linarith
  have hwr : ∀ ℓ i a, (θ.write ℓ * X ℓ.succ) i a + α ℓ i * θ.write ℓ i a
      - (k : ℝ) * β ℓ i * θ.write ℓ i a + U.write ℓ i a = 0 := by
    intro ℓ i a
    have h1 := congrFun (congrFun (congrArg (fun η => η.write ℓ) h) i) a
    change (θ.write ℓ * X ℓ.succ) i a + (α ℓ i * θ.write ℓ i a
      + (-((k : ℝ) * β ℓ i) * θ.write ℓ i a + U.write ℓ i a)) = 0 at h1
    linarith
  -- a block up to `m`: if `X_{ℓ-1} = 0`, then `α_ℓ = 0` and `β_ℓ = 0`. The value column `e_i` of
  -- hidden unit `i` moves by `-α_i e_i`, its gate column `g_i` by `β_i g_i`, and by `δe`, `δg`
  -- for the unit `j` of block `m`, where `α_j = β_j = 0`; entries `a` with `e_i a ≠ 0`,
  -- `g_i a ≠ 0` give `α_i = 0`, `β_i = 0`
  have hfwd : ∀ ℓ, ℓ ≤ m → X ℓ.castSucc = 0 → α ℓ = 0 ∧ β ℓ = 0 := by
    intro ℓ hℓm hℓ
    constructor
    · funext i
      obtain ⟨a, ha'⟩ := Function.ne_iff.mp (hv ℓ hℓm i)
      have h1 := hval ℓ a i
      rw [hℓ, Matrix.zero_mul, Matrix.zero_apply, neg_zero, zero_sub] at h1
      by_cases hℓm' : ℓ = m
      · subst hℓm'
        by_cases hij : i = j
        · subst hij
          exact hα0
        · rw [hUv, ite_eq_right_iff.2 fun h => absurd h hij, add_zero, neg_eq_zero] at h1
          exact (mul_eq_zero.1 h1).resolve_right ha'
      · rw [hUr ℓ hℓm', Matrix.zero_apply, add_zero, neg_eq_zero] at h1
        exact (mul_eq_zero.1 h1).resolve_right ha'
    · funext i
      obtain ⟨a, ha'⟩ := Function.ne_iff.mp (hg ℓ hℓm i)
      have h1 := hgate ℓ a i
      rw [hℓ, Matrix.zero_mul, Matrix.zero_apply, neg_zero, zero_add] at h1
      by_cases hℓm' : ℓ = m
      · subst hℓm'
        by_cases hij : i = j
        · subst hij
          exact hβ0
        · rw [hUg, ite_eq_right_iff.2 fun h => absurd h hij, add_zero] at h1
          exact (mul_eq_zero.1 h1).resolve_right ha'
      · rw [hUr ℓ hℓm', Matrix.zero_apply, add_zero] at h1
        exact (mul_eq_zero.1 h1).resolve_right ha'
  -- a block before `m`: if `α_ℓ = β_ℓ = 0`, then `W X_ℓ = 0`, and `W` has rank `d`
  have hXw : ∀ ℓ, ℓ < m → α ℓ = 0 → β ℓ = 0 → X ℓ.succ = 0 := by
    intro ℓ hℓm hα hβ
    refine cancel_left_of_rank_igts _ (hw ℓ hℓm) (Y := 0) ?_
    ext i a
    have h1 := hwr ℓ i a
    rw [hα, hβ, hUw ℓ hℓm.ne] at h1
    simp only [Pi.zero_apply, zero_mul, mul_zero, Matrix.zero_apply, add_zero, sub_zero] at h1
    rw [Matrix.mul_zero, Matrix.zero_apply]
    exact h1
  -- a block after `m`: if `X_ℓ = 0`, then `α_ℓ = 0`, `β_ℓ = 0` and `X_{ℓ-1} = 0`
  have hback : ∀ ℓ, m < ℓ → X ℓ.succ = 0 → α ℓ = 0 ∧ β ℓ = 0 ∧ X ℓ.castSucc = 0 := by
    intro ℓ hℓm hℓ
    -- the block has a hidden unit `i₀`, and `d ≥ 1` (the write row of `i₀` is not zero)
    have hcs := hcard ℓ hℓm
    rw [Fintype.card_sum] at hcs
    obtain ⟨i₀⟩ : Nonempty (hid ℓ) := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨a₀, -⟩ := Function.ne_iff.mp (ha ℓ hℓm i₀)
    have hd : 0 < Fintype.card d := Fintype.card_pos_iff.mpr ⟨a₀⟩
    -- the write row `a_i` of hidden unit `i` moves by `(α_i - k β_i) a_i`; an entry `a` with
    -- `a_i a ≠ 0` gives `α_i - k β_i = 0`
    have hwi : ∀ i, α ℓ i - k * β ℓ i = 0 := by
      intro i
      obtain ⟨a, ha'⟩ := Function.ne_iff.mp (ha ℓ hℓm i)
      have h1 := hwr ℓ i a
      rw [hℓ, hUw ℓ hℓm.ne'] at h1
      simp only [Matrix.mul_zero, Matrix.zero_apply] at h1
      have h2 : (α ℓ i - k * β ℓ i) * θ.write ℓ i a = 0 := by linear_combination h1
      exact (mul_eq_zero.1 h2).resolve_right ha'
    -- the read: `X_ℓ g_i = β_i g_i` on the gate columns and `X_ℓ e_i = -α_i e_i` on the value
    -- columns
    have hgate' : ∀ a i, (X ℓ.castSucc * θ.read ℓ) a (Sum.inl i) =
        β ℓ i * θ.read ℓ a (Sum.inl i) := by
      intro a i
      have h1 := hgate ℓ a i
      rw [hUr ℓ hℓm.ne', Matrix.zero_apply, add_zero] at h1
      linarith
    have hval' : ∀ a i, (X ℓ.castSucc * θ.read ℓ) a (Sum.inr i) =
        -(α ℓ i) * θ.read ℓ a (Sum.inr i) := by
      intro a i
      have h1 := hval ℓ a i
      rw [hUr ℓ hℓm.ne', Matrix.zero_apply, add_zero] at h1
      linarith
    -- every column is an eigenvector of `X_ℓ`, so `X_ℓ = μ 1` (general position)
    obtain ⟨μ, hμ⟩ := eq_smul_one_of_eigenvectors_generalPosition (q := hid ℓ ⊕ hid ℓ)
      (fun j => (θ.read ℓ)ᵀ j) (hgp ℓ hℓm) (hcard ℓ hℓm) (X ℓ.castSucc) (by
        rintro (i | i)
        · exact ⟨β ℓ i, funext fun a => hgate' a i⟩
        · exact ⟨-(α ℓ i), funext fun a => hval' a i⟩)
    have hYμ : ∀ a j, (X ℓ.castSucc * θ.read ℓ) a j = μ * θ.read ℓ a j := by
      intro a j
      rw [hμ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]
    -- no column is zero, so `β_i = μ` and `-α_i = μ` for every `i`
    have hβi : ∀ i, β ℓ i = μ := by
      intro i
      obtain ⟨a, ha'⟩ := exists_ne_zero_col_igts (θ.read ℓ) (hgp ℓ hℓm) hd (Sum.inl i)
      exact mul_right_cancel₀ ha' ((hgate' a i).symm.trans (hYμ a _))
    have hαi : ∀ i, -(α ℓ i) = μ := by
      intro i
      obtain ⟨a, ha'⟩ := exists_ne_zero_col_igts (θ.read ℓ) (hgp ℓ hℓm) hd (Sum.inr i)
      exact mul_right_cancel₀ ha' ((hval' a i).symm.trans (hYμ a _))
    -- so `-μ = k μ` at the unit `i₀`, and `μ = 0`
    have hμ0 : μ = 0 := by
      have h1 : (1 + (k : ℝ)) * μ = 0 := by
        linear_combination -(hαi i₀) - hwi i₀ - (k : ℝ) * hβi i₀
      have h2 : (1 + (k : ℝ)) ≠ 0 := by positivity
      exact (mul_eq_zero.1 h1).resolve_left h2
    refine ⟨funext fun i => ?_, funext fun i => ?_, ?_⟩
    · rw [Pi.zero_apply]
      linarith [hαi i]
    · rw [Pi.zero_apply]
      linarith [hβi i]
    · rw [hμ, hμ0, zero_smul]
  -- from the embedding, by induction along the network: `X_j = 0` up to the hidden state that
  -- block `m` reads
  have hfw : ∀ l : Fin (L + 1), l ≤ m.castSucc → X l = 0 := by
    intro l
    induction l using Fin.induction with
    | zero => exact fun _ => cancel_left_of_rank_igts θ.E hE hE0
    | succ ℓ ih =>
      intro hl
      have hℓ : ℓ < m := Fin.succ_le_castSucc_iff.1 hl
      have h0 := hfwd ℓ hℓ.le (ih (Fin.castSucc_le_castSucc_iff.2 hℓ.le))
      exact hXw ℓ hℓ h0.1 h0.2
  -- from the readout, by induction down the network: `X_j = 0` from the hidden state that block
  -- `m` writes on
  have hbw : ∀ l : Fin (L + 1), m.succ ≤ l → X l = 0 := by
    intro l
    induction l using Fin.reverseInduction with
    | last => exact fun _ => cancel_right_of_rank_igts θ.D hD hL
    | cast ℓ ih =>
      intro hl
      have hℓ : m < ℓ := Fin.succ_le_castSucc_iff.1 hl
      exact (hback ℓ hℓ (ih (Fin.succ_le_succ_iff.2 hℓ.le))).2.2
  -- every hidden state is on one of the two sides
  have hX : ∀ l, X l = 0 := by
    intro l
    rcases le_or_gt l m.castSucc with hl | hl
    · exact hfw l hl
    · exact hbw l (Fin.castSucc_lt_iff_succ_le.1 hl)
  -- then `α_ℓ = β_ℓ = 0` from the read for `ℓ ≤ m`, from the block step from the readout for
  -- `ℓ > m`
  have hα : α = 0 := by
    funext ℓ
    rcases le_or_gt ℓ m with hℓ | hℓ
    · exact (hfwd ℓ hℓ (hX _)).1
    · exact (hback ℓ hℓ (hX _)).1
  have hβ : β = 0 := by
    funext ℓ
    rcases le_or_gt ℓ m with hℓ | hℓ
    · exact (hfwd ℓ hℓ (hX _)).2
    · exact (hback ℓ hℓ (hX _)).2.1
  refine ⟨funext hX, hα, hβ, ?_, ?_, ?_⟩
  · -- the gate column of unit `j` of block `m` moves by `δg` alone
    funext a
    have h1 := hgate m a j
    rw [hX] at h1
    simp only [hβ, Matrix.zero_mul, Matrix.zero_apply, neg_zero, Pi.zero_apply, zero_mul,
      zero_add, hUg, ↓reduceIte] at h1
    exact h1
  · -- the value column of unit `j` of block `m` moves by `δe` alone
    funext a
    have h1 := hval m a j
    rw [hX] at h1
    simp only [hα, Matrix.zero_mul, Matrix.zero_apply, neg_zero, Pi.zero_apply, zero_mul,
      sub_zero, zero_add, hUv, ↓reduceIte] at h1
    exact h1
  · -- the write row `j` of block `m` moves by `δa` alone (the other rows of the write of block
    -- `m` give nothing more)
    funext a
    have h1 := hwr m j a
    rw [hX] at h1
    simp only [hα, hβ, Matrix.mul_zero, Matrix.zero_apply, Pi.zero_apply, zero_mul,
      mul_zero, add_zero, sub_zero, zero_add, hUwm, ↓reduceIte] at h1
    exact h1

/-- **Proposition A.35, the bound, at one parameter (ReGLU blocks), with the conditions from
both ends.** Let the gate activation be positively homogeneous of degree `k` and vanish on
`z ≤ 0`, and let the gate of hidden unit `j` of block `m` be closed at every input at all
parameters near `θ`. If `E` and `D` have rank `d`, the writes of the blocks before `m` have rank
`d`, no gate column and no value column of a read of a block up to `m` vanishes, and for every
block after `m` no write row vanishes and the gate and value columns of its read are in general
position, then `fd(θ) ≤ P − (L+1) d² − s − (3d − 2)`, with `s` twice the number of hidden
units. -/
theorem funDim_add_le_of_eventually_gateInactive_of_rank_E_D {L : ℕ} {hid : Fin L → Type}
    [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hθ : ∀ᶠ θ' in 𝓝 θ, GateInactive θ' m j)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∀ ℓ, ℓ < m → (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ, ℓ ≤ m → ∀ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0)
    (ha : ∀ ℓ, m < ℓ → ∀ i, (fun a => θ.write ℓ i a) ≠ 0)
    (hgp : ∀ ℓ, m < ℓ → ∀ S : Finset (hid ℓ ⊕ hid ℓ), S.card ≤ Fintype.card d →
      LinearIndependent ℝ fun j : S => (θ.read ℓ)ᵀ j)
    (hcard : ∀ ℓ, m < ℓ → Fintype.card d < Fintype.card (hid ℓ ⊕ hid ℓ)) :
    funDim (Arch.gated σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ)
          + (3 * Fintype.card d - 2))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the families of numbers on the hidden units that vanish at `(m, j)`
  set K := LinearMap.ker (evalAt_igts m j) with hK
  -- the linear map `(X, α, β, δ) ↦ cobDir θ X + rescaleDir θ α + rescaleDirGate k θ β
  -- + unitDirGated m j δ`, with `α m j = β m j = 0`
  let Φ := (cobDirLin θ).coprod (((rescaleDirLin_igts θ).comp K.subtype).coprod
    (((rescaleDirGateLin_igts k θ).comp K.subtype).coprod (unitDirGatedLin_igts m j)))
  -- its directions are flat, since the four summands are
  have hV : LinearMap.range Φ ≤ flat (Arch.gated σ id hid) 0 θ := by
    rintro _ ⟨p, rfl⟩
    exact Submodule.add_mem _ (cobDir_mem_flat_skipless' θ rfl p.1)
      (Submodule.add_mem _ (rescaleDir_mem_flat' θ 0 p.2.1.1)
        (Submodule.add_mem _ (rescaleDirGate_mem_flat hσ θ 0 p.2.2.1.1)
          (unitDirGated_mem_flat hσ0 θ m j hθ p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)))
  -- it is injective (Lemma A.18 from both ends, with the dead gated unit)
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 ?_
    rintro ⟨X, ⟨α, hα⟩, ⟨β, hβ⟩, δg, δe, δa⟩ hp
    have h : cobDir θ X + (rescaleDir θ α + (rescaleDirGate k θ β
        + unitDirGated m j δg δe δa)) = 0 := hp
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := eq_zero_of_dir_eq_zero_igts k θ m j hE hD hw hv hg ha
      hgp hcard X α β (LinearMap.mem_ker.1 hα) (LinearMap.mem_ker.1 hβ) δg δe δa h
    exact Prod.ext h1 (Prod.ext (Subtype.ext h2) (Prod.ext (Subtype.ext h3)
      (Prod.ext h4 (Prod.ext h5 h6))))
  -- the domain has dimension `(L + 1) d² + 2 (∑ d_hidden - 1) + 3 d`
  have hdim : Module.finrank ℝ
        ((Fin (L + 1) → Matrix d d ℝ) × K × K × ((d → ℝ) × (d → ℝ) × (d → ℝ))) + 2
      = (L + 1) * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ) + 3 * Fintype.card d := by
    have hk := finrank_ker_evalAt_igts m j
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
      Module.finrank_prod, finrank_cobDomain]
    simp only [Module.finrank_fintype_fun_eq_card]
    rw [← hK] at hk
    omega
  -- `d ≥ 1`: a value column is not zero
  have hd : 1 ≤ Fintype.card d := by
    obtain ⟨a, -⟩ := Function.ne_iff.mp (hv m le_rfl j)
    exact Fintype.card_pos_iff.2 ⟨a⟩
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rw [LinearMap.finrank_range_of_inj hinj] at h
  omega

variable {L : ℕ} {hid : Fin (L + 1) → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)]

/-- **Proposition A.35 for ReGLU blocks with at least `d` hidden units:** for
`d_in, d_out ≥ d ≥ 1` and at least `d` hidden units in every block, there is a nonempty open set
of weights on which the gate of hidden unit `j` of block `ℓ.succ` is closed at every input, and
at almost every point of this set `fd ≤ P − (L+2) d² − s − (3d − 2)`, with `s` twice the number
of hidden units. -/
theorem exists_isOpen_gateInactive_reglu_bound_of_le [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ) :
    ∃ U : Set (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, GateInactive θ ℓ.succ j) ∧
      ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.gated relu id hid) 0 θ
          + ((L + 2) * Fintype.card d ^ 2 + 2 * ∑ m, Fintype.card (hid m)
            + (3 * Fintype.card d - 2))
        ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- the open set on which the gate of the hidden unit is closed at every input
  obtain ⟨U, hU, hUne, hUin⟩ :=
    exists_isOpen_gateInactive_reglu (T := T) (dIn := dIn) (dOut := dOut) ℓ j (hhid ℓ.castSucc)
  refine ⟨U, hU, hUne, hUin, ?_⟩
  -- the reads have the `2 s_m > d` columns `hid m ⊕ hid m`, since `s_m ≥ d ≥ 1`
  have hcard : ∀ m, Fintype.card d < Fintype.card (hid m ⊕ hid m) := fun m => by
    rw [Fintype.card_sum]
    have h0 : 0 < Fintype.card d := Fintype.card_pos
    have h1 := hhid m
    omega
  have hr : ∀ m, Fintype.card d
      ≤ Fintype.card ((Arch.gated (T := T) (d := d) relu id hid).r m) := fun m => (hcard m).le
  -- at generic parameters `E`, `D`, the writes and the reads have rank `d`, no gate column, no
  -- value column and no write row vanishes, and the columns of the reads are in general position
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_rank_D_read μ hdOut hr, ae_value_ne_zero μ,
    ae_gate_ne_zero μ, ae_write_row_ne_zero μ, ae_read_cols_generalPosition μ hr]
    with θ h1 h2 h3 h4 h5 h6 hθU
  -- the gate is closed at every input at all parameters near `θ`
  have hθ : ∀ᶠ θ' in 𝓝 θ, GateInactive θ' ℓ.succ j :=
    Filter.mem_of_superset (hU.mem_nhds hθU) hUin
  -- the bound at one parameter, from both ends, for a network of `L + 1` blocks and `m = ℓ.succ`
  have := funDim_add_le_of_eventually_gateInactive_of_rank_E_D relu_homogeneous
    (fun z hz => max_eq_right hz) θ ℓ.succ j hθ h1.1 h2.1 (fun m _ => h1.2 m)
    (fun m _ i => h3 m i) (fun m _ i => h4 m i) (fun m _ i => h5 m i)
    (fun m _ S hS => h6 m S hS) (fun m _ => hcard m)
  simpa [add_assoc] using this

/-- **Proposition A.35, "so the equality condition fails there", for ReGLU blocks with at least
`d` hidden units:** for at least two blocks (`L ≥ 1`) and `d_in, d_out ≥ d ≥ 1`, it is not the
case that `fd = P − (L+2) d² − s` at almost every parameter, with `s` twice the number of hidden
units. -/
theorem not_ae_funDim_add_eq_reglu_skipless_of_le [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) :
    ¬ ∀ᵐ θ ∂μ, funDim (Arch.gated relu id hid) 0 θ
        + ((L + 2) * Fintype.card d ^ 2 + 2 * ∑ m, Fintype.card (hid m))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  intro hae
  -- block `ℓ.succ` with `ℓ = 0` and one of its hidden units (it has at least `d ≥ 1` of them)
  let ℓ : Fin L := ⟨0, hL⟩
  have hd : 0 < Fintype.card d := Fintype.card_pos
  have hpos : 0 < Fintype.card (hid ℓ.succ) := hd.trans_le (hhid ℓ.succ)
  obtain ⟨j⟩ : Nonempty (hid ℓ.succ) := Fintype.card_pos_iff.1 hpos
  obtain ⟨U, hU, hUne, -, hbound⟩ :=
    exists_isOpen_gateInactive_reglu_bound_of_le μ hdIn hdOut hhid ℓ j
  -- the equality and the bound with `3d − 2 ≥ 1` cannot both hold on `U`, so `U` is null
  have hnull : μ U = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hae, hbound] with θ heq hle hθU
    have := hle hθU
    omega
  -- but a nonempty open set has positive measure
  exact (hU.measure_pos μ hUne).ne' hnull

end Skips
