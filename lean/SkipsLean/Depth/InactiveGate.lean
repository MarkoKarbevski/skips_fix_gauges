import SkipsLean.Dimension.RescalingGate

/-!
# A hidden unit of a gated block whose gate is closed at every input: the bound

Paper (dimension paper): Appendix E, Proposition E.1, the part "The rank" of its proof, for ReGLU
blocks: "The columns of the Jacobian that belong to the weights of the inactive hidden unit vanish:
`2 d_model` columns, or `3 d_model` for ReGLU. The other columns form the Jacobian of the network
without this hidden unit, which computes the same function. That network has `P − 2 d_model`
parameters, or `P − 3 d_model`, its blocks have at least `d_model` hidden units, and its symmetries
have the dimension `(L+1) d_model² + s − 1`, or `(L+1) d_model² + s − 2` for ReGLU, since the
inactive hidden unit had one rescaling, or two."

Stated here, for a skipless network of gated blocks without normalization whose gate activation is
positively homogeneous of degree `k` and vanishes on `z ≤ 0` (the ReLU gate of ReGLU), and for a
hidden unit `j` of any block `m`:

* `GateInactive θ m j`: the gate of the hidden unit reads a number `≤ 0` at every token of every
  input.
* `unitDirGated m j δg δe δa`: the direction that moves only the gate column, the value column and
  the write row of the hidden unit. If the gate is closed at every input at all parameters near
  `θ`, these `3d` directions are flat at `θ` (`unitDirGated_mem_flat`).
* The bound (`funDim_add_le_of_eventually_gateInactive`): if moreover `E` and the writes have rank
  `d`, the write of block `m` without the row of the unit still has rank `d`, and no gate column
  and no value column of a read vanishes, then `fd(θ) ≤ P − (L+1) d² − s − (3d − 2)`, where `s` is
  twice the number of hidden units (each has a rescaling of its value and one of its gate).

The twin for ReLU and ReLU² blocks is `Depth/InactiveUnit.lean`. As there, the Lean Jacobian is
taken at all inputs. The open set of weights for ReGLU blocks is in `Depth/InactiveGateOpen.lean`,
the statement of the proposition in `Depth/InactiveGateReGLU.lean`.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)]

/-- The gate of hidden unit `j` of block `m` of a skipless network of gated blocks without
normalization is closed at every input at `θ`: it reads a number `≤ 0` at every token of every
input. -/
def GateInactive (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L)
    (j : hid m) : Prop :=
  ∀ (x : Matrix T dIn ℝ) (t : T),
    (hidden (Arch.gated σ id hid) 0 θ x m.castSucc * θ.read m) t (Sum.inl j) ≤ 0

/-- The direction that moves only hidden unit `j` of block `m` of a gated network: its gate column
by `δg`, its value column by `δe` and its write row by `δa`. -/
def unitDirGated {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m) (δg δe δa : d → ℝ) :
    Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  E := 0
  read := Function.update (fun _ => 0) m
    (Matrix.of fun (a : d) (i : hid m ⊕ hid m) =>
      Sum.elim (fun i' => if i' = j then δg a else 0) (fun i' => if i' = j then δe a else 0) i)
  write := Function.update (fun _ => 0) m
    (Matrix.of fun (i : hid m) (a : d) => if i = j then δa a else 0)
  D := 0

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read of `unitDirGated` vanishes at the blocks other than `m`. -/
private theorem unitDirGated_read_ne_ig {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L)
    (j : hid m) (δg δe δa : d → ℝ) {ℓ : Fin L} (h : ℓ ≠ m) :
    (unitDirGated (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δg δe δa).read ℓ = 0 := by
  simp only [unitDirGated]
  exact Function.update_of_ne h _ _

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write of `unitDirGated` vanishes at the blocks other than `m`. -/
private theorem unitDirGated_write_ne_ig {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L)
    (j : hid m) (δg δe δa : d → ℝ) {ℓ : Fin L} (h : ℓ ≠ m) :
    (unitDirGated (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δg δe δa).write ℓ = 0 := by
  simp only [unitDirGated]
  exact Function.update_of_ne h _ _

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the gate columns of the read of `unitDirGated` at block `m`. -/
private theorem unitDirGated_gate_ig {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L)
    (j : hid m) (δg δe δa : d → ℝ) (a : d) (i : hid m) :
    (unitDirGated (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δg δe δa).read m a
      (Sum.inl i) = if i = j then δg a else 0 := by
  simp only [unitDirGated, Function.update_self, Matrix.of_apply, Sum.elim_inl]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the value columns of the read of `unitDirGated` at block `m`. -/
private theorem unitDirGated_value_ig {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L)
    (j : hid m) (δg δe δa : d → ℝ) (a : d) (i : hid m) :
    (unitDirGated (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δg δe δa).read m a
      (Sum.inr i) = if i = j then δe a else 0 := by
  simp only [unitDirGated, Function.update_self, Matrix.of_apply, Sum.elim_inr]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write rows of `unitDirGated` at block `m`. -/
private theorem unitDirGated_write_ig {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L)
    (j : hid m) (δg δe δa : d → ℝ) (i : hid m) (a : d) :
    (unitDirGated (σ := σ) (χ := χ) (dIn := dIn) (dOut := dOut) m j δg δe δa).write m i a
      = if i = j then δa a else 0 := by
  simp only [unitDirGated, Function.update_self, Matrix.of_apply]

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper (the claim of the proof): if `θ'` and `θ` have the same `E`, the same reads and writes
except at the gate column, the value column and the write row of hidden unit `j` of block `m`, and
the gate of this unit is closed at every input at both, then they have the same hidden states at
every input. -/
private theorem hidden_eq_of_gateInactive_ig (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ θ' : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hE : θ'.E = θ.E) (hr : ∀ ℓ, ℓ ≠ m → θ'.read ℓ = θ.read ℓ)
    (hg : ∀ a i, i ≠ j → θ'.read m a (Sum.inl i) = θ.read m a (Sum.inl i))
    (hv : ∀ a i, i ≠ j → θ'.read m a (Sum.inr i) = θ.read m a (Sum.inr i))
    (hw : ∀ ℓ, ℓ ≠ m → θ'.write ℓ = θ.write ℓ)
    (hwm : ∀ i a, i ≠ j → θ'.write m i a = θ.write m i a)
    (h1 : GateInactive θ m j) (h2 : GateInactive θ' m j) (x : Matrix T dIn ℝ)
    (ℓ : Fin (L + 1)) :
    hidden (Arch.gated σ id hid) 0 θ' x ℓ = hidden (Arch.gated σ id hid) 0 θ x ℓ := by
  induction ℓ using Fin.induction with
  | zero => rw [hidden_zero, hidden_zero, hE]
  | succ ℓ ih =>
    -- the stream term is `0`; compare the outputs of block `ℓ`
    rw [hidden_succ, hidden_succ, ih]
    congr 1
    by_cases hℓ : ℓ = m
    · -- block `m`: the hidden units `i ≠ j` are the same, and unit `j` gives `0` at both
      subst hℓ
      have h2' := h2 x
      rw [ih] at h2'
      set h := hidden (Arch.gated σ id hid) 0 θ x ℓ.castSucc
      ext t a
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show σ ((h * θ'.read ℓ) t (Sum.inl i)) * (h * θ'.read ℓ) t (Sum.inr i) * θ'.write ℓ i a =
        σ ((h * θ.read ℓ) t (Sum.inl i)) * (h * θ.read ℓ) t (Sum.inr i) * θ.write ℓ i a
      by_cases hij : i = j
      · -- the gate of unit `j` reads a number `≤ 0` at both, so `σ` vanishes there
        subst hij
        rw [hσ0 _ (h2' t), hσ0 _ (h1 x t)]
        simp only [zero_mul]
      · -- the gate and value columns and the write row of unit `i ≠ j` are the same
        have hz : (h * θ'.read ℓ) t (Sum.inl i) = (h * θ.read ℓ) t (Sum.inl i) := by
          simp only [Matrix.mul_apply, hg _ _ hij]
        have hu : (h * θ'.read ℓ) t (Sum.inr i) = (h * θ.read ℓ) t (Sum.inr i) := by
          simp only [Matrix.mul_apply, hv _ _ hij]
        rw [hz, hu, hwm _ _ hij]
    · -- another block: the same read and write
      rw [hr ℓ hℓ, hw ℓ hℓ]

/-- Helper: the line `τ ↦ a + τ b` has the velocity `b`. -/
private theorem hasDerivAt_line_ig {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) : HasDerivAt (fun τ : ℝ => a + τ • b) b 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a
  rw [one_smul] at h
  exact h

omit [DecidableEq d] in
/-- **Proof of Proposition E.1 for gated blocks, "The columns of the Jacobian that belong to the
weights of the inactive hidden unit vanish":** if the gate activation vanishes on `z ≤ 0` and the
gate of hidden unit `j` of block `m` is closed at every input at all parameters near `θ`, then
every direction that moves only the gate column, the value column and the write row of this hidden
unit is flat at `θ`. -/
theorem unitDirGated_mem_flat (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hθ : ∀ᶠ θ' in 𝓝 θ, GateInactive θ' m j) (δg δe δa : d → ℝ) :
    unitDirGated m j δg δe δa ∈ flat (Arch.gated σ id hid) 0 θ := by
  set η := unitDirGated (σ := σ) (dIn := dIn) (dOut := dOut) m j δg δe δa with hη
  -- the curve `τ ↦ θ + τ η` passes through `θ` with velocity `η`
  have hγ : HasDerivAt (fun τ : ℝ => θ + τ • η) η 0 := hasDerivAt_line_ig θ η
  have hγ0 : (fun τ : ℝ => θ + τ • η) 0 = θ := by simp
  -- near `τ = 0` the gate of the unit is closed at every input along the curve
  have hc : Tendsto (fun τ : ℝ => θ + τ • η) (𝓝 0) (𝓝 θ) := by
    have h := hγ.continuousAt.tendsto
    rwa [zero_smul, add_zero] at h
  refine mem_flat_of_hasDerivAt' θ (fun τ : ℝ => θ + τ • η) η hγ hγ0
    ((hc.eventually hθ).mono fun τ hτ x => ?_)
  -- the curve moves only the gate column, the value column and the write row of the unit, so the
  -- hidden states, and the outputs, are those of `θ`
  have hh := hidden_eq_of_gateInactive_ig hσ0 θ (θ + τ • η) m j
    (by rw [Params.add_E, Params.smul_E]; simp [hη, unitDirGated])
    (fun ℓ hℓ => by
      rw [Params.add_read, Params.smul_read, hη, unitDirGated_read_ne_ig m j δg δe δa hℓ,
        smul_zero, add_zero])
    (fun a i hij => by
      rw [Params.add_read, Params.smul_read, Matrix.add_apply, Matrix.smul_apply, hη,
        unitDirGated_gate_ig, ite_eq_right_iff.2 fun h => absurd h hij, smul_zero, add_zero])
    (fun a i hij => by
      rw [Params.add_read, Params.smul_read, Matrix.add_apply, Matrix.smul_apply, hη,
        unitDirGated_value_ig, ite_eq_right_iff.2 fun h => absurd h hij, smul_zero, add_zero])
    (fun ℓ hℓ => by
      rw [Params.add_write, Params.smul_write, hη, unitDirGated_write_ne_ig m j δg δe δa hℓ,
        smul_zero, add_zero])
    (fun i a hij => by
      rw [Params.add_write, Params.smul_write, Matrix.add_apply, Matrix.smul_apply, hη,
        unitDirGated_write_ig, ite_eq_right_iff.2 fun h => absurd h hij, smul_zero, add_zero])
    hθ.self_of_nhds hτ x (Fin.last L)
  rw [eval, eval, hh, Params.add_D, Params.smul_D]
  simp [hη, unitDirGated]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `cancel_left_of_rank_gate` of `Dimension/RescalingGate.lean`): a matrix
`M` of rank equal to its number of columns cancels on the left, `M X = M Y → X = Y`. -/
private theorem cancel_left_of_rank_ig {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

/-- Helper: `α ↦ rescaleDir θ α` is linear (the private `rescaleDirLinValue` of
`Dimension/RescalingGate.lean`). -/
private noncomputable def rescaleDirLin_ig
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

/-- Helper: `β ↦ rescaleDirGate k θ β` is linear (the private `rescaleDirGateLin` of
`Dimension/RescalingGate.lean`). -/
private noncomputable def rescaleDirGateLin_ig (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) :
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

/-- Helper: `(δg, δe, δa) ↦ unitDirGated m j δg δe δa` is linear. -/
private noncomputable def unitDirGatedLin_ig (m : Fin L) (j : hid m) :
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
          rw [Params.add_read, Matrix.add_apply, unitDirGated_gate_ig, unitDirGated_gate_ig,
            unitDirGated_gate_ig]
          split_ifs <;> simp
        | inr i =>
          rw [Params.add_read, Matrix.add_apply, unitDirGated_value_ig, unitDirGated_value_ig,
            unitDirGated_value_ig]
          split_ifs <;> simp
      · rw [Params.add_read, unitDirGated_read_ne_ig _ _ _ _ _ hℓ,
          unitDirGated_read_ne_ig _ _ _ _ _ hℓ, unitDirGated_read_ne_ig _ _ _ _ _ hℓ, add_zero]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext i a
        rw [Params.add_write, Matrix.add_apply, unitDirGated_write_ig, unitDirGated_write_ig,
          unitDirGated_write_ig]
        split_ifs <;> simp
      · rw [Params.add_write, unitDirGated_write_ne_ig _ _ _ _ _ hℓ,
          unitDirGated_write_ne_ig _ _ _ _ _ hℓ, unitDirGated_write_ne_ig _ _ _ _ _ hℓ, add_zero]
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
          rw [Params.smul_read, Matrix.smul_apply, unitDirGated_gate_ig, unitDirGated_gate_ig]
          split_ifs <;> simp
        | inr i =>
          rw [Params.smul_read, Matrix.smul_apply, unitDirGated_value_ig, unitDirGated_value_ig]
          split_ifs <;> simp
      · rw [Params.smul_read, unitDirGated_read_ne_ig _ _ _ _ _ hℓ,
          unitDirGated_read_ne_ig _ _ _ _ _ hℓ, smul_zero]
    · intro ℓ
      by_cases hℓ : ℓ = m
      · subst hℓ
        ext i a
        rw [Params.smul_write, Matrix.smul_apply, unitDirGated_write_ig, unitDirGated_write_ig]
        split_ifs <;> simp
      · rw [Params.smul_write, unitDirGated_write_ne_ig _ _ _ _ _ hℓ,
          unitDirGated_write_ne_ig _ _ _ _ _ hℓ, smul_zero]
    · simp [unitDirGated]

/-- Helper: the value `α m j` of a family of numbers on the hidden units, as a linear
functional. -/
private noncomputable def evalAt_ig (m : Fin L) (j : hid m) : (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.proj j).comp (LinearMap.proj (R := ℝ) (φ := fun ℓ => hid ℓ → ℝ) m)

omit [∀ ℓ, DecidableEq (hid ℓ)] in
/-- Helper: the families that vanish at `(m, j)` form a space of dimension `∑ d_hidden - 1`
(rank–nullity for the functional `α ↦ α m j`, which is onto). -/
private theorem finrank_ker_evalAt_ig (m : Fin L) (j : hid m) :
    Module.finrank ℝ (LinearMap.ker (evalAt_ig m j)) + 1 = ∑ ℓ, Fintype.card (hid ℓ) := by
  have h := LinearMap.finrank_range_add_finrank_ker (evalAt_ig m j)
  have hr : LinearMap.range (evalAt_ig m j) = ⊤ :=
    LinearMap.range_eq_top.2 fun c => ⟨fun _ _ => c, rfl⟩
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_pi_fintype] at h
  simp only [Module.finrank_fintype_fun_eq_card] at h
  omega

/-- **Proposition E.1, the bound, at one parameter (ReGLU blocks):** let the gate activation be
positively homogeneous of degree `k` and vanish on `z ≤ 0`, and let the gate of hidden unit `j` of
block `m` be closed at every input at all parameters near `θ`. If `E` and the writes have rank
`d`, the write of block `m` without the row of the unit has rank `d`, and no value column and no
gate column of a read vanishes, then `fd(θ) ≤ P − (L+1) d² − s − (3d − 2)`, with `s` twice the
number of hidden units of the network. -/
theorem funDim_add_le_of_eventually_gateInactive {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hθ : ∀ᶠ θ' in 𝓝 θ, GateInactive θ' m j)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hwj : ((θ.write m).submatrix (fun i : {i : hid m // i ≠ j} => (i : hid m)) id).rank
      = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.gated σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ)
          + (3 * Fintype.card d - 2))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the families of numbers on the hidden units that vanish at `(m, j)`
  set K := LinearMap.ker (evalAt_ig m j) with hK
  -- the linear map `(X, α, β, δ) ↦ cobDir θ X + rescaleDir θ α + rescaleDirGate k θ β
  -- + unitDirGated m j δ`, with `α m j = β m j = 0`
  let Φ := (cobDirLin θ).coprod (((rescaleDirLin_ig θ).comp K.subtype).coprod
    (((rescaleDirGateLin_ig k θ).comp K.subtype).coprod (unitDirGatedLin_ig m j)))
  -- its directions are flat, since the four summands are
  have hV : LinearMap.range Φ ≤ flat (Arch.gated σ id hid) 0 θ := by
    rintro _ ⟨p, rfl⟩
    exact Submodule.add_mem _ (cobDir_mem_flat_skipless' θ rfl p.1)
      (Submodule.add_mem _ (rescaleDir_mem_flat' θ 0 p.2.1.1)
        (Submodule.add_mem _ (rescaleDirGate_mem_flat hσ θ 0 p.2.2.1.1)
          (unitDirGated_mem_flat hσ0 θ m j hθ p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)))
  -- it is injective
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 ?_
    rintro ⟨X, ⟨α, hα⟩, ⟨β, hβ⟩, δg, δe, δa⟩ hp
    have hα0 : α m j = 0 := LinearMap.mem_ker.1 hα
    have hβ0 : β m j = 0 := LinearMap.mem_ker.1 hβ
    set U := unitDirGated (σ := σ) (dIn := dIn) (dOut := dOut) m j δg δe δa with hU
    have h : cobDir θ X + (rescaleDir θ α + (rescaleDirGate k θ β + U)) = 0 := hp
    -- the entries of the four summands: `E`, the gate and value columns, the write rows
    have hE0 : θ.E * X 0 = θ.E * (0 : Matrix d d ℝ) := by
      have h1 := congrArg Params.E h
      change θ.E * X 0 + (0 + (0 + 0)) = 0 at h1
      rw [Matrix.mul_zero]
      simpa only [add_zero] using h1
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
    -- `E` has rank `d`, so `X_0 = 0`
    have hX0 : X 0 = 0 := cancel_left_of_rank_ig θ.E hE hE0
    -- block `ℓ`: if `X_{ℓ-1} = 0`, then `α_ℓ = 0`, `β_ℓ = 0` and `X_ℓ = 0`
    have key : ∀ ℓ : Fin L, X ℓ.castSucc = 0 → α ℓ = 0 ∧ β ℓ = 0 ∧ X ℓ.succ = 0 := by
      intro ℓ hℓ
      -- the gate column of unit `i`: `β_i g_i + δ = 0`, with `δ = 0` unless `(ℓ, i) = (m, j)`
      have hβℓ : β ℓ = 0 := by
        funext i
        obtain ⟨a, ha⟩ := Function.ne_iff.mp (hg ℓ i)
        have h1 := hgate ℓ a i
        rw [hℓ, Matrix.zero_mul, Matrix.zero_apply, neg_zero, zero_add] at h1
        by_cases hℓm : ℓ = m
        · subst hℓm
          by_cases hij : i = j
          · subst hij
            exact hβ0
          · rw [hU, unitDirGated_gate_ig, ite_eq_right_iff.2 fun h => absurd h hij,
              add_zero] at h1
            exact (mul_eq_zero.1 h1).resolve_right ha
        · rw [hU, unitDirGated_read_ne_ig _ _ _ _ _ hℓm, Matrix.zero_apply, add_zero] at h1
          exact (mul_eq_zero.1 h1).resolve_right ha
      -- the value column of unit `i`: `-α_i e_i + δ = 0`
      have hαℓ : α ℓ = 0 := by
        funext i
        obtain ⟨a, ha⟩ := Function.ne_iff.mp (hv ℓ i)
        have h1 := hval ℓ a i
        rw [hℓ, Matrix.zero_mul, Matrix.zero_apply, neg_zero, zero_sub] at h1
        by_cases hℓm : ℓ = m
        · subst hℓm
          by_cases hij : i = j
          · subst hij
            exact hα0
          · rw [hU, unitDirGated_value_ig, ite_eq_right_iff.2 fun h => absurd h hij,
              add_zero, neg_eq_zero] at h1
            exact (mul_eq_zero.1 h1).resolve_right ha
        · rw [hU, unitDirGated_read_ne_ig _ _ _ _ _ hℓm, Matrix.zero_apply, add_zero,
            neg_eq_zero] at h1
          exact (mul_eq_zero.1 h1).resolve_right ha
      refine ⟨hαℓ, hβℓ, ?_⟩
      -- the write: `W X_ℓ + δ = 0`, with `δ` only on row `j` of block `m`
      have hW : ∀ i a, (θ.write ℓ * X ℓ.succ) i a + U.write ℓ i a = 0 := by
        intro i a
        have h1 := hwr ℓ i a
        simp only [hαℓ, hβℓ, Pi.zero_apply, zero_mul, mul_zero, add_zero, sub_zero] at h1
        exact h1
      by_cases hℓm : ℓ = m
      · -- block `m`: the rows `i ≠ j` of `W X_m` vanish, and `W` without row `j` has rank `d`
        subst hℓm
        refine cancel_left_of_rank_ig _ hwj (Y := 0) ?_
        ext i a
        have h1 := hW i a
        rw [hU, unitDirGated_write_ig, ite_eq_right_iff.2 fun h => absurd h i.2, add_zero]
          at h1
        rw [Matrix.mul_zero, Matrix.zero_apply]
        exact h1
      · -- another block: `W X_ℓ = 0`, and `W` has rank `d`
        refine cancel_left_of_rank_ig _ (hw ℓ) (Y := 0) ?_
        ext i a
        have h1 := hW i a
        rw [hU, unitDirGated_write_ne_ig _ _ _ _ _ hℓm, Matrix.zero_apply, add_zero] at h1
        rw [Matrix.mul_zero, Matrix.zero_apply]
        exact h1
    -- by induction along the network, `X = 0`; then `α = 0` and `β = 0`
    have hX : ∀ ℓ : Fin (L + 1), X ℓ = 0 := by
      intro ℓ
      induction ℓ using Fin.induction with
      | zero => exact hX0
      | succ ℓ ih => exact (key ℓ ih).2.2
    have hα' : α = 0 := funext fun ℓ => (key ℓ (hX ℓ.castSucc)).1
    have hβ' : β = 0 := funext fun ℓ => (key ℓ (hX ℓ.castSucc)).2.1
    -- the gate column, the value column and the write row of unit `j` give `δ = 0`
    have hδg : δg = 0 := by
      funext a
      have h1 := hgate m a j
      rw [hX] at h1
      simp only [hβ', Matrix.zero_mul, Matrix.zero_apply, neg_zero, Pi.zero_apply, zero_mul,
        zero_add, hU, unitDirGated_gate_ig, ↓reduceIte] at h1
      exact h1
    have hδe : δe = 0 := by
      funext a
      have h1 := hval m a j
      rw [hX] at h1
      simp only [hα', Matrix.zero_mul, Matrix.zero_apply, neg_zero, Pi.zero_apply, zero_mul,
        sub_zero, zero_add, hU, unitDirGated_value_ig, ↓reduceIte] at h1
      exact h1
    have hδa : δa = 0 := by
      funext a
      have h1 := hwr m j a
      rw [hX] at h1
      simp only [hα', hβ', Matrix.mul_zero, Matrix.zero_apply, Pi.zero_apply, zero_mul,
        mul_zero, add_zero, sub_zero, zero_add, hU, unitDirGated_write_ig, ↓reduceIte] at h1
      exact h1
    subst hδg hδe hδa
    have hα'' : (⟨α, hα⟩ : K) = 0 := Subtype.ext hα'
    have hβ'' : (⟨β, hβ⟩ : K) = 0 := Subtype.ext hβ'
    rw [hα'', hβ'', funext hX]
    rfl
  -- the domain has dimension `(L + 1) d² + 2 (∑ d_hidden - 1) + 3 d`
  have hdim : Module.finrank ℝ
        ((Fin (L + 1) → Matrix d d ℝ) × K × K × ((d → ℝ) × (d → ℝ) × (d → ℝ))) + 2
      = (L + 1) * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ) + 3 * Fintype.card d := by
    have hk := finrank_ker_evalAt_ig m j
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
      Module.finrank_prod, finrank_cobDomain]
    simp only [Module.finrank_fintype_fun_eq_card]
    rw [← hK] at hk
    omega
  -- `d ≥ 1`: a value column is not zero
  have hd : 1 ≤ Fintype.card d := by
    obtain ⟨a, -⟩ := Function.ne_iff.mp (hv m j)
    exact Fintype.card_pos_iff.2 ⟨a⟩
  have h := funDim_add_finrank_le_of_le_flat' θ _ hV
  rw [LinearMap.finrank_range_of_inj hinj] at h
  omega

end Skips
