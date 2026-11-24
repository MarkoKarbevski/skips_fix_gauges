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
  sorry

end Skips
