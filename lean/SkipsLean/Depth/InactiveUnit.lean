import SkipsLean.Dimension.RescalingMlp

/-!
# A hidden unit that is inactive at every input: the bound on the functional dimension

Paper (dimension paper): Appendix E, "Inactive hidden units: where the count fails",
Proposition E.1, the part "The rank" of its proof, for ReLU and ReLU² blocks.

"Proposition E.1 (Inactive hidden units). Consider networks of `L ≥ 2` ReLU, ReLU² or ReGLU blocks
without normalization, each with more than `d_model` hidden units. There is a nonempty open set of
weights on which a hidden unit of block 2 is inactive at every input. At almost every point of this
set the functional dimension is at most `P − (L+1) d_model² − s − (2 d_model − 1)`, and at most
`P − (L+1) d_model² − s − (3 d_model − 2)` for ReGLU blocks. So these networks do not satisfy the
equality condition."

"The rank. On this open set of weights, take a batch of inputs at which no hidden unit sits at its
kink. The columns of the Jacobian that belong to the weights of the inactive hidden unit vanish:
`2 d_model` columns, or `3 d_model` for ReGLU. The other columns form the Jacobian of the network
without this hidden unit, which computes the same function. That network has `P − 2 d_model`
parameters […], its blocks have at least `d_model` hidden units, and its symmetries have the
dimension `(L+1) d_model² + s − 1` […], since the inactive hidden unit had one rescaling […]. By
Lemma B.1 they move generic parameters in as many independent directions, which lie in the kernel
of the Jacobian."

Stated here, for a skipless network of MLP blocks without normalization whose activation is
positively homogeneous of degree `k` and vanishes on `z ≤ 0` (ReLU, ReLU²), and for a hidden unit
`j` of any block `m`:

* `UnitInactive θ m j`: the hidden unit reads a number `≤ 0` at every token of every input.
* `unitDir m j δr δa`: the direction that moves only the read column and the write row of the
  hidden unit. If the unit is inactive at every input at all parameters near `θ`, these `2d`
  directions are flat at `θ` (`unitDir_mem_flat`).
* The bound (`funDim_add_le_of_eventually_unitInactive`): if moreover `E` and the writes have rank
  `d`, the write of block `m` without the row of the unit still has rank `d`, and no read column
  vanishes, then `fd(θ) ≤ P − (L+1) d² − s − (2d − 1)`, with `s` the number of hidden units. The
  flat directions are the changes of basis, the rescalings of the other hidden units, and the `2d`
  directions of the inactive unit.

In Lean the Jacobian on a batch is taken at all inputs, also where a hidden unit sits at its kink
(see the note on ReLU in `STATEMENTS.md`), so the bound is on a number that is at least the paper's
functional dimension. The open set of weights and the statement of the proposition are in
`Depth/InactiveUnitRelu.lean`; ReGLU blocks in `Depth/InactiveGate.lean`.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)]

/-- Hidden unit `j` of block `m` of a skipless network of MLP blocks without normalization is
inactive at every input at `θ`: it reads a number `≤ 0` at every token of every input. -/
def UnitInactive (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L)
    (j : hid m) : Prop :=
  ∀ (x : Matrix T dIn ℝ) (t : T),
    (hidden (Arch.mlp σ id hid) 0 θ x m.castSucc * θ.read m) t j ≤ 0

/-- The direction that moves only hidden unit `j` of block `m`: its read column by `δr` and its
write row by `δa`. -/
def unitDir {χ : Matrix T d ℝ → Matrix T d ℝ} (m : Fin L) (j : hid m) (δr δa : d → ℝ) :
    Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut where
  E := 0
  read := Function.update (fun _ => 0) m
    (Matrix.of fun (a : d) (i : hid m) => if i = j then δr a else 0)
  write := Function.update (fun _ => 0) m
    (Matrix.of fun (i : hid m) (a : d) => if i = j then δa a else 0)
  D := 0

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- Helper: two parameters that differ only in the read column and the write row of hidden unit
`j` of block `m`, at both of which this unit is inactive at every input, have the same hidden
states at every input. -/
private theorem hidden_eq_of_unitInactive_iu (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (h1 : UnitInactive θ m j) (h2 : UnitInactive θ' m j) (hE : θ'.E = θ.E)
    (hr : ∀ ℓ, ℓ ≠ m → θ'.read ℓ = θ.read ℓ) (hw : ∀ ℓ, ℓ ≠ m → θ'.write ℓ = θ.write ℓ)
    (hrm : ∀ a i, i ≠ j → θ'.read m a i = θ.read m a i)
    (hwm : ∀ i a, i ≠ j → θ'.write m i a = θ.write m i a)
    (x : Matrix T dIn ℝ) (ℓ : Fin (L + 1)) :
    hidden (Arch.mlp σ id hid) 0 θ' x ℓ = hidden (Arch.mlp σ id hid) 0 θ x ℓ := by
  induction ℓ using Fin.induction with
  | zero => rw [hidden_zero, hidden_zero, hE]
  | succ ℓ ih =>
    -- the stream term is the same; compare the outputs of block `ℓ`
    rw [hidden_succ, hidden_succ, ih]
    congr 1
    show (hidden (Arch.mlp σ id hid) 0 θ x ℓ.castSucc * θ'.read ℓ).map σ * θ'.write ℓ =
      (hidden (Arch.mlp σ id hid) 0 θ x ℓ.castSucc * θ.read ℓ).map σ * θ.write ℓ
    by_cases hℓ : ℓ = m
    · -- block `m`: the terms of the hidden units `i ≠ j` agree, the term of `j` is `0`
      subst hℓ
      ext t a
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.map_apply, Matrix.map_apply]
      by_cases hi : i = j
      · subst hi
        have e1 := h1 x t
        have e2 := h2 x t
        rw [ih] at e2
        rw [hσ0 _ e1, hσ0 _ e2, zero_mul, zero_mul]
      · have hu : (hidden (Arch.mlp σ id hid) 0 θ x ℓ.castSucc * θ'.read ℓ) t i =
            (hidden (Arch.mlp σ id hid) 0 θ x ℓ.castSucc * θ.read ℓ) t i := by
          rw [Matrix.mul_apply, Matrix.mul_apply]
          exact Finset.sum_congr rfl fun b _ => by rw [hrm b i hi]
        rw [hu, hwm i a hi]
    · -- another block: nothing changed
      rw [hr ℓ hℓ, hw ℓ hℓ]

omit [Fintype T] [DecidableEq d] in
/-- Helper: the line `τ ↦ θ + τ η` passes through `θ` at `τ = 0` with velocity `η`. -/
private theorem hasDerivAt_line_iu {A : Arch T d L} (θ η : Params A dIn dOut) :
    HasDerivAt (fun τ : ℝ => θ + τ • η) η 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const η).const_add θ
  rw [one_smul] at h
  exact h

/-- **Proof of Proposition E.1, "The columns of the Jacobian that belong to the weights of the
inactive hidden unit vanish":** if `σ` vanishes on `z ≤ 0` and hidden unit `j` of block `m` is
inactive at every input at all parameters near `θ`, then every direction that moves only the read
column and the write row of this hidden unit is flat at `θ`. -/
theorem unitDir_mem_flat (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hθ : ∀ᶠ θ' in 𝓝 θ, UnitInactive θ' m j) (δr δa : d → ℝ) :
    unitDir m j δr δa ∈ flat (Arch.mlp σ id hid) 0 θ := by
  set η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut := unitDir m j δr δa
  -- the line `τ ↦ θ + τ η` passes through `θ` with velocity `η`
  have hline := hasDerivAt_line_iu θ η
  have h0 : θ + (0 : ℝ) • η = θ := by rw [zero_smul, add_zero]
  -- near `τ = 0` the hidden unit is inactive at every input along the line
  have hnear : ∀ᶠ τ in 𝓝 (0 : ℝ), UnitInactive (θ + τ • η) m j := by
    have ht := hline.continuousAt.tendsto
    rw [h0] at ht
    exact ht.eventually hθ
  refine mem_flat_of_hasDerivAt' θ (fun τ => θ + τ • η) η hline h0
    (hnear.mono fun τ hτ x => ?_)
  -- the line moves only the read column and the write row of the unit, so the hidden states, and
  -- then the outputs, are those of `θ`
  have hh := hidden_eq_of_unitInactive_iu hσ0 θ (θ + τ • η) m j hθ.self_of_nhds hτ
    (by simp [η, unitDir])
    (fun ℓ hℓ => by
      simp [η, unitDir, Function.update_of_ne hℓ])
    (fun ℓ hℓ => by
      simp [η, unitDir, Function.update_of_ne hℓ])
    (fun a i hi => by
      simp [η, unitDir, hi])
    (fun i a hi => by
      simp [η, unitDir, hi])
    x (Fin.last L)
  show (Arch.mlp σ id hid).χ (hidden _ 0 (θ + τ • η) x (Fin.last L)) * (θ + τ • η).D =
    (Arch.mlp σ id hid).χ (hidden _ 0 θ x (Fin.last L)) * θ.D
  rw [hh]
  simp [η, unitDir]

/-- **Proposition E.1, the bound, at one parameter (ReLU and ReLU² blocks):** let `σ` be positively
homogeneous of degree `k` and vanish on `z ≤ 0`, and let hidden unit `j` of block `m` be inactive
at every input at all parameters near `θ`. If `E` and the writes have rank `d`, the write of block
`m` without the row of the unit has rank `d`, and no read column vanishes, then
`fd(θ) ≤ P − (L+1) d² − s − (2d − 1)`, with `s` the number of hidden units of the network. -/
theorem funDim_add_le_of_eventually_unitInactive {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hθ : ∀ᶠ θ' in 𝓝 θ, UnitInactive θ' m j)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hwj : ((θ.write m).submatrix (fun i : {i : hid m // i ≠ j} => (i : hid m)) id).rank
      = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) + (2 * Fintype.card d - 1))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

end Skips
