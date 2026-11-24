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

/-- **Proof of Proposition E.1 for gated blocks, "The columns of the Jacobian that belong to the
weights of the inactive hidden unit vanish":** if the gate activation vanishes on `z ≤ 0` and the
gate of hidden unit `j` of block `m` is closed at every input at all parameters near `θ`, then
every direction that moves only the gate column, the value column and the write row of this hidden
unit is flat at `θ`. -/
theorem unitDirGated_mem_flat (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hθ : ∀ᶠ θ' in 𝓝 θ, GateInactive θ' m j) (δg δe δa : d → ℝ) :
    unitDirGated m j δg δe δa ∈ flat (Arch.gated σ id hid) 0 θ := by
  sorry

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
