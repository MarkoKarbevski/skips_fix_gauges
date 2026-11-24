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

/-- **Proof of Proposition E.1, "The columns of the Jacobian that belong to the weights of the
inactive hidden unit vanish":** if `σ` vanishes on `z ≤ 0` and hidden unit `j` of block `m` is
inactive at every input at all parameters near `θ`, then every direction that moves only the read
column and the write row of this hidden unit is flat at `θ`. -/
theorem unitDir_mem_flat (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (m : Fin L) (j : hid m)
    (hθ : ∀ᶠ θ' in 𝓝 θ, UnitInactive θ' m j) (δr δa : d → ℝ) :
    unitDir m j δr δa ∈ flat (Arch.mlp σ id hid) 0 θ := by
  sorry

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
