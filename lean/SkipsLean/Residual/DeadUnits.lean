import SkipsLean.Residual.Folding
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.Depth.InactiveUnit

/-!
# Dead units of a residual network lower the functional dimension

Paper (skips paper): Appendix A.8, Proposition A.33 (ii) and its proof.

"Proposition A.33 (Folding blocks can kill units and lower the functional dimension). Consider
residual networks of `L ≥ 2` ReLU blocks without normalization. (i) There is a nonempty open set of
weights on which block 1 folds and block 2 has a dead unit. (ii) If `ν` units are dead, then on
every batch on which no pre-activation vanishes, the Jacobian has rank at most
`P − d_model² − s − (2 d_model − 1) ν`."

"(ii) The columns of the Jacobian that belong to the read and the write of a dead unit vanish,
`2 d_model ν` columns in all. The other columns are those of the network with the dead units
deleted. That network has `P − 2 d_model ν` parameters and `s − ν` unit rescalings, since `s`
counts one rescaling per ReLU unit. Its function does not change under the change of basis of the
hidden states and these rescalings. At generic parameters they act with orbits of dimension
`d_model² + s − ν`, since `E` has rank `d_model`."

Stated here, for a residual network of MLP blocks without normalization whose activation is
positively homogeneous of degree `k` and vanishes on `z ≤ 0` (ReLU, ReLU²), and a finite set `J`
of units (pairs of a block and one of its hidden units): if every unit of `J` is dead at all
parameters near `θ` (`UnitInactiveRes`, `Residual/Folding.lean`), `E` has rank `d` and no read
column vanishes, then `fd(θ) ≤ P − d² − s − (2d − 1) ν` with `ν` the number of units of `J`. The
flat directions are the change of basis by one matrix at all hidden states (`d²`), the rescalings
of the units outside `J` (`s − ν`), and the directions that move the read column and the write row
of a unit of `J` (`2dν`).

Differences from the paper's sentence: the paper asks that the units are dead at `θ` and takes
batches on which no pre-activation vanishes; Lean's `funDim` takes the Jacobian at all inputs, and
the hypothesis is that the units are dead on a neighborhood of `θ`, as on the open set of part
(i). The twin without skip connections, for one unit, is `Depth/InactiveUnit.lean`
(Proposition E.1 of the dimension paper, Proposition A.35 of the skips paper).
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)]

/-- **Proposition A.33 (ii) of the skips paper, at one parameter:** let `σ` be positively
homogeneous of degree `k` and vanish on `z ≤ 0`, and let every unit of the finite set `J` be dead
at all parameters near `θ`, in the residual network. If `E` has rank `d` and no read column
vanishes, then `fd(θ) ≤ P − d² − s − (2d − 1) ν`, with `s` the number of hidden units of the
network and `ν` the number of units of `J`. -/
theorem funDim_add_le_residual_of_eventually_unitInactive {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (J : Finset (Σ m, hid m))
    (hθ : ∀ p ∈ J, ∀ᶠ θ' in 𝓝 θ, UnitInactiveRes θ' p.1 p.2)
    (hE : θ.E.rank = Fintype.card d) (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ) + (2 * Fintype.card d - 1) * J.card)
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

end Skips
