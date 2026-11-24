import SkipsLean.Depth.GeluPathBlock
import SkipsLean.Depth.ComplexSuffixStep

/-!
# A parameter that satisfies all conditions of the case (0), for GELU blocks

Paper (dimension paper): Appendix D.6, "Parameters that satisfy all conditions, in the case (0)":
"We choose the blocks from the last to the first. Let `D` and the blocks `ℓ + 1, …, L` be chosen,
regular and with […] (P1) and (P2) for GELU. This fixes `κ_ℓ` (Lemma D.14). We choose
`(W, V) = (W_read^ℓ, W_write^ℓ)`. […] So there are parameters `θ*` that are regular and whose
blocks all satisfy […] (P1) and (P2) for GELU."

Stated here: for `d_in, d_out ≥ d ≥ 2` and at least `d` hidden units in every block there is a
parameter `θ*` that is regular in the sense of the case (0) (`RegularZero`) and whose every block
`k` satisfies (P1), and (P2) for a `κ ∈ (0, 1]` such that the network after the block, `𝓑_{>k+1}`
with GELU at complex arguments (`geluC`), is holomorphic on `C_κ` (the `κ_ℓ` of Lemma D.14). These
are the hypotheses of Lemma D.19 (`claimZero_castSucc_gelu`, `Depth/StepZeroGelu.lean`) at every
block.

One block is `exists_geluPathBlock` (`Depth/GeluPathBlock.lean`); the cone of a block depends only
on the later blocks (`Depth/ComplexSuffixStep.lean`). `Depth/RegularZeroTanh.lean` is the same
statement for `tanh`. Numbering: the block `k : Fin L` is the paper's block `k + 1`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **"So there are parameters `θ*` that are regular and whose blocks all satisfy […] (P1) and (P2)
for GELU":** for `d_in, d_out ≥ d ≥ 2` and at least `d` hidden units in every block, there is a
regular `θ*` whose every block `k` satisfies (P1), and (P2) for a `κ ∈ (0, 1]` such that
`𝓑_{>k+1}` is holomorphic on `C_κ`. -/
theorem exists_regularZero_gelu_path [Nonempty T] (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut,
      RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ ∧
      ∀ k : Fin L, CondP1 θ k ∧
        ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ HolomorphicOnCone geluC θ k.succ κ ∧ CondP2 θ k κ := by
  sorry

end Skips
