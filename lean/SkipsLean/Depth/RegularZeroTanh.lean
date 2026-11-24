import SkipsLean.Depth.TanhPathBlock
import SkipsLean.Depth.ComplexSuffixStep
import SkipsLean.Depth.StepZeroTanh

/-!
# A parameter that satisfies all conditions of the case (0), for `tanh` blocks

Paper (dimension paper): Appendix D.6, "Parameters that satisfy all conditions, in the case (0)":
"We choose the blocks from the last to the first. Let `D` and the blocks `ℓ + 1, …, L` be chosen,
regular and with (S1) to (S3) for tanh […]. This fixes `κ_ℓ` (Lemma D.14). We choose
`(W, V) = (W_read^ℓ, W_write^ℓ)`. […] So there are parameters `θ*` that are regular and whose
blocks all satisfy (S1) to (S3) for tanh".

Stated here: for `d_in, d_out ≥ d ≥ 2` and at least `d` hidden units in every block there is a
parameter `θ*` that is regular in the sense of the case (0) (`RegularZero`) and whose every block
`k` satisfies (S1), (S2), and (S3) for a cone `C_κ` on which the network after the block,
`𝓑_{>k+1}`, is holomorphic (the `κ_ℓ` of Lemma D.14). These are the hypotheses of Lemma D.18
(`claimZero_castSucc_tanh`, `Depth/StepZeroTanh.lean`) at every block.

One block is `exists_tanhPathBlock` (`Depth/TanhPathBlock.lean`); the cone of a block depends only
on the later blocks (`Depth/ComplexSuffixStep.lean`). Numbering: the block `k : Fin L` is the
paper's block `k + 1`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **"So there are parameters `θ*` that are regular and whose blocks all satisfy (S1) to (S3) for
tanh"** (Appendix D.6): for `d_in, d_out ≥ d ≥ 2` and at least `d` hidden units in every block,
there is a parameter that is regular in the sense of the case (0) and whose every block `k`
satisfies (S1), (S2), and (S3) for a cone `C_κ`, `κ > 0`, on which `𝓑_{>k+1}` is holomorphic. -/
theorem exists_regularZero_tanh_path [Nonempty T] (hd : 2 ≤ Fintype.card d)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∃ θ : Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm 0) hid) dIn dOut,
      RegularZero (Arch.mlp Real.tanh (rmsNorm 0) hid) θ ∧
      ∀ k : Fin L,
        (∀ i j : hid k, i ≠ j → ∀ a c : ℝ, a • θ.write k i + c • θ.write k j = 0 →
          a = 0 ∧ c = 0) ∧
        LinearIndependent ℚ (fun j : hid k => fun i : d => θ.read k i j) ∧
        ∃ κ : ℝ, 0 < κ ∧ HolomorphicOnCone Complex.tanh θ k.succ κ ∧ CondS3 θ k κ := by
  sorry

end Skips
