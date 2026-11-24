import SkipsLean.Depth.SuffixZeroClaim

/-!
# The case (0): the rank on a finite batch of inputs with nonzero hidden states

Paper (dimension paper): Proposition D.4 (The claim gives the rank), its last clause in the case
(0): "… and the Jacobian of the network has the rank (13) on some finite batch of such inputs",
the inputs `x` with `xE ≠ 0`. Appendix D.7 uses it: "By Proposition D.4 there is a finite batch
`X*`, with `xE ≠ 0` for all its inputs, on which the Jacobian at `θ*` has the rank (13)."

`funDim_of_claimZero` (`Depth/SuffixZeroClaim.lean`) gives the functional dimension, the largest
rank over all finite batches. Here the batch is named, with its inputs: no row of `xE` vanishes
(a hidden state has the rows `T`). In the case (0) the rank (13) is
`P − (L + 1)(d(d−1)/2 + 1)`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L) (θ : Params A dIn dOut)

/-- **Proposition D.4 of the dimension paper, the case (0), the batch:** for real-analytic blocks
under pre-RMSNorm with `ε = 0`, `d ≥ 2`, regular `θ` and `(D_0)`, there is a finite batch of inputs
`x` such that `xE` has no zero row on which the Jacobian has the rank
`P − (L + 1)(d(d−1)/2 + 1)`. -/
theorem exists_batch_jacobianRank_of_claimZero [Nonempty T] (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hθ : RegularZero A θ)
    (hd : 2 ≤ Fintype.card d) (h0 : ClaimZero A θ 0) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i t, (X i * θ.E) t ≠ 0) ∧
      jacobianRank A 0 X θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
        = Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end Skips
