import SkipsLean.Depth.StepZeroGeluPath
import SkipsLean.Depth.SuffixZeroRows
import SkipsLean.Depth.FlatAtMatrixRows

/-!
# The step for GELU on the path: Step 1

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), proof of Lemma D.19, Step 1:

"At `t = 1`, where `n(t)` is the row `n = √d ξ`, this reads, by (21), (20) and (15),
`0 = 𝓛(nW, 1; n) = 𝐃𝓑(n W V)(n (Z W V + η_W V + W η_V)) + 𝐃_θ𝓑(n W V) η'`. The right side is
real-analytic and homogeneous of degree `0` in the row `n ≠ 0`, and it vanishes for `ξ` in the open
set `P`, hence for all `n ≠ 0`. With `h = n W V`, which takes every value by (P1), this is (16) for
`k + 1` with `Z' = (W V)⁻¹ (Z W V + η_W V + W η_V)` (49) and `η'`."

The open set `P` is `isOpen_setOf_pathP2` (`Depth/CondP.lean`), the identity at one `ξ` is
`gelu_path_step_zero_real` (`Depth/StepZeroGeluPath.lean`), and Lemma D.3 at the matrix `W V` is
`flat_at_matrix_of_isOpen_rows` with `suffixFlatZero_of_flat_at_write`. Block `k : Fin L` is the
paper's block `k + 1`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Lemma D.19, Step 1:** for GELU in the case (0), `d ≥ 2`, regular `θ`, `𝓑_{>k+1}` holomorphic
on `C_κ`, `0 < κ ≤ 1`, and block `k` with (P1) and (P2): if `Z` and `η` satisfy (16) before block
`k`, then there is `Z'` with `Z W V + η_W V + W η_V = W V Z'` (49) such that `Z'` and `η` satisfy
(16) after block `k`. -/
theorem exists_suffixFlatZero_succ_gelu [Nonempty T]
    {θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut}
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d)
    (k : Fin L) (hP1 : CondP1 θ k) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hhol : HolomorphicOnCone geluC θ k.succ κ) (hP2 : CondP2 θ k κ)
    (Z : Matrix d d ℝ) (η : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut)
    (h16 : SuffixFlatZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.castSucc Z η) :
    ∃ Z' : Matrix d d ℝ,
      Z * (θ.read k * θ.write k) + η.read k * θ.write k + θ.read k * η.write k
        = θ.read k * θ.write k * Z' ∧
      SuffixFlatZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.succ Z' η := by
  sorry

end Skips
