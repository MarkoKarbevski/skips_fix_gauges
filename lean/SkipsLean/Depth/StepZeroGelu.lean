import SkipsLean.Depth.StepZeroGeluOne
import SkipsLean.Depth.SuffixFlatZeroConverse

/-!
# The step for GELU on the path (Lemma D.19)

Paper (dimension paper): Appendix D.6 (the case `ε = 0`).

"Lemma D.19 (The step for GELU on the path). Let `σ` be GELU, in the case (0), let `θ` be regular,
and let block `k + 1` satisfy (P1) and (P2). Then `(D_{k+1})` implies `(D_k)`."

Its proof, after the path and the expansion (`Depth/StepZeroGeluPath.lean`):

"Step 1: […] At `t = 1` […] `0 = 𝓛(nW, 1; n) = 𝐃𝓑(n W V)(n (Z W V + η_W V + W η_V)) +
𝐃_θ𝓑(n W V) η'`. The right side is real-analytic and homogeneous of degree `0` in the row `n ≠ 0`,
and it vanishes for `ξ` in the open set `P`, hence for all `n ≠ 0`. With `h = n W V`, which takes
every value by (P1), this is (16) for `k + 1` with `Z' = (W V)⁻¹ (Z W V + η_W V + W η_V)` (49) and
`η'`. By `(D_{k+1})`, `Z' = Y_{k+1} + β' I` and `η'` is as in (18) […].

Step 2: the slowest hidden unit gives `Z`. […] `𝓛'_j(t) = ż_j(n(t)) 𝐃𝓑(n(t) W V) a_j`. At `t = 1`
this is `ż_j(n) 𝐃𝓑(n W V) a_j = 0` at `n = √d ξ`, for `ξ` in an open set. By (P1), `a_j ≠ 0`, so by
Lemma D.2 `𝐃𝓑(n W V) a_j ≠ 0` on an open dense set of `n`. So `ż_j(n) = 0` on an open subset of
`S` […]. So `Z = Y_k + β_k I` with `Y_k` antisymmetric.

Step 3: subtracting a symmetry. Let `β_{k+1} = β' − β_k`. The pair `Y_k + β_k I` and
`(−Y_k W, V (Y_{k+1} + β_{k+1} I), η')` is of the form (18), so it satisfies (16) for `k`.
Subtracting it from `Z` and `η` leaves the pair `0` and `(η°_W, η°_V, 0)` with
`η°_W = η_W + Y_k W`, `η°_V = η_V − V (Y_{k+1} + β_{k+1} I)`, which satisfies (16) for `k` as well,
and by (49) and Step 1 `η°_W V + W η°_V = 0` (51). […] It remains to show `η°_W = 0` and
`η°_V = 0`.

Step 4: the hidden units in the order of their rates. […] We show by induction on `i` that
column `j_i` of `η°_W` and row `j_i` of `η°_V` vanish. […] `𝓛°'_j(t) = (n η°_{c_j}) 𝐃𝓑(n W V) a_j`,
`𝓛°_j(t) = 𝐃𝓑(n W V) η°_{a_j}` at `n = n(t)` […]. At `t = 1`, for `ξ` in an open set and
`n = √d ξ`: by Lemma D.2, `n η°_{c_j} = 0`, so `η°_{c_j} = 0`, and `η°_{a_j}` is a multiple of
`n W V` for an open set of rows `n`, so `η°_{a_j} = 0`. After `i = q`: `η_W = −Y_k W` and
`η_V = V (Y_{k+1} + β_{k+1} I)`. With Step 1 for `η'` and Step 2 for `Z` this is (18) for `k`."

Stated here: the lemma, `claimZero_castSucc_gelu`. Step 1 is `exists_suffixFlatZero_succ_gelu`
(`Depth/StepZeroGeluOne.lean`: (49) and (16) for `k + 1`). The conditions (P1), (P2) are
`CondP1`, `CondP2` (`Depth/CondP.lean`); the `κ_ℓ` of Lemma D.14 is any `κ ∈ (0, 1]` such that `𝓑_{>k+1}` is
holomorphic on `C_κ`, as a hypothesis (as for `tanh`, `Depth/StepZeroTanh.lean`). Numbering as in
`Depth/StepTanh.lean`: the block is `k : Fin L`, the paper's block `k + 1`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut] {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Lemma D.19 of the dimension paper (the step for GELU on the path).** Let `σ` be GELU, in the
case (0), `d ≥ 2`, let `θ` be regular, let `𝓑_{>k+1}` be holomorphic on the cone `C_κ`,
`0 < κ ≤ 1` (Lemma D.14), and let block `k` satisfy (P1) and (P2) for `κ`. Then `(D_{k+1})` implies
`(D_k)`. -/
theorem claimZero_castSucc_gelu [Nonempty T]
    {θ : Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm 0) hid) dIn dOut}
    (hθ : RegularZero (Arch.mlp gelu (rmsNorm 0) hid) θ) (hd : 2 ≤ Fintype.card d)
    (k : Fin L) (hP1 : CondP1 θ k) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hhol : HolomorphicOnCone geluC θ k.succ κ) (hP2 : CondP2 θ k κ)
    (hk : ClaimZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.succ) :
    ClaimZero (Arch.mlp gelu (rmsNorm 0) hid) θ k.castSucc := by
  sorry

end Skips
