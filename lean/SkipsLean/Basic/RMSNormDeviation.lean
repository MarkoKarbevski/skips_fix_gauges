import SkipsLean.Basic.RMSNorm

/-!
# RMSNorm and a conformal change of basis for `ε > 0`: the deviation

Paper (skips paper), Lemma A.2 (RMSNorm equivariance), (ii): "If `ε > 0` and `G = cQ`, then
`‖N(hG) − N_ε(h)Q‖/‖N(h)‖ = (ε/(2r²)) |1 − c⁻²| + O(ε²)`, where `r² = ‖h‖²/d_model`." Its proof:
"For `G = cQ`, `N_ε(h cQ) = c hQ/√(c²‖h‖²/d_model + ε)` and `N_ε(h)Q = hQ/√(‖h‖²/d_model + ε)`
[…] The expansion of the deviation is the Taylor expansion of `c√(r²+ε)/√(c²r²+ε) − 1` in `ε`."
(The two `N` without a subscript in (ii) are `N_ε`.)

Part (i) is in `Basic/RMSNorm.lean` and `Basic/RMSNormConverse.lean`. Here part (ii), for a row
`v`, `r² = (v ⬝ᵥ v)/d` and an orthogonal `Q`, in three statements:

* the exact relation `N_ε(v (cQ)) = (c√(r²+ε)/√(c²r²+ε)) · N_ε(v) Q`, for every real `c` and
  `ε > 0`;
* the deviation in the Euclidean norm (the square root of the dot product of a row with itself):
  `‖N_ε(v (cQ)) − N_ε(v)Q‖ = |c√(r²+ε)/√(c²r²+ε) − 1| · ‖N_ε(v)‖`;
* the expansion `|c√(r²+ε)/√(c²r²+ε) − 1| = (ε/(2r²)) |1 − c⁻²| + O(ε²)` as `ε → 0` from above,
  for `r² > 0` and `c > 0` (as `ε → 0` from below the two sides differ at first order:
  `ai_notes/rmsnorm_deviation_check_2026-11-25.py`).
-/

namespace Skips

open Matrix Filter Topology

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **Lemma A.2 (ii), the exact relation.** For `ε > 0`, an orthogonal `Q`, a real `c` and a row
`v` with `r² = (v ⬝ᵥ v)/d`: `N_ε(v (cQ)) = (c√(r²+ε)/√(c²r²+ε)) · N_ε(v) Q`. -/
theorem rmsRow_vecMul_smul_orthogonal {ε : ℝ} (hε : 0 < ε) (c : ℝ) {Q : Matrix d d ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup d ℝ) (v : d → ℝ) :
    rmsRow ε (v ᵥ* (c • Q))
      = (c * Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε)
          / Real.sqrt (c ^ 2 * ((v ⬝ᵥ v) / (Fintype.card d : ℝ)) + ε)) • (rmsRow ε v ᵥ* Q) := by
  sorry

/-- **Lemma A.2 (ii), the deviation in the Euclidean norm.** For `ε > 0`, an orthogonal `Q`, a
real `c` and a row `v` with `r² = (v ⬝ᵥ v)/d`:
`‖N_ε(v (cQ)) − N_ε(v)Q‖ = |c√(r²+ε)/√(c²r²+ε) − 1| · ‖N_ε(v)‖`. -/
theorem sqrt_dotProduct_rmsRow_vecMul_smul_orthogonal_sub {ε : ℝ} (hε : 0 < ε) (c : ℝ)
    {Q : Matrix d d ℝ} (hQ : Q ∈ Matrix.orthogonalGroup d ℝ) (v : d → ℝ) :
    Real.sqrt ((rmsRow ε (v ᵥ* (c • Q)) - rmsRow ε v ᵥ* Q)
        ⬝ᵥ (rmsRow ε (v ᵥ* (c • Q)) - rmsRow ε v ᵥ* Q))
      = |c * Real.sqrt ((v ⬝ᵥ v) / (Fintype.card d : ℝ) + ε)
          / Real.sqrt (c ^ 2 * ((v ⬝ᵥ v) / (Fintype.card d : ℝ)) + ε) - 1|
        * Real.sqrt (rmsRow ε v ⬝ᵥ rmsRow ε v) := by
  sorry

/-- **Lemma A.2 (ii), the expansion.** For `r² > 0` and `c > 0`, as `ε → 0` from above:
`|c√(r²+ε)/√(c²r²+ε) − 1| = (ε/(2r²)) |1 − c⁻²| + O(ε²)`. -/
theorem abs_rmsNorm_deviation_sub_isBigO {r2 c : ℝ} (hr : 0 < r2) (hc : 0 < c) :
    (fun ε : ℝ => |c * Real.sqrt (r2 + ε) / Real.sqrt (c ^ 2 * r2 + ε) - 1|
        - ε / (2 * r2) * |1 - (c ^ 2)⁻¹|) =O[𝓝[>] 0] fun ε : ℝ => ε ^ 2 := by
  sorry

end Skips
