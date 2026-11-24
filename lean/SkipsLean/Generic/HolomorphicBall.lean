import SkipsLean.Imports

/-!
# A bounded holomorphic map on a ball: the first terms of its expansion

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), proof of Lemma D.19, "The expansion":
"For fixed `t`, by (46) the map `(δ, δ') ↦ 𝓛(z(t) − δ, 1 − δ'; n(t))` is holomorphic in the rows
`δ` with `|δ_j| ≤ ϱ t` and affine in the row `δ'`. We expand it in powers of `δ` and `δ'`. […] So
by Cauchy's estimates on the polydisc of (46), the coefficient of a product of `i` factors `δ_j`
and of at most one factor `δ'_j` is at most a fixed power of `t` times `(ϱ t)^{−i}`. […] the sum
of any set of its terms is at most a power of `t` times `e^{−(d/8)(t − t⁻¹)² r}`, where `r` is the
smallest sum of the numbers `r_j` of the factors of a term of the set."

The proof of Lemma D.19 uses this for three sets of terms: all terms with at least one factor
(Step 1); all terms other than the two terms of first order of one hidden unit `j` (Step 2); and,
when the map vanishes on the points `x` whose entries outside a set of hidden units vanish, all
terms that have a factor outside that set, other than the two terms of unit `j` (Step 4). The
statement below gives the three bounds without the power series: for a map `f` that is holomorphic
and bounded by `M` on the ball of radius `r` of a complex normed space, and for small `x`, `y`,
`w`,

  `‖f(x + y + w) − f(x) − 𝐃f(0) y‖ ≤ 16 M (‖w‖/r + (‖y‖/r) (‖x‖/r + ‖y‖/r))`.

(`f(x + y + w) − f(x + y)` is of first order in `w`; `f(x + y) − f(x) − 𝐃f(x) y` is of second
order in `y`; `𝐃f(x) y − 𝐃f(0) y` is of first order in `x` and in `y`. Each follows from Cauchy's
estimate in one complex variable, on a line through the ball.) With the sup norm on
`ℂ^q × ℂ^q`, a ball is the paper's polydisc.
-/

namespace Skips

/-- **Cauchy's estimates for the first terms of the expansion:** let `f` be holomorphic on the open
ball of radius `r` around `0` of a complex normed space, with `‖f‖ ≤ M` there. For `x`, `y`, `w`
of norm at most `r/8`,
`‖f(x + y + w) − f(x) − 𝐃f(0) y‖ ≤ 16 M (‖w‖/r + (‖y‖/r) (‖x‖/r + ‖y‖/r))`. -/
theorem norm_sub_sub_fderiv_le_of_analyticOnNhd_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {f : E → F} {r M : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 r)) (hM : ∀ x ∈ Metric.ball (0 : E) r, ‖f x‖ ≤ M)
    {x y w : E} (hx : ‖x‖ ≤ r / 8) (hy : ‖y‖ ≤ r / 8) (hw : ‖w‖ ≤ r / 8) :
    ‖f (x + y + w) - f x - fderiv ℂ f 0 y‖
      ≤ 16 * M * (‖w‖ / r + ‖y‖ / r * (‖x‖ / r + ‖y‖ / r)) := by
  sorry

end Skips
