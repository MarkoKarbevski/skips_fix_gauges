import SkipsLean.Activations.MillsC

/-!
# The expansion of the Mills ratio at complex arguments

Paper (dimension paper): Appendix D.5, Lemma D.8 (ii).

"(ii) For `Re z > 0` and every integer `m ≥ 0`, with `(−1)!! = 1`,

  `|mr(z) − ∑_{l=0}^{m−1} (−1)^l (2l−1)!! / z^{2l+1}| ≤ (2m−1)!! / (Re z)^{2m+1}`."

Its proof: "`mr(z) = ∫_0^∞ e^{−zu−u²/2} du` […]. For a number `y ≥ 0`,
`|e^{−y} − ∑_{l<m} (−y)^l / l!| ≤ y^m / m!`. With `y = u²/2`, and with
`∫_0^∞ e^{−zu} u^{2l} du = (2l)! / z^{2l+1}` and `(2l)! / (2^l l!) = (2l−1)!!`, this gives (ii)."

Here `mr` is `millsRatioC` (`Activations/MillsC.lean`), defined by that integral. The double
factorial `(2l − 1)!!` is `(2 * l - 1)‼` with the subtraction of natural numbers, so that `l = 0`
gives `0‼ = 1`, the paper's `(−1)!! = 1` (as in `Activations/FarFromZero.lean`, which has the
lemma for real `z > 0`).
-/

namespace Skips

open scoped Nat

/-- **Lemma D.8 (ii), for complex `z` with `Re z > 0`:** the partial sums of
`∑_l (−1)^l (2l−1)!! / z^{2l+1}` approximate the Mills ratio with an error of at most
`(2m−1)!! / (Re z)^{2m+1}`. -/
theorem norm_millsRatioC_sub_sum_le {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    ‖millsRatioC z
        - ∑ l ∈ Finset.range m, (-1 : ℂ) ^ l * (((2 * l - 1)‼ : ℕ) : ℂ) / z ^ (2 * l + 1)‖
      ≤ ((2 * m - 1)‼ : ℝ) / z.re ^ (2 * m + 1) := by
  sorry

/-- The case `m = 0` of Lemma D.8 (ii): `|mr(z)| ≤ 1 / Re z` for `Re z > 0`. -/
theorem norm_millsRatioC_le {z : ℂ} (hz : 0 < z.re) : ‖millsRatioC z‖ ≤ 1 / z.re := by
  sorry

end Skips
