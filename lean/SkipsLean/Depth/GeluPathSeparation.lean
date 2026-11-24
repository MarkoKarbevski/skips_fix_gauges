import SkipsLean.Activations.GeluOnPath
import SkipsLean.Activations.MillsAtInfinityC
import SkipsLean.Generic.HolomorphicBall

/-!
# GELU on the path: the hidden units are told apart by their rates

Paper (dimension paper): Appendix D.6 (the case `ε = 0`), proof of Lemma D.19 (the step for GELU
on the path), its parts "The expansion", "Step 1", the analytic part of "Step 2" and of "Step 4".

"As `σ(z) = z − δ(t)` and `σ'(z) = 1 − δ'(t)` on the path, Lemma D.15 applies:
`𝓛(z(t) − δ(t), 1 − δ'(t); n(t)) = 0` for all `t ≥ 1` (47). The expansion. For fixed `t`, by (46)
the map `(δ, δ') ↦ 𝓛(z(t) − δ, 1 − δ'; n(t))` is holomorphic in the rows `δ` with `|δ_j| ≤ ϱ t`
and affine in the row `δ'`. We expand it in powers of `δ` and `δ'`. Its value at `0` and its first
derivatives are `𝓛_0(t) = 𝓛(z(t), 1; n(t))`, `𝓛_j(t) = ∂𝓛/∂w̃_j (z(t), 1; n(t))`,
`𝓛'_j(t) = ∂𝓛/∂w̃'_j (z(t), 1; n(t))`, so that (47) is

  `𝓛_0(t) − ∑_j [𝓛_j(t) δ_j(t) + 𝓛'_j(t) δ'_j(t)] + (terms with two or more factors) = 0`,   (48)

where the factors are entries of `δ(t)` and `δ'(t)`. We use two facts about the coefficients.
First, every coefficient is meromorphic at infinity. […] Second, […] by Cauchy's estimates on the
polydisc of (46), the coefficient of a product of `i` factors `δ_j` and of at most one factor
`δ'_j` is at most a fixed power of `t` times `(ϱ t)^{−i}`. With (45), the series (48) therefore
converges absolutely for large `t`, and the sum of any set of its terms is at most a power of `t`
times `e^{−(d/8)(t − t⁻¹)² r}`, where `r` is the smallest sum of the numbers `r_j` of the factors
of a term of the set.

Step 1: […] By (48), `𝓛_0(t)` tends to `0` faster than every power of `1/t`. It is meromorphic at
infinity, so `𝓛_0(t) = 0` for large `t`, and then for all `t ≥ 1`, because it is holomorphic near
`[1, ∞)`.

Step 2: […] Take a hidden unit `j` and a nonempty open set of pairs […] on which `r_j < r_i` for
all `i ≠ j`, and let `γ = min(r_j, min_{i ≠ j}(r_i − r_j))`. By Step 1, all terms of (48) other
than the two of unit `j` are, together, at most a power of `t` times
`e^{−(d/8)(t − t⁻¹)² (r_j + γ)}`. Dividing by `φ(z_j)`, whose absolute value is a constant times
`e^{−(d/8)(t − t⁻¹)² r_j}` by (44), `(z_j 𝓛_j + 𝓛'_j) mr(z_j) − z_j 𝓛'_j → 0` faster than every
power of `1/t`. Here `z_j(t) = (√d/2)(t νc_j + (1/t) ν̄c_j)` with `Re(νc_j) = ξc_j > 0`, and
`z_j 𝓛_j + 𝓛'_j` and `z_j 𝓛'_j` are meromorphic at infinity. By Lemma D.9 both vanish, so
`𝓛'_j(t) = 0` and `𝓛_j(t) = 0` for large `t`, hence for all `t ≥ 1` (50).

Step 4: […] So in the expansion (48) of `𝓛°` every term has a factor `δ_l(t)` or `δ'_l(t)` of a
unit `l` other than `j_1, …, j_{i−1}`. Other than the two terms of unit `j`, such a term has a
factor of a unit `j_{i'}` with `i' > i`, or a factor of unit `j` and a second factor. With
`γ = min(r_{j_1}, r_{j_{i+1}} − r_j)`, or `γ = r_{j_1}` if `i = q`, we get (50) as in Step 2."

**The form here.** With `s = 1/t`, the degree of homogeneity of `𝓑` and of its derivatives turns
the map of (47) into `t²` times a map `Ψ(s, x, y)` of `s`, of `x = c₀ δ / t` (with the number
`c₀ = 2/√d`) and of `y = δ'`, which is holomorphic near the points with `s ∈ [0, 1]` and `(x, y)`
in a fixed polydisc: this is how "every coefficient is meromorphic at infinity" and the bound on
the polydisc of (46) are used. The statements below take such a map `Ψ` as given, with values in a
complex Banach space, and no network: the hidden units `i ∈ ι` have the inputs
`z_i(t) = ω_i t + ω̄_i/t` on the path (`unitPath`, `Activations/GeluOnPath.lean`), with
`|Im ω_i| < Re ω_i`, and the rates `(Re ω_i)² − (Im ω_i)² = (d/4) r_i`. The point of the polydisc
on the path is `geluGap c₀ ω t = (c₀ δ(t)/t, δ'(t))`, and (47) is `Ψ(1/t, geluGap c₀ ω t) = 0` for
large `t`.

* Step 1 is `gelu_path_zero`: `Ψ(s, 0) = 0` for `s ∈ (0, 1]`.
* Steps 2 and 4 are `gelu_path_unit`: if `Ψ(s, ·)` vanishes on the points whose entries outside a
  set `A` of hidden units vanish (for `A = ∅` this is Step 1), and the unit `j ∉ A` has a smaller
  rate than every other unit outside `A`, then the two first derivatives of `Ψ(s, ·)` at `0` in
  the entries of unit `j` vanish, for `s ∈ (0, 1]`. These are `(t c₀)⁻¹ t⁻² 𝓛_j` and `t⁻² 𝓛'_j`
  up to sign, at `t = 1/s`.

The norm on `(ι → ℂ) × (ι → ℂ)` is the sup norm, so `‖x‖ ≤ r` is a polydisc.
-/

namespace Skips

open Filter Topology

variable {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace F]

/-- The point of the polydisc on the path: `(c₀ δ(t)/t, δ'(t))`, with
`δ_i(t) = z_i(t) − σ(z_i(t))` and `δ'_i(t) = 1 − σ'(z_i(t))` for GELU at
`z_i(t) = ω_i t + ω̄_i/t`. -/
noncomputable def geluGap (c₀ : ℝ) (ω : ι → ℂ) (t : ℝ) : (ι → ℂ) × (ι → ℂ) :=
  (fun i => ((c₀ / t : ℝ) : ℂ) * (unitPath (ω i) t - geluC (unitPath (ω i) t)),
    fun i => 1 - deriv geluC (unitPath (ω i) t))

/-- **Lemma D.19, Step 1 (analytic part):** let `Ψ` be holomorphic at the points `(s, x)` with
`s ∈ [0, 1]` and `‖x‖ ≤ r`, and let `Ψ(1/t, (c₀ δ(t)/t, δ'(t))) = 0` for all large `t` (47). Then
`Ψ(s, 0) = 0` for every `s ∈ (0, 1]`. -/
theorem gelu_path_zero (ω : ι → ℂ) (hω : ∀ i, |(ω i).im| < (ω i).re) (c₀ : ℝ)
    (Ψ : ℂ × ((ι → ℂ) × (ι → ℂ)) → F) {r : ℝ} (hr : 0 < r)
    (hΨ : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x : (ι → ℂ) × (ι → ℂ), ‖x‖ ≤ r →
      AnalyticAt ℂ Ψ ((s : ℂ), x))
    (h47 : ∀ᶠ t : ℝ in atTop, Ψ (((t : ℂ))⁻¹, geluGap c₀ ω t) = 0) :
    ∀ s : ℝ, 0 < s → s ≤ 1 → Ψ ((s : ℂ), 0) = 0 := by
  sorry

/-- **Lemma D.19, Steps 2 and 4 (analytic part), (50):** let `Ψ` be as in `gelu_path_zero`, with
`c₀ ≠ 0`. Let `A` be a set of hidden units such that `Ψ(s, x) = 0` for `s ∈ (0, 1]` and every `x`
in the polydisc whose entries outside `A` vanish, and let the unit `j ∉ A` have a smaller rate
`(Re ω_j)² − (Im ω_j)²` than every other unit outside `A`. Then, for every `s ∈ (0, 1]`, the
derivatives of `Ψ(s, ·)` at `0` along the two entries of unit `j` vanish. -/
theorem gelu_path_unit [DecidableEq ι] (ω : ι → ℂ) (hω : ∀ i, |(ω i).im| < (ω i).re) {c₀ : ℝ}
    (hc₀ : c₀ ≠ 0) (Ψ : ℂ × ((ι → ℂ) × (ι → ℂ)) → F) {r : ℝ} (hr : 0 < r)
    (hΨ : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x : (ι → ℂ) × (ι → ℂ), ‖x‖ ≤ r →
      AnalyticAt ℂ Ψ ((s : ℂ), x))
    (h47 : ∀ᶠ t : ℝ in atTop, Ψ (((t : ℂ))⁻¹, geluGap c₀ ω t) = 0)
    (A : Set ι) (j : ι) (hjA : j ∉ A)
    (hrate : ∀ i, i ∉ A → i ≠ j →
      (ω j).re ^ 2 - (ω j).im ^ 2 < (ω i).re ^ 2 - (ω i).im ^ 2)
    (hA : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ x : (ι → ℂ) × (ι → ℂ), ‖x‖ ≤ r →
      (∀ i, i ∉ A → x.1 i = 0 ∧ x.2 i = 0) → Ψ ((s : ℂ), x) = 0) :
    ∀ s : ℝ, 0 < s → s ≤ 1 →
      fderiv ℂ (fun x : (ι → ℂ) × (ι → ℂ) => Ψ ((s : ℂ), x)) 0 (Pi.single j 1, 0) = 0 ∧
      fderiv ℂ (fun x : (ι → ℂ) × (ι → ℂ) => Ψ ((s : ℂ), x)) 0 (0, Pi.single j 1) = 0 := by
  sorry

end Skips
