STATUS: complete

# Ninth audit of Lean statements against the dimension paper, part A (24 November 2026)

Reader: an independent reader who did not write the statements. Brief:
`/home/claude/proj_up/audit9a_brief_2026-11-24.md`. I edited no repository file, ran no
`lake build`, made no commit and no push.

Subject: GELU at complex arguments, for the case `ε = 0` of pre-RMSNorm: Lemma D.8, Lemma D.9 and
the first half of the proof of Lemma D.19 ("The path", "The expansion" with (48), Step 1, and the
analytic part of Steps 2 and 4), in six Lean files with 31 public names (6 definitions, 25
theorems).

Paper: "On the Functional Dimension of a Family of Analytic Neural Networks", as text (`dim.txt`;
statement and equation numbers are those of that text). I read the text file, not the PDF.

## Commit, and the files with `sorry`

Library: `/home/claude/lw/lean` (branch `lean-wip`). The branch moved once while I read.

| When | Commit of `/home/claude/lw` | Files under `SkipsLean/` that contain the word `sorry` (`grep -w`, number of lines) |
|---|---|---|
| start | `91bc064f050350fde6622209e3fa665c3f2dce30` (11:50:04 UTC) | `Dimension/ExpOrbitGated.lean` (2), `Dimension/LocalIdentifiabilityGated.lean` (6), `Residual/LocalIdentifiability.lean` (6), `Residual/LocalIdentifiabilityGated.lean` (6) |
| end | `18543e53c0416c7a64ea64fb4ec6f73085c8fab2` (11:53:29 UTC) | `Dimension/ExpOrbitGated.lean` (2) |

None of these files belongs to this audit. The six files of this audit, and
`Depth/StepZeroGeluPath.lean`, which uses them, contain no `sorry` at either commit, and
`git diff --quiet 91bc064 18543e5` finds no change in any of them, nor in
`Activations/Gaussian.lean`, `Activations/FarFromZero.lean`, `Activations/MillsAtInfinity.lean`.
Between the two commits `STATEMENTS.md` changed in one line (228), so the line numbers below hold at
both. `grep -rn "^axiom" SkipsLean` finds nothing.

## How I checked

- "By reading": I read the six Lean files in full (statements, docstrings and proofs), the parts
  of `Depth/StepZeroGeluPath.lean` that use them, the definitions they rest on (`gaussPdf`,
  `gaussCdf`, `gelu`, `geluDeriv`, `millsRatio`, `FasterThanPowers`, `MeromorphicAtInfinity`), and
  the paper (Appendix D.5 from "GELU and the Mills ratio" to Lemma D.9; Appendix D.6 in full).
- "By compiling": with `lean` 4.36.0, without `lake`, in `/home/claude/audit9a/`. The compiled
  library of `/home/claude/lw` has none of the six files, so I used the compiled library of
  `/home/claude/lp/lean` (branch `lean-plus`, at `18543e5`, no changed tracked file under
  `SkipsLean/`; the six sources and the three they import are the same files as in `lw`, by `cmp`)
  through `LEAN_PATH`. Two ways:
  1. `Chk1.lean` against the `lp` library as it is;
  2. I compiled **copies of the six source files** (taken with `git archive 18543e5`) into
     `/home/claude/audit9a/build/`, in the order of their imports, with only their imports
     (`FarFromZero`, `MillsAtInfinity`, `Imports`, Mathlib) taken from `lp`; all six compile
     without error (7 to 12 seconds each); then `Chk2.lean` and `Chk3.lean` against these copies.
  I wrote nothing under `lw`, `lp` or the repository.
- "By a computation": `py/check_mills.py` (mpmath, 30 digits). A floating-point check supports a
  claim; it proves nothing.

## Short answer

**Nothing false, vacuous or drifted was found.** The 25 public theorems of the six files are
proved: the copies compile, and each depends on `propext`, `Classical.choice`, `Quot.sound` only.

1. `geluC` is the paper's GELU at complex arguments: it is entire, it agrees on the real line with
   the real GELU `z Φ(z)` that the network statements use, and an entire function with these values
   on the real line is `geluC` (compiled). The derivative is the paper's formula.
2. Lemma D.8 (ii) in Lean is the paper's statement word for word (region `Re z > 0`, every `m`,
   the same constants). Lemma D.9 in Lean has complex `ω`, `ω'` as in the paper; "`Θ = 0`" is
   "`Θ(t) = 0` for all large `t`", which is what the paper's proof of Lemma D.19 uses. The proof of
   Lemma D.19 needs nothing more than Lean has.
3. The estimate on a ball that replaces the power series (48) is true and is enough for the three
   sums of terms that the proof uses. The hypotheses of `gelu_path_unit` are those that the paper
   has at that point, and its conclusion is (50).

One docstring has a wrong factor (a comment, no effect on a statement), and two older rows of the
index are out of date. See "What the authors should know" and the corrections.

---------------------------------------------------------------------------------------------------

## Part 1: the checks asked for by the coordinator

### Check 1. GELU at complex arguments is the paper's function

**Verdict: yes.** `geluC` is the entire function `σ(z) = (z/2)(1 + erf(z/√2))` of the paper,
`hasDerivAt_geluC` is the paper's formula for `σ'`, and `HolomorphicOnCone geluC …` is the paper's
"`𝓑_{>k}` extends to a holomorphic map on `C_κ`" for GELU blocks.

The Lean text (`Activations/MillsC.lean`):

```
noncomputable def gaussPdfC (z : ℂ) : ℂ :=
  Complex.exp (-z ^ 2 / 2) / ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)

noncomputable def millsRatioC (z : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), Complex.exp (-(z * (u : ℂ)) - (u : ℂ) ^ 2 / 2)

noncomputable def geluC (z : ℂ) : ℂ := z - gaussPdfC z * z * millsRatioC z

theorem millsRatioC_ofReal (x : ℝ) : millsRatioC (x : ℂ) = ((millsRatio x : ℝ) : ℂ)
theorem geluC_ofReal (x : ℝ) : geluC (x : ℂ) = ((gelu x : ℝ) : ℂ)
theorem hasDerivAt_millsRatioC (z : ℂ) : HasDerivAt millsRatioC (z * millsRatioC z - 1) z
theorem hasDerivAt_geluC (z : ℂ) :
    HasDerivAt geluC (1 - gaussPdfC z * (millsRatioC z - z)) z
theorem differentiable_geluC : Differentiable ℂ geluC
```

The paper: "GELU is `σ(z) = (z/2)(1 + erf(z/√2))`, which is entire. For `z ∈ ℂ` let
`φ(z) = e^{−z²/2}/√(2π)`, `mr(z) = √(π/2) e^{z²/2} (1 − erf(z/√2))` […] Lemma D.8 (i) For all
`z ∈ ℂ`: `σ(z) = z − φ(z) z mr(z)` and `σ'(z) = 1 − φ(z)(mr(z) − z)`." And in the proof of (ii):
"for real `z`, `mr(z) = e^{z²/2} ∫_z^∞ e^{−y²/2} dy`, and the substitution `y = z + u` gives
`mr(z) = ∫_0^∞ e^{−zu−u²/2} du`. Both sides are entire, so this holds for all `z`."

What I checked, point by point.

- **Which real GELU.** `gelu` of `Activations/Gaussian.lean`: `gelu z = z * gaussCdf z`,
  `gaussCdf z = 1/2 + ∫ t in 0..z, gaussPdf t`, `gaussPdf z = exp(−z²/2)/√(2π)`. This is
  `z Φ(z) = (z/2)(1 + erf(z/√2))`, the paper's GELU on the real line (by reading: with
  `erf(x) = (2/√π) ∫_0^x e^{−u²} du`, `(1/2)(1 + erf(z/√2)) = 1/2 + ∫_0^z φ`). By compiling
  (`Chk1.lean`, example (1)): `geluC ↑x = ↑(x * (1/2 + ∫ t in 0..x, gaussPdf t))` is
  `geluC_ofReal x`. It is the same `gelu` as in the network statements of the case (0)
  (`Arch.mlp gelu (rmsNorm 0) hid` in `Depth/StepZeroGeluPath.lean`, `Depth/StepZeroGelu.lean`).
- **The real Mills ratio.** `millsRatio z = (1 − gaussCdf z)/gaussPdf z`
  (`Activations/FarFromZero.lean`). This is the paper's `mr` at real `z`: `1 − Φ(z) =
  (1/2)(1 − erf(z/√2))`, divided by `φ(z)`, is `√(π/2) e^{z²/2}(1 − erf(z/√2))` (by reading).
- **The integral is defined for every `z`.** `integrableOn_millsRatioC`: the integrand is
  integrable on `(0, ∞)` for every complex `z`. So `millsRatioC` is the integral at every `z`, not
  the value `0` that Lean gives to an integral that does not exist.
- **Entire.** `hasDerivAt_millsRatioC` and `hasDerivAt_geluC` give a complex derivative at every
  `z`; `differentiable_geluC` is "GELU is entire".
- **The entire extension is this one.** By compiling (`Chk3.lean`, two statements, no `sorry`):
  an entire `f : ℂ → ℂ` with `f ↑x = ↑(gelu x)` for all real `x` is `geluC`; an entire `f` with
  `f ↑x = ↑(millsRatio x)` for all real `x` is `millsRatioC`. The paper's `σ` and `mr` are entire
  and have these values on the real line, so they are `geluC` and `millsRatioC`. Lean cannot state
  the formulas with `erf` (Mathlib has no error function); the header of the file says so.
- **By a computation** (`check_mills.py`, 40 random complex `z` with real and imaginary part in
  `[−3, 3]`, so also `Re z < 0`): the integral agrees with `√(π/2) e^{z²/2} erfc(z/√2)`, and
  `z − φ(z) z mr(z)` with `(z/2)(1 + erf(z/√2))`, to `10⁻³⁰`; `1 − φ(z)(mr(z) − z)` agrees with a
  numerical derivative of the paper's GELU to `10⁻³⁰`.
- **The formula for `σ'`.** `hasDerivAt_geluC` is `σ'(z) = 1 − φ(z)(mr(z) − z)` at every complex
  `z`: Lemma D.8 (i), second formula, word for word. The first formula of (i) is the definition of
  `geluC`; its content is then `geluC_ofReal` together with "entire". On the real line
  `deriv geluC ↑x = ↑(geluDeriv x)`, `geluDeriv x = Φ(x) + xφ(x)` (`deriv_geluC_ofReal`).
- **`HolomorphicOnCone geluC …`.** The definition (`Depth/ComplexSuffix.lean`, compared by the
  eighth reader, part B, (d)) says that `(ω, h) ↦ suffixC σC ω k h` is analytic at `(θ, h)` for
  every `h` with rows in `C_κ`, where `suffixC σC` is the paper's recursion with `N` at complex rows
  and `σC` in the place of `σ`. With `σC = geluC` and `θ` a parameter of
  `Arch.mlp gelu (rmsNorm 0) hid`: the map extends `𝓑_{>k}` (`suffixC_ofReal`, which asks that
  `σC` extends `σ`; here `geluC_ofReal`), and it is built with the paper's entire GELU. So it is
  the paper's holomorphic extension of `𝓑_{>k}` for GELU blocks. The cones are supplied by Lemma
  D.14 with these two facts: `exists_holomorphicOnCone_castSucc geluC_ofReal (fun x =>
  analyticAt_geluC _) …` (`Depth/RegularZeroGelu.lean:95`). Lemma D.15 in Lean writes `σ'(n(t)W)`
  as `deriv σC`; for `geluC` this is the paper's `σ'` at complex arguments
  (`one_sub_deriv_geluC`). (By reading.)

### Check 2. Lemma D.8 (ii) and Lemma D.9 in the form the proof of Lemma D.19 uses

**Verdict: Lemma D.8 (ii) is the same. Lemma D.9 is the same, with "`Θ = 0`" stated as
"`Θ(t) = 0` for all large `t`"; in the hypotheses Lean asks less than the paper. The proof of
Lemma D.19 needs nothing that Lean does not have.**

**Lemma D.8 (ii).** Lean (`Activations/MillsCExpansion.lean`):

```
theorem norm_millsRatioC_sub_sum_le {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    ‖millsRatioC z
        - ∑ l ∈ Finset.range m, (-1 : ℂ) ^ l * (((2 * l - 1)‼ : ℕ) : ℂ) / z ^ (2 * l + 1)‖
      ≤ ((2 * m - 1)‼ : ℝ) / z.re ^ (2 * m + 1)

theorem norm_millsRatioC_le {z : ℂ} (hz : 0 < z.re) : ‖millsRatioC z‖ ≤ 1 / z.re
```

| Clause of the paper | Lean | Same? |
|---|---|---|
| "For `Re z > 0`" | `0 < z.re`: the half-plane, not a sector | yes |
| "every integer `m ≥ 0`" | `m : ℕ` | yes |
| the sum over `l = 0, …, m − 1` of `(−1)^l (2l−1)!!/z^{2l+1}` | `Finset.range m`, the same terms | yes |
| "with `(−1)!! = 1`" | `2 * l - 1` is subtraction of natural numbers, so `l = 0` gives `0‼ = 1` | yes |
| the bound `(2m−1)!!/(Re z)^{2m+1}` | the same | yes |

By compiling (`Chk1.lean`, example (2)): the case `m = 1` reads `‖millsRatioC z − 1/z‖ ≤
1/(Re z)³`. By a computation: 2100 cases (`Re z` between 0.03 and 16, any imaginary part,
`m = 0, …, 6`), the largest ratio of the left side to the right side is 0.995. The second
statement is the case `m = 0`, `|mr(z)| ≤ 1/Re z`, which the proof of Lemma D.19 quotes.

**"Meromorphic at infinity".** Lean (`Activations/MillsAtInfinityC.lean`):

```
def MeromorphicAtInfinityC (Θ : ℝ → F) : Prop :=
  ∃ (l : ℕ) (Θ₀ : ℂ → F), AnalyticAt ℂ Θ₀ 0 ∧
    ∀ᶠ t : ℝ in atTop, Θ t = ((t : ℂ) ^ l) • Θ₀ ((t : ℂ)⁻¹)

theorem MeromorphicAtInfinityC.eventually_eq_zero {Θ : ℝ → F} (hΘ : MeromorphicAtInfinityC Θ)
    (h : FasterThanPowers Θ) : ∀ᶠ t in atTop, Θ t = 0
```

The paper: "a map `Θ` on an interval `(t₀, ∞)` is meromorphic at infinity if `Θ(t) = t^l Θ₀(1/t)`
for an integer `l` and a map `Θ₀` that is holomorphic near `0`. Such a map vanishes identically if
it tends to `0` faster than every power of `1/t`."

| The paper | Lean | Effect |
|---|---|---|
| `Θ` on an interval `(t₀, ∞)` | `Θ : ℝ → F`, the equation asked for all large real `t` | the same class of maps near infinity |
| "an integer `l`" | `l : ℕ` | the same: a negative exponent is covered by `l = 0` with `s^n Θ₀(s)` in the place of `Θ₀` (by compiling, `Chk1.lean`, example (3)). The header of this file does not say it; the header of the real-variable file does |
| "`Θ₀` holomorphic near `0`" | `Θ₀ : ℂ → F`, `AnalyticAt ℂ Θ₀ 0` | the same |
| values in `ℂ^{1×d_out}` | any complex normed space `F` | Lean more general |
| "vanishes identically" | "`Θ(t) = 0` for all large `t`" | Lean says less in the letter. It is all that an equation for large `t` can give, and the paper uses it so: "`𝓛_0(t) = 0` for large `t`, and then for all `t ≥ 1`, because it is holomorphic near `[1, ∞)`" |

`FasterThanPowers f` is `t^m ‖f(t)‖ → 0` for every natural `m` (`fasterThanPowers_iff`, true by
definition): the paper's "tends to `0` faster than every power of `1/t`".

**Lemma D.9.** Lean:

```
theorem eventually_eq_zero_of_millsRatioC_smul_add {ω ω' : ℂ} (hω : 0 < ω.re) {Θ₁ Θ₂ : ℝ → F}
    (h₁ : MeromorphicAtInfinityC Θ₁) (h₂ : MeromorphicAtInfinityC Θ₂)
    (h : FasterThanPowers fun t : ℝ =>
      millsRatioC (ω * (t : ℂ) + ω' / (t : ℂ)) • Θ₁ t + Θ₂ t) :
    (∀ᶠ t in atTop, Θ₁ t = 0) ∧ ∀ᶠ t in atTop, Θ₂ t = 0
```

| Clause of the paper | Lean | Same? |
|---|---|---|
| "`z(t) = ω t + ω'/t` with `ω, ω' ∈ ℂ` and `Re ω > 0`" | `ω ω' : ℂ`, `0 < ω.re`, the argument `ω * t + ω' / t` | yes |
| "`Θ₁` and `Θ₂` meromorphic at infinity, with values in `ℂ^{1×d_out}`" | `MeromorphicAtInfinityC`, values in any complex normed space | yes; Lean more general |
| "`Θ₁(t) mr(z(t)) + Θ₂(t)` tends to `0` faster than every power of `1/t` as `t → +∞`" | `FasterThanPowers` of `mr(z(t)) • Θ₁ t + Θ₂ t` | yes |
| "then `Θ₁ = 0` and `Θ₂ = 0`" | both vanish for all large `t` | as above |

Where Lean is stronger: the values may lie in any complex normed space, and the maps need to have
the form `t^l Θ₀(1/t)` for large `t` only. Where Lean is weaker: the conclusion is for all large
`t`. Nothing else differs. I read the proof: it follows the paper's (a component by a functional
from Hahn–Banach; `1/t` as `w S₁(w)` with `w = 1/z` and the explicit `S₁(w) = 2ω/(1 + √(1 −
4ωω'w²))`; uniqueness of the asymptotic expansion; `l! ≤ (2l−1)!!` against the radius of
convergence).

**What the proof of Lemma D.19 needs.** (By reading the paper's proof and `gelu_path_unit`.)

- Lemma D.8 (i) at complex `z`: `δ_j = φ(z_j) z_j mr(z_j)`, `δ'_j = φ(z_j)(mr(z_j) − z_j)`. Lean:
  `sub_geluC`, `one_sub_deriv_geluC`.
- Lemma D.8 (ii) for `m = 0`: `|mr(z_j)| ≤ 1/Re z_j`. Lean: `norm_millsRatioC_le`.
- Lemma D.9 with `z_j(t) = (√d/2)(t νc_j + (1/t) ν̄c_j)`, that is `ω = (√d/2) νc_j`, `ω' = ω̄`,
  `Re ω = (√d/2) ξc_j > 0`, and with `Θ₁ = z_j 𝓛_j + 𝓛'_j`, `Θ₂ = −z_j 𝓛'_j`. Lean has every
  complex `ω'`; by compiling (`Chk1.lean`, example (4)) the lemma applies to the curve `unitPath ω`
  as it stands. In `gelu_path_unit` it is used with `Θ₁(t) = (c₀/t) z_j(t) a(1/t) + b(1/t)` and
  `Θ₂(t) = −z_j(t) b(1/t)`, which are the paper's two maps up to the factors of the change of
  variables.
- "for large `t`, hence for all `t ≥ 1`": the continuation along `[1, ∞)`. Lean has it inside
  `gelu_path_zero` and `gelu_path_unit` (a private lemma: a map analytic at the real points of
  `[0, 1]` in `s = 1/t` that vanishes for small `s > 0` vanishes on `(0, 1]`).

So Lean has all that the proof uses, and no step of the proof asks for the conclusion of Lemma D.9
on a given interval.

### Check 3. The replacement of the power series (48)

**Verdict: the three statements are true as written, also in the degenerate cases; the hypotheses
of `gelu_path_unit` are what the paper's proof has at that point; its conclusion is (50).**

**(a) The estimate on a ball.** Lean (`Generic/HolomorphicBall.lean`):

```
theorem norm_sub_sub_fderiv_le_of_analyticOnNhd_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {f : E → F} {r M : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 r)) (hM : ∀ x ∈ Metric.ball (0 : E) r, ‖f x‖ ≤ M)
    {x y w : E} (hx : ‖x‖ ≤ r / 8) (hy : ‖y‖ ≤ r / 8) (hw : ‖w‖ ≤ r / 8) :
    ‖f (x + y + w) - f x - fderiv ℂ f 0 y‖
      ≤ 16 * M * (‖w‖ / r + ‖y‖ / r * (‖x‖ / r + ‖y‖ / r))
```

True: proved (by compiling), and by hand: `f` is `2M/r`-Lipschitz on the ball of radius `3r/8`
(Cauchy's estimate with radius `r/2`), `𝐃f` is bounded by `2M/r` on the ball of radius `r/2` and so
`16M/r²`-Lipschitz on the ball of radius `r/4` (radius `r/8`), and the three differences
`f(x+y+w) − f(x+y)`, `f(x+y) − f(x) − 𝐃f(x)y`, `𝐃f(x)y − 𝐃f(0)y` are at most `2M‖w‖/r`,
`16M‖y‖²/r²`, `16M‖x‖‖y‖/r²`. Degenerate cases: for a space `E` with the one point `0` it reads
`0 ≤ 0`; every `r > 0` is allowed; `hM` at `x = 0` forces `M ≥ 0`, so no negative `M` makes it
empty; `f` is differentiable at `0`, so `fderiv ℂ f 0` is the true derivative.

It is enough for the proof. The paper bounds "the sum of any set of terms" of (48) and uses three
sets; each is one case of the estimate, with `f = Ψ(s, ·)`:

| Paper | The sum of terms | Case of the estimate |
|---|---|---|
| Step 1 | all terms with at least one factor | `x = y = 0`, `w = X(t)`: `‖f(X) − f(0)‖ ≤ 16M‖X‖/r` |
| Step 2 | all terms other than the two of unit `j`, given `𝓛_0 = 0` | `x = 0`, `y = X_j`, `w` the entries of the other units |
| Step 4 | the terms with a factor outside `A = {j_1, …, j_{i−1}}`, other than the two of unit `j` | `x = X_A`, `y = X_j`, `w` the entries of the units outside `A ∪ {j}`, with `f(X_A) = 0` |

No convergence of a series is needed. With the sup norm on `(ι → ℂ) × (ι → ℂ)` the ball is a
polydisc in `δ` and in `δ'`; the paper's polydisc is in `δ` only (it uses that `𝓛` is affine in
`δ'`), and a bounded `δ'` is all that the proof needs, since `δ'(t) → 0`.

**(b) `gelu_path_zero` and `gelu_path_unit`.** Lean (`Depth/GeluPathSeparation.lean`; elaborated
forms printed by compiling, `Chk1.lean`):

```
noncomputable def unitPath (ω : ℂ) (t : ℝ) : ℂ := ω * (t : ℂ) + (starRingEnd ℂ) ω / (t : ℂ)

noncomputable def geluGap (c₀ : ℝ) (ω : ι → ℂ) (t : ℝ) : (ι → ℂ) × (ι → ℂ) :=
  (fun i => ((c₀ / t : ℝ) : ℂ) * (unitPath (ω i) t - geluC (unitPath (ω i) t)),
    fun i => 1 - deriv geluC (unitPath (ω i) t))

theorem gelu_path_zero (ω : ι → ℂ) (hω : ∀ i, |(ω i).im| < (ω i).re) (c₀ : ℝ)
    (Ψ : ℂ × ((ι → ℂ) × (ι → ℂ)) → F) {r : ℝ} (hr : 0 < r)
    (hΨ : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x : (ι → ℂ) × (ι → ℂ), ‖x‖ ≤ r →
      AnalyticAt ℂ Ψ ((s : ℂ), x))
    (h47 : ∀ᶠ t : ℝ in atTop, Ψ (((t : ℂ))⁻¹, geluGap c₀ ω t) = 0) :
    ∀ s : ℝ, 0 < s → s ≤ 1 → Ψ ((s : ℂ), 0) = 0

theorem gelu_path_unit [DecidableEq ι] (ω : ι → ℂ) (hω : ∀ i, |(ω i).im| < (ω i).re) {c₀ : ℝ}
    (hc₀ : c₀ ≠ 0) (Ψ : ℂ × ((ι → ℂ) × (ι → ℂ)) → F) {r : ℝ} (hr : 0 < r)
    (hΨ : … the same …) (h47 : … the same …)
    (A : Set ι) (j : ι) (hjA : j ∉ A)
    (hrate : ∀ i, i ∉ A → i ≠ j →
      (ω j).re ^ 2 - (ω j).im ^ 2 < (ω i).re ^ 2 - (ω i).im ^ 2)
    (hA : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ x : (ι → ℂ) × (ι → ℂ), ‖x‖ ≤ r →
      (∀ i, i ∉ A → x.1 i = 0 ∧ x.2 i = 0) → Ψ ((s : ℂ), x) = 0) :
    ∀ s : ℝ, 0 < s → s ≤ 1 →
      fderiv ℂ (fun x : (ι → ℂ) × (ι → ℂ) => Ψ ((s : ℂ), x)) 0 (Pi.single j 1, 0) = 0 ∧
      fderiv ℂ (fun x : (ι → ℂ) × (ι → ℂ) => Ψ ((s : ℂ), x)) 0 (0, Pi.single j 1) = 0
```

(`ι` is a finite type, `F` a complex Banach space.)

True as written: both are proved (by compiling). I read both proofs; they are the paper's
argument. The degenerate cases:

- *No hidden unit* (`ι` empty). `gelu_path_zero` then says: `Ψ(1/t, 0) = 0` for large `t` gives
  `Ψ(s, 0) = 0` on `(0, 1]`. By compiling (`Chk1.lean`, example (5)). `gelu_path_unit` takes a unit
  `j`, so `ι` is not empty there.
- *`A` is all units but `j`* (Step 4 for the last unit): `hrate` asks nothing; the proof takes
  `γ = ρ_min`, the paper's "`γ = r_{j_1}` if `i = q`".
- *`A = ∅`*: `hA` is `Ψ(s, 0) = 0` on `(0, 1]`, the conclusion of `gelu_path_zero`.
- *`r` small*: any `r > 0`; the proofs use `‖X(t)‖ ≤ r/8` for large `t` only.
- *`s = 0`*: `hΨ` asks analyticity at `s = 0` too (this is "meromorphic at infinity"); `hA` and
  the conclusions are for `0 < s ≤ 1`, that is `t ≥ 1`. Nothing is claimed at `s = 0`.
- *`c₀ = 0`* is allowed in `gelu_path_zero` (then `x(t) = 0`) and excluded in `gelu_path_unit`,
  which needs it to pass from `(c₀/t) z_j a = 0` to `a = 0`.
- *Values of total functions*: `geluGap` at `t ≤ 0` is not used (the hypothesis is for large `t`);
  `deriv geluC` is the true derivative (`geluC` is entire); `fderiv ℂ (Ψ(s, ·)) 0` in the
  conclusion is the true derivative, since `hΨ` makes `Ψ(s, ·)` analytic at `0`. So the conclusion
  is not true for the empty reason that a derivative does not exist.
- *The hypotheses can hold together*: for `Ψ = 0`; and for the map `Ψ` of
  `Depth/StepZeroGeluPath.lean` built from any pair `Z, η` with (16), where `hΨ` and `h47` are
  proved (`analyticAt_psi_poly_gzp`, `psi_path_gzp`), the symmetry directions included.

**(c) The hypotheses of `gelu_path_unit` against the paper's proof.** In the proof, `ω_i =
(√d/2)(ξc_i + iξ'c_i)`, `c₀ = 2/√d`, `s = 1/t`, and `t² Ψ(1/t, (c₀δ/t, δ')) = 𝓛(z(t) − δ, 1 − δ';
n(t))`.

| Lean | The paper at that point | Same? |
|---|---|---|
| `hω`: `\|Im ω_i\| < Re ω_i` | (P2), first inequality, for `ξ ∈ P`: `\|ξ'c_j\| < ξc_j`; it gives (44) and `r_j > 0` | yes |
| `unitPath (ω i) t = ω_i t + ω̄_i/t` | `z_j(t) = n(t)c_j = (√d/2)(t νc_j + (1/t) ν̄c_j)`, `ξ, ξ', c_j` real | yes |
| the rate `(Re ω_i)² − (Im ω_i)²` | `(d/4) r_i`, `r_i = (ξc_i)² − (ξ'c_i)²` | yes |
| `hrate`: the rate of `j` is smaller than that of every other unit outside `A` | Step 2: "`r_j < r_i` for all `i ≠ j`" (`A = ∅`); Step 4: `r_{j_1} < ⋯ < r_{j_q}`, `A = {j_1, …, j_{i−1}}`, `j = j_i` | yes |
| `hA`: `Ψ(s, x) = 0` for `0 < s ≤ 1` and `x` in the polydisc with entries only in `A` | Step 2: Step 1, `𝓛_0(t) = 0` for all `t ≥ 1`. Step 4: "If the rows `δ` and `δ'` vanish outside the entries `j_1, …, j_{i−1}`, then […] `𝓛°(z − δ, 1 − δ'; n) = 0`" | yes; Lean asks it in the polydisc only, the paper has it wherever `(z − δ)V ∈ C_κ` |
| `h47`: `Ψ(1/t, (c₀δ(t)/t, δ'(t))) = 0` for all large `t` | (47), for all `t ≥ 1` | yes; Lean asks less |
| `hΨ`: `Ψ` analytic at `(s, x)` for real `s ∈ [0, 1]`, `‖x‖ ≤ r` | three facts: "the map `(δ, δ') ↦ 𝓛(…)` is holomorphic in the rows `δ` with `\|δ_j\| ≤ ϱt` and affine in the row `δ'`" (in `x = c₀δ/t` the polydisc `\|x_j\| ≤ c₀ϱ` does not depend on `t`); "every coefficient is meromorphic at infinity" (`s = 0`); "holomorphic near `[1, ∞)`" (`0 < s ≤ 1`) | yes |
| (no hypothesis) the bound `M` of `Ψ` | "on the rows `u + iu' ∈ C_{3κ/4}` with `‖u‖ = 1`, `𝐃𝓑` and `𝐃_θ𝓑` are bounded" | Lean gets `M` from `hΨ`: `Ψ` is continuous on the compact set `[0, 1] × {‖x‖ ≤ r}` |
| `γ = min(γ₁, ρ_min)` in the proof | "`γ = min(r_j, min_{i≠j}(r_i − r_j))`"; "`γ = min(r_{j_1}, r_{j_{i+1}} − r_j)`" | yes |

**(d) The conclusion.** With `t² Ψ(1/t, (c₀δ/t, δ')) = 𝓛(z(t) − δ, 1 − δ'; n(t))`, the derivative of
`Ψ(s, ·)` at `0` along `(e_j, 0)` is `−(c₀t)⁻¹ 𝓛_j(t)` and along `(0, e_j)` it is `−t⁻² 𝓛'_j(t)`,
at `t = 1/s` (by hand: `δ = t x/c₀`, and `𝓛_j`, `𝓛'_j` are the derivatives in `w̃_j = z_j − δ_j`
and `w̃'_j = 1 − δ'_j`). The factors are not zero, so the conclusion is "`𝓛'_j(t) = 0` and
`𝓛_j(t) = 0` for all `t ≥ 1`", the paper's (50): both coefficients of the slowest unit vanish.
Steps 2 and 4 of the paper then use (50) at `t = 1`; so does Lean (`gelu_path_step_unit` calls
`gelu_path_unit … 1 one_pos le_rfl`).

---------------------------------------------------------------------------------------------------

## Part 2: the statements, file by file

### Verdict table

"Proved": the copy of the file compiles in `/home/claude/audit9a/` and the statement depends on
`propext`, `Classical.choice`, `Quot.sound` only (`Chk2.lean`).

| Paper | Lean | File | Verdict | Difference |
|---|---|---|---|---|
| `φ(z) = e^{−z²/2}/√(2π)`, `z ∈ ℂ` | `gaussPdfC` | `MillsC` | SAME | — |
| `mr(z) = √(π/2) e^{z²/2}(1 − erf(z/√2))`, `z ∈ ℂ` | `millsRatioC` | `MillsC` | SAME | Defined by the integral `∫_0^∞ e^{−zu−u²/2} du` of the paper's proof of Lemma D.8 (ii). That it is the paper's `mr`: Check 1. |
| "GELU is `σ(z) = (z/2)(1 + erf(z/√2))`, which is entire" | `geluC`, `differentiable_geluC`, `analyticAt_geluC`, `geluC_ofReal` | `MillsC` | SAME | Defined by the first formula of Lemma D.8 (i); see Check 1. Proved. |
| (helpers) | `gaussPdfC_ofReal`, `gaussPdfC_ne_zero`, `integrableOn_millsRatioC`, `deriv_geluC_ofReal` | `MillsC` | — | `φ` at real `z`; `φ(z) ≠ 0` (the paper divides by `φ(z_j)`); the integral exists for every `z`; `σ'` at real `z` is `Φ + zφ`. True. Proved. |
| Proof of Lemma D.8: "Both sides are entire" | `hasDerivAt_millsRatioC` | `MillsC` | PART | Also the formula `mr' = z mr − 1`, which the paper does not write. Proved. |
| Proof of Lemma D.8 (ii): "for real `z`, `mr(z) = e^{z²/2} ∫_z^∞ e^{−y²/2} dy`, and the substitution `y = z + u` gives `mr(z) = ∫_0^∞ e^{−zu−u²/2} du`" | `millsRatioC_ofReal` | `MillsC` | SAME | As: at real `x` the integral is `(1 − Φ(x))/φ(x)`. Proved. |
| Lemma D.8 (i), first formula | `geluC` (definition), `sub_geluC` | `MillsC` | SAME | True by definition in Lean; `sub_geluC` is `δ(z) = z − σ(z) = φ(z) z mr(z)`, the form of the proof of Lemma D.19. Proved. |
| Lemma D.8 (i), second formula | `hasDerivAt_geluC`, `one_sub_deriv_geluC` | `MillsC` | SAME | At every complex `z`. `one_sub_deriv_geluC` is `δ'(z) = 1 − σ'(z) = φ(z)(mr(z) − z)`. Proved. |
| Lemma D.8 (ii) | `norm_millsRatioC_sub_sum_le` | `MillsCExpansion` | SAME | Check 2. Proved. |
| Lemma D.8 (ii), `m = 0` ("`\|mr(z_j)\| ≤ 1/Re z_j`", proof of Lemma D.19) | `norm_millsRatioC_le` | `MillsCExpansion` | SAME | Proved. |
| "meromorphic at infinity" | `MeromorphicAtInfinityC` | `MillsAtInfinityC` | SAME | `l` a natural number; the equation for large `t`; values in any complex normed space. Check 2. |
| "Such a map vanishes identically if it tends to `0` faster than every power of `1/t`" | `MeromorphicAtInfinityC.eventually_eq_zero` | `MillsAtInfinityC` | LEAN WEAKER in the letter | "vanishes for all large `t`"; this is what the paper's proofs use. Proved. |
| Lemma D.9 | `eventually_eq_zero_of_millsRatioC_smul_add` | `MillsAtInfinityC` | SAME, with "`Θ = 0`" as "for all large `t`" | Complex `ω`, `ω'`, `Re ω > 0`, as in the paper; values in any complex normed space. Proved. |
| Proof of Lemma D.19, "The path": `z_j(t) = n(t) c_j` | `unitPath` | `GeluOnPath` | SAME | `ω t + ω̄/t` with `ω = (√d/2)(ξc_j + iξ'c_j)`. |
| (44), `Re z_j ≥ √d ξc_j > 0` and `\|Im z_j\| ≤ Re z_j` | `unitPath_re`, `unitPath_im` | `GeluOnPath` | LEAN STRONGER | The equalities `Re z = Re ω (t + 1/t)`, `Im z = Im ω (t − 1/t)`; the paper's two inequalities follow for `t ≥ 1` and `\|Im ω\| < Re ω` (a private lemma has them). Proved. |
| (44), `Re z_j² = d(ξc_j)² + (d/4)(t − t⁻¹)² r_j` | `unitPath_sq_re` | `GeluOnPath` | SAME | For `t > 0`. Proved. |
| Step 2: "`φ(z_j)`, whose absolute value is a constant times `e^{−(d/8)(t−t⁻¹)² r_j}` by (44)" | `norm_gaussPdfC_unitPath` | `GeluOnPath` | SAME | With the constant `e^{−2(Re ω)²}/√(2π)`. Proved. |
| (45), first bound | `norm_sub_geluC_unitPath_le` | `GeluOnPath` | SAME | `e^{−2(Re ω)²} = e^{−d(ξc_j)²/2}`. Proved. |
| (45), second bound, "with a constant `κ`" | `norm_one_sub_deriv_geluC_unitPath_le` | `GeluOnPath` | SAME | `κ = 1/(2 Re ω) + 2 Re ω`. Proved. |
| "The expansion": "by Cauchy's estimates on the polydisc of (46) […] the sum of any set of its terms is at most a power of `t` times `e^{−(d/8)(t−t⁻¹)² r}`" | `norm_sub_sub_fderiv_le_of_analyticOnNhd_ball` | `HolomorphicBall` | DIFFERENT in form, true | One estimate on a ball in the place of the power series; it covers the three sums of terms that the proof uses. Check 3 (a). Proved. |
| "The expansion": the rows `δ(t)`, `δ'(t)` | `geluGap` | `GeluPathSeparation` | SAME | The point `(c₀δ(t)/t, δ'(t))`; the factor `c₀/t` is Lean's change of variables. |
| Step 1: "By (48), `𝓛_0(t)` tends to `0` faster than every power of `1/t`. It is meromorphic at infinity, so `𝓛_0(t) = 0` for large `t`, and then for all `t ≥ 1`" | `gelu_path_zero` | `GeluPathSeparation` | PART, true | For a map `Ψ` given with its analyticity; no network. Check 3. Proved. |
| Steps 2 and 4, up to (50) | `gelu_path_unit` | `GeluPathSeparation` | PART, true | The same; one statement for both steps, with the set `A`. Check 3. Proved. |

### (a) Are the statements true as written?

Yes, all 25 (by compiling). Beyond Check 3 I looked for statements that would be true for an
empty reason, by reading:

- `norm_millsRatioC_sub_sum_le`: `z ≠ 0` and `Re z ≠ 0` follow from `Re z > 0`, so no division by
  zero hides in the statement. For `m = 0` the sum is empty and the bound is `1/Re z`.
- `unitPath_re`, `unitPath_im` take `0 < t` and do not use it (the compiler warns "unused
  variable"): the two equalities hold for every real `t`, with Lean's `1/0 = 0`. Harmless.
  `unitPath_sq_re` and `norm_gaussPdfC_unitPath` need `t ≠ 0` and take `0 < t`.
- (45): the hypotheses `|Im ω| < Re ω` and `t ≥ 1` can hold; by a computation (400 random `ω`,
  `t`, with `t = 1` among them) the largest ratio of `|δ|` to its bound is 0.40 and of `|δ'|` to
  its bound 0.07, and the formulas (44) and for `|φ(z(t))|` hold to `10⁻¹⁴`.
- `MeromorphicAtInfinityC` holds for the zero map and for every `t ↦ t^l Θ₀(1/t)`; Lemma D.9 is
  not empty (its hypothesis holds for `Θ₁ = Θ₂ = 0`, and the statement says that this is the only
  case, for large `t`).

### (b) Do the docstrings say honestly what part of the paper each piece is?

Yes, with one wrong factor in a comment. By reading every file header and every docstring of a
public statement.

- **The wrong factor** (`Depth/GeluPathSeparation.lean`, header, lines 61-62): "These are
  `(t c₀)⁻¹ t⁻² 𝓛_j` and `t⁻² 𝓛'_j` up to sign, at `t = 1/s`." With the header's own
  normalization (`𝓛 = t² Ψ`, `x = c₀δ/t`) the first is `(t c₀)⁻¹ 𝓛_j`, equally `(t/c₀) t⁻² 𝓛_j`;
  the second is right. See Check 3 (d). The factor is not zero either way, so nothing follows
  from the slip.
- `Activations/MillsC.lean`: says that `mr` and GELU are defined by the integral and by the first
  formula of (i), that Mathlib has no error function, and why `geluC` is the paper's GELU. Right.
- `Activations/MillsAtInfinityC.lean`: says that `t` stays real, that `Θ₀` is holomorphic at `0`,
  that the values lie in a complex normed space and that "`Θ = 0`" is "for all large `t`". It does
  not say that `l` is a natural number (the header of `Activations/MillsAtInfinity.lean` says it
  for the real form).
- `Activations/GeluOnPath.lean`: gives the dictionary `ω = (√d/2)(ξc_j + iξ'c_j)`,
  `d(ξc_j)² = 4(Re ω)²`, `(d/4) r_j = (Re ω)² − (Im ω)²`, and the constant `κ`. Right (by hand).
  "The statements below are (44) and (45)": the first two clauses of (44) are public as
  equalities, not as the paper's inequalities.
- `Generic/HolomorphicBall.lean`: says that the estimate stands for the three sums of terms
  "without the power series". Right. "With the sup norm on `ℂ^q × ℂ^q`, a ball is the paper's
  polydisc": the paper's polydisc is in `δ` only; see Check 3 (a).
- `Depth/GeluPathSeparation.lean`: "The form here" states the change of variables, that `Ψ` is
  taken as given "and no network", and which step is which statement. Right, except the factor.

### (c) Do the pieces fit the file that uses them?

Yes. By reading `Depth/StepZeroGeluPath.lean`, and by compiling: `gelu_path_step_zero`,
`gelu_path_step_zero_real`, `gelu_path_step_unit` depend on the three standard axioms only
(`Chk1.lean`, against the `lp` library), so every hypothesis of the pieces is discharged there.

- The map: `psi_gzp`, with `t² Ψ(1/t, (x, y)) = 𝓛(λ(m(1/t)W − x), 1 − y; ż(n(t)))`, `λ = √d t/2`,
  `n(t) = λ m(1/t)` (`psi_identity_gzp`). With `c₀ = 2/√d`, `λ c₀/t = 1`, so `x = c₀δ/t` gives
  `λ(m(1/t)W − x) = n(t)W − δ = z(t) − δ` (by hand).
- `ω`: `omega_gzp W ξ ξ' j = (√d/2)(ξc_j + iξ'c_j)`; `hω` from the first inequality of (P2)
  (`omega_im_lt_gzp`); the entries of `n(t)W` are `unitPath (ω_j) t` (`path_entry_gzp`, with
  `unitPath_re`, `unitPath_im`).
- `r`: `rad_gzp = κ‖ξWV‖/(8(1 + ∑_j ‖a_j‖))`. The paper's `ϱ` gives `c₀ϱ = κ‖ξWV‖/(8 ∑_j ‖a_j‖)`
  in the variable `x`; Lean's radius is a little smaller (the `1 +` avoids a division by zero).
- `hΨ`: `analyticAt_psi_poly_gzp`, from the cone (the second inequality of (P2)) and
  `HolomorphicOnCone geluC`.
- `h47`: `psi_path_gzp`, for every `t ≥ 1`, from Lemma D.15 (`blockLHSC_pathMatrix_eq_zero` with
  `geluC_ofReal`, `analyticAt_geluC`), the cone on the path (the third inequality of (P2), with
  `norm_sub_geluC_unitPath_le`) and `σ(n(t)W) = λ(m W − c₀δ(t)/t)`, `σ'(n(t)W) = 1 − δ'(t)`
  (`path_gelu_gzp`).
- `gelu_path_zero` is used for all `s ∈ (0, 1]` (`psi_zero_gzp`, then `gelu_path_step_zero` for
  all `t ≥ 1`); `gelu_path_unit` is used with the caller's `A`, `j`, `hrate` (multiplied by `d/4`)
  and `hA` (through the identity), at `s = 1`.
- Lemma D.19 itself (`claimZero_castSucc_gelu`, `Depth/StepZeroGelu.lean`) and the other files of
  the GELU case are not in this part; I did not compare them.

---------------------------------------------------------------------------------------------------

## What the authors should know

Nothing false, vacuous or drifted. In order of weight:

1. **One docstring has a wrong factor.** `Depth/GeluPathSeparation.lean`, header, lines 61-62:
   "`(t c₀)⁻¹ t⁻² 𝓛_j`" should be "`(t c₀)⁻¹ 𝓛_j`". A comment only; no statement depends on it.
   (I changed nothing.)
2. **Two rows of the index are out of date** (lines 315 and 318): they say that the complex
   variable of Lemma D.8 and complex `ω`, `ω'` of Lemma D.9 "are not stated". They are stated now
   (rows 207 to 209). See the corrections.
3. **GELU at complex arguments is a definition by a formula, and it is the right function.**
   Lean cannot write `erf`; `geluC` is `z − φ(z) z mr(z)` with `mr` the integral of the paper's
   proof. It is entire and is `z Φ(z)` on the real line, and I compiled that an entire function
   with these values on the real line is `geluC`. So every statement about `geluC`, and
   `HolomorphicOnCone geluC`, is about the paper's GELU.
4. **"`Θ = 0`" in Lemma D.9 is "`Θ(t) = 0` for all large `t`" in Lean**, as in the real form that
   an earlier reader compared. The paper's definition gives an equation near infinity, and its
   proof of Lemma D.19 says "for large `t`, hence for all `t ≥ 1`" each time. If the authors want
   the paper to match, "vanishes identically" and "`Θ₁ = 0` and `Θ₂ = 0`" could read "for all
   large `t`". Not an error.
5. **The power series (48) is not needed.** Lean proves Step 1 and (50) from one estimate for a
   bounded holomorphic map on a ball, used three times, with no series and no convergence. The
   paper's sentence "the sum of any set of its terms is at most …" is more than its proof uses.
   Not an error; the paper may keep it.
6. **Small things in Lean, harmless:** `unitPath_re` and `unitPath_im` take a hypothesis `0 < t`
   that they do not use; the header of `Activations/MillsAtInfinityC.lean` does not say that the
   exponent `l` is a natural number.

## Corrections for `STATEMENTS.md` (lines at `18543e5`; the same line numbers at `91bc064`)

None corrects a wrong claim about what is proved.

1. **Lines 84-86** ("Not yet compared by such a reader"): after this audit, remove
   `Activations/MillsC.lean`, `Activations/MillsCExpansion.lean`,
   `Activations/MillsAtInfinityC.lean`, `Generic/HolomorphicBall.lean`,
   `Activations/GeluOnPath.lean`, `Depth/GeluPathSeparation.lean` from the list (compared here, 31
   public names: none false, vacuous or changed in meaning). The other files of the list are not
   part of this audit.
2. **Line 315** (Lemma D.8 for a real variable): "The complex variable of the paper is not
   stated" is no longer true. Write "The complex variable of the paper: rows of
   `Activations/MillsC.lean` and `Activations/MillsCExpansion.lean`".
3. **Line 318** (Lemma D.9 for real `ω`): "Complex `ω`, `ω'` are not stated" is no longer true.
   Write "Complex `ω`, `ω'`: row of `Activations/MillsAtInfinityC.lean`".
4. **Line 209** (Lemma D.9, complex): add "the exponent `l` is a natural number (the paper: an
   integer; a negative one is covered by `l = 0`)" and "values in any complex normed space", as
   line 317 does for the real form.
5. **Line 207**: "on the real line they are the real Mills ratio and the real GELU" may name them:
   "`(1 − Φ(x))/φ(x)` (`millsRatio`) and `x Φ(x)` (`gelu`)". It may add that the paper's formulas
   with `erf` are not Lean statements and that `geluC` is the paper's GELU because an entire
   function is determined by its values on the real line. Optional.
6. **Line 211**: "real and imaginary part of `z(t)`" may say "(the first two clauses of (44) as
   equalities)". Optional.
7. **Line 212**: "the unit `j ∉ A` has the smallest rate outside `A`" may say "a strictly smaller
   rate than every other unit outside `A`", and add "`c₀ ≠ 0`" and "for `s ∈ (0, 1]`" for the
   second statement. Optional.

## What I could not check

- I did not build the library. The six files I compiled myself, as copies; their imports
  (`Activations/FarFromZero`, `Activations/MillsAtInfinity`, `SkipsLean/Imports`, Mathlib) and, for
  `Chk1.lean`, `Depth/StepZeroGeluPath` come from the compiled library of `/home/claude/lp`, built
  by its owner. Its sources are the same as those of `lw` for the files I named; some of its
  compiled files were copied from another worktree (their build log says so), and I did not check
  that each was compiled from exactly the present source.
- The paper's formulas with `erf` are not Lean statements. That `millsRatioC` and `geluC` are the
  paper's functions rests on: the definitions of the real `gaussCdf`, `millsRatio`, `gelu` (by
  reading), the two uniqueness statements (by compiling), and a floating-point check.
- Of `Depth/StepZeroGeluPath.lean` I read the header, the definitions of `Ψ`, `ω`, `r` and the
  lines that call the pieces; I did not compare its three public statements with the paper (they
  are not in this part), and I did not read its other private lemmas.
- `HolomorphicOnCone`, `suffixC`, `blockLHSC`, Lemma D.15 in Lean: I relied on the eighth audit
  (part B) for their comparison with the paper and read only how `geluC` enters.
- The computations are floating-point checks at random points (40 complex `z`; 2100 cases of
  Lemma D.8 (ii); 400 points of the path).
- Of the paper I read Appendix D.5 from "GELU and the Mills ratio" to Lemma D.9 and Appendix D.6;
  not the rest, for this audit.

## Files of this audit (`/home/claude/audit9a/`)

- `scratch/Chk1.lean`: the elaborated statements, `#print axioms` for the 25 theorems and for the
  three statements of `Depth/StepZeroGeluPath.lean`, and five examples; against the `lp` library.
- `scratch/Chk2.lean`: the same without `StepZeroGeluPath`, against my compiled copies.
- `scratch/Chk3.lean`: the two uniqueness statements (an entire function with the values of `gelu`,
  of `millsRatio`, on the real line is `geluC`, `millsRatioC`).
- `snap/`: the six sources and `STATEMENTS.md` at `18543e5` (`git archive`). `build/`: my compiled
  copies of the six files, and links to the compiled files of `lp` for everything else.
- `py/check_mills.py`: the computations.
