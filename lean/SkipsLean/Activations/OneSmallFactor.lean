import SkipsLean.Activations.MillsAtInfinity
import SkipsLean.Activations.GateFar

/-!
# "One small factor" for GELU and for SiLU

Paper (dimension): Appendix D.5, proof of Lemma D.12, "One small factor, `α = 1_j`". "With
`y = t |ξ c_j|`, (36) is `L_j + s_j L'_j δ'(y)/δ(y) → 0`. For GELU and GeGLU blocks,
`δ'(y)/δ(y) = (mr(y) − y)/(y mr(y))` and `y mr(y) ≤ 1`, so
`(y L_j + s_j L'_j) mr(y) − s_j y L'_j → 0` faster than every power of `1/t`. By (a), the maps
`y L_j + s_j L'_j` and `y L'_j` are meromorphic at infinity. By Lemma D.9 with `z(t) = |ξ c_j| t`
both vanish, so `L'_j = 0` and `L_j = 0`. For SwiGLU blocks, `y δ'(y)/δ(y) = 1 − y + δ(y)`, and
`δ(y)` tends to `0` faster than every power of `1/t`, so
`f(t) = |ξ c_j| t L_j(t) + s_j (1 − |ξ c_j| t) L'_j(t)` tends to `0` faster than every power of
`1/t` as `t → +∞`. By (a), `f` is meromorphic at infinity, so `f(t) = 0` for large `t`, and then for
all `t ∈ ℝ`, because `f` is real-analytic on `ℝ`. By (30), `L_j` is odd in `t` and `L'_j` is even.
So `0 = f(t) − f(−t) = −2 s_j |ξ c_j| t L'_j(t)`: `L'_j = 0`, and then `L_j = 0`."

Stated here without the network, in the variable `s = 1/t`: `a` and `b` are real-analytic at `0`
(they stand for the two coefficients, up to powers of `t` and signs), `u = |ξ c_j| > 0`, and
`ν(t) = t δ'(t u)/δ(t u)` with `δ(y) = y − σ(y)`, `δ'(y) = 1 − σ'(y)`. If
`a(1/t) + ν(t) b(1/t)` tends to `0` faster than every power of `1/t`, then `b` vanishes near `0`:
for GELU by Lemma D.9; for SiLU if `a` and `b` are even near `0`, which is what the parity (30)
gives in this variable.
-/

namespace Skips

open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **"One small factor" for GELU** (by Lemma D.9). -/
theorem one_small_factor_gelu {u : ℝ} (hu : 0 < u) {a b : ℝ → F} (ha : AnalyticAt ℝ a 0)
    (hb : AnalyticAt ℝ b 0)
    (h : FasterThanPowers fun t : ℝ =>
      a (1 / t) + (t * (1 - geluDeriv (t * u)) / (t * u - gelu (t * u))) • b (1 / t)) :
    ∀ᶠ s in 𝓝 (0 : ℝ), b s = 0 := by
  sorry

/-- **"One small factor" for SiLU** (by parity): here `a` and `b` are even near `0`. -/
theorem one_small_factor_silu {u : ℝ} (hu : 0 < u) {a b : ℝ → F} (ha : AnalyticAt ℝ a 0)
    (hb : AnalyticAt ℝ b 0) (heven : ∀ᶠ s in 𝓝 (0 : ℝ), a (-s) = a s ∧ b (-s) = b s)
    (h : FasterThanPowers fun t : ℝ =>
      a (1 / t) + (t * (1 - siluDeriv (t * u)) / (t * u - silu (t * u))) • b (1 / t)) :
    ∀ᶠ s in 𝓝 (0 : ℝ), b s = 0 := by
  sorry

end Skips
