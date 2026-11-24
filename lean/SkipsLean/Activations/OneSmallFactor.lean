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

/-- `1/t → 0` as `t → +∞`. -/
private lemma tendsto_one_div_atTop_osf : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
  simpa only [one_div] using tendsto_inv_atTop_zero

/-- A map whose values at `1/t` vanish for all large `t` and that is real-analytic at `0`
vanishes near `0`. -/
private lemma eventually_nhds_eq_zero_of_eventually_inv {b : ℝ → F} (hb : AnalyticAt ℝ b 0)
    (h : ∀ᶠ t in atTop, b (1 / t) = 0) : ∀ᶠ s in 𝓝 (0 : ℝ), b s = 0 := by
  -- the zero map tends to `0` faster than every power, and so does `b(1/t)`
  have h0 : FasterThanPowers fun _ : ℝ => (0 : F) := (fasterThanPowers_iff _).2 fun m => by
    simp only [norm_zero, mul_zero]
    exact tendsto_const_nhds
  exact eventually_nhds_eq_zero_of_fasterThanPowers hb
    (h0.congr (h.mono fun t ht => ht.symm))

/-- **"One small factor" for GELU** (by Lemma D.9). -/
theorem one_small_factor_gelu {u : ℝ} (hu : 0 < u) {a b : ℝ → F} (ha : AnalyticAt ℝ a 0)
    (hb : AnalyticAt ℝ b 0)
    (h : FasterThanPowers fun t : ℝ =>
      a (1 / t) + (t * (1 - geluDeriv (t * u)) / (t * u - gelu (t * u))) • b (1 / t)) :
    ∀ᶠ s in 𝓝 (0 : ℝ), b s = 0 := by
  -- `Θ₁(t) = u a(1/t) + b(1/t)` and `Θ₂(t) = t (−u b(1/t))` are meromorphic at infinity
  have hΘ₁ : MeromorphicAtInfinity fun t : ℝ => u • a (1 / t) + b (1 / t) :=
    ⟨0, fun s => u • a s + b s, (ha.const_smul (c := u)).add hb,
      Eventually.of_forall fun t => by rw [pow_zero, one_smul]⟩
  have hΘ₂ : MeromorphicAtInfinity fun t : ℝ => t ^ 1 • ((-u) • b (1 / t)) :=
    ⟨1, fun s => (-u) • b s, hb.const_smul (c := -u), Eventually.of_forall fun t => rfl⟩
  -- multiplied by `u mr(t u)`, which is at most `1/t ≤ 1`, the hypothesis becomes
  -- `mr(u t) (u a(1/t) + b(1/t)) − u t b(1/t)`, since `u mr(y) ν(t) = mr(y) − y` with `y = t u`
  have hfast : FasterThanPowers fun t : ℝ =>
      millsRatio (u * t) • (u • a (1 / t) + b (1 / t)) + t ^ 1 • ((-u) • b (1 / t)) := by
    refine (h.smul_of_le_pow (c := fun t => u * millsRatio (t * u)) (A := 1) (N := 0)
      ?_).congr ?_
    · filter_upwards [eventually_ge_atTop 1] with t ht
      have ht0 : 0 < t := by linarith
      have hy : 0 < t * u := mul_pos ht0 hu
      obtain ⟨hm, hle⟩ := millsRatio_pos_le hy
      rw [pow_zero, mul_one, abs_of_pos (mul_pos hu hm)]
      calc u * millsRatio (t * u) ≤ u * (1 / (t * u)) := mul_le_mul_of_nonneg_left hle hu.le
        _ = 1 / t := by field_simp
        _ ≤ 1 := (div_le_one ht0).2 ht
    · filter_upwards [eventually_gt_atTop 0] with t ht
      have hy : 0 < t * u := mul_pos ht hu
      obtain ⟨hδ, hδ'⟩ := gelu_gap_eq (t * u)
      obtain ⟨hm, -⟩ := millsRatio_pos_le hy
      have hP := gaussPdf_pos (t * u)
      have hm' := hm.ne'
      have hP' := hP.ne'
      have ht' := ht.ne'
      have hu' := hu.ne'
      -- `u mr(y) · t φ(y) (mr(y) − y) / (φ(y) y mr(y)) = mr(y) − y`
      have hsc : u * millsRatio (t * u) * (t * (1 - geluDeriv (t * u)) / (t * u - gelu (t * u)))
          = millsRatio (t * u) - t * u := by
        rw [hδ, hδ', ← mul_div_assoc, div_eq_iff (mul_ne_zero (mul_ne_zero hP' hy.ne') hm')]
        ring
      rw [mul_comm u t]
      calc (u * millsRatio (t * u)) •
            (a (1 / t) + (t * (1 - geluDeriv (t * u)) / (t * u - gelu (t * u))) • b (1 / t))
          = (u * millsRatio (t * u)) • a (1 / t) + (u * millsRatio (t * u) *
            (t * (1 - geluDeriv (t * u)) / (t * u - gelu (t * u)))) • b (1 / t) := by
            rw [smul_add, smul_smul]
        _ = millsRatio (t * u) • (u • a (1 / t) + b (1 / t)) + t ^ 1 • ((-u) • b (1 / t)) := by
            rw [hsc]
            module
  -- Lemma D.9: `Θ₂ = 0` for large `t`, so `b(1/t) = 0` for large `t`
  obtain ⟨-, h₂⟩ := eventually_eq_zero_of_millsRatio_smul_add hu hΘ₁ hΘ₂ hfast
  refine eventually_nhds_eq_zero_of_eventually_inv hb ?_
  filter_upwards [h₂, eventually_gt_atTop 0] with t ht ht0
  rw [smul_smul, smul_eq_zero] at ht
  exact ht.resolve_left (mul_ne_zero (pow_ne_zero 1 ht0.ne') (neg_ne_zero.2 hu.ne'))

/-- **"One small factor" for SiLU** (by parity): here `a` and `b` are even near `0`. -/
theorem one_small_factor_silu {u : ℝ} (hu : 0 < u) {a b : ℝ → F} (ha : AnalyticAt ℝ a 0)
    (hb : AnalyticAt ℝ b 0) (heven : ∀ᶠ s in 𝓝 (0 : ℝ), a (-s) = a s ∧ b (-s) = b s)
    (h : FasterThanPowers fun t : ℝ =>
      a (1 / t) + (t * (1 - siluDeriv (t * u)) / (t * u - silu (t * u))) • b (1 / t)) :
    ∀ᶠ s in 𝓝 (0 : ℝ), b s = 0 := by
  -- `b(1/t)` is bounded for large `t`
  have hbnd : ∀ᶠ t in atTop, ‖b (1 / t)‖ < ‖b 0‖ + 1 :=
    tendsto_one_div_atTop_osf.eventually
      (Filter.Tendsto.eventually_lt_const (lt_add_one _) hb.continuousAt.norm)
  -- `(δ(t u)/u) b(1/t)` tends to `0` faster than every power: `δ(y) ≤ y e^{−y}` for `y ≥ 2`
  have hD : FasterThanPowers fun t : ℝ => ((t * u - silu (t * u)) / u) • b (1 / t) := by
    refine fasterThanPowers_of_le_pow_mul_exp (A := ‖b 0‖ + 1) (κ := u) (N := 1) (p := 1) hu
      le_rfl ?_
    filter_upwards [eventually_ge_atTop (2 / u), hbnd] with t ht hbt
    have hy : 2 ≤ t * u := (div_le_iff₀ hu).1 ht
    obtain ⟨hlo, hup, -⟩ := silu_gap_bounds hy
    have hδ0 : 0 ≤ t * u - silu (t * u) := le_trans (by positivity) hlo
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hδ0 hu.le), pow_one]
    calc (t * u - silu (t * u)) / u * ‖b (1 / t)‖
        ≤ t * u * Real.exp (-(t * u)) / u * (‖b 0‖ + 1) :=
          mul_le_mul (div_le_div_of_nonneg_right hup hu.le) hbt.le (norm_nonneg _)
            (by positivity)
      _ = (‖b 0‖ + 1) * t * Real.exp (-(u * t)) := by
          rw [mul_comm t u]
          field_simp
  have hnegD : FasterThanPowers fun t : ℝ => -(((t * u - silu (t * u)) / u) • b (1 / t)) :=
    hD.mono (Eventually.of_forall fun t => (norm_neg _).le)
  -- subtracting and multiplying by `u/t`: `f(1/t)` tends to `0` faster than every power, with
  -- `f(s) = (u s) a(s) + (s − u) b(s)`, since `y δ'(y)/δ(y) = 1 − y + δ(y)`
  have hfast : FasterThanPowers fun t : ℝ =>
      (u * (1 / t)) • a (1 / t) + (1 / t - u) • b (1 / t) := by
    refine ((h.add hnegD).smul_of_le_pow (c := fun t => u / t) (A := u) (N := 0) ?_).congr ?_
    · filter_upwards [eventually_ge_atTop 1] with t ht
      have ht0 : 0 < t := by linarith
      rw [pow_zero, mul_one, abs_of_pos (div_pos hu ht0)]
      exact div_le_self hu.le ht
    · filter_upwards [eventually_gt_atTop 0] with t ht
      obtain ⟨hδ, hδ'⟩ := silu_gap_eq (t * u)
      have hE : 0 < 1 + Real.exp (t * u) := by positivity
      have hE' := hE.ne'
      have ht' := ht.ne'
      have hu' := hu.ne'
      have hsc : u / t * (t * (1 - siluDeriv (t * u)) / (t * u - silu (t * u))
          - (t * u - silu (t * u)) / u) = 1 / t - u := by
        rw [hδ, hδ']
        field_simp
        ring
      calc (u / t) • (a (1 / t) + (t * (1 - siluDeriv (t * u)) / (t * u - silu (t * u))) •
            b (1 / t) + -(((t * u - silu (t * u)) / u) • b (1 / t)))
          = (u / t) • a (1 / t) + (u / t * (t * (1 - siluDeriv (t * u)) / (t * u - silu (t * u))
            - (t * u - silu (t * u)) / u)) • b (1 / t) := by module
        _ = (u * (1 / t)) • a (1 / t) + (1 / t - u) • b (1 / t) := by rw [hsc, mul_one_div]
  -- so `f = 0` near `0`
  have hfa : AnalyticAt ℝ (fun s => (u * s) • a s + (s - u) • b s) 0 :=
    ((analyticAt_const.mul analyticAt_id).fun_smul ha).add
      ((analyticAt_id.sub analyticAt_const).fun_smul hb)
  have hf0 : ∀ᶠ s in 𝓝 (0 : ℝ), (u * s) • a s + (s - u) • b s = 0 :=
    eventually_nhds_eq_zero_of_fasterThanPowers hfa hfast
  -- and `f(−s) = 0` near `0`
  have hf0' : ∀ᶠ s in 𝓝 (0 : ℝ), (u * -s) • a (-s) + (-s - u) • b (-s) = 0 :=
    (continuous_neg.tendsto' (0 : ℝ) 0 neg_zero).eventually
      (p := fun s => (u * s) • a s + (s - u) • b s = 0) hf0
  -- with `a`, `b` even: `0 = f(s) + f(−s) = −2 u b(s)`
  filter_upwards [hf0, hf0', heven] with s h1 h2 ⟨ha', hb'⟩
  have e : (-2 * u) • b s
      = ((u * s) • a s + (s - u) • b s) + ((u * -s) • a (-s) + (-s - u) • b (-s)) := by
    rw [ha', hb']
    module
  rw [h1, h2, add_zero] at e
  exact (smul_eq_zero.1 e).resolve_left (by linarith)

end Skips
