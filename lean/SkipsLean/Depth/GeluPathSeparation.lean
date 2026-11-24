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
  the entries of unit `j` vanish, for `s ∈ (0, 1]`. These are `(t c₀)⁻¹ 𝓛_j` and `t⁻² 𝓛'_j`
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

omit [CompleteSpace F] in
/-- (a) `Ψ` is bounded on the compact set of the points `(s, x)` with `s ∈ [0, 1]` real and
`‖x‖ ≤ r`, since it is continuous there. -/
private lemma exists_bound_gps (Ψ : ℂ × ((ι → ℂ) × (ι → ℂ)) → F) {r : ℝ}
    (hΨ : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x : (ι → ℂ) × (ι → ℂ), ‖x‖ ≤ r →
      AnalyticAt ℂ Ψ ((s : ℂ), x)) :
    ∃ M, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x : (ι → ℂ) × (ι → ℂ), ‖x‖ ≤ r →
      ‖Ψ ((s : ℂ), x)‖ ≤ M := by
  let g : ℝ × ((ι → ℂ) × (ι → ℂ)) → ℂ × ((ι → ℂ) × (ι → ℂ)) := fun p => ((p.1 : ℂ), p.2)
  have hg : Continuous g := (Complex.continuous_ofReal.comp continuous_fst).prodMk continuous_snd
  have hK : IsCompact (g '' (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall 0 r)) :=
    (isCompact_Icc.prod (isCompact_closedBall 0 r)).image hg
  have hc : ContinuousOn Ψ (g '' (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall 0 r)) := by
    rintro _ ⟨⟨s, x⟩, ⟨⟨hs0, hs1⟩, hx⟩, rfl⟩
    exact (hΨ s hs0 hs1 x (mem_closedBall_zero_iff.1 hx)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc
  exact ⟨M, fun s hs0 hs1 x hx =>
    hM _ ⟨(s, x), ⟨⟨hs0, hs1⟩, mem_closedBall_zero_iff.2 hx⟩, rfl⟩⟩

omit [CompleteSpace F] in
/-- (a) For real `s ∈ [0, 1]`, `x ↦ Ψ(s, x)` is holomorphic on the ball of radius `r`. -/
private lemma analyticOnNhd_slice_gps (Ψ : ℂ × ((ι → ℂ) × (ι → ℂ)) → F) {r : ℝ}
    (hΨ : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x : (ι → ℂ) × (ι → ℂ), ‖x‖ ≤ r →
      AnalyticAt ℂ Ψ ((s : ℂ), x)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    AnalyticOnNhd ℂ (fun x : (ι → ℂ) × (ι → ℂ) => Ψ ((s : ℂ), x)) (Metric.ball 0 r) := by
  intro x hx
  exact (hΨ s hs0 hs1 x (mem_ball_zero_iff.1 hx).le).comp₂ analyticAt_const analyticAt_id

/-- (a) The estimate of `HolomorphicBall.lean` for `x ↦ Ψ(s, x)`, `s ∈ [0, 1]` real. -/
private lemma estimate_gps (Ψ : ℂ × ((ι → ℂ) × (ι → ℂ)) → F) {r M : ℝ} (hr : 0 < r)
    (hΨ : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x : (ι → ℂ) × (ι → ℂ), ‖x‖ ≤ r →
      AnalyticAt ℂ Ψ ((s : ℂ), x))
    (hM : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x : (ι → ℂ) × (ι → ℂ), ‖x‖ ≤ r →
      ‖Ψ ((s : ℂ), x)‖ ≤ M) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {x y w : (ι → ℂ) × (ι → ℂ)} (hx : ‖x‖ ≤ r / 8) (hy : ‖y‖ ≤ r / 8) (hw : ‖w‖ ≤ r / 8) :
    ‖Ψ ((s : ℂ), x + y + w) - Ψ ((s : ℂ), x)
        - fderiv ℂ (fun x : (ι → ℂ) × (ι → ℂ) => Ψ ((s : ℂ), x)) 0 y‖
      ≤ 16 * M * (‖w‖ / r + ‖y‖ / r * (‖x‖ / r + ‖y‖ / r)) :=
  norm_sub_sub_fderiv_le_of_analyticOnNhd_ball hr (analyticOnNhd_slice_gps Ψ hΨ hs0 hs1)
    (fun x hx => hM s hs0 hs1 x (mem_ball_zero_iff.1 hx).le) hx hy hw

/-- (a) For real `s ∈ [0, 1]`, `σ ↦ 𝐃(Ψ(σ, ·))(0) v` is holomorphic at `σ = s`: near `s` it is
`σ ↦ 𝐃Ψ(σ, 0)(0, v)`, by the chain rule. -/
private lemma analyticAt_fderiv_slice_gps (Ψ : ℂ × ((ι → ℂ) × (ι → ℂ)) → F) {r : ℝ}
    (hr : 0 < r)
    (hΨ : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x : (ι → ℂ) × (ι → ℂ), ‖x‖ ≤ r →
      AnalyticAt ℂ Ψ ((s : ℂ), x)) (v : (ι → ℂ) × (ι → ℂ)) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    AnalyticAt ℂ (fun σ : ℂ => fderiv ℂ (fun x : (ι → ℂ) × (ι → ℂ) => Ψ (σ, x)) 0 v)
      (s : ℂ) := by
  have h0 : AnalyticAt ℂ Ψ ((s : ℂ), 0) := hΨ s hs0 hs1 0 (by simp [hr.le])
  -- `σ ↦ 𝐃Ψ(σ, 0)(0, v)` is holomorphic at `s`
  have h2 : AnalyticAt ℂ (fderiv ℂ Ψ) ((s : ℂ), 0) := h0.fderiv
  have h3 : AnalyticAt ℂ (fun σ : ℂ => fderiv ℂ Ψ (σ, 0)) (s : ℂ) :=
    h2.comp₂ analyticAt_id analyticAt_const
  have h1 : AnalyticAt ℂ (fun σ : ℂ => fderiv ℂ Ψ (σ, 0) (0, v)) (s : ℂ) := by
    have h := AnalyticAt.comp (f := fun σ : ℂ => fderiv ℂ Ψ (σ, 0)) (x := (s : ℂ))
      ((ContinuousLinearMap.apply ℂ F ((0 : ℂ), v)).analyticAt _) h3
    exact h
  refine h1.congr ?_
  -- near `s`, `Ψ` is holomorphic at `(σ, 0)`, and the chain rule applies
  have h4 : ∀ᶠ σ in 𝓝 (s : ℂ), AnalyticAt ℂ Ψ (σ, 0) :=
    ((continuous_id.prodMk continuous_const).tendsto (s : ℂ)).eventually
      h0.eventually_analyticAt
  filter_upwards [h4] with σ hσ
  have h5 : HasFDerivAt (fun x : (ι → ℂ) × (ι → ℂ) => Ψ (σ, x))
      ((fderiv ℂ Ψ (σ, 0)).comp (ContinuousLinearMap.inr ℂ ℂ ((ι → ℂ) × (ι → ℂ)))) 0 :=
    hσ.differentiableAt.hasFDerivAt.comp (0 : (ι → ℂ) × (ι → ℂ))
      (hasFDerivAt_prodMk_right σ 0)
  rw [h5.fderiv]
  rfl

/-- (c) Continuation: a map `g` holomorphic at the real points of `[0, 1]` with `g(1/t) = 0` for
all large `t` vanishes at the real points of `(0, 1]`. -/
private lemma eq_zero_of_eventually_gps {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {g : ℂ → G} (hg : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → AnalyticAt ℂ g (s : ℂ))
    (h : ∀ᶠ t : ℝ in atTop, g ((t : ℂ))⁻¹ = 0) :
    ∀ s : ℝ, 0 < s → s ≤ 1 → g (s : ℂ) = 0 := by
  -- the real map `s ↦ g(s)` is real-analytic on `[0, 1]`
  have hgr : AnalyticOnNhd ℝ (fun s : ℝ => g (s : ℂ)) (Set.Icc 0 1) := by
    intro s hs
    have h1 : AnalyticAt ℝ g (s : ℂ) := (hg s hs.1 hs.2).restrictScalars
    have h2 := h1.comp (Complex.ofRealCLM.analyticAt s)
    exact h2
  -- it vanishes on `(0, 1/T)`
  obtain ⟨T, hT⟩ := eventually_atTop.1 h
  have hT1 : (1 : ℝ) ≤ max T 1 := le_max_right _ _
  have hT0 : (0 : ℝ) < max T 1 := lt_of_lt_of_le one_pos hT1
  have hzero : ∀ s : ℝ, 0 < s → s < 1 / max T 1 → g (s : ℂ) = 0 := by
    intro s hs0 hs1
    have h1 : max T 1 < s⁻¹ := by
      rw [lt_inv_comm₀ hT0 hs0]
      simpa only [one_div] using hs1
    have h2 := hT s⁻¹ ((le_max_left _ _).trans h1.le)
    rwa [Complex.ofReal_inv, inv_inv] at h2
  have hev : (fun s : ℝ => g (s : ℂ)) =ᶠ[𝓝 (1 / (2 * max T 1))] 0 := by
    have hmem : Set.Ioo 0 (1 / max T 1) ∈ 𝓝 (1 / (2 * max T 1)) :=
      Ioo_mem_nhds (by positivity)
        (one_div_lt_one_div_of_lt hT0 (by linarith))
    filter_upwards [hmem] with s hs
    exact hzero s hs.1 hs.2
  have hmem : 1 / (2 * max T 1) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one (by positivity)]; linarith⟩
  intro s hs0 hs1
  exact hgr.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Icc hmem hev
    ⟨hs0.le, hs1⟩

/-- `ρ ↦ e^{−ρ u/2}` is antitone, `u = (t − 1/t)²`. -/
private lemma exp_le_exp_of_le_gps {a b : ℝ} (t : ℝ) (hab : a ≤ b) :
    Real.exp (-(b * (t - 1 / t) ^ 2 / 2)) ≤ Real.exp (-(a * (t - 1 / t) ^ 2 / 2)) := by
  rw [Real.exp_le_exp]
  have := sq_nonneg (t - 1 / t)
  nlinarith

/-- `e^{−(a+b) u/2} = e^{−a u/2} e^{−b u/2}`. -/
private lemma exp_add_gps (a b t : ℝ) :
    Real.exp (-((a + b) * (t - 1 / t) ^ 2 / 2))
      = Real.exp (-(a * (t - 1 / t) ^ 2 / 2)) * Real.exp (-(b * (t - 1 / t) ^ 2 / 2)) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- (b) A map at most `A t^N e^{−γ (t − 1/t)²/2}` with `γ > 0` tends to `0` faster than every
power: `(t − 1/t)² ≥ t − 2` for `t ≥ 1`. -/
private lemma fasterThanPowers_of_le_gps {G : Type*} [NormedAddCommGroup G] {f : ℝ → G}
    {A γ : ℝ} {N : ℕ} (hγ : 0 < γ)
    (hf : ∀ᶠ t in atTop, ‖f t‖ ≤ A * t ^ N * Real.exp (-(γ * (t - 1 / t) ^ 2 / 2))) :
    FasterThanPowers f := by
  refine fasterThanPowers_of_le_pow_mul_exp (A := |A| * Real.exp γ) (κ := γ / 2) (N := N)
    (p := 1)
    (by positivity) le_rfl ?_
  filter_upwards [hf, eventually_ge_atTop 1] with t ht ht1
  have hu : t - 2 ≤ (t - 1 / t) ^ 2 := by
    have h1 : 1 / t ≤ 1 := by rw [div_le_one (by linarith)]; exact ht1
    have h2 : t - 1 ≤ t - 1 / t := by linarith
    nlinarith [mul_le_mul h2 h2 (by linarith) (by linarith), sq_nonneg (t - 3 / 2)]
  have he : Real.exp (-(γ * (t - 1 / t) ^ 2 / 2))
      ≤ Real.exp γ * Real.exp (-(γ / 2 * t ^ 1)) := by
    rw [← Real.exp_add, Real.exp_le_exp, pow_one]
    nlinarith [mul_le_mul_of_nonneg_left hu hγ.le]
  have htN : 0 ≤ t ^ N := pow_nonneg (by linarith) N
  calc ‖f t‖ ≤ A * t ^ N * Real.exp (-(γ * (t - 1 / t) ^ 2 / 2)) := ht
    _ ≤ |A| * t ^ N * (Real.exp γ * Real.exp (-(γ / 2 * t ^ 1))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self A) htN) he (Real.exp_pos _).le
          (mul_nonneg (abs_nonneg A) htN)
    _ = |A| * Real.exp γ * t ^ N * Real.exp (-(γ / 2 * t ^ 1)) := by ring

/-- The rate `(Re ω)² − (Im ω)²` is positive when `|Im ω| < Re ω`. -/
private lemma rate_pos_gps {w : ℂ} (hw : |w.im| < w.re) : 0 < w.re ^ 2 - w.im ^ 2 := by
  obtain ⟨h1, h2⟩ := abs_lt.1 hw
  nlinarith

/-- A positive lower bound of finitely many positive numbers. -/
private lemma exists_pos_le_gps (P : ι → Prop) (g : ι → ℝ) (hg : ∀ i, P i → 0 < g i) :
    ∃ m, 0 < m ∧ ∀ i, P i → m ≤ g i := by
  by_cases h : {i | P i}.Nonempty
  · obtain ⟨i₀, hi₀, hmin⟩ := Set.exists_min_image {i | P i} g (Set.toFinite _) h
    exact ⟨g i₀, hg i₀ hi₀, fun i hi => hmin i hi⟩
  · exact ⟨1, one_pos, fun i hi => absurd ⟨i, hi⟩ h⟩

/-- (b) The entries of `X(t)` decay: `‖x_i(t)‖, ‖y_i(t)‖ ≤ C t e^{−ρ_i u/2}` for `t ≥ 1`. -/
private lemma exists_entry_bound_gps (ω : ι → ℂ) (hω : ∀ i, |(ω i).im| < (ω i).re) (c₀ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ i,
      ‖(geluGap c₀ ω t).1 i‖
          ≤ C * t * Real.exp (-(((ω i).re ^ 2 - (ω i).im ^ 2) * (t - 1 / t) ^ 2 / 2)) ∧
        ‖(geluGap c₀ ω t).2 i‖
          ≤ C * t * Real.exp (-(((ω i).re ^ 2 - (ω i).im ^ 2) * (t - 1 / t) ^ 2 / 2)) := by
  let κ : ι → ℝ := fun i => 1 / (2 * (ω i).re) + 2 * (ω i).re
  have hsum : 0 ≤ ∑ i, |κ i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨|c₀| + ∑ i, |κ i|, by positivity, fun t ht i => ⟨?_, ?_⟩⟩
  · -- `‖x_i‖ ≤ |c₀/t| e^{−2 (Re ω_i)²} e^{−ρ_i u/2} ≤ |c₀| e^{−ρ_i u/2}`
    have h1 := norm_sub_geluC_unitPath_le (hω i) ht
    have hE := Real.exp_pos (-(((ω i).re ^ 2 - (ω i).im ^ 2) * (t - 1 / t) ^ 2 / 2))
    have he : Real.exp (-(2 * (ω i).re ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (ω i).re])
    have hct : |c₀ / t| ≤ |c₀| := by
      rw [abs_div, abs_of_pos (by linarith : 0 < t)]
      exact div_le_self (abs_nonneg _) ht
    show ‖((c₀ / t : ℝ) : ℂ) * (unitPath (ω i) t - geluC (unitPath (ω i) t))‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |c₀ / t| * ‖unitPath (ω i) t - geluC (unitPath (ω i) t)‖
        ≤ |c₀| * (1 * Real.exp (-(((ω i).re ^ 2 - (ω i).im ^ 2) * (t - 1 / t) ^ 2 / 2))) :=
          mul_le_mul hct (h1.trans (mul_le_mul_of_nonneg_right he hE.le)) (norm_nonneg _)
            (abs_nonneg _)
      _ ≤ _ := by
          nlinarith [mul_nonneg (mul_nonneg (abs_nonneg c₀) (sub_nonneg.2 ht)) hE.le,
            mul_nonneg (mul_nonneg hsum (by linarith : (0 : ℝ) ≤ t)) hE.le]
  · -- `‖y_i‖ ≤ κ_i t e^{−ρ_i u/2}`
    have h2 := norm_one_sub_deriv_geluC_unitPath_le (hω i) ht
    have hE := Real.exp_pos (-(((ω i).re ^ 2 - (ω i).im ^ 2) * (t - 1 / t) ^ 2 / 2))
    have hκ : κ i ≤ |c₀| + ∑ i, |κ i| :=
      (le_abs_self _).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (κ j))
        (Finset.mem_univ i)).trans (le_add_of_nonneg_left (abs_nonneg _)))
    show ‖1 - deriv geluC (unitPath (ω i) t)‖ ≤ _
    exact h2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hκ (by linarith)) hE.le)

/-- A point of `(ι → ℂ) × (ι → ℂ)` whose entries are at most `K` has norm at most `K`. -/
private lemma norm_le_of_entries_gps {v : (ι → ℂ) × (ι → ℂ)} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ i, ‖v.1 i‖ ≤ K ∧ ‖v.2 i‖ ≤ K) : ‖v‖ ≤ K :=
  norm_prod_le_iff.2 ⟨(pi_norm_le_iff_of_nonneg hK).2 fun i => (h i).1,
    (pi_norm_le_iff_of_nonneg hK).2 fun i => (h i).2⟩

/-- The part of `X(t)` made of the entries of the units in `S`. -/
private noncomputable def gapPart_gps (c₀ : ℝ) (ω : ι → ℂ) (S : Set ι) (t : ℝ) :
    (ι → ℂ) × (ι → ℂ) :=
  (S.indicator (geluGap c₀ ω t).1, S.indicator (geluGap c₀ ω t).2)

omit [Fintype ι] in
/-- An entry of an indicator is at most the entry. -/
private lemma norm_indicator_le_gps (S : Set ι) (f : ι → ℂ) (i : ι) :
    ‖S.indicator f i‖ ≤ ‖f i‖ := by
  by_cases hi : i ∈ S
  · rw [Set.indicator_of_mem hi]
  · rw [Set.indicator_of_notMem hi, norm_zero]
    exact norm_nonneg _

/-- A part of `X(t)` is at most `X(t)`. -/
private lemma norm_gapPart_le_gps (c₀ : ℝ) (ω : ι → ℂ) (S : Set ι) (t : ℝ) :
    ‖gapPart_gps c₀ ω S t‖ ≤ ‖geluGap c₀ ω t‖ :=
  norm_le_of_entries_gps (norm_nonneg _) fun i =>
    ⟨(norm_indicator_le_gps S _ i).trans ((norm_le_pi_norm _ i).trans (norm_fst_le _)),
      (norm_indicator_le_gps S _ i).trans ((norm_le_pi_norm _ i).trans (norm_snd_le _))⟩

/-- (b) A part of `X(t)` made of units of rates at least `ρ` is at most `C t e^{−ρ u/2}`. -/
private lemma norm_gapPart_le_exp_gps (c₀ : ℝ) (ω : ι → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t : ℝ, 1 ≤ t → ∀ i,
      ‖(geluGap c₀ ω t).1 i‖
          ≤ C * t * Real.exp (-(((ω i).re ^ 2 - (ω i).im ^ 2) * (t - 1 / t) ^ 2 / 2)) ∧
        ‖(geluGap c₀ ω t).2 i‖
          ≤ C * t * Real.exp (-(((ω i).re ^ 2 - (ω i).im ^ 2) * (t - 1 / t) ^ 2 / 2)))
    (S : Set ι) {ρ : ℝ} (hρ : ∀ i ∈ S, ρ ≤ (ω i).re ^ 2 - (ω i).im ^ 2) {t : ℝ} (ht : 1 ≤ t) :
    ‖gapPart_gps c₀ ω S t‖ ≤ C * t * Real.exp (-(ρ * (t - 1 / t) ^ 2 / 2)) := by
  have hCt : 0 ≤ C * t := mul_nonneg hC (by linarith)
  have hK : 0 ≤ C * t * Real.exp (-(ρ * (t - 1 / t) ^ 2 / 2)) :=
    mul_nonneg hCt (Real.exp_pos _).le
  refine norm_le_of_entries_gps hK fun i => ?_
  by_cases hi : i ∈ S
  · simp only [gapPart_gps, Set.indicator_of_mem hi]
    have hE := mul_le_mul_of_nonneg_left (exp_le_exp_of_le_gps t (hρ i hi)) hCt
    exact ⟨(hb t ht i).1.trans hE, (hb t ht i).2.trans hE⟩
  · simp only [gapPart_gps, Set.indicator_of_notMem hi, norm_zero]
    exact ⟨hK, hK⟩

/-- (b) `‖X(t)‖ ≤ C t e^{−ρ u/2}` for `t ≥ 1`, with `ρ > 0` the smallest rate. -/
private lemma exists_norm_geluGap_le_gps (ω : ι → ℂ) (hω : ∀ i, |(ω i).im| < (ω i).re)
    (c₀ : ℝ) :
    ∃ C ρ, 0 < ρ ∧ ∀ t : ℝ, 1 ≤ t →
      ‖geluGap c₀ ω t‖ ≤ C * t ^ 1 * Real.exp (-(ρ * (t - 1 / t) ^ 2 / 2)) := by
  obtain ⟨C, hC, hb⟩ := exists_entry_bound_gps ω hω c₀
  obtain ⟨ρ, hρ, hρle⟩ := exists_pos_le_gps (fun _ => True)
    (fun i => (ω i).re ^ 2 - (ω i).im ^ 2) (fun i _ => rate_pos_gps (hω i))
  refine ⟨C, ρ, hρ, fun t ht => ?_⟩
  have h := norm_gapPart_le_exp_gps c₀ ω hC hb Set.univ (ρ := ρ)
    (fun i _ => hρle i trivial) ht
  simp only [gapPart_gps, Set.indicator_univ] at h
  rw [pow_one]
  exact h

/-- (b) `X(t) → 0`: `‖X(t)‖ ≤ ε` for all large `t`. -/
private lemma eventually_norm_geluGap_le_gps (ω : ι → ℂ) (hω : ∀ i, |(ω i).im| < (ω i).re)
    (c₀ : ℝ) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ t in atTop, ‖geluGap c₀ ω t‖ ≤ ε := by
  obtain ⟨C, ρ, hρ, hX⟩ := exists_norm_geluGap_le_gps ω hω c₀
  have h : FasterThanPowers (geluGap c₀ ω) :=
    fasterThanPowers_of_le_gps hρ ((eventually_ge_atTop 1).mono hX)
  have h0 := (fasterThanPowers_iff _).1 h 0
  simp only [pow_zero, one_mul] at h0
  exact h0.eventually (eventually_le_nhds hε)

/-- **Lemma D.19, Step 1 (analytic part):** let `Ψ` be holomorphic at the points `(s, x)` with
`s ∈ [0, 1]` and `‖x‖ ≤ r`, and let `Ψ(1/t, (c₀ δ(t)/t, δ'(t))) = 0` for all large `t` (47). Then
`Ψ(s, 0) = 0` for every `s ∈ (0, 1]`. -/
theorem gelu_path_zero (ω : ι → ℂ) (hω : ∀ i, |(ω i).im| < (ω i).re) (c₀ : ℝ)
    (Ψ : ℂ × ((ι → ℂ) × (ι → ℂ)) → F) {r : ℝ} (hr : 0 < r)
    (hΨ : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x : (ι → ℂ) × (ι → ℂ), ‖x‖ ≤ r →
      AnalyticAt ℂ Ψ ((s : ℂ), x))
    (h47 : ∀ᶠ t : ℝ in atTop, Ψ (((t : ℂ))⁻¹, geluGap c₀ ω t) = 0) :
    ∀ s : ℝ, 0 < s → s ≤ 1 → Ψ ((s : ℂ), 0) = 0 := by
  -- (a) the bound `M`, (b) the decay of `X(t)`
  obtain ⟨M, hM⟩ := exists_bound_gps Ψ hΨ
  have hr8 : ‖(0 : (ι → ℂ) × (ι → ℂ))‖ ≤ r / 8 := by rw [norm_zero]; positivity
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 le_rfl zero_le_one 0 (by simp [hr.le]))
  obtain ⟨C, ρ, hρ, hX⟩ := exists_norm_geluGap_le_gps ω hω c₀
  have hsmall := eventually_norm_geluGap_le_gps ω hω c₀ (ε := r / 8) (by positivity)
  -- the estimate with `x = y = 0`, `w = X(t)`: `‖Ψ(1/t, 0)‖ ≤ 16 M ‖X(t)‖ / r`
  have hΘ : FasterThanPowers fun t : ℝ => Ψ (((t : ℂ))⁻¹, 0) := by
    refine fasterThanPowers_of_le_gps (A := 16 * M / r * C) (N := 1) hρ ?_
    filter_upwards [eventually_ge_atTop 1, hsmall, h47] with t ht1 hts h47t
    have hs0 : 0 ≤ t⁻¹ := inv_nonneg.2 (by linarith)
    have hest := estimate_gps Ψ hr hΨ hM hs0 (inv_le_one_of_one_le₀ ht1) hr8 hr8 hts
    simp only [zero_add, map_zero, sub_zero, Complex.ofReal_inv, h47t, zero_sub, norm_neg,
      norm_zero, zero_div, zero_mul, add_zero] at hest
    calc ‖Ψ (((t : ℂ))⁻¹, 0)‖ ≤ 16 * M * (‖geluGap c₀ ω t‖ / r) := hest
      _ ≤ 16 * M * (C * t ^ 1 * Real.exp (-(ρ * (t - 1 / t) ^ 2 / 2)) / r) := by
          gcongr
          exact hX t ht1
      _ = 16 * M / r * C * t ^ 1 * Real.exp (-(ρ * (t - 1 / t) ^ 2 / 2)) := by ring
  -- `t ↦ Ψ(1/t, 0)` is meromorphic at infinity, so it vanishes for large `t`; then (c)
  have hg : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → AnalyticAt ℂ (fun σ : ℂ => Ψ (σ, 0)) (s : ℂ) :=
    fun s hs0 hs1 =>
      (hΨ s hs0 hs1 0 (hr8.trans (by linarith))).comp₂ analyticAt_id analyticAt_const
  have hmer : MeromorphicAtInfinityC fun t : ℝ => Ψ (((t : ℂ))⁻¹, 0) := by
    refine ⟨0, fun σ => Ψ (σ, 0), ?_, Eventually.of_forall fun t => by simp⟩
    have h := hg 0 le_rfl zero_le_one
    rwa [Complex.ofReal_zero] at h
  exact eq_zero_of_eventually_gps hg (hmer.eventually_eq_zero hΘ)

omit [Fintype ι] in
/-- `X(t)` is the sum of its parts on `A`, on `{j}` and on the other units. -/
private lemma geluGap_split_gps (c₀ : ℝ) (ω : ι → ℂ) (A : Set ι) {j : ι} (hjA : j ∉ A)
    (t : ℝ) :
    geluGap c₀ ω t = gapPart_gps c₀ ω A t + gapPart_gps c₀ ω {j} t
      + gapPart_gps c₀ ω {i | i ∉ A ∧ i ≠ j} t := by
  classical
  ext i
  all_goals
    by_cases hiA : i ∈ A
    · have hij : i ≠ j := fun h => hjA (h ▸ hiA)
      simp [gapPart_gps, hiA, hij]
    · by_cases hij : i = j
      · subst hij
        simp [gapPart_gps, hiA]
      · simp [gapPart_gps, hiA, hij]

omit [Fintype ι] in
/-- The part of `X(t)` on the unit `j` is `x_j(t) (e_j, 0) + y_j(t) (0, e_j)`. -/
private lemma gapPart_single_gps [DecidableEq ι] (c₀ : ℝ) (ω : ι → ℂ) (j : ι) (t : ℝ) :
    gapPart_gps c₀ ω {j} t
      = (geluGap c₀ ω t).1 j • ((Pi.single j 1 : ι → ℂ), (0 : ι → ℂ))
        + (geluGap c₀ ω t).2 j • ((0 : ι → ℂ), (Pi.single j 1 : ι → ℂ)) := by
  ext i
  all_goals
    by_cases hij : i = j
    · subst hij
      simp [gapPart_gps]
    · simp [gapPart_gps, hij]

/-- Step 1, the arithmetic: the bound of the estimate is at most `K t² e^{−(ρ_j + γ) u/2}`. -/
private lemma step1_arith_gps {M r C t nA nj nC Ej Em Eg : ℝ} (hM : 0 ≤ M) (hr : 0 < r)
    (hC : 0 ≤ C) (ht : 1 ≤ t) (hEj : 0 ≤ Ej) (hEg : 0 ≤ Eg)
    (hjm : Ej * Em ≤ Eg) (hnC : nC ≤ C * t * Eg) (hj : nj ≤ C * t * Ej)
    (hj' : nj ≤ C * t * Em) (hA : nA ≤ C * t * Em) (hnj : 0 ≤ nj) (hnA : 0 ≤ nA) :
    16 * M * (nC / r + nj / r * (nA / r + nj / r))
      ≤ 16 * M / r * (C + 2 * C ^ 2 / r) * t ^ 2 * Eg := by
  have htt : t ≤ t ^ 2 := by nlinarith
  have hCt : 0 ≤ C * t := mul_nonneg hC (by linarith)
  -- `‖X_C‖ ≤ C t² E_{ρ_j+γ}`
  have hnC' : nC ≤ C * t ^ 2 * Eg :=
    hnC.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htt hC) hEg)
  -- `‖X_j‖ (‖X_A‖ + ‖X_j‖) ≤ 2 C² t² E_{ρ_j} E_{ρ_m} ≤ 2 C² t² E_{ρ_j+γ}`
  have hprod : nj * (nA + nj) ≤ 2 * C ^ 2 * t ^ 2 * Eg :=
    calc nj * (nA + nj) ≤ (C * t * Ej) * (C * t * Em + C * t * Em) :=
          mul_le_mul hj (add_le_add hA hj') (add_nonneg hnA hnj) (mul_nonneg hCt hEj)
      _ = 2 * C ^ 2 * t ^ 2 * (Ej * Em) := by ring
      _ ≤ 2 * C ^ 2 * t ^ 2 * Eg := mul_le_mul_of_nonneg_left hjm (by positivity)
  calc 16 * M * (nC / r + nj / r * (nA / r + nj / r))
      = 16 * M / r * (nC + nj * (nA + nj) / r) := by ring
    _ ≤ 16 * M / r * (C * t ^ 2 * Eg + 2 * C ^ 2 * t ^ 2 * Eg / r) :=
        mul_le_mul_of_nonneg_left (add_le_add hnC' (div_le_div_of_nonneg_right hprod hr.le))
          (div_nonneg (by linarith) hr.le)
    _ = 16 * M / r * (C + 2 * C ^ 2 / r) * t ^ 2 * Eg := by ring

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
  -- the rates: `ρ_m ≤ ρ_i` for all `i`, and `ρ_j + γ₁ ≤ ρ_i` for the other units outside `A`
  obtain ⟨ρm, hρm, hρmle⟩ := exists_pos_le_gps (fun _ => True)
    (fun i => (ω i).re ^ 2 - (ω i).im ^ 2) (fun i _ => rate_pos_gps (hω i))
  obtain ⟨γ₁, hγ₁, hγ₁le⟩ := exists_pos_le_gps (fun i => i ∉ A ∧ i ≠ j)
    (fun i => ((ω i).re ^ 2 - (ω i).im ^ 2) - ((ω j).re ^ 2 - (ω j).im ^ 2))
    (fun i hi => sub_pos.2 (hrate i hi.1 hi.2))
  have hγ : 0 < min γ₁ ρm := lt_min hγ₁ hρm
  -- (a) the bound `M`; (b) the entry bounds, and `‖X(t)‖ ≤ r/8` for large `t`
  obtain ⟨M, hM⟩ := exists_bound_gps Ψ hΨ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 le_rfl zero_le_one 0 (by simp [hr.le]))
  obtain ⟨C, hC, hb⟩ := exists_entry_bound_gps ω hω c₀
  have hsmall := eventually_norm_geluGap_le_gps ω hω c₀ (ε := r / 8) (by positivity)
  -- the derivatives `a(σ)`, `b(σ)` of `Ψ(σ, ·)` at `0` along the two entries of unit `j`
  obtain ⟨a, ha⟩ : ∃ a : ℂ → F, ∀ σ, a σ = fderiv ℂ (fun x : (ι → ℂ) × (ι → ℂ) => Ψ (σ, x)) 0
      ((Pi.single j 1 : ι → ℂ), (0 : ι → ℂ)) := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb'⟩ : ∃ b : ℂ → F, ∀ σ, b σ = fderiv ℂ (fun x : (ι → ℂ) × (ι → ℂ) => Ψ (σ, x)) 0
      ((0 : ι → ℂ), (Pi.single j 1 : ι → ℂ)) := ⟨_, fun _ => rfl⟩
  have haa : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → AnalyticAt ℂ a (s : ℂ) := fun s hs0 hs1 =>
    (analyticAt_fderiv_slice_gps Ψ hr hΨ _ hs0 hs1).congr
      (Eventually.of_forall fun σ => (ha σ).symm)
  have hba : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → AnalyticAt ℂ b (s : ℂ) := fun s hs0 hs1 =>
    (analyticAt_fderiv_slice_gps Ψ hr hΨ _ hs0 hs1).congr
      (Eventually.of_forall fun σ => (hb' σ).symm)
  -- Step 1: `‖x_j(t) a(1/t) + y_j(t) b(1/t)‖ ≤ K t² e^{−(ρ_j + γ) u/2}`
  have hD : ∀ᶠ t : ℝ in atTop,
      ‖(geluGap c₀ ω t).1 j • a ((t : ℂ))⁻¹ + (geluGap c₀ ω t).2 j • b ((t : ℂ))⁻¹‖
        ≤ 16 * M / r * (C + 2 * C ^ 2 / r) * t ^ 2
          * Real.exp (-(((ω j).re ^ 2 - (ω j).im ^ 2 + min γ₁ ρm) * (t - 1 / t) ^ 2 / 2)) := by
    filter_upwards [eventually_ge_atTop 1, hsmall, h47] with t ht1 hts h47t
    have hs0 : 0 ≤ t⁻¹ := inv_nonneg.2 (by linarith)
    have hs1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1
    have hXA := (norm_gapPart_le_gps c₀ ω A t).trans hts
    have hXj := (norm_gapPart_le_gps c₀ ω {j} t).trans hts
    have hXC := (norm_gapPart_le_gps c₀ ω {i | i ∉ A ∧ i ≠ j} t).trans hts
    have hest := estimate_gps Ψ hr hΨ hM hs0 hs1 hXA hXj hXC
    -- `Ψ(1/t, X_A) = 0` (the hypothesis on `A`) and `Ψ(1/t, X(t)) = 0` (47)
    have hAz : Ψ (((t⁻¹ : ℝ) : ℂ), gapPart_gps c₀ ω A t) = 0 :=
      hA t⁻¹ (inv_pos.2 (by linarith)) hs1 _ (hXA.trans (by linarith)) fun i hi =>
        ⟨Set.indicator_of_notMem hi _, Set.indicator_of_notMem hi _⟩
    -- `𝐃f_s(0) X_j = x_j a(s) + y_j b(s)`
    have hlin : fderiv ℂ (fun x : (ι → ℂ) × (ι → ℂ) => Ψ (((t⁻¹ : ℝ) : ℂ), x)) 0
        (gapPart_gps c₀ ω {j} t)
          = (geluGap c₀ ω t).1 j • a ((t : ℂ))⁻¹ + (geluGap c₀ ω t).2 j • b ((t : ℂ))⁻¹ := by
      rw [gapPart_single_gps, map_add, map_smul, map_smul, ha, hb', Complex.ofReal_inv]
    rw [← geluGap_split_gps c₀ ω A hjA t, hAz, hlin, Complex.ofReal_inv, h47t, sub_self,
      zero_sub, norm_neg] at hest
    refine hest.trans (step1_arith_gps
      (Ej := Real.exp (-(((ω j).re ^ 2 - (ω j).im ^ 2) * (t - 1 / t) ^ 2 / 2)))
      (Em := Real.exp (-(ρm * (t - 1 / t) ^ 2 / 2))) hM0 hr hC ht1 (Real.exp_pos _).le
      (Real.exp_pos _).le ?_ ?_ ?_ ?_ ?_ (norm_nonneg _) (norm_nonneg _))
    · -- `E_{ρ_j} E_{ρ_m} = E_{ρ_j+ρ_m} ≤ E_{ρ_j+γ}`
      rw [← exp_add_gps]
      exact exp_le_exp_of_le_gps t (by linarith [min_le_right γ₁ ρm])
    · exact norm_gapPart_le_exp_gps c₀ ω hC hb _ (fun i hi => by
        linarith [hγ₁le i hi, min_le_left γ₁ ρm]) ht1
    · exact norm_gapPart_le_exp_gps c₀ ω hC hb _ (fun i hi => by
        rw [Set.mem_singleton_iff.1 hi]) ht1
    · exact norm_gapPart_le_exp_gps c₀ ω hC hb _ (fun i _ => hρmle i trivial) ht1
    · exact norm_gapPart_le_exp_gps c₀ ω hC hb _ (fun i _ => hρmle i trivial) ht1
  -- Step 2: `x_j a + y_j b = φ(z) (mr(z) Θ₁(t) + Θ₂(t))`, `z = z_j(t)`
  obtain ⟨Θ₁, hΘ₁⟩ : ∃ Θ : ℝ → F, ∀ t, Θ t
      = (((c₀ / t : ℝ) : ℂ) * unitPath (ω j) t) • a ((t : ℂ))⁻¹ + b ((t : ℂ))⁻¹ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Θ₂, hΘ₂⟩ : ∃ Θ : ℝ → F, ∀ t, Θ t = (-unitPath (ω j) t) • b ((t : ℂ))⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have hdec : ∀ t : ℝ,
      (geluGap c₀ ω t).1 j • a ((t : ℂ))⁻¹ + (geluGap c₀ ω t).2 j • b ((t : ℂ))⁻¹
        = gaussPdfC (unitPath (ω j) t)
          • (millsRatioC (unitPath (ω j) t) • Θ₁ t + Θ₂ t) := by
    intro t
    show (((c₀ / t : ℝ) : ℂ) * (unitPath (ω j) t - geluC (unitPath (ω j) t))) • a ((t : ℂ))⁻¹
        + (1 - deriv geluC (unitPath (ω j) t)) • b ((t : ℂ))⁻¹ = _
    rw [sub_geluC, one_sub_deriv_geluC, hΘ₁, hΘ₂]
    module
  -- Step 3: dividing by `φ(z)`, `‖mr(z) Θ₁(t) + Θ₂(t)‖ ≤ K' t² e^{−γ u/2}`
  have hW : ∀ᶠ t : ℝ in atTop,
      ‖millsRatioC (unitPath (ω j) t) • Θ₁ t + Θ₂ t‖
        ≤ 16 * M / r * (C + 2 * C ^ 2 / r) * Real.sqrt (2 * Real.pi)
            / Real.exp (-(2 * (ω j).re ^ 2)) * t ^ 2
          * Real.exp (-(min γ₁ ρm * (t - 1 / t) ^ 2 / 2)) := by
    filter_upwards [hD, eventually_gt_atTop 0] with t hDt ht0
    rw [hdec, norm_smul, norm_gaussPdfC_unitPath (ω j) ht0,
      exp_add_gps ((ω j).re ^ 2 - (ω j).im ^ 2) (min γ₁ ρm) t] at hDt
    have he := Real.exp_pos (-(2 * (ω j).re ^ 2))
    have hEj := Real.exp_pos (-(((ω j).re ^ 2 - (ω j).im ^ 2) * (t - 1 / t) ^ 2 / 2))
    have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    refine le_of_mul_le_mul_left (hDt.trans_eq ?_) (by positivity)
    field_simp
  have hftp : FasterThanPowers fun t : ℝ =>
      millsRatioC (ω j * (t : ℂ) + (starRingEnd ℂ) (ω j) / (t : ℂ)) • Θ₁ t + Θ₂ t :=
    fasterThanPowers_of_le_gps hγ hW
  -- Step 4: `Θ₁`, `Θ₂` are meromorphic at infinity; Lemma D.9
  have ha0 : AnalyticAt ℂ a 0 := by
    have h := haa 0 le_rfl zero_le_one
    rwa [Complex.ofReal_zero] at h
  have hb0 : AnalyticAt ℂ b 0 := by
    have h := hba 0 le_rfl zero_le_one
    rwa [Complex.ofReal_zero] at h
  have hmer₁ : MeromorphicAtInfinityC Θ₁ := by
    refine ⟨0, fun σ => ((c₀ : ℂ) * (ω j + (starRingEnd ℂ) (ω j) * σ ^ 2)) • a σ + b σ,
      by fun_prop, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with t ht
    have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    rw [hΘ₁, pow_zero, one_smul]
    congr 2
    unfold unitPath
    push_cast
    field_simp
  have hmer₂ : MeromorphicAtInfinityC Θ₂ := by
    refine ⟨1, fun σ => (-(ω j + (starRingEnd ℂ) (ω j) * σ ^ 2)) • b σ, by fun_prop, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with t ht
    have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    rw [hΘ₂, smul_smul]
    congr 1
    unfold unitPath
    field_simp
  have hre : 0 < (ω j).re := lt_of_le_of_lt (abs_nonneg _) (hω j)
  obtain ⟨h₁, h₂⟩ := eventually_eq_zero_of_millsRatioC_smul_add hre hmer₁ hmer₂ hftp
  -- `z_j(t) ≠ 0`, as `Re z_j(t) > 0`
  have hz : ∀ t : ℝ, 0 < t → unitPath (ω j) t ≠ 0 := by
    intro t ht h0
    have h := unitPath_re (ω j) ht
    rw [h0, Complex.zero_re] at h
    have : 0 < (ω j).re * (t + 1 / t) := mul_pos hre (by positivity)
    linarith
  have hbz : ∀ᶠ t : ℝ in atTop, b ((t : ℂ))⁻¹ = 0 := by
    filter_upwards [h₂, eventually_gt_atTop 0] with t ht ht0
    rw [hΘ₂] at ht
    exact (smul_eq_zero.1 ht).resolve_left (neg_ne_zero.2 (hz t ht0))
  have haz : ∀ᶠ t : ℝ in atTop, a ((t : ℂ))⁻¹ = 0 := by
    filter_upwards [h₁, hbz, eventually_gt_atTop 0] with t ht hbt ht0
    rw [hΘ₁, hbt, add_zero] at ht
    have hq : ((c₀ / t : ℝ) : ℂ) * unitPath (ω j) t ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.2 (div_ne_zero hc₀ ht0.ne')) (hz t ht0)
    exact (smul_eq_zero.1 ht).resolve_left hq
  -- Step 5: by (c), `a(s) = b(s) = 0` for `s ∈ (0, 1]`
  intro s hs0 hs1
  rw [← ha (s : ℂ), ← hb' (s : ℂ)]
  exact ⟨eq_zero_of_eventually_gps haa haz s hs0 hs1,
    eq_zero_of_eventually_gps hba hbz s hs0 hs1⟩

end Skips
