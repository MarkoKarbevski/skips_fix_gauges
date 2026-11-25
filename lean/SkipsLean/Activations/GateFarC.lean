import SkipsLean.Activations.GateFar
import SkipsLean.Activations.MillsCExpansion

/-!
# A gate far from zero, at complex arguments

Paper (dimension): proof of Lemma D.11, "One gate. Let `z ∈ ℂ` with `Re z ≥ 2` and
`|Im z| ≤ ½ Re z`, so that `Re(z²) ≥ ¾ (Re z)²` and `|z| ≤ 2 Re z`. For GELU, by Lemma D.8,
`σ(z) − z = −φ(z) z mr(z)` and `|z mr(z)| ≤ |z|/Re z ≤ 2`, so `|σ(z) − z| ≤ e^{−(3/8)(Re z)²}`.
For SiLU, `σ(z) − z = −z/(1 + e^z)` and `|1 + e^z| ≥ ½ e^{Re z}`, so
`|σ(z) − z| ≤ 4 Re z e^{−Re z}`. Both gates are holomorphic at `z` and at `−z`, and
`σ(−z) = σ(z) − z`. So there is a number `κ_1 > 0` such that, for large `Re z`,
`|σ(z) − z| ≤ e^{−κ_1 (Re z)^p}` and `|σ(−z)| ≤ e^{−κ_1 (Re z)^p}`. (31)"

`GateFarC σ p` is (31) for a gate `σ` on the reals: `σ` has an extension to complex arguments
that is holomorphic at `z` and at `−z` and satisfies the two bounds, for all `z` in the sector
`|Im z| ≤ ½ Re z` with `Re z ≥ R`. It holds for GELU with `p = 2` (the extension `geluC` of
`Activations/MillsC.lean`) and for SiLU with `p = 1` (the extension `z/(1 + e^{−z})`). It is not
a notion of the paper; `GateFar` (`Activations/GateFar.lean`) is its twin on the reals.
-/

namespace Skips

/-- **Equation (31):** the gate `σ` has an extension `σc` to complex arguments such that, for a
number `R` and a number `κ > 0`, at every `z` with `Re z ≥ R` and `|Im z| ≤ ½ Re z`, `σc` is
holomorphic at `z` and at `−z`, `|σc(z) − z| ≤ e^{−κ (Re z)^p}` and `|σc(−z)| ≤ e^{−κ (Re z)^p}`. -/
def GateFarC (σ : ℝ → ℝ) (p : ℕ) : Prop :=
  ∃ σc : ℂ → ℂ, (∀ x : ℝ, σc (x : ℂ) = ((σ x : ℝ) : ℂ)) ∧ ∃ R κ : ℝ, 0 < κ ∧
    ∀ z : ℂ, R ≤ z.re → |z.im| ≤ z.re / 2 →
      AnalyticAt ℂ σc z ∧ AnalyticAt ℂ σc (-z) ∧
        ‖σc z - z‖ ≤ Real.exp (-(κ * z.re ^ p)) ∧ ‖σc (-z)‖ ≤ Real.exp (-(κ * z.re ^ p))

/-- Helper: in the sector `|Im z| ≤ ½ Re z` with `Re z ≥ 0`: `‖z‖ ≤ 2 Re z` and
`Re(z²) ≥ ¾ (Re z)²`. -/
private theorem sector_facts_gfc {z : ℂ} (hx : 0 ≤ z.re) (him : |z.im| ≤ z.re / 2) :
    ‖z‖ ≤ 2 * z.re ∧ 3 / 4 * z.re ^ 2 ≤ (z ^ 2).re := by
  constructor
  · calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 2 * z.re := by rw [abs_of_nonneg hx]; linarith
  · have h1 : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
      rw [pow_two, Complex.mul_re]; ring
    have h2 : z.im ^ 2 ≤ (z.re / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) him 2
    rw [h1]; nlinarith

/-- Helper: `‖φ(z)‖ = e^{−Re(z²)/2}/√(2π)`. -/
private theorem norm_gaussPdfC_gfc (z : ℂ) :
    ‖gaussPdfC z‖ = Real.exp (-((z ^ 2).re / 2)) / Real.sqrt (2 * Real.pi) := by
  unfold gaussPdfC
  rw [norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  congr 2
  simp [neg_div]

/-- Helper: GELU in the sector, `‖geluC z − z‖ ≤ e^{−(3/8)(Re z)²}`. -/
private theorem norm_geluC_sub_le_gfc {z : ℂ} (hx : 0 < z.re) (him : |z.im| ≤ z.re / 2) :
    ‖geluC z - z‖ ≤ Real.exp (-(3 / 8 * z.re ^ 2)) := by
  obtain ⟨hz, hsq⟩ := sector_facts_gfc hx.le him
  have hmr := norm_millsRatioC_le hx
  -- `‖z‖ ‖mr(z)‖ ≤ 2`
  have hzm : ‖z‖ * ‖millsRatioC z‖ ≤ 2 := by
    calc ‖z‖ * ‖millsRatioC z‖ ≤ (2 * z.re) * (1 / z.re) :=
          mul_le_mul hz hmr (norm_nonneg _) (by positivity)
      _ = 2 := by field_simp
  -- `‖φ(z)‖ ≤ e^{−(3/8)(Re z)²}/√(2π)`
  have hs0 : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hφ : ‖gaussPdfC z‖ ≤ Real.exp (-(3 / 8 * z.re ^ 2)) / Real.sqrt (2 * Real.pi) := by
    rw [norm_gaussPdfC_gfc]
    gcongr
    linarith
  -- `2 ≤ √(2π)`
  have hs : 2 ≤ Real.sqrt (2 * Real.pi) := by
    have h4 : (2 : ℝ) ^ 2 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    calc (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ _ := Real.sqrt_le_sqrt h4
  have hE := Real.exp_pos (-(3 / 8 * z.re ^ 2))
  rw [← neg_sub, norm_neg, sub_geluC, norm_mul, norm_mul, mul_assoc]
  calc ‖gaussPdfC z‖ * (‖z‖ * ‖millsRatioC z‖)
      ≤ Real.exp (-(3 / 8 * z.re ^ 2)) / Real.sqrt (2 * Real.pi) * 2 :=
        mul_le_mul hφ hzm (by positivity) (by positivity)
    _ ≤ Real.exp (-(3 / 8 * z.re ^ 2)) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hs0]
        exact mul_le_mul_of_nonneg_left hs hE.le

/-- Helper: `geluC (−z) = geluC z − z` for every complex `z`: both sides are entire and agree on
the reals (`gelu_neg_eq`), which accumulate at `0`. -/
private theorem geluC_neg_gfc (z : ℂ) : geluC (-z) = geluC z - z := by
  have hf : AnalyticOnNhd ℂ (fun w : ℂ => geluC (-w)) Set.univ := fun w _ =>
    (analyticAt_geluC (-w)).comp (f := fun w : ℂ => -w) analyticAt_id.neg
  have hg : AnalyticOnNhd ℂ (fun w : ℂ => geluC w - w) Set.univ := fun w _ =>
    (analyticAt_geluC w).sub analyticAt_id
  -- they agree on the real points, which are frequently near `0`
  have hreal : ∀ x : ℝ, geluC (-(x : ℂ)) = geluC (x : ℂ) - (x : ℂ) := by
    intro x
    rw [← Complex.ofReal_neg, geluC_ofReal, geluC_ofReal, (gelu_neg_eq x).1]
    push_cast
    ring
  have ht : Filter.Tendsto (fun x : ℝ => (x : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := Complex.continuous_ofReal.tendsto 0
      rw [Complex.ofReal_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact Complex.ofReal_ne_zero.2 hx
  have hfr : ∃ᶠ w in nhdsWithin (0 : ℂ) {0}ᶜ, geluC (-w) = geluC w - w :=
    ht.frequently (Filter.Frequently.of_forall hreal)
  exact congrFun (hf.eq_of_frequently_eq hg hfr) z

/-- **Equation (31) for GELU,** with `p = 2`. -/
theorem gateFarC_gelu : GateFarC gelu 2 := by
  refine ⟨geluC, geluC_ofReal, 2, 3 / 8, by norm_num, fun z hR him => ?_⟩
  have hx : 0 < z.re := by linarith
  refine ⟨analyticAt_geluC z, analyticAt_geluC (-z), norm_geluC_sub_le_gfc hx him, ?_⟩
  rw [geluC_neg_gfc]
  exact norm_geluC_sub_le_gfc hx him


/-- Helper: SiLU at a complex `z`, `z / (1 + e^{−z})`. -/
private noncomputable def siluC_gfc (z : ℂ) : ℂ := z / (1 + Complex.exp (-z))

/-- Helper: on the real line `siluC_gfc` is SiLU. -/
private theorem siluC_ofReal_gfc (x : ℝ) : siluC_gfc (x : ℂ) = ((silu x : ℝ) : ℂ) := by
  rw [siluC_gfc, silu]
  push_cast
  rfl

/-- Helper: `siluC_gfc` is holomorphic where `1 + e^{−w} ≠ 0`. -/
private theorem analyticAt_siluC_gfc {w : ℂ} (hw : 1 + Complex.exp (-w) ≠ 0) :
    AnalyticAt ℂ siluC_gfc w :=
  analyticAt_id.fun_div (analyticAt_const.fun_add analyticAt_id.neg.cexp') hw

/-- Helper: for `x ≥ 32`, `4 x e^{−x} ≤ e^{−x/2}` (as `e^{x/2} ≥ x²/8 ≥ 4x`). -/
private theorem four_mul_exp_le_gfc {x : ℝ} (hx : 32 ≤ x) :
    4 * x * Real.exp (-x) ≤ Real.exp (-(1 / 2 * x)) := by
  have h1 := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ x / 2)
  have h2 : 4 * x ≤ Real.exp (x / 2) := by nlinarith
  have e : Real.exp (-x) = Real.exp (-(1 / 2 * x)) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e, ← mul_assoc, mul_comm _ (Real.exp (-(1 / 2 * x))), mul_assoc]
  have h3 : 4 * x * Real.exp (-(x / 2)) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    exact h2
  calc Real.exp (-(1 / 2 * x)) * (4 * x * Real.exp (-(x / 2)))
      ≤ Real.exp (-(1 / 2 * x)) * 1 := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = _ := mul_one _

/-- **Equation (31) for SiLU,** with `p = 1`. -/
theorem gateFarC_silu : GateFarC silu 1 := by
  refine ⟨siluC_gfc, siluC_ofReal_gfc, 32, 1 / 2, by norm_num, fun z hR him => ?_⟩
  have hx : 0 < z.re := by linarith
  obtain ⟨hz, -⟩ := sector_facts_gfc hx.le him
  -- `e^x ≥ 1 + x ≥ 2`
  have hex : 2 ≤ Real.exp z.re := by linarith [Real.add_one_le_exp z.re]
  have hexn : Real.exp (-z.re) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hex
  have hn1 : ‖Complex.exp (-z)‖ = Real.exp (-z.re) := by
    rw [Complex.norm_exp, Complex.neg_re]
  have hn2 : ‖Complex.exp z‖ = Real.exp z.re := Complex.norm_exp z
  -- `‖1 + e^{−z}‖ ≥ 1/2` and `‖1 + e^{z}‖ ≥ e^x/2`
  have hd1 : 1 / 2 ≤ ‖1 + Complex.exp (-z)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-Complex.exp (-z))
    rw [norm_one, norm_neg, hn1, sub_neg_eq_add] at this
    linarith
  have hd2 : Real.exp z.re / 2 ≤ ‖1 + Complex.exp z‖ := by
    have := norm_sub_norm_le (Complex.exp z) (-1)
    rw [norm_neg, norm_one, hn2, sub_neg_eq_add, add_comm] at this
    linarith
  have hne1 : 1 + Complex.exp (-z) ≠ 0 := fun h => by
    rw [h, norm_zero] at hd1; linarith
  have hne2 : 1 + Complex.exp (-(-z)) ≠ 0 := fun h => by
    rw [neg_neg] at h
    rw [h, norm_zero] at hd2; linarith [Real.exp_pos z.re]
  have hbound := four_mul_exp_le_gfc hR
  rw [pow_one]
  refine ⟨analyticAt_siluC_gfc hne1, analyticAt_siluC_gfc hne2, ?_, ?_⟩
  · -- `σ(z) − z = −z e^{−z}/(1 + e^{−z})`
    have e : siluC_gfc z - z = -(z * Complex.exp (-z)) / (1 + Complex.exp (-z)) := by
      rw [siluC_gfc]; field_simp; ring
    rw [e, norm_div, norm_neg, norm_mul, hn1, div_le_iff₀ (by linarith)]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hd1 (Real.exp_pos _).le)
    calc ‖z‖ * Real.exp (-z.re) ≤ 2 * z.re * Real.exp (-z.re) :=
          mul_le_mul_of_nonneg_right hz (Real.exp_pos _).le
      _ = 4 * z.re * Real.exp (-z.re) * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbound (by norm_num)
  · -- `σ(−z) = −z/(1 + e^{z})`
    rw [siluC_gfc, neg_neg, norm_div, norm_neg, div_le_iff₀ (by linarith [Real.exp_pos z.re])]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hd2 (Real.exp_pos _).le)
    have e2 : Real.exp (-z.re) * Real.exp z.re = 1 := by rw [← Real.exp_add]; simp
    calc ‖z‖ ≤ 2 * z.re := hz
      _ = 4 * z.re * Real.exp (-z.re) * (Real.exp z.re / 2) := by
          rw [show 4 * z.re * Real.exp (-z.re) * (Real.exp z.re / 2)
            = 2 * z.re * (Real.exp (-z.re) * Real.exp z.re) by ring, e2, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hbound (by positivity)

end Skips
