import SkipsLean.Activations.MillsAtInfinity
import SkipsLean.Depth.RaySeparation

/-!
# The induction on the exponents along a ray

Paper (dimension): Appendix D.5, proof of Lemma D.12, the paragraphs "The expansion", facts (a) to
(c), and "The induction", equations (34) to (36).

On a ray `n = t ξ` the left side of the identity for one block is expanded in the small terms
`δ_j(t)` of the gates: "at `δ = δ(t)` and `δ' = δ'(t)` the term of `δ^α` is of the order of
`e^{-r_α t^p / p}`, up to powers of `t`, and the term of `δ^α δ'_i` of the order of
`e^{-(r_α + r_i) t^p / p}`", with `r_α = ∑_j α_j r_j`. The numbers `r_j` are linearly independent
over `ℚ`, so "different multi-indices have different exponents `r_α`, and only finitely many
exponents lie below any bound." The paper shows by induction on the exponent `r_α` that every
coefficient vanishes: "No small factor, `α = 0`", "One small factor, `α = 1_j`", "Two or more small
factors, `|α| ≥ 2`".

Stated here in a form that does not mention the network. The small terms are positive functions
`ζ_j(t)` that lie between `e^{-r_j t^p}` divided and multiplied by a power of `t` (for the gates,
`ζ_j = δ_j(t)/t` and `r_j = |ξ c_j|^p / p`, by (25) and (32)). The left side of (34), divided by a
power of `t`, is `G₀(1/t, ζ(t)) + ∑_j ν_j(t) ζ_j(t) G_j(1/t, ζ(t))` with maps `G₀`, `G_j` that are
real-analytic at `(0, 0)` (fact (a): the coefficients are meromorphic at infinity) and with
functions `ν_j` that are at most a power of `t` (for the gates, `ν_j = t δ'_j(t)/δ_j(t)`, by (32)).
Fact (b) is the hypothesis `hid`: the left side is smaller than `e^{-R t^p}` for every `R`. The
step "one small factor" depends on the gate (Lemma D.9 for GELU, parity for SiLU) and on the
block (equation (29)); it is the hypothesis `hstep`: if (36) holds for `α = 1_j`, then `G_j`
vanishes. The conclusion is that `G₀` and every `G_j` vanish near `(0, 0)`: all coefficients of the
expansion vanish. Fact (c), the bound on the terms with a larger exponent, is part of the proof.

The values lie in a complete normed space `F` (in the paper, `ℝ^{1×d_out}`). Completeness is
needed: for a space that is not complete, a map that is real-analytic at `(0, 0)` need not be
differentiable at nearby points, and the derivative `∂G₀/∂y_j (1/t, 0)` in `hstep` loses its
meaning.
-/

namespace Skips

open Filter Topology
open scoped Matrix.Norms.Elementwise NNReal ENNReal

/-- Expansion of a multilinear map at a linear combination of vectors:
`f (∑_j y_j b_j, …) = ∑_v (∏_k y_{v k}) • f (b_{v 1}, …, b_{v n})`. -/
private lemma cmm_apply_sum_smul' {ι X F : Type*} [Fintype ι] [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => X) F) (b : ι → X) (y : ι → ℝ) :
    f (fun _ => ∑ j, y j • b j) = ∑ v : Fin n → ι, (∏ k, y (v k)) • f (fun k => b (v k)) := by
  rw [f.map_sum (fun (_ : Fin n) (j : ι) => y j • b j)]
  refine Finset.sum_congr rfl fun v _ => ?_
  exact f.map_smul_univ (fun k => y (v k)) (fun k => b (v k))

/-- Over the words `w = (n, v)` on `ι`, `∑_w ∏_k c_{v k}` converges when `∑_j c_j < 1`. -/
private lemma summable_prod_words {ι : Type*} [Fintype ι] (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j)
    (h1 : ∑ j, c j < 1) :
    Summable (fun w : Σ n : ℕ, (Fin n → ι) => ∏ k, c (w.2 k)) := by
  refine (summable_sigma_of_nonneg fun w => Finset.prod_nonneg fun k _ => hc _).2
    ⟨fun n => Summable.of_finite, ?_⟩
  have h : ∀ n : ℕ, ∑' v : Fin n → ι, ∏ k, c (v k) = (∑ j, c j) ^ n := fun n => by
    rw [tsum_fintype, ← Fintype.prod_sum (fun (_ : Fin n) j => c j), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  simp only [h]
  exact summable_geometric_of_lt_one (Finset.sum_nonneg fun j _ => hc j) h1

/-- **The expansion in `y` at `(s, 0)`.** A map `G₀` that is analytic at `(0, 0)` is, for small
`s` and `y`, the sum over the words `w = (n, v)` of `(∏_k y_{v k}) • a_w(s)`, with coefficients
`a_w` that are analytic in `s`, bounded by `S / ρ^n`, and with `a_{(1, j)}(s) = ∂G₀/∂y_j (s, 0)`. -/
private lemma exists_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (G₀ : ℝ × (ι → ℝ) → F) (hG₀ : AnalyticAt ℝ G₀ 0) :
    ∃ (ρ S : ℝ) (a : (Σ n : ℕ, (Fin n → ι)) → ℝ → F), 0 < ρ ∧
      (∀ w, AnalyticOnNhd ℝ (a w) (Metric.ball 0 ρ)) ∧
      (∀ w s, |s| < ρ → ‖a w s‖ * ρ ^ w.1 ≤ S) ∧
      (∀ s (y : ι → ℝ), |s| < ρ → ∑ j, |y j| < ρ →
        HasSum (fun w => (∏ k, y (w.2 k)) • a w s) (G₀ (s, y))) ∧
      (∀ s j, |s| < ρ →
        fderiv ℝ (fun y : ι → ℝ => G₀ (s, y)) 0 (Pi.single j 1) = a ⟨1, fun _ => j⟩ s) := by
  classical
  obtain ⟨P, R, hP⟩ := hG₀
  obtain ⟨ρ₂, hρ₂0, hρ₂R⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hP.r_pos
  let ρ : ℝ≥0 := ρ₂ / 2
  have hρ0 : (0 : ℝ) < ρ := by
    have : (0 : ℝ≥0) < ρ₂ := by exact_mod_cast hρ₂0
    exact_mod_cast (half_pos this)
  have hρρ : ((ρ + ρ : ℝ≥0) : ℝ≥0∞) < R := by
    rw [add_halves]; exact hρ₂R
  have hρρ' : ((ρ : ℝ≥0∞) + ρ) < P.radius := by
    exact_mod_cast hρρ.trans_le hP.r_le
  have hρR : (ρ : ℝ≥0∞) < R :=
    lt_of_le_of_lt (by exact_mod_cast le_add_self) hρρ
  have hρrad : (ρ : ℝ≥0∞) < P.radius := hρR.trans_le hP.r_le
  -- The vectors `e_j = (0, 1_j)` and the coefficients `a_w(s)`.
  let e : ι → ℝ × (ι → ℝ) := fun j => (0, Pi.single j 1)
  have he : ∀ j, ‖e j‖ = 1 := fun j => by
    simp [e, Prod.norm_def, Pi.norm_single]
  let a : (Σ n : ℕ, (Fin n → ι)) → ℝ → F := fun w s =>
    P.changeOrigin ((s, 0) : ℝ × (ι → ℝ)) w.1 (fun k => e (w.2 k))
  have hnorm_s : ∀ s : ℝ, ‖((s, 0) : ℝ × (ι → ℝ))‖ = |s| := fun s => by
    simp [Prod.norm_def]
  -- The uniform bound `‖p.changeOrigin x n‖ ρ^n ≤ S` for `‖x‖ ≤ ρ`.
  let Snn : ℝ≥0 := ∑' z : (Σ k l : ℕ, {s : Finset (Fin (k + l)) // s.card = l}),
    ‖P (z.1 + z.2.1)‖₊ * ρ ^ z.2.1 * ρ ^ z.1
  have hsum1 := P.changeOriginSeries_summable_aux₁ hρρ'
  have hbdnn : ∀ n (x : ℝ × (ι → ℝ)), ‖x‖₊ ≤ ρ → ‖P.changeOrigin x n‖₊ * ρ ^ n ≤ Snn := by
    intro n x hx
    have hxr : (‖x‖₊ : ℝ≥0∞) < P.radius :=
      lt_of_le_of_lt (by exact_mod_cast hx) hρrad
    have hs2 := P.changeOriginSeries_summable_aux₂ hρrad n
    calc ‖P.changeOrigin x n‖₊ * ρ ^ n
        ≤ (∑' s : Σ l : ℕ, {s : Finset (Fin (n + l)) // s.card = l},
            ‖P (n + s.1)‖₊ * ρ ^ s.1) * ρ ^ n := by
          gcongr
          refine (P.nnNorm_changeOrigin_le n hxr).trans ?_
          refine Summable.tsum_le_tsum (fun s => by gcongr) ?_ hs2
          exact NNReal.summable_of_le (fun s => by gcongr) hs2
      _ = ∑' s : Σ l : ℕ, {s : Finset (Fin (n + l)) // s.card = l},
            ‖P (n + s.1)‖₊ * ρ ^ s.1 * ρ ^ n := (NNReal.tsum_mul_right _ _).symm
      _ ≤ Snn := by
          have hfib : Summable (fun s : Σ l : ℕ, {s : Finset (Fin (n + l)) // s.card = l} =>
              ‖P (n + s.1)‖₊ * ρ ^ s.1 * ρ ^ n) := (NNReal.summable_sigma.1 hsum1).1 n
          have h2 := NNReal.summable_sigma.1 hsum1
          calc _ ≤ ∑' k, ∑' s : Σ l : ℕ, {s : Finset (Fin (k + l)) // s.card = l},
                ‖P (k + s.1)‖₊ * ρ ^ s.1 * ρ ^ k := h2.2.le_tsum' n
            _ = Snn := (Summable.tsum_sigma' h2.1 hsum1).symm
  let S : ℝ := Snn
  have hbd : ∀ w (s : ℝ), |s| < (ρ : ℝ) → ‖a w s‖ * (ρ : ℝ) ^ w.1 ≤ S := by
    intro w s hs
    have h1 : ‖a w s‖ ≤ ‖P.changeOrigin ((s, 0) : ℝ × (ι → ℝ)) w.1‖ := by
      refine ((P.changeOrigin _ w.1).le_opNorm _).trans (le_of_eq ?_)
      simp [he]
    have h2 := hbdnn w.1 ((s, 0) : ℝ × (ι → ℝ)) (by
      rw [← NNReal.coe_le_coe, coe_nnNorm, hnorm_s]; exact hs.le)
    have h3 : ‖P.changeOrigin ((s, 0) : ℝ × (ι → ℝ)) w.1‖ * (ρ : ℝ) ^ w.1 ≤ S := by
      exact_mod_cast h2
    exact (mul_le_mul_of_nonneg_right h1 (pow_nonneg hρ0.le _)).trans h3
  refine ⟨(ρ : ℝ), S, a, hρ0, ?_, hbd, ?_, ?_⟩
  · -- Analyticity in `s`.
    intro w s₀ hs₀
    have hs₀' : |s₀| < ρ := by simpa [Real.dist_eq] using hs₀
    have hco := P.hasFPowerSeriesOnBall_changeOrigin w.1 (lt_of_le_of_lt zero_le hρrad)
    have hmem : ((s₀, 0) : ℝ × (ι → ℝ)) ∈ Metric.eball (0 : ℝ × (ι → ℝ)) P.radius := by
      rw [mem_eball_zero_iff, eNorm_eq_nnNorm]
      refine lt_of_le_of_lt ?_ hρrad
      rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnNorm, hnorm_s]
      exact hs₀'.le
    have h1 := hco.analyticAt_of_mem hmem
    have h2 : AnalyticAt ℝ (fun s : ℝ => ((s, 0) : ℝ × (ι → ℝ))) s₀ :=
      (ContinuousLinearMap.inl ℝ ℝ (ι → ℝ)).analyticAt s₀
    have h4 : AnalyticAt ℝ (fun s : ℝ => P.changeOrigin ((s, 0) : ℝ × (ι → ℝ)) w.1) s₀ :=
      h1.comp_of_eq h2 rfl
    have h3 : AnalyticAt ℝ (fun c : ContinuousMultilinearMap ℝ (fun _ : Fin w.1 => ℝ × (ι → ℝ)) F =>
        c (fun k => e (w.2 k))) (P.changeOrigin ((s₀, 0) : ℝ × (ι → ℝ)) w.1) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin w.1 => ℝ × (ι → ℝ)) F
        (fun k => e (w.2 k))).analyticAt _
    have hc := h3.comp_of_eq h4 rfl
    exact hc
  · -- The sum over the words.
    intro s y hs hy
    have hs' : (‖((s, 0) : ℝ × (ι → ℝ))‖₊ : ℝ≥0∞) < R := by
      refine lt_of_le_of_lt ?_ hρR
      rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnNorm, hnorm_s]
      exact hs.le
    have hco := hP.changeOrigin hs'
    have hyn : ‖y‖ ≤ ∑ j, |y j| := by
      refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)).2 fun j => ?_
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun j _ => abs_nonneg (y j)) (Finset.mem_univ j)
    have hymem : ((0 : ℝ), y) ∈ Metric.eball (0 : ℝ × (ι → ℝ))
        (R - ‖((s, 0) : ℝ × (ι → ℝ))‖₊) := by
      rw [mem_eball_zero_iff, eNorm_eq_nnNorm, lt_tsub_iff_right]
      refine lt_of_le_of_lt ?_ hρρ
      rw [← ENNReal.coe_add, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_add,
        coe_nnNorm, coe_nnNorm, hnorm_s]
      have : ‖((0 : ℝ), y)‖ = ‖y‖ := by simp [Prod.norm_def]
      rw [this]
      push_cast
      linarith
    have h2 := hco.hasSum hymem
    have hpt : (0 : ℝ × (ι → ℝ)) + (s, 0) + (0, y) = (s, y) := by simp
    rw [hpt] at h2
    have hyeq : ((0 : ℝ), y) = ∑ j, y j • e j := by
      ext i
      · rw [Prod.fst_sum]; simp [e]
      · simp only [e, Prod.snd_sum, Prod.smul_snd]
        rw [Finset.sum_apply]
        simp [Pi.single_apply]
    have h3 : ∀ n, ∑ v : Fin n → ι, (∏ k, y (v k)) • a ⟨n, v⟩ s =
        P.changeOrigin ((s, 0) : ℝ × (ι → ℝ)) n (fun _ => ((0 : ℝ), y)) := by
      intro n
      rw [hyeq, cmm_apply_sum_smul']
    -- Summability over the words.
    let c : ι → ℝ := fun j => |y j| / ρ
    have hc : ∑ j, c j < 1 := by
      rw [← Finset.sum_div, div_lt_one hρ0]; exact hy
    have hmaj := (summable_prod_words c (fun j => div_nonneg (abs_nonneg _) hρ0.le) hc).mul_left S
    have hsm : Summable (fun w : Σ n : ℕ, (Fin n → ι) => (∏ k, y (w.2 k)) • a w s) := by
      refine Summable.of_norm_bounded hmaj fun w => ?_
      have hb := hbd w s hs
      have hb' : ‖a w s‖ ≤ S / (ρ : ℝ) ^ w.1 := by
        rw [le_div_iff₀ (pow_pos hρ0 _)]; exact hb
      rw [norm_smul, norm_prod]
      calc (∏ k, ‖y (w.2 k)‖) * ‖a w s‖ ≤ (∏ k, |y (w.2 k)|) * (S / (ρ : ℝ) ^ w.1) := by
            simp only [Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left hb' (Finset.prod_nonneg fun k _ => abs_nonneg _)
        _ = S * ∏ k, c (w.2 k) := by
            simp only [c, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
              Fintype.card_fin]
            ring
    have h1 := hsm.hasSum.sigma fun n => hasSum_fintype _
    simp only [h3] at h1
    rw [← h1.unique h2]
    exact hsm.hasSum
  · -- The derivative in `y_j`.
    intro s j hs
    have hs' : (‖((s, 0) : ℝ × (ι → ℝ))‖₊ : ℝ≥0∞) < R := by
      refine lt_of_le_of_lt ?_ hρR
      rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnNorm, hnorm_s]
      exact hs.le
    have hd := (hP.changeOrigin hs').hasFPowerSeriesAt.hasFDerivAt
    rw [zero_add] at hd
    have hc := hd.comp (0 : ι → ℝ) (hasFDerivAt_prodMk_right (𝕜 := ℝ) s (0 : ι → ℝ))
    rw [show (fun y : ι → ℝ => G₀ (s, y)) = G₀ ∘ fun y => (s, y) from rfl, hc.fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.inr_apply, continuousMultilinearCurryFin1_apply]
    exact congrArg _ (funext fun k => by rw [show k = Fin.last 0 from Fin.fin_one_eq_zero k, Fin.snoc_last])

/-- **The induction on the exponents** (proof of Lemma D.12, (34) to (36)). Let the rates
`r_j > 0` be linearly independent over `ℚ`, let `ζ_j(t)` lie between `e^{-r_j t^p}` divided and
multiplied by `A t^N`, let `|ν_j(t)| ≤ A t^N`, and let `G₀` and `G_j` be real-analytic at `(0, 0)`.
Suppose that `G₀(1/t, ζ(t)) + ∑_j ν_j(t) ζ_j(t) G_j(1/t, ζ(t))` is, for every `R`, at most
`e^{-R t^p}` for large `t`, and that, for every `j`, `G_j` vanishes near `(0, 0)` as soon as
`∂G₀/∂y_j (1/t, 0) + ν_j(t) G_j(1/t, 0)` tends to `0` faster than every power of `1/t`. Then `G₀`
and every `G_j` vanish near `(0, 0)`. -/
theorem ray_induction {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (p : ℕ) (hp : 1 ≤ p) (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (hrQ : LinearIndependent ℚ r) (ζ ν : ℝ → ι → ℝ) (A : ℝ) (N : ℕ)
    (hζl : ∀ᶠ t : ℝ in atTop, ∀ j, Real.exp (-(r j * t ^ p)) ≤ A * t ^ N * ζ t j)
    (hζu : ∀ᶠ t : ℝ in atTop, ∀ j, |ζ t j| ≤ A * t ^ N * Real.exp (-(r j * t ^ p)))
    (hν : ∀ᶠ t : ℝ in atTop, ∀ j, |ν t j| ≤ A * t ^ N)
    (G₀ : ℝ × (ι → ℝ) → F) (G : ι → ℝ × (ι → ℝ) → F)
    (hG₀ : AnalyticAt ℝ G₀ 0) (hG : ∀ j, AnalyticAt ℝ (G j) 0)
    (hid : ∀ R : ℝ, ∀ᶠ t : ℝ in atTop,
      ‖G₀ (1 / t, ζ t) + ∑ j, (ν t j * ζ t j) • G j (1 / t, ζ t)‖ ≤ Real.exp (-(R * t ^ p)))
    (hstep : ∀ j,
      FasterThanPowers (fun t : ℝ =>
        fderiv ℝ (fun y : ι → ℝ => G₀ (1 / t, y)) 0 (Pi.single j 1) + ν t j • G j (1 / t, 0)) →
      ∀ᶠ z in 𝓝 (0 : ℝ × (ι → ℝ)), G j z = 0) :
    (∀ᶠ z in 𝓝 (0 : ℝ × (ι → ℝ)), G₀ z = 0) ∧
      ∀ j, ∀ᶠ z in 𝓝 (0 : ℝ × (ι → ℝ)), G j z = 0 := by
  sorry

/-- **The induction on the exponents, for the hidden units of several tokens:** the same statement
with the small terms arranged in a matrix (one row per token, one column per hidden unit). -/
theorem ray_induction_matrix {T q : Type*} [Fintype T] [Fintype q] [DecidableEq T] [DecidableEq q]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (p : ℕ) (hp : 1 ≤ p)
    (r : Matrix T q ℝ) (hr : ∀ a j, 0 < r a j)
    (hrQ : LinearIndependent ℚ (fun i : T × q => r i.1 i.2)) (ζ ν : ℝ → Matrix T q ℝ) (A : ℝ)
    (N : ℕ)
    (hζl : ∀ᶠ t : ℝ in atTop, ∀ a j, Real.exp (-(r a j * t ^ p)) ≤ A * t ^ N * ζ t a j)
    (hζu : ∀ᶠ t : ℝ in atTop, ∀ a j, |ζ t a j| ≤ A * t ^ N * Real.exp (-(r a j * t ^ p)))
    (hν : ∀ᶠ t : ℝ in atTop, ∀ a j, |ν t a j| ≤ A * t ^ N)
    (G₀ : ℝ × Matrix T q ℝ → F) (G : T → q → ℝ × Matrix T q ℝ → F)
    (hG₀ : AnalyticAt ℝ G₀ 0) (hG : ∀ a j, AnalyticAt ℝ (G a j) 0)
    (hid : ∀ R : ℝ, ∀ᶠ t : ℝ in atTop,
      ‖G₀ (1 / t, ζ t) + ∑ a, ∑ j, (ν t a j * ζ t a j) • G a j (1 / t, ζ t)‖
        ≤ Real.exp (-(R * t ^ p)))
    (hstep : ∀ a j,
      FasterThanPowers (fun t : ℝ =>
        fderiv ℝ (fun y : Matrix T q ℝ => G₀ (1 / t, y)) 0 (Matrix.single a j 1)
          + ν t a j • G a j (1 / t, 0)) →
      ∀ᶠ z in 𝓝 (0 : ℝ × Matrix T q ℝ), G a j z = 0) :
    (∀ᶠ z in 𝓝 (0 : ℝ × Matrix T q ℝ), G₀ z = 0) ∧
      ∀ a j, ∀ᶠ z in 𝓝 (0 : ℝ × Matrix T q ℝ), G a j z = 0 := by
  sorry

end Skips
