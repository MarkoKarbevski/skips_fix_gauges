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

/-- A sum over `k : Fin n` of `f (v k)`, grouped by the value of `v k`. -/
private lemma sum_comp_eq_sum_card_words {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] {n : ℕ} (v : Fin n → ι) (f : ι → M) :
    ∑ k, f (v k) = ∑ j, (Finset.univ.filter fun k => v k = j).card • f j := by
  rw [← Finset.sum_fiberwise Finset.univ v (fun k => f (v k))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2]), Finset.sum_const]

/-- A product over `k : Fin n` of `f (v k)`, grouped by the value of `v k`. -/
private lemma prod_comp_eq_prod_pow_words {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [CommMonoid M] {n : ℕ} (v : Fin n → ι) (f : ι → M) :
    ∏ k, f (v k) = ∏ j, f j ^ (Finset.univ.filter fun k => v k = j).card := by
  rw [← Finset.prod_fiberwise Finset.univ v (fun k => f (v k))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2]), Finset.prod_const]

/-- If the rates `r_j` are linearly independent over `ℚ`, the rate `∑_k r_{v k}` of a word `v`
determines how often each letter `j` occurs in `v`. -/
private lemma card_fiber_eq_of_rate_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℝ}
    (hr : LinearIndependent ℚ r) {n n' : ℕ} (v : Fin n → ι) (v' : Fin n' → ι)
    (h : ∑ k, r (v k) = ∑ k, r (v' k)) (j : ι) :
    (Finset.univ.filter fun k => v k = j).card = (Finset.univ.filter fun k => v' k = j).card := by
  have e1 := sum_comp_eq_sum_card_words v r
  have e2 := sum_comp_eq_sum_card_words v' r
  simp only [nsmul_eq_mul] at e1 e2
  have := (Fintype.linearIndependent_iff.1 hr)
    (fun j => ((Finset.univ.filter fun k => v k = j).card : ℚ) -
      (Finset.univ.filter fun k => v' k = j).card) ?_ j
  · exact_mod_cast sub_eq_zero.1 this
  · simp only [sub_smul, Finset.sum_sub_distrib, Rat.smul_def, Rat.cast_natCast]
    rw [← e1, ← e2, h, sub_self]

/-- The length of a word is the sum of the numbers of occurrences of the letters. -/
private lemma card_eq_sum_card_fiber_words {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (v : Fin n → ι) : n = ∑ j, (Finset.univ.filter fun k => v k = j).card := by
  have := sum_comp_eq_sum_card_words v (fun _ => (1 : ℕ))
  simpa using this

/-- `∏_k e^{-c_k x} = e^{-(∑_k c_k) x}`. -/
private lemma prod_exp_neg_mul {n : ℕ} (c : Fin n → ℝ) (x : ℝ) :
    ∏ k, Real.exp (-(c k * x)) = Real.exp (-((∑ k, c k) * x)) := by
  rw [← Real.exp_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]

/-- The zero map tends to `0` faster than every power. -/
private lemma ftp_zero {F : Type*} [NormedAddCommGroup F] :
    FasterThanPowers (fun _ : ℝ => (0 : F)) :=
  fasterThanPowers_of_le_pow_mul_exp (A := 0) (κ := 1) (N := 0) (p := 1) one_pos le_rfl
    (Eventually.of_forall fun t => by simp)

/-- A map that vanishes for large `t` tends to `0` faster than every power. -/
private lemma ftp_of_eventually_eq_zero {F : Type*} [NormedAddCommGroup F] {f : ℝ → F}
    (h : ∀ᶠ t in atTop, f t = 0) : FasterThanPowers f :=
  ftp_zero.congr (h.mono fun _ ht => ht.symm)

/-- Differences of maps that tend to `0` faster than every power. -/
private lemma ftp_sub {F : Type*} [NormedAddCommGroup F] {f g : ℝ → F}
    (hf : FasterThanPowers f) (hg : FasterThanPowers g) :
    FasterThanPowers (fun t => f t - g t) := by
  have hg' : FasterThanPowers (fun t => -g t) :=
    hg.mono (Eventually.of_forall fun t => by rw [norm_neg])
  simpa only [sub_eq_add_neg] using hf.add hg'

/-- Finite sums of maps that tend to `0` faster than every power. -/
private lemma ftp_sum {F : Type*} [NormedAddCommGroup F] {α : Type*} (s : Finset α)
    (f : α → ℝ → F) (h : ∀ i ∈ s, FasterThanPowers (f i)) :
    FasterThanPowers (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (ftp_zero : FasterThanPowers fun _ => (0 : F))
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- A map at most `K t^M e^{m t^p}` times `e^{-(m + c) t^p}`, with `c > 0`, tends to `0` faster
than every power. -/
private lemma ftp_of_le_exp_sub {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} {K m c : ℝ}
    {M p : ℕ} (hc : 0 < c) (hp : 1 ≤ p)
    (h : ∀ᶠ t in atTop, ‖f t‖ ≤ K * t ^ M * Real.exp (m * t ^ p) * Real.exp (-((m + c) * t ^ p))) :
    FasterThanPowers f := by
  refine fasterThanPowers_of_le_pow_mul_exp (A := K) (N := M) hc hp ?_
  filter_upwards [h] with t ht
  refine ht.trans (le_of_eq ?_)
  rw [mul_assoc, ← Real.exp_add, show m * t ^ p + -((m + c) * t ^ p) = -(c * t ^ p) by ring]

/-- `A t^N e^{-κ t^p} → 0`. -/
private lemma tendsto_mul_pow_mul_exp_neg {A κ : ℝ} {N p : ℕ} (hκ : 0 < κ) (hp : 1 ≤ p) :
    Tendsto (fun t : ℝ => A * t ^ N * Real.exp (-(κ * t ^ p))) atTop (𝓝 0) := by
  have hf : FasterThanPowers (fun t : ℝ => A * t ^ N * Real.exp (-(κ * t ^ p))) := by
    refine fasterThanPowers_of_le_pow_mul_exp (A := |A|) (N := N) hκ hp ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht N), Real.abs_exp]
  have := (fasterThanPowers_iff _).1 hf 0
  simp only [pow_zero, one_mul] at this
  exact tendsto_zero_iff_norm_tendsto_zero.2 this

/-- **The induction on the exponents, with normalized bounds** (`A ≥ 1`, `ζ_j > 0`). -/
private lemma ray_induction_core {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (p : ℕ) (hp : 1 ≤ p)
    (r : ι → ℝ) (hr : ∀ j, 0 < r j) (hrQ : LinearIndependent ℚ r) (ζ ν : ℝ → ι → ℝ) (A : ℝ)
    (N : ℕ) (hA : 1 ≤ A)
    (hray : ∀ᶠ t : ℝ in atTop, 1 ≤ t ∧ ∀ j, 0 < ζ t j ∧
      Real.exp (-(r j * t ^ p)) ≤ A * t ^ N * ζ t j ∧
      ζ t j ≤ A * t ^ N * Real.exp (-(r j * t ^ p)) ∧ |ν t j| ≤ A * t ^ N)
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
  classical
  -- The expansion `G₀(s, y) = ∑_w (∏_k y_{w k}) a_w(s)` over the words `w`.
  obtain ⟨ρ, S, a, hρ, han, hbd, hsum, hder⟩ := exists_expansion G₀ hG₀
  have hS : 0 ≤ S := (mul_nonneg (norm_nonneg _) (pow_nonneg hρ.le _)).trans
    (hbd ⟨0, fun k => k.elim0⟩ 0 (by simpa using hρ))
  -- The rate `μ_w = ∑_k r_{w k}` of a word.
  let μ : (Σ n : ℕ, (Fin n → ι)) → ℝ := fun w => ∑ k, r (w.2 k)
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ j, δ ≤ r j := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun j => isEmptyElim j⟩
    · obtain ⟨j₀, hj₀⟩ := Finite.exists_min r
      exact ⟨r j₀, hr j₀, hj₀⟩
  have hμn : ∀ w, δ * w.1 ≤ μ w := fun w => by
    have : ∑ k : Fin w.1, δ ≤ μ w := Finset.sum_le_sum fun k _ => hδle _
    simpa [mul_comm] using this
  have hμ0 : ∀ w, 0 ≤ μ w := fun w =>
    (mul_nonneg hδ.le (Nat.cast_nonneg _)).trans (hμn w)
  -- Finitely many words have a rate below any bound.
  have hfin : ∀ B, {w | μ w ≤ B}.Finite := by
    intro B
    refine ((Finset.range (⌊B / δ⌋₊ + 1)).sigma fun n => (Finset.univ : Finset (Fin n → ι))
      ).finite_toSet.subset fun w hw => ?_
    obtain ⟨n, v⟩ := w
    have hw' : μ ⟨n, v⟩ ≤ B := hw
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio,
      Finset.coe_univ, Set.mem_univ, and_true]
    have hn : (n : ℝ) * δ ≤ B := by rw [mul_comm]; exact (hμn ⟨n, v⟩).trans hw'
    have : n ≤ ⌊B / δ⌋₊ := Nat.le_floor (by rw [le_div_iff₀ hδ]; exact hn)
    omega
  -- Words with the same rate have the same letters: same length, same monomial.
  have hlen : ∀ w w', μ w = μ w' → w.1 = w'.1 := fun w w' h => by
    rw [card_eq_sum_card_fiber_words w.2, card_eq_sum_card_fiber_words w'.2]
    exact Finset.sum_congr rfl fun j _ => card_fiber_eq_of_rate_eq hrQ w.2 w'.2 h j
  have hmono : ∀ w w', μ w = μ w' → ∀ y : ι → ℝ, ∏ k, y (w.2 k) = ∏ k, y (w'.2 k) :=
    fun w w' h y => by
      rw [prod_comp_eq_prod_pow_words, prod_comp_eq_prod_pow_words]
      exact Finset.prod_congr rfl fun j _ => by rw [card_fiber_eq_of_rate_eq hrQ w.2 w'.2 h j]
  have hμsingle : ∀ i, μ ⟨1, fun _ => i⟩ = r i := fun i => by simp [μ]
  have hsingle : ∀ w i, μ w = r i → w = ⟨1, fun _ => i⟩ := by
    intro w i h
    obtain ⟨n, v⟩ := w
    have h' : μ ⟨n, v⟩ = μ ⟨1, fun _ => i⟩ := h.trans (hμsingle i).symm
    have hc := card_fiber_eq_of_rate_eq hrQ v (fun _ : Fin 1 => i) h'
    have hn : n = 1 := hlen _ _ h'
    subst hn
    have hv : ∀ k, v k = i := by
      intro k
      by_contra hne
      have h1 := hc (v k)
      rw [Finset.filter_false_of_mem (fun k' _ => Ne.symm hne), Finset.card_empty] at h1
      have h2 : 0 < (Finset.univ.filter fun k' => v k' = v k).card :=
        Finset.card_pos.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
      omega
    rw [show v = fun _ => i from funext hv]
  -- The fibre of a rate, and the coefficient `C_m(s) = ∑_{μ_w = m} a_w(s)`.
  let fib : ℝ → Finset (Σ n : ℕ, (Fin n → ι)) := fun m =>
    (hfin m).toFinset.filter fun w => μ w = m
  have hfib : ∀ m w, w ∈ fib m ↔ μ w = m := fun m w => by
    simp only [fib, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
  clear_value fib
  let C : ℝ → ℝ → F := fun m s => ∑ w ∈ fib m, a w s
  have hCan : ∀ m, AnalyticOnNhd ℝ (C m) (Metric.ball 0 ρ) := fun m =>
    Finset.analyticOnNhd_fun_sum _ fun w _ => han w
  -- Grouping the terms of a finite set of words by their rates.
  have hfibsum : ∀ (y : ι → ℝ) s w₁, ∑ w ∈ fib (μ w₁), (∏ k, y (w.2 k)) • a w s =
      (∏ k, y (w₁.2 k)) • C (μ w₁) s := fun y s w₁ => by
    rw [Finset.sum_congr rfl fun w hw => by rw [hmono w w₁ ((hfib _ _).1 hw) y],
      ← Finset.smul_sum]
  have hgroup : ∀ (L : Finset (Σ n : ℕ, (Fin n → ι))) (y : ι → ℝ) (s : ℝ),
      (∀ w ∈ L, ∀ w', μ w' = μ w → w' ∈ L) → (∀ w ∈ L, C (μ w) s = 0) →
      ∑ w ∈ L, (∏ k, y (w.2 k)) • a w s = 0 := by
    intro L y s hL hC
    rw [← Finset.sum_fiberwise_of_maps_to (g := μ) (t := L.image μ)
      (fun w hw => Finset.mem_image_of_mem μ hw)]
    refine Finset.sum_eq_zero fun m' hm' => ?_
    obtain ⟨w₁, hw₁, rfl⟩ := Finset.mem_image.1 hm'
    have hset : L.filter (fun w => μ w = μ w₁) = fib (μ w₁) := Finset.ext fun w => by
      rw [Finset.mem_filter, hfib]
      exact ⟨fun h => h.2, fun h => ⟨hL w₁ hw₁ w h, h⟩⟩
    rw [hset, hfibsum, hC w₁ hw₁, smul_zero]
  -- Facts along the ray `(1/t, ζ(t))`.
  have hζ0 : ∀ j, Tendsto (fun t => ζ t j) atTop (𝓝 0) := by
    intro j
    refine squeeze_zero' ?_ ?_ (tendsto_mul_pow_mul_exp_neg (A := A) (N := N) (hr j) hp)
    · filter_upwards [hray] with t ht; exact (ht.2 j).1.le
    · filter_upwards [hray] with t ht; exact (ht.2 j).2.2.1
  have hinv : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hpt : Tendsto (fun t => ((1 / t, ζ t) : ℝ × (ι → ℝ))) atTop (𝓝 0) := by
    rw [← Prod.mk_zero_zero]
    exact hinv.prodMk_nhds (tendsto_pi_nhds.2 hζ0)
  have hpt0 : Tendsto (fun t => ((1 / t, (0 : ι → ℝ)) : ℝ × (ι → ℝ))) atTop (𝓝 0) := by
    rw [← Prod.mk_zero_zero]
    exact hinv.prodMk_nhds tendsto_const_nhds
  have hdom : ∀ᶠ t : ℝ in atTop, |1 / t| < ρ ∧ ∑ j, |ζ t j| < ρ := by
    have h1 : Tendsto (fun t : ℝ => |1 / t|) atTop (𝓝 0) := by simpa using hinv.abs
    have h2 : Tendsto (fun t => ∑ j, |ζ t j|) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ fun j _ => (hζ0 j).abs
    exact (h1.eventually (Iio_mem_nhds hρ)).and (h2.eventually (Iio_mem_nhds hρ))
  have hζnorm : ∀ᶠ t : ℝ in atTop, ‖ζ t‖ ≤ A * t ^ N * Real.exp (-(δ * t ^ p)) := by
    filter_upwards [hray] with t ht
    have htp : 0 ≤ t ^ p := pow_nonneg (by linarith [ht.1]) p
    have hB : 0 ≤ A * t ^ N := mul_nonneg (by linarith) (pow_nonneg (by linarith [ht.1]) N)
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hB (Real.exp_pos _).le)).2 fun j => ?_
    rw [Real.norm_of_nonneg (ht.2 j).1.le]
    refine (ht.2 j).2.2.1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hB)
    nlinarith [hδle j]
  -- Bounds on the monomials `∏_k ζ_{w k}(t)`.
  have hZup : ∀ᶠ t : ℝ in atTop, ∀ w : Σ n : ℕ, (Fin n → ι),
      ∏ k, ζ t (w.2 k) ≤ (A * t ^ N) ^ w.1 * Real.exp (-(μ w * t ^ p)) := by
    filter_upwards [hray] with t ht
    intro w
    calc ∏ k, ζ t (w.2 k) ≤ ∏ k, (A * t ^ N * Real.exp (-(r (w.2 k) * t ^ p))) :=
          Finset.prod_le_prod₀ (fun k _ => (ht.2 _).1.le) fun k _ => (ht.2 _).2.2.1
      _ = (A * t ^ N) ^ w.1 * Real.exp (-(μ w * t ^ p)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            prod_exp_neg_mul (fun k => r (w.2 k))]
  have hZlo : ∀ᶠ t : ℝ in atTop, ∀ w : Σ n : ℕ, (Fin n → ι),
      Real.exp (-(μ w * t ^ p)) ≤ (A * t ^ N) ^ w.1 * ∏ k, ζ t (w.2 k) := by
    filter_upwards [hray] with t ht
    intro w
    calc Real.exp (-(μ w * t ^ p)) = ∏ k, Real.exp (-(r (w.2 k) * t ^ p)) :=
          (prod_exp_neg_mul (fun k => r (w.2 k)) _).symm
      _ ≤ ∏ k, (A * t ^ N * ζ t (w.2 k)) :=
          Finset.prod_le_prod₀ (fun k _ => (Real.exp_pos _).le) fun k _ => (ht.2 _).2.1
      _ = (A * t ^ N) ^ w.1 * ∏ k, ζ t (w.2 k) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- The statement proved by induction on the rate: the coefficient of the rate `μ_w` vanishes,
  -- and if `μ_w = r_i` then `G_i` vanishes.
  let Pr : (Σ n : ℕ, (Fin n → ι)) → Prop := fun w =>
    (∀ s ∈ Metric.ball (0 : ℝ) ρ, C (μ w) s = 0) ∧
      ∀ i, r i = μ w → ∀ᶠ z in 𝓝 (0 : ℝ × (ι → ℝ)), G i z = 0
  have step : ∀ w₀, (∀ w, μ w < μ w₀ → Pr w) → Pr w₀ := by
    intro w₀ IH
    -- (a) The gap `γ` between `m = μ_{w₀}` and the next larger rate.
    obtain ⟨γ, hγ, hgap⟩ : ∃ γ > 0, ∀ w, μ w₀ < μ w → μ w₀ + γ ≤ μ w := by
      let S' := (hfin (μ w₀ + 1)).toFinset.filter fun w => μ w₀ < μ w
      by_cases hS' : S'.Nonempty
      · obtain ⟨w₂, hw₂S, hw₂min⟩ := S'.exists_min_image μ hS'
        have h2 := (Finset.mem_filter.1 hw₂S).2
        refine ⟨min 1 (μ w₂ - μ w₀), lt_min one_pos (by linarith), fun w hw => ?_⟩
        by_cases hw1 : μ w ≤ μ w₀ + 1
        · have := hw₂min w (Finset.mem_filter.2 ⟨by simpa using hw1, hw⟩)
          have := min_le_right 1 (μ w₂ - μ w₀); linarith
        · have := min_le_left 1 (μ w₂ - μ w₀); linarith
      · refine ⟨1, one_pos, fun w hw => ?_⟩
        by_contra hw1
        have hwS : w ∈ (hfin (μ w₀ + 1)).toFinset := by
          simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]; linarith
        exact hS' ⟨w, Finset.mem_filter.2 ⟨hwS, hw⟩⟩
    -- (b) `D(t) = 1 / ∏_k ζ_{w₀ k}(t)`, at most `A^{n₀} t^{N n₀} e^{m t^p}`.
    obtain ⟨D, hD_def⟩ : ∃ D : ℝ → ℝ, ∀ t, D t = (∏ k, ζ t (w₀.2 k))⁻¹ := ⟨_, fun t => rfl⟩
    have hD : ∀ᶠ t : ℝ in atTop, 0 < ∏ k, ζ t (w₀.2 k) ∧ 0 ≤ D t ∧
        D t * ∏ k, ζ t (w₀.2 k) = 1 ∧
        D t ≤ A ^ w₀.1 * t ^ (N * w₀.1) * Real.exp (μ w₀ * t ^ p) := by
      filter_upwards [hray, hZlo] with t ht hlo
      have hZ : 0 < ∏ k, ζ t (w₀.2 k) := Finset.prod_pos fun k _ => (ht.2 _).1
      refine ⟨hZ, by rw [hD_def]; exact inv_nonneg.2 hZ.le,
        by rw [hD_def]; exact inv_mul_cancel₀ hZ.ne', ?_⟩
      rw [hD_def, inv_le_iff_one_le_mul₀ hZ]
      have h1 := hlo w₀
      have h2 : Real.exp (-(μ w₀ * t ^ p)) * Real.exp (μ w₀ * t ^ p) = 1 := by
        rw [← Real.exp_add]; simp
      rw [mul_pow, ← pow_mul] at h1
      calc (1 : ℝ) = Real.exp (-(μ w₀ * t ^ p)) * Real.exp (μ w₀ * t ^ p) := h2.symm
        _ ≤ (A ^ w₀.1 * t ^ (N * w₀.1) * ∏ k, ζ t (w₀.2 k)) * Real.exp (μ w₀ * t ^ p) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = _ := by ring
    -- (c) The left side `E(t)` of the identity, times `D(t)`.
    obtain ⟨E, hE_def⟩ : ∃ E : ℝ → F, ∀ t,
        E t = G₀ (1 / t, ζ t) + ∑ j, (ν t j * ζ t j) • G j (1 / t, ζ t) := ⟨_, fun t => rfl⟩
    have hQ : FasterThanPowers (fun t => D t • E t) := by
      refine ftp_of_le_exp_sub (K := A ^ w₀.1) (M := N * w₀.1) (m := μ w₀) (c := 1) one_pos hp ?_
      filter_upwards [hD, hid (μ w₀ + 1)] with t hDt hEt
      rw [norm_smul, Real.norm_of_nonneg hDt.2.1, hE_def]
      exact mul_le_mul hDt.2.2.2 hEt (norm_nonneg _) (hDt.2.1.trans hDt.2.2.2)
    -- (d) The words of rate at most `m`: those of smaller rate cancel, those of rate `m` give
    -- the monomial of `w₀` times `C_m`.
    have hhead : ∀ s, |s| < ρ → ∀ y : ι → ℝ,
        ∑ w ∈ (hfin (μ w₀)).toFinset, (∏ k, y (w.2 k)) • a w s =
          (∏ k, y (w₀.2 k)) • C (μ w₀) s := by
      intro s hs y
      have hs' : s ∈ Metric.ball (0 : ℝ) ρ := mem_ball_zero_iff.2 (by rwa [Real.norm_eq_abs])
      rw [← Finset.sum_filter_add_sum_filter_not _ (fun w => μ w < μ w₀)]
      have h1 : ∑ w ∈ (hfin (μ w₀)).toFinset.filter (fun w => μ w < μ w₀),
          (∏ k, y (w.2 k)) • a w s = 0 := by
        refine hgroup _ y s (fun w hw w' hw' => ?_) (fun w hw => ?_)
        · obtain ⟨hw1, hw2⟩ := Finset.mem_filter.1 hw
          refine Finset.mem_filter.2 ⟨?_, by rw [hw']; exact hw2⟩
          simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hw1 ⊢
          linarith
        · exact (IH w (Finset.mem_filter.1 hw).2).1 s hs'
      have h2 : (hfin (μ w₀)).toFinset.filter (fun w => ¬ μ w < μ w₀) = fib (μ w₀) :=
        Finset.ext fun w => by
          rw [Finset.mem_filter, hfib, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨h1, h2⟩; exact le_antisymm h1 (not_lt.1 h2)
          · intro h; exact ⟨h.le, not_lt.2 h.ge⟩
      rw [h1, zero_add, h2, hfibsum]
    -- (e) The words of larger rate: at most `e^{-(m + γ/2) t^p}` times a constant.
    obtain ⟨Rest, hRest_def⟩ : ∃ Rest : ℝ → F, ∀ t, Rest t = G₀ (1 / t, ζ t) -
        ∑ w ∈ (hfin (μ w₀)).toFinset, (∏ k, ζ t (w.2 k)) • a w (1 / t) := ⟨_, fun t => rfl⟩
    obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = γ / (2 * (μ w₀ + γ)) * δ := ⟨_, rfl⟩
    have hm0 := hμ0 w₀
    have hκ : 0 < κ := by rw [hκ_def]; positivity
    obtain ⟨ε, hε_def⟩ : ∃ ε : ℝ, ε = ρ / (2 * ((Fintype.card ι : ℝ) + 1)) := ⟨_, rfl⟩
    have hε : 0 < ε := by rw [hε_def]; positivity
    have hsmall : ∀ᶠ t : ℝ in atTop, A * t ^ N * Real.exp (-(κ * t ^ p)) ≤ ε :=
      (tendsto_mul_pow_mul_exp_neg hκ hp).eventually (Iic_mem_nhds hε)
    have hterm : ∀ᶠ t : ℝ in atTop, ∀ w : Σ n : ℕ, (Fin n → ι), μ w₀ < μ w →
        ‖(∏ k, ζ t (w.2 k)) • a w (1 / t)‖ ≤
          Real.exp (-((μ w₀ + γ / 2) * t ^ p)) * (S * ∏ k, (fun _ : ι => ε / ρ) (w.2 k)) := by
      filter_upwards [hray, hZup, hsmall, hdom] with t ht hup hsm hdt
      intro w hw
      have htp : 0 ≤ t ^ p := pow_nonneg (by linarith [ht.1]) p
      have hB : 0 ≤ A * t ^ N := mul_nonneg (by linarith) (pow_nonneg (by linarith [ht.1]) N)
      have hZ0 : 0 ≤ ∏ k, ζ t (w.2 k) := Finset.prod_nonneg fun k _ => (ht.2 _).1.le
      -- `μ_w ≥ κ n + m + γ/2` for `μ_w ≥ m + γ`.
      have hrate : κ * w.1 + (μ w₀ + γ / 2) ≤ μ w := by
        have hμw := hgap w hw
        have hlam : γ / (2 * (μ w₀ + γ)) * (μ w₀ + γ) = γ / 2 := by field_simp
        have hlam0 : 0 ≤ γ / (2 * (μ w₀ + γ)) := by positivity
        have hlam1 : γ / (2 * (μ w₀ + γ)) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]; linarith
        rw [hκ_def]
        nlinarith [mul_le_mul_of_nonneg_left (hμn w) hlam0,
          mul_le_mul_of_nonneg_left hμw (by linarith : (0 : ℝ) ≤ 1 - γ / (2 * (μ w₀ + γ)))]
      have hmon : ∏ k, ζ t (w.2 k) ≤ ε ^ w.1 * Real.exp (-((μ w₀ + γ / 2) * t ^ p)) := by
        calc ∏ k, ζ t (w.2 k) ≤ (A * t ^ N) ^ w.1 * Real.exp (-(μ w * t ^ p)) := hup w
          _ ≤ (A * t ^ N) ^ w.1 *
              (Real.exp (-(κ * t ^ p)) ^ w.1 * Real.exp (-((μ w₀ + γ / 2) * t ^ p))) := by
              refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hB _)
              rw [← Real.exp_nat_mul, ← Real.exp_add]
              apply Real.exp_le_exp.2
              nlinarith [mul_le_mul_of_nonneg_right hrate htp]
          _ = (A * t ^ N * Real.exp (-(κ * t ^ p))) ^ w.1 *
              Real.exp (-((μ w₀ + γ / 2) * t ^ p)) := by ring
          _ ≤ ε ^ w.1 * Real.exp (-((μ w₀ + γ / 2) * t ^ p)) :=
              mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (mul_nonneg hB (Real.exp_pos _).le) hsm _)
                (Real.exp_pos _).le
      have ha : ‖a w (1 / t)‖ ≤ S / ρ ^ w.1 := by
        rw [le_div_iff₀ (pow_pos hρ _)]; exact hbd w _ hdt.1
      rw [norm_smul, Real.norm_of_nonneg hZ0]
      calc (∏ k, ζ t (w.2 k)) * ‖a w (1 / t)‖
          ≤ (ε ^ w.1 * Real.exp (-((μ w₀ + γ / 2) * t ^ p))) * (S / ρ ^ w.1) :=
            mul_le_mul hmon ha (norm_nonneg _)
              (mul_nonneg (pow_nonneg hε.le _) (Real.exp_pos _).le)
        _ = _ := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow]
            field_simp
    have hcsum : ∑ _j : ι, ε / ρ < 1 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have h1 : ε / ρ = 1 / (2 * ((Fintype.card ι : ℝ) + 1)) := by
        rw [hε_def]; field_simp
      rw [h1, mul_one_div, div_lt_one (by positivity)]
      linarith
    have hmaj := (summable_prod_words (fun _ : ι => ε / ρ) (fun _ => by positivity) hcsum).mul_left S
    obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℝ,
        T₀ = ∑' w : Σ n : ℕ, (Fin n → ι), S * ∏ k, (fun _ : ι => ε / ρ) (w.2 k) := ⟨_, rfl⟩
    have hRestle : ∀ᶠ t : ℝ in atTop,
        ‖Rest t‖ ≤ Real.exp (-((μ w₀ + γ / 2) * t ^ p)) * T₀ := by
      filter_upwards [hterm, hdom] with t hterm hdt
      have h1 := hsum (1 / t) (ζ t) hdt.1 hdt.2
      have h2 : HasSum (fun w => if w ∈ (hfin (μ w₀)).toFinset then
            (∏ k, ζ t (w.2 k)) • a w (1 / t) else 0)
          (∑ w ∈ (hfin (μ w₀)).toFinset, (∏ k, ζ t (w.2 k)) • a w (1 / t)) := by
        have h2' : HasSum (fun w => if w ∈ (hfin (μ w₀)).toFinset then
              (∏ k, ζ t (w.2 k)) • a w (1 / t) else 0)
            (∑ w ∈ (hfin (μ w₀)).toFinset, if w ∈ (hfin (μ w₀)).toFinset then
              (∏ k, ζ t (w.2 k)) • a w (1 / t) else 0) :=
          hasSum_sum_of_ne_finset_zero fun w hw => by simp [hw]
        rwa [Finset.sum_congr rfl fun w hw => ite_eq_left hw] at h2'
      have h3 := h1.sub h2
      rw [hRest_def, hT₀]
      refine h3.norm_le_of_bounded
        (hmaj.hasSum.mul_left (Real.exp (-((μ w₀ + γ / 2) * t ^ p)))) fun w => ?_
      by_cases hw : w ∈ (hfin (μ w₀)).toFinset
      · simp only [hw, ↓reduceIte, sub_self, norm_zero]
        exact mul_nonneg (Real.exp_pos _).le
          (mul_nonneg hS (Finset.prod_nonneg fun _ _ => by positivity))
      · have hlt : μ w₀ < μ w := by
          simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] at hw; exact hw
        simp only [hw, ↓reduceIte, sub_zero]
        exact hterm w hlt
    have hRest : FasterThanPowers (fun t => D t • Rest t) := by
      refine ftp_of_le_exp_sub (K := A ^ w₀.1 * T₀) (M := N * w₀.1) (m := μ w₀) (c := γ / 2)
        (by positivity) hp ?_
      filter_upwards [hD, hRestle] with t hDt hRt
      rw [norm_smul, Real.norm_of_nonneg hDt.2.1]
      calc D t * ‖Rest t‖ ≤ (A ^ w₀.1 * t ^ (N * w₀.1) * Real.exp (μ w₀ * t ^ p)) *
            (Real.exp (-((μ w₀ + γ / 2) * t ^ p)) * T₀) :=
            mul_le_mul hDt.2.2.2 hRt (norm_nonneg _) (hDt.2.1.trans hDt.2.2.2)
        _ = _ := by ring
    -- (f) The terms `ν_j ζ_j G_j(1/t, ζ)`, divided by the monomial of `w₀`.
    obtain ⟨Ej, hEj_def⟩ : ∃ Ej : ι → ℝ → F, ∀ j t, Ej j t =
        D t • ((ν t j * ζ t j) • G j (1 / t, ζ t)) -
          if r j = μ w₀ then ν t j • G j (1 / t, 0) else 0 := ⟨_, fun j t => rfl⟩
    have hEj : ∀ j, FasterThanPowers (Ej j) := by
      intro j
      rcases lt_trichotomy (r j) (μ w₀) with hlt | heq | hgt
      · -- Smaller rate: `G_j` vanishes near `(0, 0)` by the induction hypothesis.
        have hGj := (IH ⟨1, fun _ => j⟩ (by rw [hμsingle]; exact hlt)).2 j (hμsingle j).symm
        refine ftp_of_eventually_eq_zero ?_
        filter_upwards [hpt.eventually hGj] with t ht
        rw [hEj_def, ht, smul_zero, smul_zero, ite_eq_right hlt.ne, sub_zero]
      · -- Equal rate: the monomial of `w₀` is `ζ_j`; `G_j` is locally Lipschitz.
        have hZj : ∀ t, ∏ k, ζ t (w₀.2 k) = ζ t j := fun t => by
          rw [hmono w₀ ⟨1, fun _ => j⟩ (by rw [hμsingle]; exact heq.symm)]; simp
        obtain ⟨K, U, hU, hLip⟩ := ((hG j).contDiffAt (n := 1)).exists_lipschitzOnWith
        refine fasterThanPowers_of_le_pow_mul_exp (A := A * K * A) (N := N + N) hδ hp ?_
        filter_upwards [hray, hD, hζnorm, hpt hU, hpt0 hU] with t ht hDt hζt hU1 hU0
        have hB : 0 ≤ A * t ^ N := mul_nonneg (by linarith) (pow_nonneg (by linarith [ht.1]) N)
        have h1 : D t * (ν t j * ζ t j) = ν t j := by
          have := hDt.2.2.1
          rw [hZj] at this
          calc D t * (ν t j * ζ t j) = ν t j * (D t * ζ t j) := by ring
            _ = ν t j := by rw [this, mul_one]
        rw [hEj_def, ite_eq_left heq, smul_smul, h1, ← smul_sub, norm_smul, Real.norm_eq_abs]
        have hL := hLip.dist_le_mul _ hU1 _ hU0
        rw [dist_eq_norm, Prod.dist_eq, dist_self, dist_zero_right,
          max_eq_right (norm_nonneg _)] at hL
        calc |ν t j| * ‖G j (1 / t, ζ t) - G j (1 / t, 0)‖
            ≤ (A * t ^ N) * (K * (A * t ^ N * Real.exp (-(δ * t ^ p)))) :=
              mul_le_mul (ht.2 j).2.2.2 (hL.trans (mul_le_mul_of_nonneg_left hζt K.coe_nonneg))
                (norm_nonneg _) hB
          _ = A * K * A * t ^ (N + N) * Real.exp (-(δ * t ^ p)) := by ring
      · -- Larger rate: at most `e^{-(r_j - m) t^p}` times a power of `t`.
        have hbdd : ∀ᶠ z in 𝓝 (0 : ℝ × (ι → ℝ)), ‖G j z‖ ≤ ‖G j 0‖ + 1 := by
          filter_upwards [(hG j).continuousAt.norm.eventually
            (Iio_mem_nhds (lt_add_one ‖G j 0‖))] with z hz
          exact le_of_lt hz
        refine ftp_of_le_exp_sub (K := A ^ w₀.1 * (A * A * (‖G j 0‖ + 1)))
          (M := N * w₀.1 + (N + N)) (m := μ w₀) (c := r j - μ w₀) (by linarith) hp ?_
        filter_upwards [hray, hD, hpt.eventually hbdd] with t ht hDt hGt
        have hB : 0 ≤ A * t ^ N := mul_nonneg (by linarith) (pow_nonneg (by linarith [ht.1]) N)
        rw [hEj_def, ite_eq_right hgt.ne', sub_zero, norm_smul, norm_smul, Real.norm_of_nonneg hDt.2.1,
          Real.norm_eq_abs, abs_mul, abs_of_pos (ht.2 j).1]
        calc D t * (|ν t j| * ζ t j * ‖G j (1 / t, ζ t)‖)
            ≤ (A ^ w₀.1 * t ^ (N * w₀.1) * Real.exp (μ w₀ * t ^ p)) *
              ((A * t ^ N) * (A * t ^ N * Real.exp (-(r j * t ^ p))) * (‖G j 0‖ + 1)) := by
              refine mul_le_mul hDt.2.2.2 ?_
                (mul_nonneg (mul_nonneg (abs_nonneg _) (ht.2 j).1.le) (norm_nonneg _))
                (hDt.2.1.trans hDt.2.2.2)
              exact mul_le_mul (mul_le_mul (ht.2 j).2.2.2 (ht.2 j).2.2.1 (ht.2 j).1.le hB) hGt
                (norm_nonneg _) (mul_nonneg hB (mul_nonneg hB (Real.exp_pos _).le))
          _ = _ := by rw [show μ w₀ + (r j - μ w₀) = r j by ring]; ring
    -- (g) Hence `C_m(1/t) + ∑_{r_j = m} ν_j(t) G_j(1/t, 0)` tends to `0` faster than every power.
    have hY : FasterThanPowers (fun t => C (μ w₀) (1 / t) +
        ∑ j, if r j = μ w₀ then ν t j • G j (1 / t, 0) else 0) := by
      have h := ftp_sub (ftp_sub hQ hRest) (ftp_sum Finset.univ Ej fun j _ => hEj j)
      refine h.congr ?_
      filter_upwards [hD, hdom] with t hDt hdt
      have hh := hhead (1 / t) hdt.1 (ζ t)
      have hDZ : D t • (∏ k, ζ t (w₀.2 k)) • C (μ w₀) (1 / t) = C (μ w₀) (1 / t) := by
        rw [smul_smul, hDt.2.2.1, one_smul]
      rw [hE_def, hRest_def, hh, smul_add, smul_sub, hDZ, Finset.smul_sum]
      simp only [hEj_def, Finset.sum_sub_distrib]
      abel
    -- (h) One small factor: if `m = r_i`, then `G_i` vanishes near `(0, 0)` (`hstep`).
    have hGi : ∀ i, r i = μ w₀ → ∀ᶠ z in 𝓝 (0 : ℝ × (ι → ℝ)), G i z = 0 := by
      intro i hi
      apply hstep i
      have hw : fib (μ w₀) = {⟨1, fun _ => i⟩} := Finset.ext fun w => by
        rw [hfib, Finset.mem_singleton]
        exact ⟨fun h => hsingle w i (h.trans hi.symm), fun h => by rw [h, hμsingle, hi]⟩
      refine hY.congr ?_
      filter_upwards [hdom] with t hdt
      have hC : C (μ w₀) (1 / t) =
          fderiv ℝ (fun y : ι → ℝ => G₀ (1 / t, y)) 0 (Pi.single i 1) := by
        rw [hder _ i hdt.1]; simp only [C, hw, Finset.sum_singleton]
      have hs1 : (∑ j, if r j = μ w₀ then ν t j • G j (1 / t, 0) else 0) =
          ν t i • G i (1 / t, 0) := by
        rw [Finset.sum_eq_single i]
        · rw [ite_eq_left hi]
        · intro j _ hji
          rw [ite_eq_right]
          intro hj
          exact hji (hrQ.injective (hj.trans hi.symm))
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [hC, hs1]
    -- (i) The coefficient `C_m` tends to `0` faster than every power, so it vanishes.
    have hite : ∀ᶠ t : ℝ in atTop,
        (∑ j, if r j = μ w₀ then ν t j • G j (1 / t, 0) else 0) = 0 := by
      have h : ∀ j, ∀ᶠ t : ℝ in atTop,
          (if r j = μ w₀ then ν t j • G j (1 / t, 0) else 0) = 0 := by
        intro j
        by_cases hj : r j = μ w₀
        · filter_upwards [hpt0.eventually (hGi j hj)] with t ht
          rw [ite_eq_left hj, ht, smul_zero]
        · exact Eventually.of_forall fun t => ite_eq_right hj
      filter_upwards [eventually_all.2 h] with t ht
      exact Finset.sum_eq_zero fun j _ => ht j
    have hCm : FasterThanPowers (fun t => C (μ w₀) (1 / t)) := by
      refine hY.congr ?_
      filter_upwards [hite] with t ht
      rw [ht, add_zero]
    have h0 := eventually_nhds_eq_zero_of_fasterThanPowers
      ((hCan (μ w₀)) 0 (Metric.mem_ball_self hρ)) hCm
    refine ⟨fun s hs => ?_, hGi⟩
    exact (hCan (μ w₀)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball 0 ρ).isPreconnected (Metric.mem_ball_self hρ) h0 hs
  -- The induction, on the number of words of smaller or equal rate.
  have hall : ∀ w, Pr w := by
    have key : ∀ n : ℕ, ∀ w, (hfin (μ w)).toFinset.card = n → Pr w := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro w hw
        refine step w fun w' hw' => ih _ ?_ w' rfl
        rw [← hw]
        refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
        · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx ⊢; linarith
        · have := hsub (show w ∈ (hfin (μ w)).toFinset by simp)
          simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at this; linarith
    exact fun w => key _ w rfl
  refine ⟨?_, fun j => (hall ⟨1, fun _ => j⟩).2 j (hμsingle j).symm⟩
  -- `G₀ = 0` near `(0, 0)`: every homogeneous part of its expansion in `y` vanishes.
  have h1 : ∀ᶠ z : ℝ × (ι → ℝ) in 𝓝 0, |z.1| < ρ := by
    have : ContinuousAt (fun z : ℝ × (ι → ℝ) => |z.1|) 0 :=
      (continuous_abs.comp continuous_fst).continuousAt
    exact this.eventually_lt continuousAt_const (by simpa using hρ)
  have h2 : ∀ᶠ z : ℝ × (ι → ℝ) in 𝓝 0, ∑ j, |z.2 j| < ρ := by
    have : ContinuousAt (fun z : ℝ × (ι → ℝ) => ∑ j, |z.2 j|) 0 :=
      (continuous_finsetSum _ fun j _ =>
        continuous_abs.comp ((continuous_apply j).comp continuous_snd)).continuousAt
    exact this.eventually_lt continuousAt_const (by simpa using hρ)
  filter_upwards [h1, h2] with z hz1 hz2
  have hs := (hsum z.1 z.2 hz1 hz2).sigma fun n => hasSum_fintype _
  have hn : ∀ n, ∑ v : Fin n → ι, (∏ k, z.2 (v k)) • a ⟨n, v⟩ z.1 = 0 := by
    intro n
    have := hgroup ((Finset.univ : Finset (Fin n → ι)).map ⟨Sigma.mk n, sigma_mk_injective⟩)
      z.2 z.1 ?_ ?_
    · rwa [Finset.sum_map] at this
    · intro w hw w' hw'
      obtain ⟨v, -, rfl⟩ := Finset.mem_map.1 hw
      obtain ⟨n', v'⟩ := w'
      have hn' : n' = n := hlen _ _ hw'
      subst hn'
      exact Finset.mem_map.2 ⟨v', Finset.mem_univ _, rfl⟩
    · intro w _
      exact (hall w).1 z.1 (mem_ball_zero_iff.2 (by rwa [Real.norm_eq_abs]))
  simp only [hn] at hs
  exact hs.unique hasSum_zero

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
  -- The small terms are positive for large `t`, and the bounds hold with `max A 1 ≥ 1`.
  have hev : ∀ᶠ t : ℝ in atTop, 1 ≤ t ∧ ∀ j, 0 < ζ t j ∧
      Real.exp (-(r j * t ^ p)) ≤ max A 1 * t ^ N * ζ t j ∧
      ζ t j ≤ max A 1 * t ^ N * Real.exp (-(r j * t ^ p)) ∧ |ν t j| ≤ max A 1 * t ^ N := by
    filter_upwards [hζl, hζu, hν, eventually_ge_atTop 1] with t h1 h2 h3 ht
    refine ⟨ht, fun j => ?_⟩
    have he := Real.exp_pos (-(r j * t ^ p))
    have htN : 0 ≤ t ^ N := pow_nonneg (by linarith) N
    have hAA : A ≤ max A 1 := le_max_left A 1
    have hl := h1 j
    have hu := h2 j
    have hpos : 0 < ζ t j := by
      by_contra hneg
      push Not at hneg
      rw [abs_of_nonpos hneg] at hu
      nlinarith [mul_le_mul_of_nonneg_left hu (neg_nonneg.2 hneg),
        mul_le_mul_of_nonneg_left hl he.le, mul_pos he he]
    refine ⟨hpos, ?_, ?_, ?_⟩
    · exact hl.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAA htN) hpos.le)
    · exact (le_abs_self _).trans
        (hu.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAA htN) he.le))
    · exact (h3 j).trans (mul_le_mul_of_nonneg_right hAA htN)
  exact ray_induction_core p hp r hr hrQ ζ ν (max A 1) N (le_max_right A 1) hev G₀ G hG₀ hG hid
    hstep

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
  classical
  -- The continuous linear equivalence `v ↦ (a, b) ↦ v (a, b)` from `ℝ^{T × q}` onto the matrices.
  let eL : (T × q → ℝ) ≃ₗ[ℝ] Matrix T q ℝ :=
    { toFun := fun v => Matrix.of fun a b => v (a, b)
      invFun := fun M i => M i.1 i.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e : (T × q → ℝ) ≃L[ℝ] Matrix T q ℝ := eL.toContinuousLinearEquiv
  have he : ∀ v, e v = Matrix.of fun a b => v (a, b) := fun v => rfl
  -- The map `φ (s, v) = (s, e v)` and its inverse `ψ`.
  let φ : ℝ × (T × q → ℝ) →L[ℝ] ℝ × Matrix T q ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (T × q → ℝ)).prod
      ((e : (T × q → ℝ) →L[ℝ] Matrix T q ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (T × q → ℝ)))
  have hφ : ∀ s v, φ (s, v) = (s, e v) := fun s v => rfl
  have hψ : Continuous fun z : ℝ × Matrix T q ℝ => ((z.1, e.symm z.2) : ℝ × (T × q → ℝ)) :=
    continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)
  have hφψ : ∀ z : ℝ × Matrix T q ℝ, φ (z.1, e.symm z.2) = z := fun z => by
    rw [hφ, e.apply_symm_apply]
  -- Pulling back a statement "near `0`" along `ψ`, and pushing one forward along `φ`.
  have hback : ∀ H : ℝ × Matrix T q ℝ → F,
      (∀ᶠ z in 𝓝 (0 : ℝ × (T × q → ℝ)), H (φ z) = 0) → ∀ᶠ z in 𝓝 (0 : ℝ × Matrix T q ℝ), H z = 0 := by
    intro H h
    have h0 : ((0 : ℝ × Matrix T q ℝ).1, e.symm (0 : ℝ × Matrix T q ℝ).2) = (0 : ℝ × (T × q → ℝ)) := by
      simp
    have ht := hψ.tendsto (0 : ℝ × Matrix T q ℝ)
    rw [h0] at ht
    filter_upwards [ht.eventually h] with z hz
    rwa [hφψ] at hz
  have hfwd : ∀ H : ℝ × Matrix T q ℝ → F,
      (∀ᶠ z in 𝓝 (0 : ℝ × Matrix T q ℝ), H z = 0) → ∀ᶠ z in 𝓝 (0 : ℝ × (T × q → ℝ)), H (φ z) = 0 := by
    intro H h
    have ht := φ.continuous.tendsto (0 : ℝ × (T × q → ℝ))
    rw [map_zero] at ht
    exact ht.eventually h
  have hζe : ∀ t, e (fun i : T × q => ζ t i.1 i.2) = ζ t := fun t => rfl
  have key := ray_induction p hp (fun i : T × q => r i.1 i.2) (fun i => hr i.1 i.2) hrQ
    (fun t i => ζ t i.1 i.2) (fun t i => ν t i.1 i.2) A N
    (by filter_upwards [hζl] with t ht; exact fun i => ht i.1 i.2)
    (by filter_upwards [hζu] with t ht; exact fun i => ht i.1 i.2)
    (by filter_upwards [hν] with t ht; exact fun i => ht i.1 i.2)
    (fun z => G₀ (φ z)) (fun i z => G i.1 i.2 (φ z))
    (by
      have h := hG₀
      rw [← map_zero φ] at h
      exact h.comp (φ.analyticAt 0))
    (fun i => by
      have h := hG i.1 i.2
      rw [← map_zero φ] at h
      exact h.comp (φ.analyticAt 0))
    (fun R => by
      filter_upwards [hid R] with t ht
      rw [hφ, hζe, Fintype.sum_prod_type]
      exact ht)
    (fun i hi => by
      refine hfwd _ (hstep i.1 i.2 (hi.congr (Eventually.of_forall fun t => ?_)))
      have h1 : (fun y : T × q → ℝ => G₀ (φ (1 / t, y))) =
          (fun Y : Matrix T q ℝ => G₀ (1 / t, Y)) ∘ e := rfl
      have h2 : e (Pi.single i (1 : ℝ)) = Matrix.single i.1 i.2 1 := by
        ext a b
        simp [he, Pi.single_apply, Matrix.single_apply, Prod.ext_iff, eq_comm]
      have h3 := e.comp_right_fderiv (f := fun Y : Matrix T q ℝ => G₀ (1 / t, Y))
        (x := (0 : T × q → ℝ))
      have h4 : (fderiv ℝ (fun y : T × q → ℝ => G₀ (φ (1 / t, y))) 0) (Pi.single i 1) =
          (fderiv ℝ (fun Y : Matrix T q ℝ => G₀ (1 / t, Y)) (e 0)) (e (Pi.single i 1)) :=
        congrArg (fun L => L (Pi.single i (1 : ℝ))) (h1 ▸ h3)
      rw [map_zero, h2] at h4
      rw [h4, hφ, map_zero])
  exact ⟨hback _ key.1, fun a j => hback _ (key.2 (a, j))⟩

end Skips
