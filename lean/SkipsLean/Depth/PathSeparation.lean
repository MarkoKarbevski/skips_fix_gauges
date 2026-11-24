import SkipsLean.Depth.RaySeparation

/-!
# Separation on the path

Paper (dimension paper): Lemma D.16 (Separation on the path), Appendix D.6 (the case `ε = 0`).
"Let `u_1, …, u_q > 0` be linearly independent over `ℚ`, let `u'_1, …, u'_q` be real, and for
`t ≥ 1` let

  `ζ_j(t) = exp(−(t + t⁻¹) u_j − i (t − t⁻¹) u'_j)`.

Let `ρ₀ > max_j e^{−2 u_j}`, and let `𝒯_{−K}, …, 𝒯_K` be holomorphic maps from the polydisc
`{ζ ∈ ℂ^q : |ζ_j| < ρ₀}` to `ℂ^{1 × d_out}`. If `∑_{i=−K}^{K} t^i 𝒯_i(ζ_1(t), …, ζ_q(t)) = 0` for all
`t ≥ 1`, then `𝒯_i = 0` for every `i`."

"This is the proof of Lemma D.1, with a phase and with negative powers": in the expansion
`𝒯_i(ζ) = ∑_α b_{i,α} ζ^α` the monomial `ζ(t)^α` has the absolute value `e^{−(t + t⁻¹) μ_α}`,
`μ_α = ∑_j α_j u_j`; these rates are pairwise different, and finitely many lie below any bound.

As for Lemma D.1 (`Depth/RaySeparation.lean`), the middle step is stated on its own, for maps that
are analytic at `0` and an identity for all large `t`, with nonnegative powers of `t` (negative
powers are removed by multiplying with `t^K`). Holomorphic maps of several variables are
`AnalyticOnNhd ℂ` here.
-/

namespace Skips

open Filter Topology

/-- A real polynomial `∑_{i ≤ K} b_i t^i` that tends to `0` as `t → ∞` has all coefficients
zero. -/
private lemma coeffs_eq_zero_of_tendsto_real_ps {K : ℕ} (b : Fin (K + 1) → ℝ)
    (h : Tendsto (fun t : ℝ => ∑ i : Fin (K + 1), t ^ (i : ℕ) * b i) atTop (𝓝 0)) :
    ∀ i, b i = 0 := by
  classical
  let P : Polynomial ℝ := ∑ i : Fin (K + 1), Polynomial.C (b i) * Polynomial.X ^ (i : ℕ)
  have heval : ∀ t, P.eval t = ∑ i : Fin (K + 1), t ^ (i : ℕ) * b i := fun t => by
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hP : P = 0 := by
    have hT : Tendsto (fun t => P.eval t) atTop (𝓝 0) := by simpa only [heval] using h
    exact Polynomial.leadingCoeff_eq_zero.1 (Polynomial.tendsto_nhds_iff.1 hT).1
  intro i
  have hc : P.coeff i = b i := by
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    simp [Fin.val_inj]
  rw [← hc, hP, Polynomial.coeff_zero]

/-- A complex polynomial `∑_{i ≤ K} b_i t^i` in the real variable `t` that tends to `0` as
`t → ∞` has all coefficients zero (real and imaginary parts separately). -/
private lemma coeffs_eq_zero_of_tendsto_ps {K : ℕ} (b : Fin (K + 1) → ℂ)
    (h : Tendsto (fun t : ℝ => ∑ i : Fin (K + 1), (t : ℂ) ^ (i : ℕ) * b i) atTop (𝓝 0)) :
    ∀ i, b i = 0 := by
  have hre := (Complex.continuous_re.tendsto 0).comp h
  have him := (Complex.continuous_im.tendsto 0).comp h
  have h1 := coeffs_eq_zero_of_tendsto_real_ps (fun i => (b i).re) (by
    refine hre.congr fun t => ?_
    simp only [Function.comp_apply, Complex.re_sum, ← Complex.ofReal_pow, Complex.re_ofReal_mul])
  have h2 := coeffs_eq_zero_of_tendsto_real_ps (fun i => (b i).im) (by
    refine him.congr fun t => ?_
    simp only [Function.comp_apply, Complex.im_sum, ← Complex.ofReal_pow, Complex.im_ofReal_mul])
  intro i
  exact Complex.ext (by simpa using h1 i) (by simpa using h2 i)

/-- Domination: if `‖c a‖ e^{-μ_a s₀}` is summable, all `μ_a ≥ 0` and `‖w_a‖ = e^{-μ_a s}` with
`s₀ ≤ s`, then `c a w_a` is summable. -/
private lemma summable_mul_of_norm_ps {A : Type*} (μ : A → ℝ) (c w : A → ℂ)
    (hμ : ∀ a, 0 ≤ μ a) {s₀ s : ℝ} (hs : s₀ ≤ s) (hw : ∀ a, ‖w a‖ = Real.exp (-(μ a * s)))
    (hsum : Summable fun a => ‖c a‖ * Real.exp (-(μ a * s₀))) :
    Summable fun a => c a * w a := by
  refine hsum.of_norm_bounded fun a => ?_
  rw [norm_mul, hw]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hμ a])) (norm_nonneg _)

/-- **The leading-term argument, with phases.** Let `∑_a (∑_i t^i c_{a,i}) w_a(t) = 0` for all
`t ≥ t₀`, where `‖w_a(t)‖ = e^{-μ_a τ(t)}` with rates `μ_a ≥ 0` of which finitely many lie below
any bound, `w_a = w_b` when `μ_a = μ_b`, `τ` nondecreasing from `t₀` on with `τ(t) ≥ t`, and an
absolutely summable majorant at `t₀`. Then for every rate `m` the coefficients `c_{a,i}` with
`μ_a = m` sum to zero. -/
private lemma fiber_sum_eq_zero_ps {A : Type*} {K : ℕ} (μ : A → ℝ) (c : A → Fin (K + 1) → ℂ)
    (w : A → ℝ → ℂ) (τ : ℝ → ℝ) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (hμ : ∀ a, 0 ≤ μ a)
    (hfin : ∀ B, {a | μ a ≤ B}.Finite)
    (hw : ∀ a t, ‖w a t‖ = Real.exp (-(μ a * τ t)))
    (hweq : ∀ a b t, μ a = μ b → w a t = w b t)
    (hτ : ∀ t, t₀ ≤ t → τ t₀ ≤ τ t) (hτt : ∀ t, t₀ ≤ t → t ≤ τ t)
    (hsum : ∀ i, Summable fun a => ‖c a i‖ * Real.exp (-(μ a * τ t₀)))
    (hzero : ∀ t, t₀ ≤ t →
      ∑ i : Fin (K + 1), (t : ℂ) ^ (i : ℕ) * ∑' a, c a i * w a t = 0)
    (m : ℝ) (s : Finset A) (hs : ∀ a, a ∈ s ↔ μ a = m) (i : Fin (K + 1)) :
    ∑ a ∈ s, c a i = 0 := by
  classical
  -- The fibre of a rate, as a finite set.
  let fib : ℝ → Finset A := fun m => (hfin m).toFinset.filter fun a => μ a = m
  have hfib : ∀ m a, a ∈ fib m ↔ μ a = m := fun m a => by
    simp only [fib, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
  clear_value fib
  have hs' : s = fib m := Finset.ext fun a => by rw [hs, hfib]
  suffices H : ∀ m i, ∑ a ∈ fib m, c a i = 0 by rw [hs']; exact H m i
  by_contra! hbad
  obtain ⟨m₀, i₀, hm₀⟩ := hbad
  -- Among the rates whose fibre does not sum to zero, take the smallest one `m₁ = μ a₁`.
  let W := (hfin m₀).toFinset.filter fun a => ∃ i, ∑ a' ∈ fib (μ a), c a' i ≠ 0
  have hW : W.Nonempty := by
    obtain ⟨a₀, ha₀⟩ := Finset.nonempty_of_sum_ne_zero hm₀
    have hμa₀ := (hfib _ _).1 ha₀
    refine ⟨a₀, Finset.mem_filter.2 ⟨?_, i₀, by rw [hμa₀]; exact hm₀⟩⟩
    simp [hμa₀]
  obtain ⟨a₁, ha₁W, ha₁min⟩ := W.exists_min_image μ hW
  obtain ⟨hm₁le, hbad₁⟩ := Finset.mem_filter.1 ha₁W
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hm₁le
  set m₁ := μ a₁ with hm₁
  -- Below `m₁` every fibre sums to zero.
  have hbelow : ∀ a, μ a < m₁ → ∀ i, ∑ a' ∈ fib (μ a), c a' i = 0 := by
    intro a ha i
    by_contra hne
    have haW : a ∈ (hfin m₀).toFinset := by
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]; linarith
    exact absurd (ha₁min a (Finset.mem_filter.2 ⟨haW, i, hne⟩)) (not_le.2 ha)
  -- The gap `γ` between `m₁` and the next larger rate.
  obtain ⟨γ, hγ, hgap⟩ : ∃ γ > 0, ∀ a, m₁ < μ a → m₁ + γ ≤ μ a := by
    let S := (hfin (m₁ + 1)).toFinset.filter fun a => m₁ < μ a
    by_cases hS : S.Nonempty
    · obtain ⟨a₂, ha₂S, ha₂min⟩ := S.exists_min_image μ hS
      have h2 := (Finset.mem_filter.1 ha₂S).2
      refine ⟨min 1 (μ a₂ - m₁), lt_min one_pos (by linarith), fun a ha => ?_⟩
      by_cases ha1 : μ a ≤ m₁ + 1
      · have := ha₂min a (Finset.mem_filter.2 ⟨by simpa using ha1, ha⟩)
        have := min_le_right 1 (μ a₂ - m₁); linarith
      · have := min_le_left 1 (μ a₂ - m₁); linarith
    · refine ⟨1, one_pos, fun a ha => ?_⟩
      by_contra ha1
      have haS : a ∈ (hfin (m₁ + 1)).toFinset := by
        simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]; linarith
      exact hS ⟨a, Finset.mem_filter.2 ⟨haS, ha⟩⟩
  -- The leading polynomial `P(t) = ∑_i t^i F_i`, `F_i` the sum over the fibre of `m₁`.
  let F : Fin (K + 1) → ℂ := fun i => ∑ a ∈ fib m₁, c a i
  -- Split every series into the rates `≤ m₁` (finitely many) and the rest.
  let L := (hfin m₁).toFinset
  have hL : ∀ a, a ∈ L ↔ μ a ≤ m₁ := fun a => by simp [L]
  clear_value L
  let R : Fin (K + 1) → ℝ → ℂ := fun i t => ∑' x : ↥((L : Set A)ᶜ), c x i * w x t
  have hcompl : ∀ x : ↥((L : Set A)ᶜ), m₁ < μ x := fun x => by
    have := x.2
    simp only [Set.mem_compl_iff, Finset.mem_coe, hL, not_le] at this
    exact this
  -- On the fibre of `m₁` all monomials are `w a₁`; below `m₁` the fibres sum to zero.
  have hhead : ∀ i t, ∑ a ∈ L, c a i * w a t = w a₁ t * F i := by
    intro i t
    rw [← Finset.sum_fiberwise_of_maps_to (g := μ) (t := L.image μ)
      (fun x hx => Finset.mem_image_of_mem μ hx)]
    rw [Finset.sum_eq_single m₁]
    · have hLm : L.filter (fun x => μ x = m₁) = fib m₁ :=
        Finset.ext fun a => by
          rw [Finset.mem_filter, hL, hfib]; exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
      rw [hLm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hweq a a₁ t ((hfib _ _).1 ha), mul_comm]
    · intro m hm hne
      obtain ⟨a, haL, rfl⟩ := Finset.mem_image.1 hm
      have hlt : μ a < m₁ := lt_of_le_of_ne ((hL a).1 haL) hne
      have hLm : L.filter (fun x => μ x = μ a) = fib (μ a) :=
        Finset.ext fun a' => by
          rw [Finset.mem_filter, hL, hfib]
          exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hlt.le, h⟩⟩
      rw [hLm, Finset.sum_congr rfl (fun a' ha' => by rw [hweq a' a t ((hfib _ _).1 ha')]),
        ← Finset.sum_mul, hbelow a hlt i, zero_mul]
    · intro h
      exact absurd (Finset.mem_image_of_mem μ ((hL a₁).2 le_rfl)) h
  have hsplit : ∀ i t, t₀ ≤ t → ∑' a, c a i * w a t = w a₁ t * F i + R i t := by
    intro i t ht
    rw [← (summable_mul_of_norm_ps μ (fun a => c a i) (fun a => w a t) hμ (hτ t ht)
      (fun a => hw a t) (hsum i)).sum_add_tsum_compl (s := L), hhead]
  -- The rest is at most `e^{-m₁ τ(t)} e^{-γ (τ(t) - τ(t₀))} e^{m₁ τ(t₀)} M_i`.
  let M : Fin (K + 1) → ℝ := fun i =>
    ∑' x : ↥((L : Set A)ᶜ), ‖c x i‖ * Real.exp (-(μ x * τ t₀))
  have hM : ∀ i, 0 ≤ M i := fun i => tsum_nonneg fun x => by positivity
  have hrest : ∀ i t, t₀ ≤ t → ‖R i t‖ ≤ Real.exp (-(m₁ * τ t)) *
      (Real.exp (-(γ * (τ t - τ t₀))) * Real.exp (m₁ * τ t₀) * M i) := by
    intro i t ht
    have hmaj : Summable fun x : ↥((L : Set A)ᶜ) => ‖c x i‖ * Real.exp (-(μ x * τ t₀)) :=
      (hsum i).subtype _
    have hterm : ∀ x : ↥((L : Set A)ᶜ), ‖c x i * w x t‖ ≤
        Real.exp (-(m₁ * τ t)) * (Real.exp (-(γ * (τ t - τ t₀))) * Real.exp (m₁ * τ t₀)) *
          (‖c x i‖ * Real.exp (-(μ x * τ t₀))) := by
      intro x
      have h1 := hgap x (hcompl x)
      have h2 := hτ t ht
      rw [norm_mul, hw]
      calc ‖c x i‖ * Real.exp (-(μ x * τ t))
          ≤ ‖c x i‖ * Real.exp (-(m₁ * τ t) + -(γ * (τ t - τ t₀)) + m₁ * τ t₀ +
              -(μ x * τ t₀)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
            nlinarith
        _ = _ := by rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring
    have hsn : Summable fun x : ↥((L : Set A)ᶜ) => ‖c x i * w x t‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hmaj.mul_left _)
    calc ‖R i t‖ ≤ ∑' x : ↥((L : Set A)ᶜ), ‖c x i * w x t‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' x : ↥((L : Set A)ᶜ), Real.exp (-(m₁ * τ t)) *
            (Real.exp (-(γ * (τ t - τ t₀))) * Real.exp (m₁ * τ t₀)) *
            (‖c x i‖ * Real.exp (-(μ x * τ t₀))) :=
          Summable.tsum_le_tsum hterm hsn (hmaj.mul_left _)
      _ = _ := by simp only [M, tsum_mul_left]; ring
  -- Hence `e^{-m₁ τ(t)} |P(t)| = |∑_i t^i R_i(t)|`, and `|P(t)|` is at most a sum of
  -- `t^i e^{-γ (τ(t) - τ(t₀))}` times constants.
  have hP : ∀ t, t₀ ≤ t → ‖∑ i : Fin (K + 1), (t : ℂ) ^ (i : ℕ) * F i‖ ≤
      ∑ i : Fin (K + 1), t ^ (i : ℕ) *
        (Real.exp (-(γ * (τ t - τ t₀))) * Real.exp (m₁ * τ t₀) * M i) := by
    intro t ht
    have ht0 : 0 ≤ t := ht₀.trans ht
    have h0 := hzero t ht
    rw [Finset.sum_congr rfl fun i _ => by rw [hsplit i t ht]] at h0
    have heq : w a₁ t * ∑ i : Fin (K + 1), (t : ℂ) ^ (i : ℕ) * F i =
        -∑ i : Fin (K + 1), (t : ℂ) ^ (i : ℕ) * R i t := by
      rw [eq_neg_iff_add_eq_zero, Finset.mul_sum, ← Finset.sum_add_distrib, ← h0]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hnorm := congrArg norm heq
    rw [norm_mul, hw, norm_neg, ← hm₁] at hnorm
    refine le_of_mul_le_mul_left ?_ (Real.exp_pos (-(m₁ * τ t)))
    rw [hnorm, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0]
    calc t ^ (i : ℕ) * ‖R i t‖ ≤ t ^ (i : ℕ) * (Real.exp (-(m₁ * τ t)) *
          (Real.exp (-(γ * (τ t - τ t₀))) * Real.exp (m₁ * τ t₀) * M i)) :=
          mul_le_mul_of_nonneg_left (hrest i t ht) (pow_nonneg ht0 _)
      _ = _ := by ring
  -- The bound tends to `0`, so `P(t) → 0`.
  have hlim : Tendsto (fun t : ℝ => ∑ i : Fin (K + 1), (t : ℂ) ^ (i : ℕ) * F i) atTop (𝓝 0) := by
    let b : ℝ → ℝ := fun t => ∑ i : Fin (K + 1),
      t ^ (i : ℕ) * (Real.exp (-(γ * (t - τ t₀))) * Real.exp (m₁ * τ t₀) * M i)
    have hb : Tendsto b atTop (𝓝 0) := by
      have hterm : ∀ i : Fin (K + 1), Tendsto (fun t : ℝ => t ^ ((i : ℕ) : ℝ) *
          Real.exp (-γ * t) * (Real.exp (γ * τ t₀) * Real.exp (m₁ * τ t₀) * M i))
          atTop (𝓝 0) := fun i => by
        simpa only [zero_mul] using
          (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((i : ℕ) : ℝ) γ hγ).mul_const
            (Real.exp (γ * τ t₀) * Real.exp (m₁ * τ t₀) * M i)
      have := tendsto_finsetSum Finset.univ fun i _ => hterm i
      simp only [Finset.sum_const_zero] at this
      refine this.congr fun t => Finset.sum_congr rfl fun i _ => ?_
      rw [Real.rpow_natCast, show -(γ * (t - τ t₀)) = -γ * t + γ * τ t₀ by ring, Real.exp_add]
      ring
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop t₀] with t ht
    have ht0 : 0 ≤ t := ht₀.trans ht
    refine (hP t ht).trans (Finset.sum_le_sum fun i _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ht0 _)
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
      (Real.exp_pos _).le) (hM i)
    nlinarith [hτt t ht]
  obtain ⟨i, hi⟩ := hbad₁
  exact hi (coeffs_eq_zero_of_tendsto_ps F hlim i)

/-- A sum over `k : Fin n` of `f (r k)`, grouped by the value of `r k`. -/
private lemma sum_comp_eq_sum_card_ps {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] {n : ℕ} (r : Fin n → ι) (f : ι → M) :
    ∑ k, f (r k) = ∑ j, (Finset.univ.filter fun k => r k = j).card • f j := by
  rw [← Finset.sum_fiberwise Finset.univ r (fun k => f (r k))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2]), Finset.sum_const]

/-- A product over `k : Fin n` of `f (r k)`, grouped by the value of `r k`. -/
private lemma prod_comp_eq_prod_pow_ps {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    {n : ℕ} (r : Fin n → ι) (f : ι → M) :
    ∏ k, f (r k) = ∏ j, f j ^ (Finset.univ.filter fun k => r k = j).card := by
  rw [← Finset.prod_fiberwise Finset.univ r (fun k => f (r k))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2]), Finset.prod_const]

/-- If the rates `u_j` are linearly independent over `ℚ`, the rate `∑_k u_{r k}` of a word `r`
determines how often each letter `j` occurs in `r`. -/
private lemma card_fiber_eq_of_sum_eq_ps {ι : Type*} [Fintype ι] [DecidableEq ι] {u : ι → ℝ}
    (hu : LinearIndependent ℚ u) {n n' : ℕ} (r : Fin n → ι) (r' : Fin n' → ι)
    (h : ∑ k, u (r k) = ∑ k, u (r' k)) (j : ι) :
    (Finset.univ.filter fun k => r k = j).card = (Finset.univ.filter fun k => r' k = j).card := by
  have e1 := sum_comp_eq_sum_card_ps r u
  have e2 := sum_comp_eq_sum_card_ps r' u
  simp only [nsmul_eq_mul] at e1 e2
  have := (Fintype.linearIndependent_iff.1 hu)
    (fun j => ((Finset.univ.filter fun k => r k = j).card : ℚ) -
      (Finset.univ.filter fun k => r' k = j).card) ?_ j
  · exact_mod_cast sub_eq_zero.1 this
  · simp only [sub_smul, Finset.sum_sub_distrib, Rat.smul_def, Rat.cast_natCast]
    rw [← e1, ← e2, h, sub_self]

/-- The length of a word is the sum of the numbers of occurrences of the letters. -/
private lemma card_eq_sum_card_fiber_ps {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (r : Fin n → ι) : n = ∑ j, (Finset.univ.filter fun k => r k = j).card := by
  have := sum_comp_eq_sum_card_ps r (fun _ => (1 : ℕ))
  simpa using this

/-- Words with the same rate give the same monomial: if `∑_k u_{r k} = ∑_k u_{r' k}` (with `u`
linearly independent over `ℚ`), then `∏_k z_{r k} = ∏_k z_{r' k}`. -/
private lemma prod_eq_of_sum_eq_ps {ι M : Type*} [Fintype ι] [CommMonoid M] {u : ι → ℝ}
    (hu : LinearIndependent ℚ u) {n n' : ℕ} (r : Fin n → ι) (r' : Fin n' → ι)
    (h : ∑ k, u (r k) = ∑ k, u (r' k)) (z : ι → M) : ∏ k, z (r k) = ∏ k, z (r' k) := by
  classical
  rw [prod_comp_eq_prod_pow_ps, prod_comp_eq_prod_pow_ps]
  exact Finset.prod_congr rfl fun j _ => by rw [card_fiber_eq_of_sum_eq_ps hu r r' h j]

/-- Expansion of a homogeneous polynomial on `ℂ^ι` in monomials:
`f (ζ, …, ζ) = ∑_r f (e_{r 1}, …, e_{r n}) ∏_k ζ_{r k}`. -/
private lemma cmm_apply_diag_eq_sum_ps {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (f : ContinuousMultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ) (ζ : ι → ℂ) :
    f (fun _ => ζ) =
      ∑ r : Fin n → ι, f (fun k => Pi.single (r k) (1 : ℂ)) * ∏ k, ζ (r k) := by
  have hζ : ζ = ∑ j, ζ j • Pi.single j (1 : ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single ζ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have h1 := f.map_sum (fun (_ : Fin n) (j : ι) => ζ j • Pi.single j (1 : ℂ))
  conv_lhs => rw [hζ]
  rw [h1]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [f.map_smul_univ (fun k => ζ (r k)) (fun k => Pi.single (r k) (1 : ℂ)), smul_eq_mul,
    mul_comm]

/-- **The middle step of the proof of Lemma D.16.** Let the rates `u_j > 0` be linearly independent
over `ℚ`, let `u'_j` be real, and let `G_0, …, G_K` be analytic near `0 ∈ ℂ^q`. If
`∑_i t^i G_i(ζ_1(t), …, ζ_q(t)) = 0` for all large real `t`, with
`ζ_j(t) = exp(−(t + t⁻¹) u_j − i (t − t⁻¹) u'_j)`, then every `G_i` vanishes near `0`. -/
theorem eventually_eq_zero_of_sum_pow_mul_exp_path {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (hpos : ∀ j, 0 < u j) (hu : LinearIndependent ℚ u) (u' : ι → ℝ)
    (K : ℕ) (G : Fin (K + 1) → (ι → ℂ) → ℂ) (hG : ∀ i, AnalyticAt ℂ (G i) 0)
    (h : ∀ᶠ t : ℝ in atTop,
      ∑ i : Fin (K + 1), (t : ℂ) ^ (i : ℕ) * G i (fun j =>
        Complex.exp (-(((t + t⁻¹) * u j : ℝ) : ℂ) - Complex.I * (((t - t⁻¹) * u' j : ℝ) : ℂ)))
        = 0) :
    ∀ i, ∀ᶠ ζ in 𝓝 (0 : ι → ℂ), G i ζ = 0 := by
  classical
  -- Power series `p i` of the `G i` at `0`, on a common ball of radius `R`.
  have hG' : ∀ i, ∃ p : FormalMultilinearSeries ℂ (ι → ℂ) ℂ, ∃ r,
      HasFPowerSeriesOnBall (G i) p 0 r := fun i => by
    obtain ⟨p, r, hr⟩ := hG i
    exact ⟨p, r, hr⟩
  choose p r hr using hG'
  let R := Finset.univ.inf' Finset.univ_nonempty r
  have hR : 0 < R := (Finset.lt_inf'_iff _).2 fun i _ => (hr i).r_pos
  have hRr : ∀ i, R ≤ r i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  have hr' : ∀ i, HasFPowerSeriesOnBall (G i) (p i) 0 R := fun i => (hr i).mono hR (hRr i)
  obtain ⟨ρ, hρ0, hρR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hR
  have hρ0' : (0 : ℝ) < ρ := by exact_mod_cast hρ0
  -- The point `ζ(t)` of the path; with `τ(t) = t + t⁻¹`, `|ζ_j(t)| = e^{-u_j τ(t)}` (the phase
  -- `e^{-i (t - t⁻¹) u'_j}` has modulus one).
  let τ : ℝ → ℝ := fun t => t + t⁻¹
  let ζ : ℝ → ι → ℂ := fun t j =>
    Complex.exp (-(((t + t⁻¹) * u j : ℝ) : ℂ) - Complex.I * (((t - t⁻¹) * u' j : ℝ) : ℂ))
  have hζn : ∀ t j, ‖ζ t j‖ = Real.exp (-(u j * τ t)) := by
    intro t j
    simp only [ζ, τ, Complex.norm_exp]
    congr 1
    simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im]
    ring
  have hτ : Tendsto τ atTop atTop := tendsto_id.atTop_add tendsto_inv_atTop_zero
  have hS : Tendsto (fun t => ∑ j, ‖ζ t j‖) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset ι) fun j _ =>
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hτ.const_mul_atTop (hpos j))
    simp only [Finset.sum_const_zero] at this
    exact this.congr fun t => Finset.sum_congr rfl fun j _ => (hζn t j).symm
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1
    ((((tendsto_order.1 hS).2 ρ hρ0').and h).and (eventually_ge_atTop 1))
  have ht₀1 : 1 ≤ t₀ := (ht₀ t₀ le_rfl).2
  -- `τ` is nondecreasing on `[1, ∞)` and `τ(t) ≥ t` there.
  have hτmono : ∀ t, t₀ ≤ t → τ t₀ ≤ τ t := by
    intro t ht
    have h1 : 0 < t₀ := by linarith
    have h2 : 0 < t := by linarith
    have h3 : t⁻¹ ≤ t₀⁻¹ := inv_anti₀ h1 ht
    have h4 : t₀⁻¹ - t⁻¹ = (t - t₀) * (t₀⁻¹ * t⁻¹) := by field_simp
    have h5 : t₀⁻¹ * t⁻¹ ≤ 1 := by
      calc t₀⁻¹ * t⁻¹ ≤ 1 * 1 :=
            mul_le_mul (inv_le_one_of_one_le₀ ht₀1) (inv_le_one_of_one_le₀ (ht₀1.trans ht))
              (by positivity) zero_le_one
        _ = 1 := one_mul 1
    simp only [τ]
    nlinarith
  have hτt : ∀ t, t₀ ≤ t → t ≤ τ t := fun t ht =>
    le_add_of_nonneg_right (inv_nonneg.2 (by linarith))
  have hζball : ∀ t, t₀ ≤ t → ζ t ∈ Metric.eball (0 : ι → ℂ) R := by
    intro t ht
    have hle : ‖ζ t‖ ≤ ∑ j, ‖ζ t j‖ := by
      refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)).2 fun j => ?_
      exact Finset.single_le_sum (f := fun j => ‖ζ t j‖) (fun j _ => norm_nonneg _)
        (Finset.mem_univ j)
    have hlt : ‖ζ t‖₊ < ρ := by
      rw [← NNReal.coe_lt_coe, coe_nnNorm]
      exact hle.trans_lt (ht₀ t ht).1.1
    rw [mem_eball_zero_iff, eNorm_eq_nnNorm]
    exact (ENNReal.coe_lt_coe.2 hlt).trans hρR
  -- Words `⟨n, r⟩`, their rates `μ`, their monomials `w` and the coefficients `c`.
  let A := Σ n : ℕ, (Fin n → ι)
  let μ : A → ℝ := fun a => ∑ k, u (a.2 k)
  let w : A → ℝ → ℂ := fun a t => ∏ k, ζ t (a.2 k)
  let c : A → Fin (K + 1) → ℂ := fun a i => p i a.1 (fun k => Pi.single (a.2 k) (1 : ℂ))
  have hμ : ∀ a, 0 ≤ μ a := fun a => Finset.sum_nonneg fun k _ => (hpos _).le
  have hw : ∀ a t, ‖w a t‖ = Real.exp (-(μ a * τ t)) := by
    intro a t
    simp only [w, μ, norm_prod, hζn]
    rw [← Real.exp_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  -- Words with the same rate have the same letters (`ℚ`-independence), hence the same monomial.
  have hweq : ∀ a b t, μ a = μ b → w a t = w b t := fun a b t hab =>
    prod_eq_of_sum_eq_ps hu a.2 b.2 hab (ζ t)
  -- Finitely many rates lie below any bound.
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ j, δ ≤ u j := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun j => isEmptyElim j⟩
    · obtain ⟨j₀, hj₀⟩ := Finite.exists_min u
      exact ⟨u j₀, hpos j₀, hj₀⟩
  have hfin : ∀ B, {a : A | μ a ≤ B}.Finite := by
    intro B
    refine ((Finset.range (⌊B / δ⌋₊ + 1)).sigma fun n => (Finset.univ : Finset (Fin n → ι))
      ).finite_toSet.subset fun a ha => ?_
    obtain ⟨n, r⟩ := a
    replace ha : ∑ k, u (r k) ≤ B := ha
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio,
      Finset.coe_univ, Set.mem_univ, and_true]
    have hn : (n : ℝ) * δ ≤ B := by
      have : ∑ k : Fin n, δ ≤ ∑ k, u (r k) := Finset.sum_le_sum fun k _ => hδle _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      exact this.trans ha
    have : n ≤ ⌊B / δ⌋₊ := Nat.le_floor (by rw [le_div_iff₀ hδ]; exact hn)
    omega
  -- An absolutely summable majorant at `t₀`.
  have hsum : ∀ i, Summable fun a : A => ‖c a i‖ * Real.exp (-(μ a * τ t₀)) := by
    intro i
    have hρp : (ρ : ENNReal) < (p i).radius := hρR.trans_le ((hRr i).trans (hr i).r_le)
    refine (summable_sigma_of_nonneg fun a => by positivity).2 ⟨fun n => Summable.of_finite, ?_⟩
    refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun r => by positivity) (fun n => ?_)
      ((p i).summable_norm_mul_pow hρp)
    rw [tsum_fintype]
    calc ∑ r : Fin n → ι, ‖c ⟨n, r⟩ i‖ * Real.exp (-(μ ⟨n, r⟩ * τ t₀))
        ≤ ∑ r : Fin n → ι, ‖p i n‖ * ∏ k, ‖ζ t₀ (r k)‖ := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [← hw ⟨n, r⟩ t₀]
          simp only [w, norm_prod]
          refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun k _ => norm_nonneg _)
          refine ((p i n).le_opNorm _).trans (le_of_eq ?_)
          simp only [Pi.norm_single, norm_one, Finset.prod_const_one, mul_one]
      _ = ‖p i n‖ * (∑ j, ‖ζ t₀ j‖) ^ n := by
          rw [← Finset.mul_sum, ← Fintype.prod_sum (fun (_ : Fin n) j => ‖ζ t₀ j‖),
            Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ‖p i n‖ * (ρ : ℝ) ^ n := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Finset.sum_nonneg fun j _ =>
            norm_nonneg _) (ht₀ t₀ le_rfl).1.1.le n) (norm_nonneg _)
  -- On the path, the series of `G i (ζ(t))` regrouped by words.
  have htsum : ∀ t, t₀ ≤ t → ∀ i, ∑' a, c a i * w a t = G i (ζ t) := by
    intro t ht i
    have hsm := summable_mul_of_norm_ps μ (fun a => c a i) (fun a => w a t) hμ (hτmono t ht)
      (fun a => hw a t) (hsum i)
    have h1 := hsm.hasSum.sigma fun n => hasSum_fintype _
    have h2 : HasSum (fun n => p i n (fun _ => ζ t)) (G i (ζ t)) := by
      simpa only [zero_add] using (hr' i).hasSum (hζball t ht)
    have h3 : ∀ n, ∑ r : Fin n → ι, c ⟨n, r⟩ i * w ⟨n, r⟩ t = p i n (fun _ => ζ t) := by
      intro n
      rw [cmm_apply_diag_eq_sum_ps]
    simp only [h3] at h1
    exact h1.unique h2
  have hzero : ∀ t, t₀ ≤ t →
      ∑ i : Fin (K + 1), (t : ℂ) ^ (i : ℕ) * ∑' a, c a i * w a t = 0 := by
    intro t ht
    simp only [htsum t ht]
    exact (ht₀ t ht).1.2
  -- The leading-term argument: the coefficients of every rate sum to zero.
  have hfib := fiber_sum_eq_zero_ps μ c w τ t₀ (by linarith) hμ hfin hw hweq hτmono hτt hsum
    hzero
  -- Hence every homogeneous part of every `G i` vanishes, and `G i = 0` on the ball.
  intro i
  filter_upwards [Metric.eball_mem_nhds (0 : ι → ℂ) hR] with z hz
  have h2 : HasSum (fun n => p i n (fun _ => z)) (G i z) := by
    simpa only [zero_add] using (hr' i).hasSum hz
  have h3 : ∀ n, p i n (fun _ => z) = 0 := by
    intro n
    rw [cmm_apply_diag_eq_sum_ps, ← Finset.sum_fiberwise_of_maps_to
      (g := fun r : Fin n → ι => μ ⟨n, r⟩) (t := Finset.univ.image fun r => μ ⟨n, r⟩)
      (fun r _ => Finset.mem_image_of_mem _ (Finset.mem_univ r))]
    refine Finset.sum_eq_zero fun m hm => ?_
    obtain ⟨r₀, -, rfl⟩ := Finset.mem_image.1 hm
    -- Words with the same rate have the same monomial.
    have hmono : ∀ r ∈ Finset.univ.filter (fun r : Fin n → ι => μ ⟨n, r⟩ = μ ⟨n, r₀⟩),
        ∏ k, z (r k) = ∏ k, z (r₀ k) := fun r hr =>
      prod_eq_of_sum_eq_ps hu r r₀ (Finset.mem_filter.1 hr).2 z
    rw [Finset.sum_congr rfl fun r hr => by rw [hmono r hr], ← Finset.sum_mul]
    have hs : ∀ a : A, a ∈ (Finset.univ.filter fun r : Fin n → ι => μ ⟨n, r⟩ = μ ⟨n, r₀⟩).map
        ⟨Sigma.mk n, sigma_mk_injective⟩ ↔ μ a = μ ⟨n, r₀⟩ := by
      rintro ⟨n', r'⟩
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨r, hr, he⟩
        rw [← he]
        exact hr
      · intro he
        have hn : n' = n := by
          rw [card_eq_sum_card_fiber_ps r', card_eq_sum_card_fiber_ps r₀]
          exact Finset.sum_congr rfl fun j _ => card_fiber_eq_of_sum_eq_ps hu r' r₀ he j
        subst hn
        exact ⟨r', he, rfl⟩
    have := hfib (μ ⟨n, r₀⟩) _ hs i
    rw [Finset.sum_map] at this
    simp only [Function.Embedding.coeFn_mk] at this
    rw [this, zero_mul]
  simp only [h3] at h2
  exact h2.unique hasSum_zero

/-- **Lemma D.16 of the dimension paper (Separation on the path).** Let `u_1, …, u_q > 0` be
linearly independent over `ℚ`, let `u'_j` be real, let `ρ₀ > e^{−2 u_j}` for every `j`, and let
`𝒯_{−K}, …, 𝒯_K` be holomorphic on the polydisc `{|ζ_j| < ρ₀}` with values in a complex normed
space. If `∑_{i=−K}^{K} t^i 𝒯_i(ζ_1(t), …, ζ_q(t)) = 0` for all real `t ≥ 1`, then every `𝒯_i`
vanishes on the polydisc. (The map `𝒯_i` of the paper is `𝒯 ⟨i + K, _⟩` here.) -/
theorem path_separation {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (u : ι → ℝ) (hpos : ∀ j, 0 < u j) (hu : LinearIndependent ℚ u)
    (u' : ι → ℝ) (ρ₀ : ℝ) (hρ : ∀ j, Real.exp (-(2 * u j)) < ρ₀) (K : ℕ)
    (𝒯 : Fin (2 * K + 1) → (ι → ℂ) → F)
    (h𝒯 : ∀ i, AnalyticOnNhd ℂ (𝒯 i) {ζ : ι → ℂ | ∀ j, ‖ζ j‖ < ρ₀})
    (h : ∀ t : ℝ, 1 ≤ t →
      ∑ i : Fin (2 * K + 1), (t : ℂ) ^ (((i : ℕ) : ℤ) - (K : ℤ)) • 𝒯 i (fun j =>
        Complex.exp (-(((t + t⁻¹) * u j : ℝ) : ℂ) - Complex.I * (((t - t⁻¹) * u' j : ℝ) : ℂ)))
        = 0) :
    ∀ i, ∀ ζ : ι → ℂ, (∀ j, ‖ζ j‖ < ρ₀) → 𝒯 i ζ = 0 := by
  intro i ζ₀ hζ₀
  -- The polydisc `D` is a product of discs, hence preconnected, and it contains `0`.
  set D := {ζ : ι → ℂ | ∀ j, ‖ζ j‖ < ρ₀} with hD
  have hD' : D = Set.univ.pi fun _ : ι => Metric.ball (0 : ℂ) ρ₀ := by
    ext ζ
    simp only [hD, Set.mem_ofPred_eq, Set.mem_univ_pi, mem_ball_zero_iff]
  have hDconn : IsPreconnected D := by
    rw [hD']
    exact isPreconnected_univ_pi fun j => (convex_ball (0 : ℂ) ρ₀).isPreconnected
  have h0D : (0 : ι → ℂ) ∈ D := fun j => by
    simpa only [Pi.zero_apply, norm_zero] using (Real.exp_pos _).trans (hρ j)
  -- It suffices that `φ (𝒯_i ζ₀) = 0` for every continuous linear functional `φ`.
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ) fun φ => ?_
  have hG : ∀ i, AnalyticAt ℂ (fun ζ => φ (𝒯 i ζ)) 0 := fun i =>
    (φ.analyticAt _).comp (h𝒯 i 0 h0D)
  -- Multiplied by `t^K`, the identity has only nonnegative powers of `t`.
  have hpath : ∀ᶠ t : ℝ in atTop, ∑ i : Fin (2 * K + 1), (t : ℂ) ^ (i : ℕ) * φ (𝒯 i (fun j =>
      Complex.exp (-(((t + t⁻¹) * u j : ℝ) : ℂ) - Complex.I * (((t - t⁻¹) * u' j : ℝ) : ℂ))))
      = 0 := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
    have := congrArg (fun v => φ ((t : ℂ) ^ K • v)) (h t ht)
    simp only [smul_zero, map_zero, Finset.smul_sum, map_sum, smul_smul, map_smul,
      smul_eq_mul] at this
    refine (Finset.sum_congr rfl fun i _ => ?_).trans this
    congr 1
    rw [← zpow_natCast (t : ℂ) (i : ℕ), ← zpow_natCast (t : ℂ) K, ← zpow_add₀ ht0]
    congr 1
    ring
  -- The middle step: `φ ∘ 𝒯_i` vanishes near `0`.
  have h0 := eventually_eq_zero_of_sum_pow_mul_exp_path u hpos hu u' (2 * K) _ hG hpath i
  -- Identity principle on the polydisc.
  have han : AnalyticOnNhd ℂ (fun ζ => φ (𝒯 i ζ)) D := fun x hx =>
    (φ.analyticAt _).comp (h𝒯 i x hx)
  exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDconn h0D h0 hζ₀

end Skips
