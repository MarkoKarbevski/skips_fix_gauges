import SkipsLean.Imports

/-!
# Separation on a ray

Paper (dimension paper): Lemma D.1 (`lem:raysep`), "Separation on a ray", stated in Appendix D.1 and
proved in Appendix D.4.

Let `u_1, …, u_q` be real numbers that are linearly independent over `ℚ`, and let `𝒯_0, …, 𝒯_K` be
real-analytic maps on `ℝ^q`. If

  `∑_{i=0}^{K} t^i 𝒯_i(tanh(t u_1), …, tanh(t u_q)) = 0`   for all `t > 0`,

then every `𝒯_i` vanishes on `ℝ^q`. Along the ray the outputs `tanh(t u_j)` of the hidden units
become free variables.

The proof of the paper writes `tanh(t u_j) = s_j (1 - ζ_j) / (1 + ζ_j)` with `s_j` the sign of `u_j`
and `ζ_j = exp(-2 |u_j| t)`, expands every `𝒯_i` in powers of `ζ_1, …, ζ_q`, and uses that the
monomials `ζ^α` decay at the pairwise different rates `2 ∑_j α_j |u_j|`. Its middle step is stated
here on its own (`eventually_eq_zero_of_sum_pow_mul_exp_ray`): it does not mention `tanh`.
-/

namespace Skips

open Filter Topology
open scoped Matrix.Norms.Elementwise

/-- A polynomial `∑_{i ≤ K} b_i t^i` that tends to `0` as `t → ∞` has all coefficients zero. -/
private lemma coeffs_eq_zero_of_tendsto {K : ℕ} (b : Fin (K + 1) → ℝ)
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

/-- Domination: if `|c a| e^{-μ_a t₀}` is summable and all `μ_a ≥ 0`, then so is
`c a e^{-μ_a t}` for `t ≥ t₀`. -/
private lemma summable_mul_exp_of_le {A : Type*} (μ c : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) {t₀ t : ℝ}
    (ht : t₀ ≤ t) (hsum : Summable fun a => |c a| * Real.exp (-(μ a * t₀))) :
    Summable fun a => c a * Real.exp (-(μ a * t)) := by
  refine hsum.of_norm_bounded fun a => ?_
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hμ a])) (abs_nonneg _)

/-- **The leading-term argument.** Let `∑_a (∑_i t^i c_{a,i}) e^{-μ_a t} = 0` for all large `t`,
with rates `μ_a ≥ 0` of which finitely many lie below any bound, and an absolutely summable
majorant at `t₀`. Then for every rate `m` the coefficients `c_{a,i}` with `μ_a = m` sum to zero. -/
private lemma fiber_sum_eq_zero {A : Type*} {K : ℕ} (μ : A → ℝ) (c : A → Fin (K + 1) → ℝ)
    (t₀ : ℝ) (hμ : ∀ a, 0 ≤ μ a) (hfin : ∀ B, {a | μ a ≤ B}.Finite)
    (hsum : ∀ i, Summable fun a => |c a i| * Real.exp (-(μ a * t₀)))
    (hzero : ∀ t, t₀ ≤ t →
      ∑ i : Fin (K + 1), t ^ (i : ℕ) * ∑' a, c a i * Real.exp (-(μ a * t)) = 0)
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
  let F : Fin (K + 1) → ℝ := fun i => ∑ a ∈ fib m₁, c a i
  -- Split every series into the rates `≤ m₁` (finitely many) and the rest.
  let L := (hfin m₁).toFinset
  have hL : ∀ a, a ∈ L ↔ μ a ≤ m₁ := fun a => by simp [L]
  clear_value L
  let R : Fin (K + 1) → ℝ → ℝ := fun i t =>
    ∑' x : ↥((L : Set A)ᶜ), c x i * Real.exp (-(μ x * t))
  have hcompl : ∀ x : ↥((L : Set A)ᶜ), m₁ < μ x := fun x => by
    have := x.2
    simp only [Set.mem_compl_iff, Finset.mem_coe, hL, not_le] at this
    exact this
  have hhead : ∀ i t, ∑ a ∈ L, c a i * Real.exp (-(μ a * t)) = Real.exp (-(m₁ * t)) * F i := by
    intro i t
    rw [← Finset.sum_fiberwise_of_maps_to (g := μ) (t := L.image μ)
      (fun x hx => Finset.mem_image_of_mem μ hx)]
    rw [Finset.sum_eq_single m₁]
    · have hLm : L.filter (fun x => μ x = m₁) = fib m₁ :=
        Finset.ext fun a => by rw [Finset.mem_filter, hL, hfib]; exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
      rw [hLm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [(hfib _ _).1 ha, mul_comm]
    · intro m hm hne
      obtain ⟨a, haL, rfl⟩ := Finset.mem_image.1 hm
      have hlt : μ a < m₁ := lt_of_le_of_ne ((hL a).1 haL) hne
      have hLm : L.filter (fun x => μ x = μ a) = fib (μ a) :=
        Finset.ext fun a' => by
          rw [Finset.mem_filter, hL, hfib]
          exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hlt.le, h⟩⟩
      rw [hLm, Finset.sum_congr rfl (fun a' ha' => by rw [(hfib _ _).1 ha']), ← Finset.sum_mul,
        hbelow a hlt i, zero_mul]
    · intro h
      exact absurd (Finset.mem_image_of_mem μ ((hL a₁).2 le_rfl)) h
  have hsplit : ∀ i t, t₀ ≤ t →
      ∑' a, c a i * Real.exp (-(μ a * t)) = Real.exp (-(m₁ * t)) * F i + R i t := by
    intro i t ht
    rw [← (summable_mul_exp_of_le μ (fun a => c a i) hμ ht (hsum i)).sum_add_tsum_compl (s := L),
      hhead]
  -- After multiplication by `e^{m₁ t}` the rest is at most `e^{-γ (t - t₀)} e^{m₁ t₀} M_i`.
  let M : Fin (K + 1) → ℝ := fun i =>
    ∑' x : ↥((L : Set A)ᶜ), |c x i| * Real.exp (-(μ x * t₀))
  have hrest : ∀ i t, t₀ ≤ t → ‖Real.exp (m₁ * t) * R i t‖ ≤
      Real.exp (-(γ * (t - t₀))) * Real.exp (m₁ * t₀) * M i := by
    intro i t ht
    have hmaj : Summable fun x : ↥((L : Set A)ᶜ) => |c x i| * Real.exp (-(μ x * t₀)) :=
      (hsum i).subtype _
    have hterm : ∀ x : ↥((L : Set A)ᶜ),
        ‖Real.exp (m₁ * t) * (c x i * Real.exp (-(μ x * t)))‖ ≤
          Real.exp (-(γ * (t - t₀))) * Real.exp (m₁ * t₀) *
            (|c x i| * Real.exp (-(μ x * t₀))) := by
      intro x
      have h1 := hgap x (hcompl x)
      calc ‖Real.exp (m₁ * t) * (c x i * Real.exp (-(μ x * t)))‖
          = |c x i| * Real.exp (m₁ * t + -(μ x * t)) := by
            rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
              Real.abs_exp, Real.abs_exp, Real.exp_add]
            ring
        _ ≤ |c x i| * Real.exp (-(γ * (t - t₀)) + m₁ * t₀ + -(μ x * t₀)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg _)
            nlinarith
        _ = _ := by rw [Real.exp_add, Real.exp_add]; ring
    have hsn : Summable fun x : ↥((L : Set A)ᶜ) =>
        ‖Real.exp (m₁ * t) * (c x i * Real.exp (-(μ x * t)))‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hmaj.mul_left _)
    calc ‖Real.exp (m₁ * t) * R i t‖
        = ‖∑' x : ↥((L : Set A)ᶜ), Real.exp (m₁ * t) * (c x i * Real.exp (-(μ x * t)))‖ := by
          simp only [R, tsum_mul_left]
      _ ≤ ∑' x : ↥((L : Set A)ᶜ), ‖Real.exp (m₁ * t) * (c x i * Real.exp (-(μ x * t)))‖ :=
          norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' x : ↥((L : Set A)ᶜ), Real.exp (-(γ * (t - t₀))) * Real.exp (m₁ * t₀) *
            (|c x i| * Real.exp (-(μ x * t₀))) :=
          Summable.tsum_le_tsum hterm hsn (hmaj.mul_left _)
      _ = _ := by simp only [M, tsum_mul_left]
  -- Hence `P(t) = -∑_i t^i e^{m₁ t} R_i(t)` tends to `0`.
  have hP : ∀ t, t₀ ≤ t → ∑ i : Fin (K + 1), t ^ (i : ℕ) * F i =
      -∑ i : Fin (K + 1), t ^ (i : ℕ) * (Real.exp (m₁ * t) * R i t) := by
    intro t ht
    have h0 := hzero t ht
    rw [Finset.sum_congr rfl fun i _ => by rw [hsplit i t ht]] at h0
    have h1 : Real.exp (m₁ * t) * Real.exp (-(m₁ * t)) = 1 := by
      rw [← Real.exp_add]; simp
    rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
    rw [← mul_zero (Real.exp (m₁ * t)), ← h0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (-(t ^ (i : ℕ) * F i)) * h1
  have hlim : Tendsto (fun t : ℝ => ∑ i : Fin (K + 1), t ^ (i : ℕ) * F i) atTop (𝓝 0) := by
    let b : ℝ → ℝ := fun t => ∑ i : Fin (K + 1),
      t ^ (i : ℕ) * (Real.exp (-(γ * (t - t₀))) * Real.exp (m₁ * t₀) * M i)
    have hb : Tendsto b atTop (𝓝 0) := by
      have hterm : ∀ i : Fin (K + 1), Tendsto (fun t : ℝ => t ^ ((i : ℕ) : ℝ) * Real.exp (-γ * t) *
          (Real.exp (γ * t₀) * Real.exp (m₁ * t₀) * M i)) atTop (𝓝 0) := fun i => by
        simpa only [zero_mul] using
          (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((i : ℕ) : ℝ) γ hγ).mul_const
            (Real.exp (γ * t₀) * Real.exp (m₁ * t₀) * M i)
      have := tendsto_finsetSum Finset.univ fun i _ => hterm i
      simp only [Finset.sum_const_zero] at this
      refine this.congr fun t => Finset.sum_congr rfl fun i _ => ?_
      rw [Real.rpow_natCast, show -(γ * (t - t₀)) = -γ * t + γ * t₀ by ring, Real.exp_add]
      ring
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop t₀, eventually_ge_atTop 0] with t ht ht0
    rw [hP t ht, norm_neg]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, norm_pow, Real.norm_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_left (hrest i t ht) (pow_nonneg ht0 _)
  obtain ⟨i, hi⟩ := hbad₁
  exact hi (coeffs_eq_zero_of_tendsto F hlim i)

/-- A sum over `k : Fin n` of `f (r k)`, grouped by the value of `r k`. -/
private lemma sum_comp_eq_sum_card {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    {n : ℕ} (r : Fin n → ι) (f : ι → M) :
    ∑ k, f (r k) = ∑ j, (Finset.univ.filter fun k => r k = j).card • f j := by
  rw [← Finset.sum_fiberwise Finset.univ r (fun k => f (r k))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2]), Finset.sum_const]

/-- A product over `k : Fin n` of `f (r k)`, grouped by the value of `r k`. -/
private lemma prod_comp_eq_prod_pow {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    {n : ℕ} (r : Fin n → ι) (f : ι → M) :
    ∏ k, f (r k) = ∏ j, f j ^ (Finset.univ.filter fun k => r k = j).card := by
  rw [← Finset.prod_fiberwise Finset.univ r (fun k => f (r k))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2]), Finset.prod_const]

/-- If the rates `λ_j` are linearly independent over `ℚ`, the rate `∑_k λ_{r k}` of a word `r`
determines how often each letter `j` occurs in `r`. -/
private lemma card_fiber_eq_of_sum_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {lam : ι → ℝ}
    (hlam : LinearIndependent ℚ lam) {n n' : ℕ} (r : Fin n → ι) (r' : Fin n' → ι)
    (h : ∑ k, lam (r k) = ∑ k, lam (r' k)) (j : ι) :
    (Finset.univ.filter fun k => r k = j).card = (Finset.univ.filter fun k => r' k = j).card := by
  have e1 := sum_comp_eq_sum_card r lam
  have e2 := sum_comp_eq_sum_card r' lam
  simp only [nsmul_eq_mul] at e1 e2
  have := (Fintype.linearIndependent_iff.1 hlam)
    (fun j => ((Finset.univ.filter fun k => r k = j).card : ℚ) -
      (Finset.univ.filter fun k => r' k = j).card) ?_ j
  · exact_mod_cast sub_eq_zero.1 this
  · simp only [sub_smul, Finset.sum_sub_distrib, Rat.smul_def, Rat.cast_natCast]
    rw [← e1, ← e2, h, sub_self]

/-- The length of a word is the sum of the numbers of occurrences of the letters. -/
private lemma card_eq_sum_card_fiber {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (r : Fin n → ι) : n = ∑ j, (Finset.univ.filter fun k => r k = j).card := by
  have := sum_comp_eq_sum_card r (fun _ => (1 : ℕ))
  simpa using this

/-- Expansion of a homogeneous polynomial on `ℝ^ι` in monomials:
`f (ζ, …, ζ) = ∑_r f (e_{r 1}, …, e_{r n}) ∏_k ζ_{r k}`. -/
private lemma cmm_apply_diag_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => ι → ℝ) ℝ) (ζ : ι → ℝ) :
    f (fun _ => ζ) =
      ∑ r : Fin n → ι, f (fun k => Pi.single (r k) (1 : ℝ)) * ∏ k, ζ (r k) := by
  have hζ : ζ = ∑ j, ζ j • Pi.single j (1 : ℝ) := by
    conv_lhs => rw [← Finset.univ_sum_single ζ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have h1 := f.map_sum (fun (_ : Fin n) (j : ι) => ζ j • Pi.single j (1 : ℝ))
  conv_lhs => rw [hζ]
  rw [h1]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [f.map_smul_univ (fun k => ζ (r k)) (fun k => Pi.single (r k) (1 : ℝ)), smul_eq_mul,
    mul_comm]

/-- **The middle step of the proof of Lemma D.1.** Let the rates `λ_j > 0` be linearly independent
over `ℚ`, and let `G_0, …, G_K` be real-analytic near `0 ∈ ℝ^q`. If
`∑_i t^i G_i(exp(-λ_1 t), …, exp(-λ_q t)) = 0` for all large `t`, then every `G_i` vanishes near
`0`. (In the expansion `G_i(ζ) = ∑_α b_{i,α} ζ^α` the monomial `ζ^α` decays at the rate
`∑_j α_j λ_j`; these rates are pairwise different, and finitely many lie below any bound.) -/
theorem eventually_eq_zero_of_sum_pow_mul_exp_ray {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (hpos : ∀ j, 0 < lam j) (hlam : LinearIndependent ℚ lam)
    (K : ℕ) (G : Fin (K + 1) → (ι → ℝ) → ℝ) (hG : ∀ i, AnalyticAt ℝ (G i) 0)
    (h : ∀ᶠ t : ℝ in atTop,
      ∑ i : Fin (K + 1), t ^ (i : ℕ) * G i (fun j => Real.exp (-(lam j * t))) = 0) :
    ∀ i, ∀ᶠ ζ in 𝓝 (0 : ι → ℝ), G i ζ = 0 := by
  classical
  -- Power series `p i` of the `G i` at `0`, on a common ball of radius `R`.
  have hG' : ∀ i, ∃ p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ, ∃ r,
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
  -- The point `ζ(t) = (e^{-λ_j t})_j` of the ray, and `S(t) = ∑_j e^{-λ_j t}`.
  let ζ : ℝ → ι → ℝ := fun t j => Real.exp (-(lam j * t))
  have hS : Tendsto (fun t => ∑ j, ζ t j) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset ι) fun j _ =>
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (hpos j))
    simp only [Finset.sum_const_zero] at this
    exact Tendsto.congr (fun t => rfl) this
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 (((tendsto_order.1 hS).2 ρ hρ0').and h)
  have hζpos : ∀ t j, 0 ≤ ζ t j := fun t j => (Real.exp_pos _).le
  have hζball : ∀ t, t₀ ≤ t → ζ t ∈ Metric.eball (0 : ι → ℝ) R := by
    intro t ht
    have hle : ‖ζ t‖ ≤ ∑ j, ζ t j := by
      refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => hζpos t j)).2 fun j => ?_
      rw [Real.norm_of_nonneg (hζpos t j)]
      exact Finset.single_le_sum (fun j _ => hζpos t j) (Finset.mem_univ j)
    have hlt : ‖ζ t‖₊ < ρ := by
      rw [← NNReal.coe_lt_coe, coe_nnNorm]
      exact hle.trans_lt (ht₀ t ht).1
    rw [mem_eball_zero_iff, eNorm_eq_nnNorm]
    exact (ENNReal.coe_lt_coe.2 hlt).trans hρR
  -- Words `⟨n, r⟩`, their rates `μ` and the coefficients `c`.
  let A := Σ n : ℕ, (Fin n → ι)
  let μ : A → ℝ := fun a => ∑ k, lam (a.2 k)
  let c : A → Fin (K + 1) → ℝ := fun a i => p i a.1 (fun k => Pi.single (a.2 k) (1 : ℝ))
  have hμ : ∀ a, 0 ≤ μ a := fun a => Finset.sum_nonneg fun k _ => (hpos _).le
  have hexp : ∀ (a : A) t, Real.exp (-(μ a * t)) = ∏ k, ζ t (a.2 k) := by
    intro a t
    simp only [μ, ζ]
    rw [← Real.exp_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  -- Finitely many rates lie below any bound.
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ j, δ ≤ lam j := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun j => isEmptyElim j⟩
    · obtain ⟨j₀, hj₀⟩ := Finite.exists_min lam
      exact ⟨lam j₀, hpos j₀, hj₀⟩
  have hfin : ∀ B, {a : A | μ a ≤ B}.Finite := by
    intro B
    refine ((Finset.range (⌊B / δ⌋₊ + 1)).sigma fun n => (Finset.univ : Finset (Fin n → ι))
      ).finite_toSet.subset fun a ha => ?_
    obtain ⟨n, r⟩ := a
    replace ha : ∑ k, lam (r k) ≤ B := ha
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio,
      Finset.coe_univ, Set.mem_univ, and_true]
    have hn : (n : ℝ) * δ ≤ B := by
      have : ∑ k : Fin n, δ ≤ ∑ k, lam (r k) := Finset.sum_le_sum fun k _ => hδle _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      exact this.trans ha
    have : n ≤ ⌊B / δ⌋₊ := Nat.le_floor (by rw [le_div_iff₀ hδ]; exact hn)
    omega
  -- An absolutely summable majorant at `t₀`.
  have hsum : ∀ i, Summable fun a : A => |c a i| * Real.exp (-(μ a * t₀)) := by
    intro i
    have hρp : (ρ : ENNReal) < (p i).radius := hρR.trans_le ((hRr i).trans (hr i).r_le)
    refine (summable_sigma_of_nonneg fun a => by positivity).2 ⟨fun n => Summable.of_finite, ?_⟩
    refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun r => by positivity) (fun n => ?_)
      ((p i).summable_norm_mul_pow hρp)
    rw [tsum_fintype]
    calc ∑ r : Fin n → ι, |c ⟨n, r⟩ i| * Real.exp (-(μ ⟨n, r⟩ * t₀))
        ≤ ∑ r : Fin n → ι, ‖p i n‖ * ∏ k, ζ t₀ (r k) := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [hexp]
          refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun k _ => hζpos _ _)
          refine ((p i n).le_opNorm _).trans (le_of_eq ?_)
          simp only [Pi.norm_single, norm_one, Finset.prod_const_one, mul_one]
      _ = ‖p i n‖ * (∑ j, ζ t₀ j) ^ n := by
          rw [← Finset.mul_sum, ← Fintype.prod_sum (fun (_ : Fin n) j => ζ t₀ j),
            Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ‖p i n‖ * (ρ : ℝ) ^ n := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Finset.sum_nonneg fun j _ =>
            hζpos _ _) (ht₀ t₀ le_rfl).1.le n) (norm_nonneg _)
  -- On the ray, the series of `G i (ζ(t))` regrouped by words.
  have htsum : ∀ t, t₀ ≤ t → ∀ i, ∑' a, c a i * Real.exp (-(μ a * t)) = G i (ζ t) := by
    intro t ht i
    have hsm := summable_mul_exp_of_le μ (fun a => c a i) hμ ht (hsum i)
    have h1 := hsm.hasSum.sigma fun n => hasSum_fintype _
    have h2 : HasSum (fun n => p i n (fun _ => ζ t)) (G i (ζ t)) := by
      simpa only [zero_add] using (hr' i).hasSum (hζball t ht)
    have h3 : ∀ n, ∑ r : Fin n → ι, c ⟨n, r⟩ i * Real.exp (-(μ ⟨n, r⟩ * t)) =
        p i n (fun _ => ζ t) := by
      intro n
      rw [cmm_apply_diag_eq_sum]
      exact Finset.sum_congr rfl fun r _ => by rw [hexp]
    simp only [h3] at h1
    exact h1.unique h2
  have hzero : ∀ t, t₀ ≤ t →
      ∑ i : Fin (K + 1), t ^ (i : ℕ) * ∑' a, c a i * Real.exp (-(μ a * t)) = 0 := by
    intro t ht
    simp only [htsum t ht]
    exact (ht₀ t ht).2
  -- The leading-term argument: the coefficients of every rate sum to zero.
  have hfib := fiber_sum_eq_zero μ c t₀ hμ hfin hsum hzero
  -- Hence every homogeneous part of every `G i` vanishes, and `G i = 0` on the ball.
  intro i
  filter_upwards [Metric.eball_mem_nhds (0 : ι → ℝ) hR] with z hz
  have h2 : HasSum (fun n => p i n (fun _ => z)) (G i z) := by
    simpa only [zero_add] using (hr' i).hasSum hz
  have h3 : ∀ n, p i n (fun _ => z) = 0 := by
    intro n
    rw [cmm_apply_diag_eq_sum, ← Finset.sum_fiberwise_of_maps_to
      (g := fun r : Fin n → ι => μ ⟨n, r⟩) (t := Finset.univ.image fun r => μ ⟨n, r⟩)
      (fun r _ => Finset.mem_image_of_mem _ (Finset.mem_univ r))]
    refine Finset.sum_eq_zero fun m hm => ?_
    obtain ⟨r₀, -, rfl⟩ := Finset.mem_image.1 hm
    -- Words with the same rate have the same letters, hence the same monomial.
    have hmono : ∀ r ∈ Finset.univ.filter (fun r : Fin n → ι => μ ⟨n, r⟩ = μ ⟨n, r₀⟩),
        ∏ k, z (r k) = ∏ k, z (r₀ k) := by
      intro r hr
      have hr' := (Finset.mem_filter.1 hr).2
      rw [prod_comp_eq_prod_pow, prod_comp_eq_prod_pow]
      exact Finset.prod_congr rfl fun j _ => by rw [card_fiber_eq_of_sum_eq hlam r r₀ hr' j]
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
          rw [card_eq_sum_card_fiber r', card_eq_sum_card_fiber r₀]
          exact Finset.sum_congr rfl fun j _ => card_fiber_eq_of_sum_eq hlam r' r₀ he j
        subst hn
        exact ⟨r', he, rfl⟩
    have := hfib (μ ⟨n, r₀⟩) _ hs i
    rw [Finset.sum_map] at this
    simp only [Function.Embedding.coeFn_mk] at this
    rw [this, zero_mul]
  simp only [h3] at h2
  exact h2.unique hasSum_zero

/-- `tanh x = (1 - e^{-2x}) / (1 + e^{-2x})`. -/
private lemma tanh_eq_one_sub_div (x : ℝ) :
    Real.tanh x = (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))) := by
  have h1 : Real.exp (-(2 * x)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hp1 : 0 < Real.exp x := Real.exp_pos x
  have hp2 : 0 < Real.exp (-x) := Real.exp_pos _
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, h1,
    div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (Real.exp (-x)) * h2

/-- **Lemma D.1 (separation on a ray).** Let `u_1, …, u_q` be real numbers that are linearly
independent over `ℚ`, and let `𝒯_0, …, 𝒯_K` be real-analytic maps from `ℝ^q` to a normed space. If
`∑_i t^i 𝒯_i(tanh(t u_1), …, tanh(t u_q)) = 0` for all `t > 0`, then every `𝒯_i` vanishes on
`ℝ^q`. -/
theorem tanh_ray_separation {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (u : ι → ℝ) (hu : LinearIndependent ℚ u) (K : ℕ)
    (𝒯 : Fin (K + 1) → (ι → ℝ) → F) (h𝒯 : ∀ i, AnalyticOnNhd ℝ (𝒯 i) Set.univ)
    (h : ∀ t : ℝ, 0 < t →
      ∑ i : Fin (K + 1), t ^ (i : ℕ) • 𝒯 i (fun j => Real.tanh (t * u j)) = 0) :
    ∀ i w, 𝒯 i w = 0 := by
  -- No `u_j` is zero; `σ j = ±1` is the sign of `u_j`, and `s j` its image in `ℝ`.
  have hu0 : ∀ j, u j ≠ 0 := fun j => hu.ne_zero j
  let σ : ι → ℚ := fun j => if 0 < u j then 1 else -1
  let s : ι → ℝ := fun j => (σ j : ℝ)
  have hσ0 : ∀ j, σ j ≠ 0 := fun j => by
    simp only [σ]; split_ifs <;> norm_num
  have hs0 : ∀ j, s j ≠ 0 := fun j => by simp only [s]; exact_mod_cast hσ0 j
  have hsabs : ∀ j, |u j| = s j * u j := fun j => by
    simp only [s, σ]
    split_ifs with hj
    · simp [abs_of_pos hj]
    · have : u j < 0 := lt_of_le_of_ne (not_lt.1 hj) (hu0 j)
      simp [abs_of_neg this]
  have hss : ∀ j, s j * s j = 1 := fun j => by
    simp only [s, σ]; split_ifs <;> norm_num
  -- The rates `λ_j = 2 |u_j|` are positive and linearly independent over `ℚ`.
  let lam : ι → ℝ := fun j => 2 * |u j|
  have hpos : ∀ j, 0 < lam j := fun j => by
    have := abs_pos.2 (hu0 j); simp only [lam]; linarith
  have hlam : LinearIndependent ℚ lam := by
    have := hu.units_smul (fun j => Units.mk0 (2 * σ j) (mul_ne_zero two_ne_zero (hσ0 j)))
    convert this using 1
    funext j
    simp only [lam, Pi.smul_apply', Units.smul_def, Units.val_mk0, Rat.smul_def, hsabs]
    push_cast
    ring
  -- `tanh` is odd: `tanh (x u_j) = s_j tanh (x |u_j|)`.
  have hodd : ∀ x j, Real.tanh (x * u j) = s j * Real.tanh (x * |u j|) := fun x j => by
    simp only [s, σ]
    split_ifs with hj
    · simp [abs_of_pos hj]
    · have : u j < 0 := lt_of_le_of_ne (not_lt.1 hj) (hu0 j)
      rw [abs_of_neg this, mul_neg, Real.tanh_neg]
      push_cast; ring
  have hs2 : ∀ j, s j + s j ≠ 0 := fun j => by
    rw [← two_mul]; exact mul_ne_zero two_ne_zero (hs0 j)
  clear_value s σ
  -- `tanh (t u_j) = s_j (1 - ζ_j) / (1 + ζ_j)` with `ζ_j = exp (-λ_j t)`.
  have htanh : ∀ t j, s j * (1 - Real.exp (-(lam j * t))) / (1 + Real.exp (-(lam j * t))) =
      Real.tanh (t * u j) := fun t j => by
    rw [hodd, mul_div_assoc, show lam j * t = 2 * (t * |u j|) by simp only [lam]; ring,
      ← tanh_eq_one_sub_div]
  -- The map `g : ζ ↦ s (1 - ζ) / (1 + ζ)` (analytic near `0`) and its inverse `ψ` near `s`.
  let g : (ι → ℝ) → (ι → ℝ) := fun ζ j => s j * (1 - ζ j) / (1 + ζ j)
  let ψ : (ι → ℝ) → (ι → ℝ) := fun w j => (s j - w j) / (s j + w j)
  have hg : AnalyticAt ℝ g 0 := by
    refine analyticAt_pi_iff.2 fun j => ?_
    have hp : AnalyticAt ℝ (fun ζ : ι → ℝ => ζ j) 0 :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j).analyticAt 0
    exact (analyticAt_const.mul (analyticAt_const.sub hp)).div (analyticAt_const.add hp)
      (by simp)
  have hψ : ContinuousAt ψ s := by
    refine continuousAt_pi.2 fun j => ?_
    exact (continuousAt_const.sub (continuous_apply j).continuousAt).div
      (continuousAt_const.add (continuous_apply j).continuousAt) (hs2 j)
  have hψs : ψ s = 0 := by funext j; simp [ψ]
  have hgψ : ∀ᶠ w in 𝓝 s, g (ψ w) = w := by
    have : ∀ᶠ w in 𝓝 s, ∀ j, s j + w j ≠ 0 := by
      refine eventually_all.2 fun j => ?_
      exact (continuousAt_const.add (continuous_apply j).continuousAt).eventually_ne (hs2 j)
    filter_upwards [this] with w hw
    funext j
    have h1 : 1 - (s j - w j) / (s j + w j) = 2 * w j / (s j + w j) := by
      field_simp [hw j]; ring
    have h2 : 1 + (s j - w j) / (s j + w j) = 2 * s j / (s j + w j) := by
      field_simp [hw j]; ring
    simp only [g, ψ]
    rw [h1, h2]
    field_simp [hw j, hs0 j]
  -- For each continuous linear functional `φ`, the function `φ ∘ 𝒯_i` vanishes everywhere.
  intro i w
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun φ => ?_
  have hG : ∀ i, AnalyticAt ℝ (fun ζ => φ (𝒯 i (g ζ))) 0 := fun i =>
    (φ.analyticAt _).comp ((h𝒯 i (g 0) trivial).comp hg)
  have hray : ∀ᶠ t : ℝ in atTop, ∑ i : Fin (K + 1), t ^ (i : ℕ) *
      φ (𝒯 i (g (fun j => Real.exp (-(lam j * t))))) = 0 := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    have hgt : g (fun j => Real.exp (-(lam j * t))) = fun j => Real.tanh (t * u j) := by
      funext j; exact htanh t j
    rw [hgt, ← map_zero φ, ← h t ht, map_sum]
    simp only [map_smul, smul_eq_mul]
  have h0 := eventually_eq_zero_of_sum_pow_mul_exp_ray lam hpos hlam K _ hG hray i
  -- Near `s`, `φ (𝒯_i w) = φ (𝒯_i (g (ψ w)))`, and `ψ w` is near `0`.
  have hnear : ∀ᶠ w in 𝓝 s, φ (𝒯 i w) = 0 := by
    have ht := hψ.tendsto
    rw [hψs] at ht
    filter_upwards [ht.eventually h0, hgψ] with w hw1 hw2
    rw [hw2] at hw1
    exact hw1
  -- Identity principle on `ℝ^q`.
  have han : AnalyticOnNhd ℝ (fun w => φ (𝒯 i w)) Set.univ := fun x _ =>
    (φ.analyticAt _).comp (h𝒯 i x trivial)
  exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ s) hnear (Set.mem_univ w)

/-- **Lemma D.1 for the hidden units of several tokens.** The same statement with the numbers
`u` arranged in a matrix `U` (one row per token, one column per hidden unit), for maps `𝒯_i` of
the matrix `tanh(t U)` of the outputs of the hidden units. -/
theorem tanh_ray_separation_matrix {T q : Type*} [Fintype T] [Fintype q] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (U : Matrix T q ℝ)
    (hU : LinearIndependent ℚ (fun p : T × q => U p.1 p.2)) (K : ℕ)
    (𝒯 : Fin (K + 1) → Matrix T q ℝ → F) (h𝒯 : ∀ i, AnalyticOnNhd ℝ (𝒯 i) Set.univ)
    (h : ∀ t : ℝ, 0 < t →
      ∑ i : Fin (K + 1), t ^ (i : ℕ) • 𝒯 i ((t • U).map Real.tanh) = 0) :
    ∀ i w, 𝒯 i w = 0 := by
  -- The continuous linear map `v ↦ (a, b) ↦ v (a, b)` from `ℝ^{T × q}` onto the matrices.
  let L : (T × q → ℝ) →ₗ[ℝ] Matrix T q ℝ :=
    { toFun := fun v => Matrix.of fun a b => v (a, b)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e : (T × q → ℝ) →L[ℝ] Matrix T q ℝ := LinearMap.toContinuousLinearMap L
  have he : ∀ v, e v = Matrix.of fun a b => v (a, b) := fun v => rfl
  have key := tanh_ray_separation (fun p : T × q => U p.1 p.2) hU K (fun i v => 𝒯 i (e v))
    (fun i x _ => (h𝒯 i (e x) trivial).comp (e.analyticAt x)) (fun t ht => by
      have hm : e (fun p => Real.tanh (t * U p.1 p.2)) = (t • U).map Real.tanh := by
        ext a b; simp [he]
      simp only [hm]
      exact h t ht)
  intro i w
  exact key i (fun p => w p.1 p.2)

end Skips
