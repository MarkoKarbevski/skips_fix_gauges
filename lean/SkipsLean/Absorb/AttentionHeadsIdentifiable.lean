import SkipsLean.Absorb.AttentionBlock

/-!
# Attention heads are identifiable on three or more tokens

Paper (absorb paper), Appendix A.2.

Lemma A.14 (Attention heads are identifiable): "Let `T ≥ 3`. Let
`Γ_1, …, Γ_m ∈ ℝ^{d_model × d_model}` be distinct, let `C_1, …, C_m, M ∈ ℝ^{d_model × d_model}`,
and write `P_Γ(h) = softmax(h Γ h^⊤)`, with the softmax taken row by row, with or without a causal
mask. If `h M + ∑_{k=1}^m P_{Γ_k}(h) h C_k = 0` for all `h` in a nonempty open subset of
`ℝ^{T × d_model}`, then `M = 0` and `C_1 = ⋯ = C_m = 0`."

Proposition A.15 (The softmaxes must match): "Let `T ≥ 3`, let `θ` and `θ′` be parameters of
attention blocks, and suppose that `h M + B_θ(h) = B_{θ′}(h)` for all `h` in a nonempty open set.
Then `M = 0`, and for every matrix `Γ`, the heads with score matrix `Γ` have the same sum of
value–output products in `B_θ` as in `B_{θ′}`."

The proof of the lemma uses the mask through one token only: "look at the last row, which attends
to all `T` tokens with or without a causal mask". So the lemma is stated for any mask `sees` in
which some token sees every token, on at least three tokens; the two masks of the paper (no mask:
`sees = fun _ _ => True`; the causal mask on `Fin n`: `sees t s` is `s ≤ t`) are stated by name.
`P_Γ(h)` is `attnWeights sees (h * Γ * hᵀ)` (`Network/Attention.lean`), and an attention block
with the score matrices `Γ_i` and the value–output products `C_i` is `attnHeads sees Γ C`; the
block `B_θ` of the paper, with the heads `W_{Q,i}, W_{K,i}, W_{V,i}, W_{O,i}` of dimension `d_h`,
is `attentionBlock`, with `Γ_i = W_{Q,i} W_{K,i}^⊤ / √d_h` and `C_i = W_{V,i} W_{O,i}`.

With two tokens the lemma fails (the paper, after Proposition A.15: "With two tokens, heads can
cancel"). The paper's proof moves one token along a complex line and compares the poles of the
heads.
-/

namespace Skips

open Matrix

variable {T d : Type*} [Fintype T] [Fintype d]

open Complex Filter Topology in
/-- **The residue step, for one complex variable:** if
`γ + ∑_{j ∈ S} (e^{b_j t} t β_j + α_j) / (e^{b_j t} + Z_j) = 0` for all real `t`, with every
`Z_j > 1`, and `b_k > 0` is the largest of the `b_j`, then `β_k = 0`. Multiplied by the
denominators, the identity is one of entire functions; at the pole
`t₊ = (log Z_k + π i) / b_k` of head `k`, no other denominator vanishes, so the numerator of head
`k` vanishes there, and its imaginary part is `−Z_k β_k π / b_k`. -/
private theorem residue_ahi {ι : Type*} (S : Finset ι) (b Z α β : ι → ℝ) (γ : ℝ)
    (hZ : ∀ j ∈ S, 1 < Z j)
    (h : ∀ t : ℝ, γ + ∑ j ∈ S,
      (Real.exp (b j * t) * t * β j + α j) / (Real.exp (b j * t) + Z j) = 0)
    (k : ι) (hk : k ∈ S) (hbk : 0 < b k) (hmax : ∀ j ∈ S, j ≠ k → b j < b k) :
    β k = 0 := by
  classical
  -- the denominators and the numerators as entire functions of `t ∈ ℂ`
  set D : ι → ℂ → ℂ := fun j t => Complex.exp (b j * t) + Z j with hD
  set N : ι → ℂ → ℂ := fun j t => Complex.exp (b j * t) * t * β j + α j with hN
  set P : ℂ → ℂ := fun t =>
    γ * ∏ j ∈ S, D j t + ∑ l ∈ S, N l t * ∏ j ∈ S.erase l, D j t with hP
  have hDa : ∀ j, AnalyticOnNhd ℂ (D j) Set.univ := fun j =>
    ((analyticOnNhd_const.mul analyticOnNhd_id).cexp).add analyticOnNhd_const
  have hNa : ∀ j, AnalyticOnNhd ℂ (N j) Set.univ := fun j =>
    ((((analyticOnNhd_const.mul analyticOnNhd_id).cexp).mul analyticOnNhd_id).mul
      analyticOnNhd_const).add analyticOnNhd_const
  have hPa : AnalyticOnNhd ℂ P Set.univ :=
    (analyticOnNhd_const.mul (Finset.analyticOnNhd_fun_prod _ fun j _ => hDa j)).add
      (Finset.analyticOnNhd_fun_sum _ fun l _ =>
        (hNa l).mul (Finset.analyticOnNhd_fun_prod _ fun j _ => hDa j))
  -- `P` vanishes on the real line: it is the identity times the product of the denominators
  have hPr : ∀ r : ℝ, P r = 0 := by
    intro r
    have hDr : ∀ j ∈ S, Real.exp (b j * r) + Z j ≠ 0 := fun j hj =>
      (add_pos (Real.exp_pos _) (lt_trans one_pos (hZ j hj))).ne'
    have key : γ * ∏ j ∈ S, (Real.exp (b j * r) + Z j)
        + ∑ l ∈ S, (Real.exp (b l * r) * r * β l + α l)
          * ∏ j ∈ S.erase l, (Real.exp (b j * r) + Z j) = 0 := by
      have e : ∀ l ∈ S, (Real.exp (b l * r) * r * β l + α l)
          * ∏ j ∈ S.erase l, (Real.exp (b j * r) + Z j)
          = (Real.exp (b l * r) * r * β l + α l) / (Real.exp (b l * r) + Z l)
            * ∏ j ∈ S, (Real.exp (b j * r) + Z j) := by
        intro l hl
        rw [← Finset.mul_prod_erase S _ hl]
        field_simp [hDr l hl]
      rw [Finset.sum_congr rfl e, ← Finset.sum_mul, ← add_mul, h r, zero_mul]
    have hc := congrArg (fun x : ℝ => (x : ℂ)) key
    push_cast at hc
    exact hc
  -- so `P` vanishes on `ℂ`
  have hP0 : ∀ t, P t = 0 := by
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), P z = 0 := by
      rw [Filter.frequently_iff]
      intro V hV
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hV
      refine ⟨((ε / 2 : ℝ) : ℂ), hball ⟨?_, ?_⟩, hPr _⟩
      · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        linarith
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
        exact (by linarith : ε / 2 ≠ 0)
    intro t
    exact hPa.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (Set.mem_univ 0) hfreq (Set.mem_univ t)
  -- the pole `t₊ = (log Z_k + π i) / b_k` of head `k`
  set L := Real.log (Z k) with hLdef
  have hL : 0 < L := Real.log_pos (hZ k hk)
  set tp : ℂ := ((L / b k : ℝ) : ℂ) + ((Real.pi / b k : ℝ) : ℂ) * I with htp
  have hre : ∀ j, ((b j : ℂ) * tp).re = b j * (L / b k) := by
    intro j
    simp only [htp, ofReal_div, mul_re, ofReal_re, add_re, div_ofReal_re, I_re, mul_zero,
      div_ofReal_im, ofReal_im, zero_div, I_im, mul_one, sub_self, add_zero, add_im, mul_im,
      zero_add, zero_mul, sub_zero]
  have him : ∀ j, ((b j : ℂ) * tp).im = b j * (Real.pi / b k) := by
    intro j
    simp only [htp, ofReal_div, mul_im, ofReal_re, add_im, div_ofReal_im, ofReal_im, zero_div,
      div_ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add, add_re, mul_re, sub_self,
      zero_mul]
  have hDk : D k tp = 0 := by
    have e : (b k : ℂ) * tp = (L : ℂ) + Real.pi * I := by
      apply Complex.ext
      · rw [hre]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im]
        field_simp
        ring
      · rw [him]
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
          Complex.ofReal_re, Complex.I_im]
        field_simp
        ring
    show Complex.exp (b k * tp) + Z k = 0
    rw [e, Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp, hLdef,
      Real.exp_log (lt_trans one_pos (hZ k hk))]
    ring
  -- no other denominator vanishes at `t₊`
  have hDj : ∀ j ∈ S, j ≠ k → D j tp ≠ 0 := by
    intro j hj hjk hzero
    have hexp : Complex.exp (b j * tp) = -(Z j : ℂ) := eq_neg_of_add_eq_zero_left hzero
    by_cases hbj : b j ≤ 0
    · -- `|e^{b_j t₊}| = e^{b_j log Z_k / b_k} ≤ 1 < Z_j`
      have h1 : ‖Complex.exp (b j * tp)‖ = Real.exp (b j * (L / b k)) := by
        rw [Complex.norm_exp, hre]
      have h2 : Real.exp (b j * (L / b k)) ≤ 1 :=
        Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hbj (div_pos hL hbk).le)
      rw [hexp, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (lt_trans one_pos (hZ j hj))] at h1
      linarith [hZ j hj]
    · -- `0 < b_j < b_k`: the imaginary part of `e^{b_j t₊}` is positive
      have h1 : (Complex.exp (b j * tp)).im
          = Real.exp (b j * (L / b k)) * Real.sin (b j * (Real.pi / b k)) := by
        rw [Complex.exp_im, hre, him]
      have hs : 0 < Real.sin (b j * (Real.pi / b k)) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · exact mul_pos (not_le.mp hbj) (div_pos Real.pi_pos hbk)
        · rw [mul_div_assoc', div_lt_iff₀ hbk, mul_comm]
          exact mul_lt_mul_of_pos_left (hmax j hj hjk) Real.pi_pos
      rw [hexp, Complex.neg_im, Complex.ofReal_im, neg_zero] at h1
      have := mul_pos (Real.exp_pos (b j * (L / b k))) hs
      linarith
  -- at `t₊`, `P = N_k(t₊) ∏_{j ≠ k} D_j(t₊)`, so `N_k(t₊) = 0`
  have hPtp : P tp = N k tp * ∏ j ∈ S.erase k, D j tp := by
    show γ * ∏ j ∈ S, D j tp + ∑ l ∈ S, N l tp * ∏ j ∈ S.erase l, D j tp = _
    rw [Finset.prod_eq_zero hk hDk, mul_zero, zero_add, Finset.sum_eq_single k]
    · intro l _ hlk
      rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hlk, hk⟩) hDk, mul_zero]
    · exact fun h' => absurd hk h'
  have hprod : ∏ j ∈ S.erase k, D j tp ≠ 0 := Finset.prod_ne_zero_iff.2 fun j hj =>
    hDj j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
  have hNk : N k tp = 0 := by
    have h1 := hP0 tp
    rw [hPtp] at h1
    exact (mul_eq_zero.1 h1).resolve_right hprod
  -- `N_k(t₊) = −Z_k t₊ β_k + α_k`, whose imaginary part is `−Z_k (π / b_k) β_k`
  have hexpk : Complex.exp (b k * tp) = -(Z k : ℂ) := eq_neg_of_add_eq_zero_left hDk
  have him2 := congrArg Complex.im hNk
  simp only [hN, hexpk] at him2
  simp only [htp, ofReal_div, neg_mul, add_im, neg_im, mul_im, mul_re, ofReal_re, add_re,
    div_ofReal_re, I_re, mul_zero, div_ofReal_im, ofReal_im, zero_div, I_im, mul_one, sub_self,
    add_zero, zero_add, zero_mul, sub_zero, zero_im, neg_eq_zero, mul_eq_zero, div_eq_zero_iff,
    Real.pi_ne_zero, false_or] at him2
  rcases him2 with (h1 | h1) | h1
  · linarith [hZ k hk]
  · linarith
  · exact h1

/-- **Lemma A.14 of the absorb paper (Attention heads are identifiable):** on at least three
tokens, with a mask in which some token sees every token, let the score matrices `Γ_1, …, Γ_m` be
distinct. If `h M + ∑_k P_{Γ_k}(h) h C_k = 0` for all `h` in a nonempty open set, then `M = 0` and
every `C_k = 0`. -/
theorem attnHeads_identifiable (sees : T → T → Prop) [DecidableRel sees]
    (hT : 3 ≤ Fintype.card T) (hsees : ∃ t₀, ∀ s, sees t₀ s) {m : ℕ}
    (Γ : Fin m → Matrix d d ℝ) (hΓ : Function.Injective Γ) (C : Fin m → Matrix d d ℝ)
    (M : Matrix d d ℝ) (U : Set (Matrix T d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U, h * M + ∑ k, attnWeights sees (h * Γ k * hᵀ) * h * C k = 0) :
    M = 0 ∧ ∀ k, C k = 0 := by
  sorry

/-- **Lemma A.14 without a mask:** every token sees every token. -/
theorem attnHeads_identifiable_noMask (hT : 3 ≤ Fintype.card T) {m : ℕ}
    (Γ : Fin m → Matrix d d ℝ) (hΓ : Function.Injective Γ) (C : Fin m → Matrix d d ℝ)
    (M : Matrix d d ℝ) (U : Set (Matrix T d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U,
      h * M + ∑ k, attnWeights (fun _ _ : T => True) (h * Γ k * hᵀ) * h * C k = 0) :
    M = 0 ∧ ∀ k, C k = 0 := by
  -- there is a token, and without a mask it sees every token
  obtain ⟨t₀⟩ : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  exact attnHeads_identifiable (fun _ _ : T => True) hT ⟨t₀, fun _ => trivial⟩ Γ hΓ C M U hU
    hne h0

/-- **Lemma A.14 with the causal mask:** on the tokens `0, …, n − 1`, `n ≥ 3`, token `t` sees the
tokens `s ≤ t`. -/
theorem attnHeads_identifiable_causal {n : ℕ} (hn : 3 ≤ n) {m : ℕ}
    (Γ : Fin m → Matrix d d ℝ) (hΓ : Function.Injective Γ) (C : Fin m → Matrix d d ℝ)
    (M : Matrix d d ℝ) (U : Set (Matrix (Fin n) d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U,
      h * M + ∑ k, attnWeights (fun t s : Fin n => s ≤ t) (h * Γ k * hᵀ) * h * C k = 0) :
    M = 0 ∧ ∀ k, C k = 0 := by
  -- the last token `n - 1` sees every token
  have hT : 3 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn
  refine attnHeads_identifiable (fun t s : Fin n => s ≤ t) hT ⟨⟨n - 1, by omega⟩, fun s => ?_⟩
    Γ hΓ C M U hU hne h0
  rw [Fin.le_def]
  show s.val ≤ n - 1
  omega

open scoped Classical in
/-- Grouping heads by score matrix: if every `Γ_j` is one of the distinct matrices `G_i`, then
`∑_i P_{G_i}(h) h (∑_{j : Γ_j = G_i} C_j) = ∑_j P_{Γ_j}(h) h C_j`. -/
private theorem sum_group_ahi (sees : T → T → Prop) [DecidableRel sees] {ι H : Type*}
    [Fintype ι] [Fintype H] (G : ι → Matrix d d ℝ) (hG : Function.Injective G)
    (Γ C : H → Matrix d d ℝ) (hS : ∀ j, ∃ i, G i = Γ j) (h : Matrix T d ℝ) :
    ∑ i, attnWeights sees (h * G i * hᵀ) * h * (∑ j, if Γ j = G i then C j else 0)
      = attnHeads sees Γ C h := by
  have e1 : ∀ i, attnWeights sees (h * G i * hᵀ) * h * (∑ j, if Γ j = G i then C j else 0)
      = ∑ j, if Γ j = G i then attnWeights sees (h * Γ j * hᵀ) * h * C j else 0 := by
    intro i
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : Γ j = G i
    · simp only [hj, ite_true]
    · simp only [hj, ite_false, Matrix.mul_zero]
  simp only [e1]
  rw [Finset.sum_comm]
  unfold attnHeads
  refine Finset.sum_congr rfl fun j _ => ?_
  -- exactly one `i` has `G_i = Γ_j`
  obtain ⟨i₀, hi₀⟩ := hS j
  rw [Finset.sum_eq_single i₀ (fun i _ hi => ite_eq_right_iff.2 fun hc => absurd
    (hG (hc.symm.trans hi₀.symm)) hi) (fun h' => absurd (Finset.mem_univ _) h')]
  simp only [hi₀, ite_true]

open scoped Classical in
/-- **Proposition A.15 of the absorb paper (The softmaxes must match), for attention blocks given
by their score matrices and value–output products:** on at least three tokens, with a mask in
which some token sees every token, if `h M + B(h) = B'(h)` for all `h` in a nonempty open set,
then `M = 0`, and for every matrix `G` the heads with the score matrix `G` have the same sum of
value–output products in `B` as in `B'`. -/
theorem attnHeads_sum_eq_of_mul_add_eq (sees : T → T → Prop) [DecidableRel sees]
    (hT : 3 ≤ Fintype.card T) (hsees : ∃ t₀, ∀ s, sees t₀ s) {H H' : Type*} [Fintype H]
    [Fintype H'] (Γ C : H → Matrix d d ℝ) (Γ' C' : H' → Matrix d d ℝ) (M : Matrix d d ℝ)
    (U : Set (Matrix T d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U, h * M + attnHeads sees Γ C h = attnHeads sees Γ' C' h) :
    M = 0 ∧ ∀ G : Matrix d d ℝ,
      (∑ i, if Γ i = G then C i else 0) = ∑ i, if Γ' i = G then C' i else 0 := by
  classical
  -- the score matrices that occur, indexed by `Fin m`
  set S : Finset (Matrix d d ℝ) := Finset.univ.image Γ ∪ Finset.univ.image Γ' with hS
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let G₀ : Fin (Fintype.card S) → Matrix d d ℝ := fun i => (e.symm i : Matrix d d ℝ)
  have hG₀ : Function.Injective G₀ := fun i j hij => e.symm.injective (Subtype.ext hij)
  have hrange : ∀ A, A ∈ S → ∃ i, G₀ i = A := fun A hA => ⟨e ⟨A, hA⟩, by
    show ((e.symm (e ⟨A, hA⟩) : S) : Matrix d d ℝ) = A
    rw [Equiv.symm_apply_apply]⟩
  have hmemΓ : ∀ j, Γ j ∈ S := fun j =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem Γ (Finset.mem_univ j))
  have hmemΓ' : ∀ j, Γ' j ∈ S := fun j =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem Γ' (Finset.mem_univ j))
  -- the coefficient of the score matrix `G₀ i`: the heads of `B` minus the heads of `B'`
  obtain ⟨hM, hC⟩ := attnHeads_identifiable sees hT hsees G₀ hG₀
    (fun i => (∑ j, if Γ j = G₀ i then C j else 0) - ∑ j, if Γ' j = G₀ i then C' j else 0)
    M U hU hne (fun h hh => by
      -- `h M + ∑_i P_{G₀ i}(h) h C̃_i = h M + B(h) - B'(h) = 0`
      simp only [Matrix.mul_sub, Finset.sum_sub_distrib]
      rw [sum_group_ahi sees G₀ hG₀ Γ C (fun j => hrange _ (hmemΓ j)) h,
        sum_group_ahi sees G₀ hG₀ Γ' C' (fun j => hrange _ (hmemΓ' j)) h, ← add_sub_assoc,
        h0 h hh, sub_self])
  refine ⟨hM, fun G => ?_⟩
  by_cases hG : G ∈ S
  · -- `G = G₀ i`, and `C̃_i = 0`
    obtain ⟨i, hi⟩ := hrange G hG
    have h1 := hC i
    rw [hi] at h1
    exact sub_eq_zero.mp h1
  · -- no head has the score matrix `G`
    rw [Finset.sum_eq_zero fun j _ =>
        ite_eq_right_iff.2 fun (h : Γ j = G) => absurd (h ▸ hmemΓ j) hG,
      Finset.sum_eq_zero fun j _ =>
        ite_eq_right_iff.2 fun (h : Γ' j = G) => absurd (h ▸ hmemΓ' j) hG]

open scoped Classical in
/-- **Proposition A.15 of the absorb paper (The softmaxes must match):** for attention blocks
`B_θ`, `B_{θ′}` with any numbers of heads and any head dimensions, on at least three tokens, with
a mask in which some token sees every token: if `h M + B_θ(h) = B_{θ′}(h)` for all `h` in a
nonempty open set, then `M = 0`, and for every matrix `G` the heads with the score matrix
`W_Q W_K^⊤ / √d_h = G` have the same sum of value–output products `W_V W_O` in `B_θ` as in
`B_{θ′}`. -/
theorem attentionBlock_sum_eq_of_mul_add_eq (sees : T → T → Prop) [DecidableRel sees]
    (hT : 3 ≤ Fintype.card T) (hsees : ∃ t₀, ∀ s, sees t₀ s) {H dh H' dh' : Type*} [Fintype H]
    [Fintype dh] [Fintype H'] [Fintype dh'] (WQ WK WV : H → Matrix d dh ℝ)
    (WO : H → Matrix dh d ℝ) (WQ' WK' WV' : H' → Matrix d dh' ℝ) (WO' : H' → Matrix dh' d ℝ)
    (M : Matrix d d ℝ) (U : Set (Matrix T d ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h0 : ∀ h ∈ U, h * M + attentionBlock sees WQ WK WV WO h
      = attentionBlock sees WQ' WK' WV' WO' h) :
    M = 0 ∧ ∀ G : Matrix d d ℝ,
      (∑ i, if (Real.sqrt (Fintype.card dh))⁻¹ • (WQ i * (WK i)ᵀ) = G then WV i * WO i else 0)
        = ∑ i, if (Real.sqrt (Fintype.card dh'))⁻¹ • (WQ' i * (WK' i)ᵀ) = G
            then WV' i * WO' i else 0 := by
  -- the blocks of equation (4) are `attnHeads` with `Γ_i = W_{Q,i} W_{K,i}ᵀ / √d_h`,
  -- `C_i = W_{V,i} W_{O,i}`
  unfold attentionBlock at h0
  exact attnHeads_sum_eq_of_mul_add_eq sees hT hsees _ _ _ _ M U hU hne h0

end Skips
