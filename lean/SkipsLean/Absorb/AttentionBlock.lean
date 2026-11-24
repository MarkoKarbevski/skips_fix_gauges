import SkipsLean.Network.Attention
import SkipsLean.Imports
import SkipsLean.Generic.AnalyticZeroSet

/-!
# No absorption in attention blocks

Paper (absorb paper): Theorem 3.4 (No absorption in attention blocks) and Theorem A.13 (Attention
and linear terms): "Let `θ` and `θ'` be parameters of attention blocks with any numbers of heads
and any head dimensions, and let `M ≠ 0` be a `d_model × d_model` matrix. (i) For almost every
`h ∈ ℝ^{T × d_model}`, `h M + B_θ(h) ≠ B_θ'(h)`. (ii) Some `h` whose rows have norm at most `1`
has a row in which `h M + B_θ(h)` and `B_θ'(h)` differ by at least `‖M‖/3`, where `‖M‖` is the
spectral norm. (iii) With an embedding `E` and a readout `D` with `E D ≠ 0`, the residual network
`X ↦ (X E + B_θ(X E)) D` differs from every skipless network `X ↦ B_θ'(X E') D'`."

Its proof: "Step 1: equal tokens. Let every row of `h` be `x`. Each row of `R_k(h)` sums to `1`,
so every row of `R_k(h) h` is `x`. […] Step 2: one zero token. Let the last row of `h` be `0` and
the other rows `y`. Every score in the last row of `R_k(h)` is a product with the last row of
`h`, which is `0`. So that row of `R_k(h)` is `(1/T, …, 1/T)`, also with a causal mask, since the
last token sees all `T` tokens."

Stated here for blocks given by the score matrices and the value–output products of their heads
(`attnHeads`, `Network/Attention.lean`): any matrices `Γ_i`, `C_i`, so any numbers of heads and
any head dimensions, and the paper's blocks (`attentionBlock`) in the two corollaries for
Theorem 3.4. The mask is any relation `sees` with one token `t₀` that sees all tokens (the last
token under the causal mask, any token without a mask), and there are at least two tokens. Norms
of rows are Euclidean, written `Real.sqrt (v ⬝ᵥ v)`; "at least `‖M‖/3`" is stated for every row
`x` of norm at most `1` as "at least `‖x M‖/3`" (the spectral norm is the largest `‖x M‖`).
-/

namespace Skips

open Matrix MeasureTheory

variable {T d : Type*} [Fintype T] [Fintype d]

/-- The denominator of row `t` of the weights is positive when token `t` sees some token. -/
private theorem attnWeights_den_pos_atb (sees : T → T → Prop) [DecidableRel sees]
    (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
    0 < ∑ s', if sees t s' then Real.exp (Z t s') else 0 := by
  obtain ⟨s, hs⟩ := ht
  refine Finset.sum_pos' (fun s' _ => ?_) ⟨s, Finset.mem_univ _, ?_⟩
  · split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  · simp only [hs, ite_true]
    exact Real.exp_pos _

/-- **(a)** Row `t` of the weights sums to `1` when token `t` sees some token. -/
private theorem attnWeights_sum_atb (sees : T → T → Prop) [DecidableRel sees]
    (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
    ∑ s, attnWeights sees Z t s = 1 := by
  have hS := attnWeights_den_pos_atb sees Z t ht
  have h1 : ∀ s, attnWeights sees Z t s = (if sees t s then Real.exp (Z t s) else 0)
      / ∑ s', if sees t s' then Real.exp (Z t s') else 0 := by
    intro s
    simp only [attnWeights, Matrix.of_apply]
    split_ifs
    · rfl
    · rw [zero_div]
  simp only [h1, ← Finset.sum_div]
  exact div_self hS.ne'

/-- **(b)** If row `t` of the scores is `0` and token `t` sees all tokens, row `t` of the
weights is uniform. -/
private theorem attnWeights_uniform_atb (sees : T → T → Prop) [DecidableRel sees]
    (Z : Matrix T T ℝ) (t : T) (ht : ∀ s, sees t s) (hZ : ∀ s, Z t s = 0) (s : T) :
    attnWeights sees Z t s = (Fintype.card T : ℝ)⁻¹ := by
  simp only [attnWeights, Matrix.of_apply, ht, ite_true, hZ, Real.exp_zero, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, one_div]

omit [Fintype T] [Fintype d] in
/-- A row of a sum of matrices. -/
private theorem sum_row_atb {H : Type*} [Fintype H] (A : H → Matrix T d ℝ) (t : T) :
    (∑ i, A i) t = ∑ i, A i t :=
  Finset.sum_apply t _ _

/-- Row `t` of one head: `(P * h * C) t = (∑_s P t s • h s) ᵥ* C`. -/
private theorem head_row_atb (P : Matrix T T ℝ) (h : Matrix T d ℝ) (C : Matrix d d ℝ) (t : T) :
    (P * h * C) t = (∑ s, P t s • h s) ᵥ* C := by
  rw [Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul, Matrix.vecMul_eq_sum (P t) h]

/-- **Proof of Theorem A.13, Step 1 (equal tokens):** if every row of `h` is `x`, the row of the
block at a token that sees some token is `x ∑_i C_i`. -/
theorem attnHeads_const_row (sees : T → T → Prop) [DecidableRel sees] {H : Type*} [Fintype H]
    (Γ C : H → Matrix d d ℝ) (x : d → ℝ) (t : T) (ht : ∃ s, sees t s) :
    attnHeads sees Γ C (Matrix.of fun _ => x) t = x ᵥ* ∑ i, C i := by
  -- each row of the weights sums to `1`, so each head gives `x C_i`
  rw [attnHeads, sum_row_atb, Matrix.vecMul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [head_row_atb]
  congr 1
  have h1 : ∀ s, (Matrix.of fun _ : T => x) s = x := fun s => rfl
  simp only [h1, ← Finset.sum_smul, attnWeights_sum_atb sees _ t ht, one_smul]

/-- **Proof of Theorem A.13, Step 2 (one zero token):** if row `t₀` of `h` is `0` and token `t₀`
sees all tokens, the row of the block at `t₀` is the mean of the rows of `h` times
`∑_i C_i`. -/
theorem attnHeads_zero_row (sees : T → T → Prop) [DecidableRel sees] {H : Type*} [Fintype H]
    (Γ C : H → Matrix d d ℝ) (h : Matrix T d ℝ) (t₀ : T) (ht₀ : ∀ s, sees t₀ s)
    (h0 : h t₀ = 0) :
    attnHeads sees Γ C h t₀ = ((Fintype.card T : ℝ)⁻¹ • ∑ s, h s) ᵥ* ∑ i, C i := by
  rw [attnHeads, sum_row_atb, Matrix.vecMul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [head_row_atb]
  congr 1
  -- row `t₀` of the scores is `0`, so row `t₀` of the weights is uniform
  have hZ : ∀ s, (h * Γ i * hᵀ) t₀ s = 0 := by
    intro s
    rw [Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul, h0, Matrix.zero_vecMul,
      Matrix.zero_vecMul, Pi.zero_apply]
  simp only [attnWeights_uniform_atb sees _ t₀ ht₀ hZ]
  exact (Finset.smul_sum (s := Finset.univ) (f := fun s => h s)).symm

omit [Fintype T] in
/-- The Euclidean norm of a row, `√(v ⬝ᵥ v)`, is the norm of `v` in `EuclideanSpace ℝ d`. -/
private theorem sqrt_dot_eq_norm_atb (v : d → ℝ) :
    Real.sqrt (v ⬝ᵥ v) = ‖WithLp.toLp 2 v‖ := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp only [dotProduct, Real.norm_eq_abs, sq, abs_mul_abs_self]

omit [Fintype T] in
/-- The case split of the proof of (ii): `‖a‖ ≤ ‖a + b‖ + ‖b‖`, so `‖a‖/3 ≤ ‖a + b‖` or
`‖a‖/3 ≤ r ‖b‖` for `r ≥ 1/2`. -/
private theorem norm_cases_atb (a b : d → ℝ) {r : ℝ} (hr : 1 / 2 ≤ r) :
    Real.sqrt (a ⬝ᵥ a) / 3 ≤ Real.sqrt ((a + b) ⬝ᵥ (a + b))
      ∨ Real.sqrt (a ⬝ᵥ a) / 3 ≤ Real.sqrt ((r • b) ⬝ᵥ (r • b)) := by
  simp only [sqrt_dot_eq_norm_atb, WithLp.toLp_add, WithLp.toLp_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r)]
  have htri : ‖WithLp.toLp 2 a‖ ≤ ‖WithLp.toLp 2 a + WithLp.toLp 2 b‖ + ‖WithLp.toLp 2 b‖ := by
    have h := norm_sub_le (WithLp.toLp 2 a + WithLp.toLp 2 b) (WithLp.toLp 2 b)
    rwa [add_sub_cancel_right] at h
  have hB := norm_nonneg (WithLp.toLp 2 b)
  by_cases hc : ‖WithLp.toLp 2 a‖ / 3 ≤ ‖WithLp.toLp 2 a + WithLp.toLp 2 b‖
  · exact Or.inl hc
  · right
    have hc' := not_le.mp hc
    nlinarith [mul_nonneg (sub_nonneg.2 hr) hB]

omit [Fintype T] [Fintype d] in
/-- A row of `A + B - C`. -/
private theorem add_sub_row_atb (A B C : Matrix T d ℝ) (t : T) :
    (A + B - C) t = A t + B t - C t := rfl

omit [Fintype d] in
/-- The rows of the matrix whose row `t₀` is `0` and whose other rows are `x` sum to
`(T - 1) x`. -/
private theorem sum_rows_zero_row_atb [DecidableEq T] (t₀ : T) (x : d → ℝ) :
    ∑ s, (Matrix.of fun t => if t = t₀ then 0 else x : Matrix T d ℝ) s
      = ((Fintype.card T : ℝ) - 1) • x := by
  have h1 : ∀ s, (Matrix.of fun t => if t = t₀ then 0 else x : Matrix T d ℝ) s
      = x - if s = t₀ then x else 0 := by
    intro s
    show (if s = t₀ then (0 : d → ℝ) else x) = x - if s = t₀ then x else 0
    by_cases hs : s = t₀
    · simp only [hs, ite_true, sub_self]
    · simp only [hs, ite_false, sub_zero]
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_smul, one_smul, Nat.cast_smul_eq_nsmul]

/-- **Theorem A.13 (ii) / Theorem 3.4 (ii):** with at least two tokens and a token that sees all
tokens, for every row `x` of norm at most `1` some `h` whose rows have norm at most `1` has a row
in which `h M + B_θ(h)` and `B_θ'(h)` differ by at least `‖x M‖/3`. -/
theorem exists_row_attnHeads_sub_ge (sees : T → T → Prop) [DecidableRel sees]
    (hT : 2 ≤ Fintype.card T) (t₀ : T) (ht₀ : ∀ s, sees t₀ s) {H H' : Type*} [Fintype H]
    [Fintype H'] (Γ C : H → Matrix d d ℝ) (Γ' C' : H' → Matrix d d ℝ) (M : Matrix d d ℝ)
    (x : d → ℝ) (hx : x ⬝ᵥ x ≤ 1) :
    ∃ h : Matrix T d ℝ, (∀ t, h t ⬝ᵥ h t ≤ 1) ∧ ∃ t,
      Real.sqrt ((x ᵥ* M) ⬝ᵥ (x ᵥ* M)) / 3
        ≤ Real.sqrt (((h * M + attnHeads sees Γ C h - attnHeads sees Γ' C' h) t)
            ⬝ᵥ ((h * M + attnHeads sees Γ C h - attnHeads sees Γ' C' h) t)) := by
  classical
  have hT2 : (2 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
  have hr : 1 / 2 ≤ (Fintype.card T : ℝ)⁻¹ * ((Fintype.card T : ℝ) - 1) := by
    rw [inv_mul_eq_div, le_div_iff₀ (by linarith)]
    linarith
  -- Step 1, all rows `x`: row `t₀` is `x M + x (∑ C_i - ∑ C'_i)`
  have hrow₁ : ((Matrix.of fun _ => x : Matrix T d ℝ) * M
      + attnHeads sees Γ C (Matrix.of fun _ => x) - attnHeads sees Γ' C' (Matrix.of fun _ => x)) t₀
        = x ᵥ* M + (x ᵥ* ∑ i, C i - x ᵥ* ∑ i, C' i) := by
    rw [add_sub_row_atb, Matrix.mul_apply_eq_vecMul,
      attnHeads_const_row sees Γ C x t₀ ⟨t₀, ht₀ t₀⟩,
      attnHeads_const_row sees Γ' C' x t₀ ⟨t₀, ht₀ t₀⟩, add_sub_assoc]
    rfl
  -- Step 2, row `t₀` zero and the other rows `x`: row `t₀` is `((T - 1)/T) x (∑ C_i - ∑ C'_i)`
  obtain ⟨h₂, hh₂⟩ : ∃ h₂ : Matrix T d ℝ, h₂ = Matrix.of fun t => if t = t₀ then 0 else x :=
    ⟨_, rfl⟩
  have h₂0 : h₂ t₀ = 0 := by
    rw [hh₂]
    show (if t₀ = t₀ then (0 : d → ℝ) else x) = 0
    rw [ite_eq_left_iff]
    exact fun h => absurd rfl h
  have hrow₂ : (h₂ * M + attnHeads sees Γ C h₂ - attnHeads sees Γ' C' h₂) t₀
      = ((Fintype.card T : ℝ)⁻¹ * ((Fintype.card T : ℝ) - 1))
        • (x ᵥ* ∑ i, C i - x ᵥ* ∑ i, C' i) := by
    rw [add_sub_row_atb, Matrix.mul_apply_eq_vecMul, attnHeads_zero_row sees Γ C h₂ t₀ ht₀ h₂0,
      attnHeads_zero_row sees Γ' C' h₂ t₀ ht₀ h₂0, h₂0, Matrix.zero_vecMul, zero_add, hh₂,
      sum_rows_zero_row_atb, smul_smul, Matrix.smul_vecMul, Matrix.smul_vecMul, smul_sub]
  rcases norm_cases_atb (x ᵥ* M) (x ᵥ* ∑ i, C i - x ᵥ* ∑ i, C' i) hr with hc | hc
  · exact ⟨Matrix.of fun _ => x, fun _ => hx, t₀, by rw [hrow₁]; exact hc⟩
  · refine ⟨h₂, fun t => ?_, t₀, by rw [hrow₂]; exact hc⟩
    by_cases ht : t = t₀
    · rw [ht, h₂0, zero_dotProduct]
      exact zero_le_one
    · rw [hh₂]
      show (if t = t₀ then (0 : d → ℝ) else x) ⬝ᵥ (if t = t₀ then (0 : d → ℝ) else x) ≤ 1
      simp only [ht, ite_false]
      exact hx

/-- A coordinate `h ↦ h t j` is analytic. -/
private theorem analyticOnNhd_coord_atb (t : T) (j : d) :
    AnalyticOnNhd ℝ (fun h : T → d → ℝ => h t j) Set.univ :=
  ((ContinuousLinearMap.proj (R := ℝ) j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => d → ℝ) t)).analyticOnNhd _

/-- An entry of `h A` is analytic in `h`. -/
private theorem analyticOnNhd_mul_entry_atb (A : Matrix d d ℝ) (t : T) (a : d) :
    AnalyticOnNhd ℝ (fun h : T → d → ℝ => (Matrix.of h * A) t a) Set.univ := by
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact Finset.analyticOnNhd_fun_sum _ fun c _ =>
    (analyticOnNhd_coord_atb t c).mul analyticOnNhd_const

/-- An entry of the scores `h Γ hᵀ` is analytic in `h`. -/
private theorem analyticOnNhd_scores_atb (Γ : Matrix d d ℝ) (t s : T) :
    AnalyticOnNhd ℝ (fun h : T → d → ℝ => (Matrix.of h * Γ * (Matrix.of h)ᵀ) t s)
      Set.univ := by
  have e : (fun h : T → d → ℝ => (Matrix.of h * Γ * (Matrix.of h)ᵀ) t s)
      = fun h => ∑ k, (Matrix.of h * Γ) t k * h s k := by
    funext h
    rw [Matrix.mul_apply]
    rfl
  rw [e]
  exact Finset.analyticOnNhd_fun_sum _ fun k _ =>
    (analyticOnNhd_mul_entry_atb Γ t k).mul (analyticOnNhd_coord_atb s k)

omit [Fintype d] in
/-- An entry of the weights of analytic scores is analytic: the denominator of a row is
positive when the token sees some token, and the row is `0` otherwise. -/
private theorem analyticOnNhd_attnWeights_atb (sees : T → T → Prop) [DecidableRel sees]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Z : E → Matrix T T ℝ)
    (hZ : ∀ t s, AnalyticOnNhd ℝ (fun h => Z h t s) Set.univ) (t s : T) :
    AnalyticOnNhd ℝ (fun h => attnWeights sees (Z h) t s) Set.univ := by
  simp only [attnWeights, Matrix.of_apply]
  by_cases hs : sees t s
  · simp only [hs, ite_true]
    refine (hZ t s).rexp.div (Finset.analyticOnNhd_fun_sum _ fun s' _ => ?_)
      fun h _ => (attnWeights_den_pos_atb sees (Z h) t ⟨s, hs⟩).ne'
    by_cases hs' : sees t s'
    · simp only [hs', ite_true]
      exact (hZ t s').rexp
    · simp only [hs', ite_false]
      exact analyticOnNhd_const
  · simp only [hs, ite_false]
    exact analyticOnNhd_const

/-- An entry of the block is analytic in `h`. -/
private theorem analyticOnNhd_attnHeads_atb (sees : T → T → Prop) [DecidableRel sees]
    {H : Type*} [Fintype H] (Γ C : H → Matrix d d ℝ) (t : T) (a : d) :
    AnalyticOnNhd ℝ (fun h : T → d → ℝ => attnHeads sees Γ C (Matrix.of h) t a) Set.univ := by
  have e : ∀ h : T → d → ℝ, attnHeads sees Γ C (Matrix.of h) t a
      = ∑ i, ∑ c, (∑ s, attnWeights sees (Matrix.of h * Γ i * (Matrix.of h)ᵀ) t s * h s c)
        * C i c a := by
    intro h
    simp only [attnHeads, Matrix.sum_apply, Matrix.mul_apply, Matrix.of_apply]
  simp only [e]
  exact Finset.analyticOnNhd_fun_sum _ fun i _ => Finset.analyticOnNhd_fun_sum _ fun c _ =>
    (Finset.analyticOnNhd_fun_sum _ fun s _ =>
      (analyticOnNhd_attnWeights_atb sees _ (analyticOnNhd_scores_atb (Γ i)) t s).mul
        (analyticOnNhd_coord_atb s c)).mul analyticOnNhd_const

/-- **Theorem A.13 (i) / Theorem 3.4 (i):** with at least two tokens and a token that sees all
tokens, for `M ≠ 0` and almost every `h`, `h M + B_θ(h) ≠ B_θ'(h)`. -/
theorem ae_mul_add_attnHeads_ne (sees : T → T → Prop) [DecidableRel sees]
    (hT : 2 ≤ Fintype.card T) (t₀ : T) (ht₀ : ∀ s, sees t₀ s) {H H' : Type*} [Fintype H]
    [Fintype H'] (Γ C : H → Matrix d d ℝ) (Γ' C' : H' → Matrix d d ℝ) (M : Matrix d d ℝ)
    (hM : M ≠ 0) (μ : Measure (T → d → ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ h ∂μ, (Matrix.of h) * M + attnHeads sees Γ C (Matrix.of h)
      ≠ attnHeads sees Γ' C' (Matrix.of h) := by
  classical
  -- some `h₀` with `h₀ M + B_θ(h₀) ≠ B_θ'(h₀)`, from (ii) at a row `x` with `x M ≠ 0`
  obtain ⟨a, b, hab⟩ : ∃ a b, M a b ≠ 0 := by
    by_contra hcon
    exact hM (Matrix.ext fun a b => not_not.mp fun h => hcon ⟨a, b, h⟩)
  have hx : (Pi.single a 1 : d → ℝ) ⬝ᵥ Pi.single a 1 ≤ 1 := by
    simp only [single_dotProduct, Pi.single_eq_same, one_mul, le_refl]
  have hxM : 0 < Real.sqrt (((Pi.single a 1 : d → ℝ) ᵥ* M) ⬝ᵥ ((Pi.single a 1 : d → ℝ) ᵥ* M)) := by
    refine Real.sqrt_pos.2 (lt_of_le_of_ne (dotProduct_self_star_nonneg _) fun h => hab ?_)
    have h' := dotProduct_self_eq_zero.mp h.symm
    have hb := congrFun h' b
    simpa only [single_vecMul, one_smul, Matrix.row_apply, Pi.zero_apply] using hb
  obtain ⟨h₀, -, t, ht⟩ := exists_row_attnHeads_sub_ge sees hT t₀ ht₀ Γ C Γ' C' M _ hx
  have hrow : (h₀ * M + attnHeads sees Γ C h₀ - attnHeads sees Γ' C' h₀) t ≠ 0 := by
    intro h0
    rw [h0, dotProduct_zero, Real.sqrt_zero] at ht
    linarith
  obtain ⟨c, hc⟩ : ∃ c, (h₀ * M + attnHeads sees Γ C h₀ - attnHeads sees Γ' C' h₀) t c ≠ 0 := by
    by_contra hcon
    exact hrow (funext fun c => not_not.mp fun h => hcon ⟨c, h⟩)
  -- entry `(t, c)` of `h M + B_θ(h) - B_θ'(h)` is analytic in `h` and not identically zero
  have hg : AnalyticOnNhd ℝ (fun h : T → d → ℝ => (Matrix.of h * M
      + attnHeads sees Γ C (Matrix.of h) - attnHeads sees Γ' C' (Matrix.of h)) t c) Set.univ := by
    simp only [Matrix.sub_apply, Matrix.add_apply]
    exact ((analyticOnNhd_mul_entry_atb M t c).add (analyticOnNhd_attnHeads_atb sees Γ C t c)).sub
      (analyticOnNhd_attnHeads_atb sees Γ' C' t c)
  have hnull := measure_zeroSet_of_analytic μ hg ⟨h₀, hc⟩
  rw [ae_iff]
  refine measure_mono_null (fun h hh => ?_) hnull
  have hh' : Matrix.of h * M + attnHeads sees Γ C (Matrix.of h)
      = attnHeads sees Γ' C' (Matrix.of h) := not_not.mp hh
  show (Matrix.of h * M + attnHeads sees Γ C (Matrix.of h)
      - attnHeads sees Γ' C' (Matrix.of h)) t c = 0
  rw [hh', sub_self]
  rfl

omit [Fintype T] [Fintype d] in
/-- A matrix with all rows `u`, times `E`, has all rows `u E`. -/
private theorem const_mul_atb {m n : Type*} [Fintype m] (u : m → ℝ) (E : Matrix m n ℝ) :
    (Matrix.of fun _ : T => u) * E = Matrix.of fun _ : T => u ᵥ* E :=
  rfl

omit [Fintype T] [Fintype d] in
/-- The matrix whose row `t₀` is `0` and whose other rows are `v`, times `F`, has row `t₀`
equal to `0`. -/
private theorem zero_row_mul_atb [DecidableEq T] {m : Type*} [Fintype m] (t₀ : T)
    (v : m → ℝ) (F : Matrix m d ℝ) :
    ((Matrix.of fun t => if t = t₀ then 0 else v : Matrix T m ℝ) * F) t₀ = 0 := by
  rw [Matrix.mul_apply_eq_vecMul]
  show (if t₀ = t₀ then (0 : m → ℝ) else v) ᵥ* F = 0
  simp only [ite_true, Matrix.zero_vecMul]

omit [Fintype d] in
/-- The same matrix times `F`: the mean of its rows is `((T - 1)/T) v F`. -/
private theorem zero_row_mul_sum_atb [DecidableEq T] {m : Type*} [Fintype m] (t₀ : T)
    (v : m → ℝ) (F : Matrix m d ℝ) :
    (Fintype.card T : ℝ)⁻¹ • ∑ s, ((Matrix.of fun t => if t = t₀ then 0 else v
        : Matrix T m ℝ) * F) s
      = ((Fintype.card T : ℝ)⁻¹ * ((Fintype.card T : ℝ) - 1)) • (v ᵥ* F) := by
  have e : ∑ s, ((Matrix.of fun t => if t = t₀ then 0 else v : Matrix T m ℝ) * F) s
      = (∑ s, (Matrix.of fun t => if t = t₀ then 0 else v : Matrix T m ℝ) s) ᵥ* F := by
    simp only [Matrix.mul_apply_eq_vecMul]
    exact (Matrix.sum_vecMul Finset.univ
      (fun s => (Matrix.of fun t => if t = t₀ then 0 else v : Matrix T m ℝ) s) F).symm
  rw [e, sum_rows_zero_row_atb, Matrix.smul_vecMul, smul_smul]

omit [Fintype T] [Fintype d] in
/-- Matrices with the same products `u A = u B` for all `u` are equal. -/
private theorem eq_of_vecMul_eq_atb {m n : Type*} [Fintype m] [DecidableEq m]
    {A B : Matrix m n ℝ} (h : ∀ u, u ᵥ* A = u ᵥ* B) : A = B := by
  ext a b
  have hb := congrFun (h (Pi.single a 1)) b
  simpa only [single_vecMul, one_smul, Matrix.row_apply] using hb

/-- **Theorem A.13 (iii):** with at least two tokens and a token that sees all tokens, an
embedding `E` and a readout `D` with `E D ≠ 0`, the residual network
`X ↦ (X E + B_θ(X E)) D` of one attention block differs from every skipless network
`X ↦ B_θ'(X E') D'` of one attention block, of any model dimension. -/
theorem exists_ne_residual_skipless_attnHeads (sees : T → T → Prop) [DecidableRel sees]
    (hT : 2 ≤ Fintype.card T) (t₀ : T) (ht₀ : ∀ s, sees t₀ s) {dIn dOut d' H H' : Type*}
    [Fintype dIn] [Fintype d'] [Fintype H] [Fintype H'] (Γ C : H → Matrix d d ℝ)
    (Γ' C' : H' → Matrix d' d' ℝ) (E : Matrix dIn d ℝ) (D : Matrix d dOut ℝ)
    (E' : Matrix dIn d' ℝ) (D' : Matrix d' dOut ℝ) (hED : E * D ≠ 0) :
    ∃ X : Matrix T dIn ℝ,
      (X * E + attnHeads sees Γ C (X * E)) * D ≠ attnHeads sees Γ' C' (X * E') * D' := by
  classical
  by_contra hcon
  have hall : ∀ X : Matrix T dIn ℝ, (X * E + attnHeads sees Γ C (X * E)) * D
      = attnHeads sees Γ' C' (X * E') * D' := fun X => not_not.mp (not_exists.mp hcon X)
  -- row `t₀` of both sides
  have hrow : ∀ X : Matrix T dIn ℝ, ((X * E) t₀ + attnHeads sees Γ C (X * E) t₀) ᵥ* D
      = attnHeads sees Γ' C' (X * E') t₀ ᵥ* D' := by
    intro X
    have h := congrFun (hall X) t₀
    rwa [Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul] at h
  -- Step 1, all rows `u`: `E D + E (∑ C_i) D = E' (∑ C'_i) D'`
  have h1 : ∀ u : dIn → ℝ, u ᵥ* (E * D) + u ᵥ* (E * (∑ i, C i) * D)
      = u ᵥ* (E' * (∑ i, C' i) * D') := by
    intro u
    have h := hrow (Matrix.of fun _ => u)
    rw [const_mul_atb, const_mul_atb, attnHeads_const_row sees Γ C _ t₀ ⟨t₀, ht₀ t₀⟩,
      attnHeads_const_row sees Γ' C' _ t₀ ⟨t₀, ht₀ t₀⟩] at h
    simp only [← Matrix.vecMul_vecMul, ← Matrix.add_vecMul]
    exact h
  -- Step 2, row `t₀` zero and the other rows `v`: `E (∑ C_i) D = E' (∑ C'_i) D'`
  have hT2 : (2 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
  have hr : (Fintype.card T : ℝ)⁻¹ * ((Fintype.card T : ℝ) - 1) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (by linarith)) (by linarith)
  have h2 : ∀ v : dIn → ℝ, v ᵥ* (E * (∑ i, C i) * D) = v ᵥ* (E' * (∑ i, C' i) * D') := by
    intro v
    have h := hrow (Matrix.of fun t => if t = t₀ then 0 else v)
    rw [attnHeads_zero_row sees Γ C _ t₀ ht₀ (zero_row_mul_atb t₀ v E),
      attnHeads_zero_row sees Γ' C' _ t₀ ht₀ (zero_row_mul_atb t₀ v E'),
      zero_row_mul_atb t₀ v E, zero_add, zero_row_mul_sum_atb, zero_row_mul_sum_atb] at h
    simp only [Matrix.smul_vecMul] at h
    have h' := congrArg (fun w => ((Fintype.card T : ℝ)⁻¹ * ((Fintype.card T : ℝ) - 1))⁻¹ • w) h
    simp only [inv_smul_smul₀ hr] at h'
    simp only [← Matrix.vecMul_vecMul]
    exact h'
  -- so `E D = 0`
  apply hED
  refine eq_of_vecMul_eq_atb fun u => ?_
  rw [Matrix.vecMul_zero]
  have h := h1 u
  rw [h2 u] at h
  exact add_right_cancel (h.trans (zero_add _).symm)

/-- **Theorem 3.4 (i), for the blocks of equation (4):** attention blocks with any numbers of
heads and any head dimensions, `M ≠ 0`: for almost every `h`, `h M + B_θ(h) ≠ B_θ'(h)`. -/
theorem ae_mul_add_attentionBlock_ne (sees : T → T → Prop) [DecidableRel sees]
    (hT : 2 ≤ Fintype.card T) (t₀ : T) (ht₀ : ∀ s, sees t₀ s) {H H' dh dh' : Type*} [Fintype H]
    [Fintype H'] [Fintype dh] [Fintype dh'] (WQ WK WV : H → Matrix d dh ℝ)
    (WO : H → Matrix dh d ℝ) (WQ' WK' WV' : H' → Matrix d dh' ℝ) (WO' : H' → Matrix dh' d ℝ)
    (M : Matrix d d ℝ) (hM : M ≠ 0) (μ : Measure (T → d → ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ h ∂μ, (Matrix.of h) * M + attentionBlock sees WQ WK WV WO (Matrix.of h)
      ≠ attentionBlock sees WQ' WK' WV' WO' (Matrix.of h) := by
  sorry

/-- **Theorem 3.4 (ii), for the blocks of equation (4).** -/
theorem exists_row_attentionBlock_sub_ge (sees : T → T → Prop) [DecidableRel sees]
    (hT : 2 ≤ Fintype.card T) (t₀ : T) (ht₀ : ∀ s, sees t₀ s) {H H' dh dh' : Type*} [Fintype H]
    [Fintype H'] [Fintype dh] [Fintype dh'] (WQ WK WV : H → Matrix d dh ℝ)
    (WO : H → Matrix dh d ℝ) (WQ' WK' WV' : H' → Matrix d dh' ℝ) (WO' : H' → Matrix dh' d ℝ)
    (M : Matrix d d ℝ) (x : d → ℝ) (hx : x ⬝ᵥ x ≤ 1) :
    ∃ h : Matrix T d ℝ, (∀ t, h t ⬝ᵥ h t ≤ 1) ∧ ∃ t,
      Real.sqrt ((x ᵥ* M) ⬝ᵥ (x ᵥ* M)) / 3
        ≤ Real.sqrt (((h * M + attentionBlock sees WQ WK WV WO h
              - attentionBlock sees WQ' WK' WV' WO' h) t)
            ⬝ᵥ ((h * M + attentionBlock sees WQ WK WV WO h
              - attentionBlock sees WQ' WK' WV' WO' h) t)) := by
  sorry

end Skips
