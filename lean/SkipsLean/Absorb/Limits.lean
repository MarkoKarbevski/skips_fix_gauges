import SkipsLean.Basic.RMSNorm
import SkipsLean.Dimension.Space

/-!
# Skipless networks are limits of residual networks

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Proposition 5.1 with its proof in
Appendix A and Remark A.16 (the rate `1/t`).

Let `F` be a skipless network whose blocks are locally Lipschitz.

(i) Without normalization, for `t ≥ 1` let `F_t` be the residual network with the embedding of `F`,
the reads `t^{1-ℓ} W_read^ℓ`, the writes `t^ℓ W_write^ℓ` and the readout `t^{-L} D` (blocks
`ℓ = 1, …, L`). On every bounded set of inputs, `‖F_t(X) - F(X)‖ ≤ C / t`.

(ii) Under pre-RMSNorm with `ε = 0`, let `F_t` keep the embedding, the reads and the readout of `F`
and have the writes `t^ℓ W_write^ℓ`. On every compact set of inputs at which `F` is defined (no row
of `X E` or of a hidden state of `F` vanishes) there are `C` and `t_0` such that, for `t ≥ t_0`,
`F_t` is defined and `‖F_t(X) - F(X)‖ ≤ C / t`.

Here the blocks are `ℓ : Fin L`, the paper's block `ℓ + 1`, so the exponents are shifted by one. A
block is `n ↦ f_ℓ(n W_read) W_write`; it is locally Lipschitz when `f_ℓ` is. Norms are the
elementwise norms of matrices; the statements do not depend on the choice of norm.
-/

namespace Skips

open Matrix Filter
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L)

/-- The weights of the residual network `F_t` of Proposition 5.1 (i): the embedding of `F`, the
reads `t^{1-ℓ} W_read^ℓ`, the writes `t^ℓ W_write^ℓ` (for the paper's block `ℓ`, here `ℓ + 1`) and
the readout `t^{-L} D`. -/
noncomputable def Params.limitScale {A : Arch T d L} (θ : Params A dIn dOut) (t : ℝ) :
    Params A dIn dOut where
  E := θ.E
  read ℓ := (t ^ (ℓ : ℕ))⁻¹ • θ.read ℓ
  write ℓ := t ^ ((ℓ : ℕ) + 1) • θ.write ℓ
  D := (t ^ L)⁻¹ • θ.D

/-- The weights of the residual network `F_t` of Proposition 5.1 (ii): the embedding, the reads and
the readout of `F`, and the writes `t^ℓ W_write^ℓ` (for the paper's block `ℓ`, here `ℓ + 1`). -/
noncomputable def Params.writeScale {A : Arch T d L} (θ : Params A dIn dOut) (t : ℝ) :
    Params A dIn dOut where
  E := θ.E
  read := θ.read
  write ℓ := t ^ ((ℓ : ℕ) + 1) • θ.write ℓ
  D := θ.D

/-- A network (with the stream matrices `S`) is **defined at** the input `X`, for `ε = 0`: no row of
`X E` or of a later hidden state vanishes. -/
def DefinedAt (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut) (X : Matrix T dIn ℝ) : Prop :=
  ∀ (k : Fin (L + 1)) (t : T), hidden A S θ X k t ≠ 0

variable (θ : Params A dIn dOut)

/-- In a real normed space, `‖x‖ ‖ y/‖y‖ - x/‖x‖ ‖ ≤ 2 ‖y - x‖` (both sides vanish for `x = 0`,
and `0/‖0‖ = 0`). -/
theorem norm_mul_norm_inv_smul_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) : ‖x‖ * ‖‖y‖⁻¹ • y - ‖x‖⁻¹ • x‖ ≤ 2 * ‖y - x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [norm_zero, zero_mul]; positivity
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  -- `y/‖y‖ - x/‖x‖ = (y - x)/‖x‖ + (1/‖y‖ - 1/‖x‖) y`
  have hsplit : ‖y‖⁻¹ • y - ‖x‖⁻¹ • x = ‖x‖⁻¹ • (y - x) + (‖y‖⁻¹ - ‖x‖⁻¹) • y := by
    rw [smul_sub, sub_smul]; abel
  -- the second term has norm `|‖x‖ - ‖y‖| / ‖x‖ ≤ ‖y - x‖ / ‖x‖`
  have h2 : ‖x‖ * ‖(‖y‖⁻¹ - ‖x‖⁻¹) • y‖ ≤ ‖y - x‖ := by
    rcases eq_or_ne y 0 with rfl | hy
    · simp only [smul_zero, norm_zero, mul_zero]; positivity
    have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
    have : ‖x‖ * ‖(‖y‖⁻¹ - ‖x‖⁻¹) • y‖ = |‖y‖ - ‖x‖| := by
      rw [norm_smul, Real.norm_eq_abs,
        show ‖y‖⁻¹ - ‖x‖⁻¹ = (‖x‖ - ‖y‖) / (‖x‖ * ‖y‖) by field_simp,
        abs_div, abs_of_pos (mul_pos hx' hy'), abs_sub_comm]
      field_simp
    rw [this]
    exact abs_norm_sub_norm_le y x
  calc ‖x‖ * ‖‖y‖⁻¹ • y - ‖x‖⁻¹ • x‖
      ≤ ‖x‖ * (‖‖x‖⁻¹ • (y - x)‖ + ‖(‖y‖⁻¹ - ‖x‖⁻¹) • y‖) := by
        rw [hsplit]; gcongr; exact norm_add_le _ _
    _ = ‖y - x‖ + ‖x‖ * ‖(‖y‖⁻¹ - ‖x‖⁻¹) • y‖ := by
        rw [mul_add, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, ← mul_assoc,
          mul_inv_cancel₀ hx'.ne', one_mul]
    _ ≤ ‖y - x‖ + ‖y - x‖ := by gcongr
    _ = 2 * ‖y - x‖ := by ring

omit [DecidableEq d] in
/-- `N_0` in terms of the Euclidean norm of the row: `N_0(v) = (√d / ‖v‖₂) v`. -/
private theorem rmsRow_zero_eq (v : d → ℝ) :
    rmsRow 0 v = (Real.sqrt (Fintype.card d) * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ d)‖⁻¹) • v := by
  unfold rmsRow
  congr 1
  have hdot : v ⬝ᵥ v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ d)‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, sq]
  rw [hdot, add_zero, Real.sqrt_div' _ (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _), inv_div,
    div_eq_mul_inv]

omit [DecidableEq d] in
/-- The sup norm of a row is at most its Euclidean norm. -/
private theorem norm_le_norm_toLp (v : d → ℝ) :
    ‖v‖ ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ d)‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    PiLp.norm_apply_le (WithLp.toLp 2 v : EuclideanSpace ℝ d) i

omit [DecidableEq d] in
/-- The Euclidean norm of a row is at most `√d` times its sup norm. -/
private theorem norm_toLp_le (v : d → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ d)‖ ≤ Real.sqrt (Fintype.card d) * ‖v‖ := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖(WithLp.toLp 2 v : EuclideanSpace ℝ d) i‖ ^ 2 ≤ ∑ _i : d, ‖v‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
    _ = (Fintype.card d : ℝ) * ‖v‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [DecidableEq d] in
/-- **`N_0` is Lipschitz away from `0`**, on one row: `‖v‖ ‖N_0(w) - N_0(v)‖ ≤ 2 d ‖w - v‖`
(sup norms; `d` the number of columns). -/
theorem norm_mul_norm_rmsRow_zero_sub_le (v w : d → ℝ) :
    ‖v‖ * ‖rmsRow 0 w - rmsRow 0 v‖ ≤ 2 * Fintype.card d * ‖w - v‖ := by
  set x : EuclideanSpace ℝ d := WithLp.toLp 2 v
  set y : EuclideanSpace ℝ d := WithLp.toLp 2 w
  have hn := Real.sqrt_nonneg (Fintype.card d)
  -- `N_0(w) - N_0(v) = √d (y/‖y‖ - x/‖x‖)` in Euclidean coordinates
  have hdiff : WithLp.toLp 2 (rmsRow 0 w - rmsRow 0 v)
      = Real.sqrt (Fintype.card d) • (‖y‖⁻¹ • y - ‖x‖⁻¹ • x) := by
    rw [rmsRow_zero_eq, rmsRow_zero_eq, smul_sub, smul_smul, smul_smul]
    rfl
  have h1 : ‖rmsRow 0 w - rmsRow 0 v‖ ≤ Real.sqrt (Fintype.card d) * ‖‖y‖⁻¹ • y - ‖x‖⁻¹ • x‖ := by
    calc ‖rmsRow 0 w - rmsRow 0 v‖ ≤ ‖WithLp.toLp 2 (rmsRow 0 w - rmsRow 0 v)‖ :=
          norm_le_norm_toLp _
      _ = _ := by rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hn]
  have hyx : ‖y - x‖ ≤ Real.sqrt (Fintype.card d) * ‖w - v‖ := norm_toLp_le (w - v)
  calc ‖v‖ * ‖rmsRow 0 w - rmsRow 0 v‖
      ≤ ‖x‖ * (Real.sqrt (Fintype.card d) * ‖‖y‖⁻¹ • y - ‖x‖⁻¹ • x‖) := by
        gcongr
        exact norm_le_norm_toLp v
    _ = Real.sqrt (Fintype.card d) * (‖x‖ * ‖‖y‖⁻¹ • y - ‖x‖⁻¹ • x‖) := by ring
    _ ≤ Real.sqrt (Fintype.card d) * (2 * (Real.sqrt (Fintype.card d) * ‖w - v‖)) := by
        refine mul_le_mul_of_nonneg_left ((norm_mul_norm_inv_smul_sub_le x y).trans ?_) hn
        exact mul_le_mul_of_nonneg_left hyx zero_le_two
    _ = 2 * (Real.sqrt (Fintype.card d) * Real.sqrt (Fintype.card d)) * ‖w - v‖ := by ring
    _ = 2 * Fintype.card d * ‖w - v‖ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]

omit [DecidableEq d] in
/-- The entries of `N_0(v)` are at most `√d` in absolute value. -/
private theorem norm_rmsRow_zero_le (v : d → ℝ) :
    ‖rmsRow 0 v‖ ≤ Real.sqrt (Fintype.card d) := by
  set x : EuclideanSpace ℝ d := WithLp.toLp 2 v
  have hn := Real.sqrt_nonneg (Fintype.card d)
  have h1 : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
    rcases eq_or_ne x 0 with hx | hx
    · rw [hx, smul_zero, norm_zero]; exact zero_le_one
    · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
  calc ‖rmsRow 0 v‖ ≤ ‖WithLp.toLp 2 (rmsRow 0 v)‖ := norm_le_norm_toLp _
    _ = ‖Real.sqrt (Fintype.card d) • (‖x‖⁻¹ • x)‖ := by rw [rmsRow_zero_eq, mul_smul]; rfl
    _ = Real.sqrt (Fintype.card d) * ‖‖x‖⁻¹ • x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn]
    _ ≤ Real.sqrt (Fintype.card d) * 1 := by gcongr
    _ = _ := mul_one _

omit [DecidableEq d] in
/-- `N_0` forgets a positive scale on a row (copy of a private lemma of `Basic/RMSNorm.lean`). -/
private theorem rmsRow_zero_smul' {c : ℝ} (hc : 0 < c) (w : d → ℝ) :
    rmsRow 0 (c • w) = rmsRow 0 w := by
  unfold rmsRow
  have hs : Real.sqrt ((c • w ⬝ᵥ c • w) / (Fintype.card d : ℝ) + 0)
      = c * Real.sqrt ((w ⬝ᵥ w) / (Fintype.card d : ℝ) + 0) := by
    have : (c • w ⬝ᵥ c • w) / (Fintype.card d : ℝ) + 0
        = c ^ 2 * ((w ⬝ᵥ w) / (Fintype.card d : ℝ) + 0) := by
      rw [smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul, add_zero]
      ring
    rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  rw [hs, mul_inv, smul_smul]
  congr 1
  rw [mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

omit [Fintype T] [DecidableEq d] in
/-- `N_0(c h) = N_0(h)` for `c > 0`. -/
theorem rmsNorm_zero_smul {c : ℝ} (hc : 0 < c) (h : Matrix T d ℝ) :
    rmsNorm 0 (c • h) = rmsNorm 0 h := by
  ext t j
  exact congrFun (rmsRow_zero_smul' hc (h t)) j

omit [DecidableEq d] in
/-- **`N_0` is Lipschitz at a state whose rows are not shorter than `ρ > 0`**:
`‖N_0(y) - N_0(z)‖ ≤ (2d/ρ) ‖y - z‖` for every `y`. -/
theorem norm_rmsNorm_zero_sub_le {ρ : ℝ} (hρ : 0 < ρ) {z : Matrix T d ℝ}
    (hz : ∀ t, ρ ≤ ‖z t‖) (y : Matrix T d ℝ) :
    ‖rmsNorm 0 y - rmsNorm 0 z‖ ≤ 2 * Fintype.card d / ρ * ‖y - z‖ := by
  rw [Matrix.norm_def, pi_norm_le_iff_of_nonneg (by positivity)]
  intro t
  have h1 := norm_mul_norm_rmsRow_zero_sub_le (z t) (y t)
  have h2 : ‖y t - z t‖ ≤ ‖y - z‖ := norm_le_pi_norm (y - z) t
  show ‖rmsRow 0 (y t) - rmsRow 0 (z t)‖ ≤ _
  rw [div_mul_eq_mul_div, le_div_iff₀ hρ, mul_comm]
  calc ρ * ‖rmsRow 0 (y t) - rmsRow 0 (z t)‖ ≤ ‖z t‖ * ‖rmsRow 0 (y t) - rmsRow 0 (z t)‖ := by
        gcongr; exact hz t
    _ ≤ 2 * Fintype.card d * ‖y t - z t‖ := h1
    _ ≤ 2 * Fintype.card d * ‖y - z‖ := by gcongr

omit [DecidableEq d] in
/-- The image of `N_0` lies in the closed ball of radius `√d`. -/
theorem norm_rmsNorm_zero_le (y : Matrix T d ℝ) :
    ‖rmsNorm 0 y‖ ≤ Real.sqrt (Fintype.card d) := by
  rw [Matrix.norm_def, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro t
  exact norm_rmsRow_zero_le (y t)

/-- Right multiplication is bounded for the elementwise norm: `‖X M‖ ≤ n ‖X‖ ‖M‖`. -/
theorem norm_mul_le_card {m n : Type*} [Fintype m] [Fintype n] (X : Matrix T n ℝ)
    (M : Matrix n m ℝ) : ‖X * M‖ ≤ Fintype.card n * ‖X‖ * ‖M‖ := by
  refine (Matrix.norm_le_iff (by positivity)).2 fun i j => ?_
  rw [Matrix.mul_apply]
  calc ‖∑ l, X i l * M l j‖ ≤ ∑ l, ‖X i l * M l j‖ := norm_sum_le _ _
    _ ≤ ∑ _l : n, ‖X‖ * ‖M‖ := Finset.sum_le_sum fun l _ => by
        rw [norm_mul]
        exact mul_le_mul (Matrix.norm_apply_le_norm X) (Matrix.norm_apply_le_norm M)
          (norm_nonneg _) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- Right multiplication by a fixed matrix is Lipschitz. -/
theorem lipschitzWith_mul_right {m n : Type*} [Fintype m] [Fintype n] (M : Matrix n m ℝ) :
    LipschitzWith (Real.toNNReal (Fintype.card n * ‖M‖)) (fun X : Matrix T n ℝ => X * M) := by
  refine LipschitzWith.of_dist_le' fun X Y => ?_
  rw [dist_eq_norm, dist_eq_norm, ← Matrix.sub_mul, mul_right_comm]
  exact norm_mul_le_card _ _

/-- `t^{-(n+1)} (h + t^{n+1} Y) = t^{-1} (t^{-n} h) + Y`: the rescaled step of `F_t`. -/
private theorem inv_pow_succ_smul_add {M : Type*} [AddCommGroup M] [Module ℝ M] {t : ℝ}
    (ht : t ≠ 0) (n : ℕ) (h Y : M) :
    (t ^ (n + 1))⁻¹ • (h + t ^ (n + 1) • Y) = t⁻¹ • ((t ^ n)⁻¹ • h) + Y := by
  rw [smul_add, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ ht), one_smul, smul_smul, ← mul_inv,
    ← pow_succ']

/-- Finitely many positive numbers have a positive lower bound. -/
private theorem exists_pos_le_of_finite {ι : Type*} [Finite ι] (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) : ∃ ρ > 0, ∀ i, ρ ≤ a i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min a
    exact ⟨a i₀, ha i₀, hi₀⟩

/-- A function continuous and positive on a compact set has a positive lower bound there. -/
private theorem exists_pos_le_of_isCompact {α : Type*} [TopologicalSpace α] {K : Set α}
    (hK : IsCompact K) {f : α → ℝ} (hf : ContinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ ρ > 0, ∀ x ∈ K, ρ ≤ f x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun x hx => by simp at hx⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hf
    exact ⟨f x₀, hpos x₀ hx₀, isMinOn_iff.1 hmin⟩

/-- A bound `C / t` for large `t` gives uniform convergence as `t → ∞`. -/
private theorem tendstoUniformlyOn_of_le_div {α β : Type*} [NormedAddCommGroup β]
    {F : ℝ → α → β} {f : α → β} {s : Set α} {C t₀ : ℝ}
    (h : ∀ x ∈ s, ∀ t, t₀ ≤ t → ‖F t x - f x‖ ≤ C / t) : TendstoUniformlyOn F f atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_ge_atTop t₀, eventually_gt_atTop (|C| / ε),
    eventually_gt_atTop 0] with t ht₀ htC ht0 x hx
  rw [dist_eq_norm, norm_sub_rev]
  rw [div_lt_iff₀ hε] at htC
  calc ‖F t x - f x‖ ≤ C / t := h x hx t ht₀
    _ ≤ |C| / t := div_le_div_of_nonneg_right (le_abs_self C) ht0.le
    _ < ε := (div_lt_iff₀ ht0).2 (by linarith)

/-- **The induction of Proposition 5.1, in abstract form.** Let `s_{k+1} = G_k(s_k)` (the hidden
states of `F`) and `u_{k+1} = t⁻¹ u_k + G_k(u_k)`, `u_0 = s_0` (the hidden states of `F_t`, divided
by `t^k`). If the `s_k` are bounded on `𝒳` and each `G_k` is Lipschitz at the points `s_k(x)` on
bounded neighbourhoods, then `‖u_k - s_k‖ ≤ C_k / t` on `𝒳` for `t ≥ 1`. -/
private theorem exists_bound_of_step {M ι : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {L : ℕ} (𝒳 : Set ι) (G : Fin L → M → M) (s : Fin (L + 1) → ι → M)
    (u : ℝ → Fin (L + 1) → ι → M)
    (hs : ∀ k x, s k.succ x = G k (s k.castSucc x)) (hu0 : ∀ t x, u t 0 x = s 0 x)
    (hu : ∀ t, 1 ≤ t → ∀ k x, u t k.succ x = t⁻¹ • u t k.castSucc x + G k (u t k.castSucc x))
    (hS : ∀ k : Fin L, ∃ S, ∀ x ∈ 𝒳, ‖s k.castSucc x‖ ≤ S)
    (hG : ∀ k C, 0 ≤ C → ∃ K, ∀ x ∈ 𝒳, ∀ y, ‖y - s k.castSucc x‖ ≤ C →
      ‖G k y - G k (s k.castSucc x)‖ ≤ K * ‖y - s k.castSucc x‖) :
    ∀ k, ∃ C, 0 ≤ C ∧ ∀ x ∈ 𝒳, ∀ t, 1 ≤ t → ‖u t k x - s k x‖ ≤ C / t := by
  intro k
  induction k using Fin.induction with
  | zero => exact ⟨0, le_rfl, fun x _ t _ => by rw [hu0, sub_self, norm_zero, zero_div]⟩
  | succ k ih =>
    -- `‖u_k - s_k‖ ≤ C/t`, `‖s_k‖ ≤ S`, and `G_k` is `K`-Lipschitz at `s_k` on the `C`-ball
    obtain ⟨C, hC, h⟩ := ih
    obtain ⟨S, hS⟩ := hS k
    obtain ⟨K, hK⟩ := hG k C hC
    refine ⟨max S 0 + C + max K 0 * C, by positivity, fun x hx t ht => ?_⟩
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht
    have hd := h x hx t ht
    have hdC : ‖u t k.castSucc x - s k.castSucc x‖ ≤ C := hd.trans (div_le_self hC ht)
    have hGd := hK x hx _ hdC
    have hy : ‖u t k.castSucc x‖ ≤ max S 0 + C := by
      calc ‖u t k.castSucc x‖ = ‖s k.castSucc x + (u t k.castSucc x - s k.castSucc x)‖ := by
            rw [add_sub_cancel]
        _ ≤ ‖s k.castSucc x‖ + ‖u t k.castSucc x - s k.castSucc x‖ := norm_add_le _ _
        _ ≤ max S 0 + C := add_le_add ((hS x hx).trans (le_max_left _ _)) hdC
    -- `u_{k+1} - s_{k+1} = t⁻¹ u_k + (G_k(u_k) - G_k(s_k))`
    rw [hu t ht, hs]
    calc ‖t⁻¹ • u t k.castSucc x + G k (u t k.castSucc x) - G k (s k.castSucc x)‖
        = ‖t⁻¹ • u t k.castSucc x + (G k (u t k.castSucc x) - G k (s k.castSucc x))‖ := by
          rw [add_sub_assoc]
      _ ≤ ‖t⁻¹ • u t k.castSucc x‖ + ‖G k (u t k.castSucc x) - G k (s k.castSucc x)‖ :=
          norm_add_le _ _
      _ ≤ (max S 0 + C) / t + max K 0 * (C / t) := by
          gcongr ?_ + ?_
          · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htpos, inv_mul_eq_div]
            exact div_le_div_of_nonneg_right hy htpos.le
          · exact hGd.trans (mul_le_mul (le_max_left _ _) hd (norm_nonneg _) (le_max_right _ _))
      _ = (max S 0 + C + max K 0 * C) / t := by ring

/-- The block `n ↦ f_ℓ(n W_read^ℓ) W_write^ℓ` of `F`, as a map of its input. -/
private def blockMap (k : Fin L) (n : Matrix T d ℝ) : Matrix T d ℝ :=
  A.f k (n * θ.read k) * θ.write k

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- A block is locally Lipschitz when its map `f_ℓ` is. -/
private theorem locallyLipschitz_blockMap (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ)) (k : Fin L) :
    LocallyLipschitz (blockMap A θ k) :=
  (lipschitzWith_mul_right (θ.write k)).locallyLipschitz.comp
    ((hf k).comp (lipschitzWith_mul_right (θ.read k)).locallyLipschitz)

/-- **Proposition 5.1 (i) with the rate of Remark A.16:** without normalization, if the maps `f_ℓ`
of the blocks are locally Lipschitz, then on every bounded set `𝒳` of inputs there is `C` with
`‖F_t(X) - F(X)‖ ≤ C / t` for all `X ∈ 𝒳` and `t ≥ 1`. -/
theorem exists_bound_eval_limitScale (hχ : A.χ = id) (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ))
    (𝒳 : Set (Matrix T dIn ℝ)) (h𝒳 : Bornology.IsBounded 𝒳) :
    ∃ C : ℝ, ∀ X ∈ 𝒳, ∀ t : ℝ, 1 ≤ t →
      ‖eval A 1 (θ.limitScale t) X - eval A 0 θ X‖ ≤ C / t := by
  -- `s k X`: the hidden states of `F`; `u t k X = t^{-k} h_k`: those of `F_t`, rescaled
  let s : Fin (L + 1) → Matrix T dIn ℝ → Matrix T d ℝ := fun k X => hidden A 0 θ X k
  let u : ℝ → Fin (L + 1) → Matrix T dIn ℝ → Matrix T d ℝ :=
    fun t k X => (t ^ (k : ℕ))⁻¹ • hidden A 1 (θ.limitScale t) X k
  -- `s_{k+1} = B_k(s_k)`: the stream of `F` is `s_k * 0`
  have hs : ∀ (k : Fin L) X, s k.succ X = blockMap A θ k (s k.castSucc X) := by
    intro k X
    simp only [s, hidden_succ, hχ, id, Pi.zero_apply, Matrix.mul_zero, zero_add, blockMap]
  have hu0 : ∀ t X, u t 0 X = s 0 X := by
    intro t X
    simp only [u, s, hidden_zero, Fin.val_zero, pow_zero, inv_one, one_smul, Params.limitScale]
  -- `t^{-(k+1)} h_{k+1} = t⁻¹ (t^{-k} h_k) + B_k(t^{-k} h_k)`: the read `t^{-k} W_read` moves
  -- the factor `t^{-k}` onto `h_k`, and the write `t^{k+1} W_write` cancels `t^{-(k+1)}`
  have hu : ∀ t : ℝ, 1 ≤ t → ∀ (k : Fin L) X,
      u t k.succ X = t⁻¹ • u t k.castSucc X + blockMap A θ k (u t k.castSucc X) := by
    intro t ht k X
    have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos ht).ne'
    simp only [u, hidden_succ, hχ, id, Fin.val_succ, Fin.val_castSucc, Pi.one_apply,
      Matrix.mul_one, blockMap, Params.limitScale, Matrix.mul_smul, Matrix.smul_mul]
    exact inv_pow_succ_smul_add ht0 _ _ _
  -- the hidden states of `F` are bounded on `𝒳`: `s_0 = X E`, and `B_k` is bounded on balls
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 h𝒳
  have hS : ∀ k, ∃ S, ∀ X ∈ 𝒳, ‖s k X‖ ≤ S := by
    intro k
    induction k using Fin.induction with
    | zero =>
      refine ⟨Fintype.card dIn * R * ‖θ.E‖, fun X hX => ?_⟩
      have h0 : s 0 X = X * θ.E := hidden_zero A 0 θ X
      rw [h0]
      exact (norm_mul_le_card X θ.E).trans (by gcongr; exact hR X hX)
    | succ k ih =>
      obtain ⟨S, hS⟩ := ih
      obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Matrix T d ℝ) S).exists_bound_of_continuousOn
        (locallyLipschitz_blockMap A θ hf k).continuous.continuousOn
      exact ⟨M, fun X hX => by rw [hs]; exact hM _ (mem_closedBall_zero_iff.2 (hS X hX))⟩
  -- `B_k` is Lipschitz on every ball, in particular near the `s_k(X)`
  have hG : ∀ (k : Fin L) C, 0 ≤ C → ∃ K, ∀ X ∈ 𝒳, ∀ y, ‖y - s k.castSucc X‖ ≤ C →
      ‖blockMap A θ k y - blockMap A θ k (s k.castSucc X)‖ ≤ K * ‖y - s k.castSucc X‖ := by
    intro k C hC
    obtain ⟨S, hS⟩ := hS k.castSucc
    obtain ⟨K, hK⟩ := (locallyLipschitz_blockMap A θ hf k).locallyLipschitzOn
      |>.exists_lipschitzOnWith_of_compact (isCompact_closedBall (0 : Matrix T d ℝ) (S + C))
    refine ⟨K, fun X hX y hy => ?_⟩
    have hs0 : ‖s k.castSucc X‖ ≤ S := hS X hX
    have h1 : s k.castSucc X ∈ Metric.closedBall (0 : Matrix T d ℝ) (S + C) :=
      mem_closedBall_zero_iff.2 (by linarith)
    have h2 : y ∈ Metric.closedBall (0 : Matrix T d ℝ) (S + C) := by
      rw [mem_closedBall_zero_iff]
      calc ‖y‖ = ‖s k.castSucc X + (y - s k.castSucc X)‖ := by rw [add_sub_cancel]
        _ ≤ ‖s k.castSucc X‖ + ‖y - s k.castSucc X‖ := norm_add_le _ _
        _ ≤ S + C := add_le_add hs0 hy
    have h3 := hK.dist_le_mul y h2 _ h1
    rwa [dist_eq_norm, dist_eq_norm] at h3
  -- the induction gives `‖u_L - s_L‖ ≤ C/t`, and `F_t(X) - F(X) = (u_L - s_L) D`
  obtain ⟨C, -, h⟩ := exists_bound_of_step 𝒳 (blockMap A θ) s u hs hu0 hu
    (fun k => hS k.castSucc) hG (Fin.last L)
  refine ⟨Fintype.card d * C * ‖θ.D‖, fun X hX t ht => ?_⟩
  have he : eval A 1 (θ.limitScale t) X - eval A 0 θ X
      = (u t (Fin.last L) X - s (Fin.last L) X) * θ.D := by
    simp only [eval, hχ, id, u, s, Fin.val_last, Params.limitScale, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.sub_mul]
  rw [he]
  calc ‖(u t (Fin.last L) X - s (Fin.last L) X) * θ.D‖
      ≤ Fintype.card d * ‖u t (Fin.last L) X - s (Fin.last L) X‖ * ‖θ.D‖ := norm_mul_le_card _ _
    _ ≤ Fintype.card d * (C / t) * ‖θ.D‖ := by gcongr; exact h X hX t ht
    _ = Fintype.card d * C * ‖θ.D‖ / t := by ring

/-- **Proposition 5.1 (i):** without normalization, a skipless network whose blocks are locally
Lipschitz is the limit, uniformly on bounded sets of inputs, of the residual networks `F_t`, which
have blocks of the same kinds and widths. -/
theorem tendstoUniformlyOn_eval_limitScale (hχ : A.χ = id)
    (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ)) (𝒳 : Set (Matrix T dIn ℝ))
    (h𝒳 : Bornology.IsBounded 𝒳) :
    TendstoUniformlyOn (fun (t : ℝ) (X : Matrix T dIn ℝ) => eval A 1 (θ.limitScale t) X)
      (fun X => eval A 0 θ X) atTop 𝒳 := by
  sorry

/-- **Proposition 5.1 (ii) with the rate of Remark A.16:** under pre-RMSNorm with `ε = 0`, if the
maps `f_ℓ` of the blocks are locally Lipschitz, then on every compact set `𝒳` of inputs at which
`F` is defined there are `C` and `t_0` such that, for all `X ∈ 𝒳` and `t ≥ t_0`, the residual
network `F_t` is defined at `X` and `‖F_t(X) - F(X)‖ ≤ C / t`. -/
theorem exists_bound_eval_writeScale (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ)) (𝒳 : Set (Matrix T dIn ℝ)) (h𝒳 : IsCompact 𝒳)
    (hdef : ∀ X ∈ 𝒳, DefinedAt A 0 θ X) :
    ∃ C t₀ : ℝ, ∀ X ∈ 𝒳, ∀ t : ℝ, t₀ ≤ t →
      DefinedAt A 1 (θ.writeScale t) X ∧
        ‖eval A 1 (θ.writeScale t) X - eval A 0 θ X‖ ≤ C / t := by
  sorry

/-- **Proposition 5.1 (ii):** under pre-RMSNorm with `ε = 0`, a skipless network whose blocks are
locally Lipschitz is the limit of the residual networks `F_t`, uniformly on compact sets of inputs
at which it is defined. -/
theorem tendstoUniformlyOn_eval_writeScale (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ)) (𝒳 : Set (Matrix T dIn ℝ)) (h𝒳 : IsCompact 𝒳)
    (hdef : ∀ X ∈ 𝒳, DefinedAt A 0 θ X) :
    TendstoUniformlyOn (fun (t : ℝ) (X : Matrix T dIn ℝ) => eval A 1 (θ.writeScale t) X)
      (fun X => eval A 0 θ X) atTop 𝒳 := by
  sorry

end Skips
