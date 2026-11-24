import SkipsLean.Absorb.Limits

/-!
# Under RMSNorm a residual network equals no skipless network: the comparison along rays

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Theorem 4.3. "Consider pre-RMSNorm
networks, with `ε ≥ 0` and blocks of any kind and width. For almost every choice of weights, a
residual network equals no skipless network, whatever its depth, widths and kinds of blocks."
Proof in Appendix A.3.

This file has the part of the proof that holds at fixed weights ("The skipless network", "The
residual network", "Comparison"); the part "Measure zero" is in `Absorb/RMSNormGeneric.lean`.

The proof compares the two networks along rays `t X`, `t → ∞`. Write `N_0` for RMSNorm with
`ε = 0`, `n̄ = N_0(X E)` and `β(n̄) = ∑_ℓ f_ℓ(n̄ W_read^ℓ) W_write^ℓ`, the sum of the outputs of all
blocks at the normalized state `n̄`. The output of the residual network at `t X` is
`n̄ D + ρ(X) / t + O(1/t²)` with `ρ(X) = DN_0(X E)[β(n̄)] D`, and that of a skipless network is
`G(X) + O(1/t²)`. So equality forces `ρ = 0`, that is, since `D` has rank `d`: for every `n̄` whose
rows have norm `√d`, each row of `β(n̄)` is a multiple of the same row of `n̄`. The condition on the
weights of the residual network under which the two networks differ is the negation
(`TurnGeneric`): `E` and `D` have rank `d`, and at some `n̄` some row of `β(n̄)` is not a multiple of
the same row of `n̄`.

Blocks are of any kind: the fixed maps `f_ℓ` of the residual network are locally Lipschitz, as in
the proof. The skipless network has its own depth `L'`, model dimension `d'`, widths and maps
`f'_ℓ`. For `ε > 0` both networks are defined at every input, and they are equal if they have the
same output at every input; the skipless network may have another constant `ε' > 0`. For `ε = 0`
the paper defines a network at the inputs at which no hidden state has a zero row (`DefinedAt`),
and "two such networks are equal if they agree on a dense set of inputs at which both are
defined" (Section 2, "Normalization"); the statement for `ε = 0` is the negation of this.
-/

namespace Skips

open Matrix Filter
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The conditions of the proof of Theorem 4.3** on the weights of the residual network: `E` and
`D` have rank `d`, and there is a normalized state `n̄` (every row of norm `√d`) at which some row of
`β(n̄) = ∑_ℓ f_ℓ(n̄ W_read^ℓ) W_write^ℓ` is not a multiple of the same row of `n̄`. -/
structure TurnGeneric (A : Arch T d L) (θ : Params A dIn dOut) : Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  /-- at some normalized state, the outputs of the blocks turn some token -/
  turn : ∃ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = (Fintype.card d : ℝ)) ∧
    ∃ t, ∀ c : ℝ, (∑ ℓ, A.f ℓ (n * θ.read ℓ) * θ.write ℓ) t ≠ c • n t

/-! ### Rows along a ray -/

/-- If `t (x_t - c) → v` as `t → ∞`, then `x_t → c`. -/
private theorem tendsto_of_tendsto_smul_sub' {M : Type*} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {x : ℝ → M} {c v : M}
    (h : Tendsto (fun t : ℝ => t • (x t - c)) atTop (𝓝 v)) : Tendsto x atTop (𝓝 c) := by
  have h1 : Tendsto (fun t : ℝ => c + t⁻¹ • (t • (x t - c))) atTop (𝓝 (c + (0 : ℝ) • v)) :=
    tendsto_const_nhds.add (tendsto_inv_atTop_zero.smul h)
  rw [zero_smul, add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_sub_cancel]

/-- The scalar identity behind the row limit: with `Q = a + y/t` (`t > 0`, `a > 0`, `Q > 0`),
`t (1/√Q - 1/√a) = -y / (√Q √a (√a + √Q))`. -/
private theorem mul_inv_sqrt_sub_inv_sqrt {a t y : ℝ} (ha : 0 < a) (ht : 0 < t)
    (hQ : 0 < a + t⁻¹ * y) :
    t * ((Real.sqrt (a + t⁻¹ * y))⁻¹ - (Real.sqrt a)⁻¹)
      = -y / (Real.sqrt (a + t⁻¹ * y) * Real.sqrt a *
          (Real.sqrt a + Real.sqrt (a + t⁻¹ * y))) := by
  have hs := Real.sqrt_pos.2 hQ
  have hr := Real.sqrt_pos.2 ha
  have hs2 := Real.sq_sqrt hQ.le
  have hr2 := Real.sq_sqrt ha.le
  -- `t √Q² = t a + y`
  have hts : t * Real.sqrt (a + t⁻¹ * y) ^ 2 = t * a + y := by
    rw [hs2, mul_add, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  generalize Real.sqrt (a + t⁻¹ * y) = s at hs hs2 hts ⊢
  generalize Real.sqrt a = r at hr hr2 ⊢
  rw [eq_div_iff (by positivity)]
  field_simp
  linear_combination t * hr2 - hts

omit [DecidableEq d] in
/-- **One row along a ray, at a fixed `t > 0`.** With `a = w·w/d`, `y = 2 (w·v)/d + ((v·v)/d + ε)/t`
and `Q = a + y/t > 0`: `t (N_ε(t w + v) - N_0(w)) = v/√Q - (y / (√Q √a (√a + √Q))) w`. -/
private theorem smul_rmsRow_ray_eq (ε : ℝ) {w v : d → ℝ} {t a y : ℝ} (ht : 0 < t)
    (hd : (0 : ℝ) < Fintype.card d) (ha : 0 < a) (ha_def : w ⬝ᵥ w / Fintype.card d = a)
    (hy_def : 2 * ((w ⬝ᵥ v) / Fintype.card d) + t⁻¹ * ((v ⬝ᵥ v) / Fintype.card d + ε) = y)
    (hQ : 0 < a + t⁻¹ * y) :
    t • (rmsRow ε (t • w + v) - rmsRow 0 w)
      = (Real.sqrt (a + t⁻¹ * y))⁻¹ • v +
        (-y / (Real.sqrt (a + t⁻¹ * y) * Real.sqrt a *
          (Real.sqrt a + Real.sqrt (a + t⁻¹ * y)))) • w := by
  -- the quantity under the root is `t² Q`
  have hq : (t • w + v) ⬝ᵥ (t • w + v) / Fintype.card d + ε = t ^ 2 * (a + t⁻¹ * y) := by
    rw [← ha_def, ← hy_def]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm v w]
    field_simp
    ring
  have hsq : Real.sqrt (t ^ 2 * (a + t⁻¹ * y)) = t * Real.sqrt (a + t⁻¹ * y) := by
    rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
  have h0 : rmsRow 0 w = (Real.sqrt a)⁻¹ • w := by
    unfold rmsRow
    rw [add_zero, ha_def]
  have h1 : rmsRow ε (t • w + v) = (t * Real.sqrt (a + t⁻¹ * y))⁻¹ • (t • w + v) := by
    unfold rmsRow
    rw [hq, hsq]
  -- `t ((t √Q)⁻¹ (t w + v) - w/√a) = v/√Q + t (1/√Q - 1/√a) w`
  rw [h0, h1, ← mul_inv_sqrt_sub_inv_sqrt ha ht hQ]
  generalize Real.sqrt (a + t⁻¹ * y) = s
  generalize Real.sqrt a = r
  have e1 : t * (t * s)⁻¹ = s⁻¹ := by
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  rw [smul_sub, smul_smul, e1, smul_add, smul_smul, smul_smul, mul_sub, sub_smul, mul_comm s⁻¹ t]
  abel

/-- The limit of `t (N_ε(t w + b_t) - N_0(w))` as `t → ∞` when `b_t → b₀` (`d` the number of
columns, `a = w·w/d`): `b₀/√a - (2 (w·b₀)/d) / (√a √a (√a + √a)) w`. -/
private noncomputable def rayLim (w b₀ : d → ℝ) : d → ℝ :=
  (Real.sqrt (w ⬝ᵥ w / Fintype.card d))⁻¹ • b₀ +
    (-(2 * ((w ⬝ᵥ b₀) / Fintype.card d)) /
      (Real.sqrt (w ⬝ᵥ w / Fintype.card d) * Real.sqrt (w ⬝ᵥ w / Fintype.card d) *
        (Real.sqrt (w ⬝ᵥ w / Fintype.card d) + Real.sqrt (w ⬝ᵥ w / Fintype.card d)))) • w

omit [DecidableEq d] in
/-- A nonzero row: `d` is not empty and `w·w > 0`. -/
private theorem card_pos_and_dotProduct_self_pos {w : d → ℝ} (hw : w ≠ 0) :
    (0 : ℝ) < Fintype.card d ∧ 0 < w ⬝ᵥ w := by
  obtain ⟨j, -⟩ := Function.ne_iff.1 hw
  exact ⟨Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩),
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (w j))
      (Ne.symm (dotProduct_self_eq_zero.not.2 hw))⟩

omit [DecidableEq d] in
/-- **(b) One row along a ray**: if `b_t → b₀` and `w ≠ 0`, then
`t (N_ε(t w + b_t) - N_0(w)) → rayLim w b₀` as `t → ∞`. -/
private theorem tendsto_smul_rmsRow_ray (ε : ℝ) {w : d → ℝ} (hw : w ≠ 0) {b : ℝ → d → ℝ}
    {b₀ : d → ℝ} (hb : Tendsto b atTop (𝓝 b₀)) :
    Tendsto (fun t : ℝ => t • (rmsRow ε (t • w + b t) - rmsRow 0 w)) atTop
      (𝓝 (rayLim w b₀)) := by
  obtain ⟨hd, hww⟩ := card_pos_and_dotProduct_self_pos hw
  obtain ⟨a, ha_def⟩ : ∃ a, w ⬝ᵥ w / (Fintype.card d : ℝ) = a := ⟨_, rfl⟩
  have ha : 0 < a := ha_def ▸ div_pos hww hd
  have hr := Real.sqrt_pos.2 ha
  obtain ⟨y, hy_def⟩ : ∃ y : ℝ → ℝ, (fun t : ℝ => 2 * ((w ⬝ᵥ b t) / Fintype.card d) +
      t⁻¹ * ((b t ⬝ᵥ b t) / Fintype.card d + ε)) = y := ⟨_, rfl⟩
  -- `y_t → 2 (w·b₀)/d`, `Q_t = a + y_t/t → a`
  have hy : Tendsto y atTop (𝓝 (2 * ((w ⬝ᵥ b₀) / Fintype.card d))) := by
    rw [← hy_def]
    have h1 : Tendsto (fun t => w ⬝ᵥ b t) atTop (𝓝 (w ⬝ᵥ b₀)) :=
      ((continuous_const.dotProduct continuous_id').tendsto b₀).comp hb
    have h2 : Tendsto (fun t => b t ⬝ᵥ b t) atTop (𝓝 (b₀ ⬝ᵥ b₀)) :=
      ((continuous_id'.dotProduct continuous_id').tendsto b₀).comp hb
    have := ((h1.div_const (Fintype.card d : ℝ)).const_mul 2).add
      (tendsto_inv_atTop_zero.mul ((h2.div_const (Fintype.card d : ℝ)).add_const ε))
    rwa [zero_mul, add_zero] at this
  have hQ : Tendsto (fun t => a + t⁻¹ * y t) atTop (𝓝 a) := by
    have := (tendsto_const_nhds (x := a)).add (tendsto_inv_atTop_zero.mul hy)
    rwa [zero_mul, add_zero] at this
  have hs : Tendsto (fun t => Real.sqrt (a + t⁻¹ * y t)) atTop (𝓝 (Real.sqrt a)) :=
    (Real.continuous_sqrt.tendsto a).comp hQ
  have hcoef : Tendsto (fun t => -y t / (Real.sqrt (a + t⁻¹ * y t) * Real.sqrt a *
      (Real.sqrt a + Real.sqrt (a + t⁻¹ * y t)))) atTop
      (𝓝 (-(2 * ((w ⬝ᵥ b₀) / Fintype.card d)) /
        (Real.sqrt a * Real.sqrt a * (Real.sqrt a + Real.sqrt a)))) :=
    hy.neg.div ((hs.mul_const _).mul (tendsto_const_nhds.add hs))
      (mul_pos (mul_pos hr hr) (add_pos hr hr)).ne'
  have hlim := ((hs.inv₀ hr.ne').smul hb).add (hcoef.smul_const w)
  have hrl : rayLim w b₀ = (Real.sqrt a)⁻¹ • b₀ + (-(2 * ((w ⬝ᵥ b₀) / Fintype.card d)) /
      (Real.sqrt a * Real.sqrt a * (Real.sqrt a + Real.sqrt a))) • w := by
    rw [rayLim, ha_def]
  rw [hrl]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hQ.eventually (lt_mem_nhds ha)] with t ht hQt
  exact (smul_rmsRow_ray_eq ε ht hd ha ha_def (congrFun hy_def t) hQt).symm

omit [DecidableEq d] in
/-- `rayLim w 0 = 0`. -/
private theorem rayLim_zero (w : d → ℝ) : rayLim w 0 = 0 := by
  simp only [rayLim, smul_zero, dotProduct_zero, zero_div, mul_zero, neg_zero, zero_smul,
    add_zero]

omit [DecidableEq d] in
/-- If `rayLim w b₀ = 0` and `w ≠ 0`, then `b₀` is a multiple of `w`. -/
private theorem exists_eq_smul_of_rayLim_eq_zero {w b₀ : d → ℝ} (hw : w ≠ 0)
    (h : rayLim w b₀ = 0) : ∃ c : ℝ, b₀ = c • w := by
  obtain ⟨hd, hww⟩ := card_pos_and_dotProduct_self_pos hw
  have hr : Real.sqrt (w ⬝ᵥ w / Fintype.card d) ≠ 0 := (Real.sqrt_pos.2 (div_pos hww hd)).ne'
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ,
      rayLim w b₀ = (Real.sqrt (w ⬝ᵥ w / Fintype.card d))⁻¹ • b₀ + κ • w := ⟨_, rfl⟩
  rw [hκ, add_eq_zero_iff_eq_neg] at h
  refine ⟨-(Real.sqrt (w ⬝ᵥ w / Fintype.card d) * κ), ?_⟩
  calc b₀ = Real.sqrt (w ⬝ᵥ w / Fintype.card d) • ((Real.sqrt (w ⬝ᵥ w / Fintype.card d))⁻¹ • b₀) := by
        rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
    _ = Real.sqrt (w ⬝ᵥ w / Fintype.card d) • -(κ • w) := by rw [h]
    _ = (-(Real.sqrt (w ⬝ᵥ w / Fintype.card d) * κ)) • w := by rw [smul_neg, smul_smul, neg_smul]

omit [Fintype T] [DecidableEq d] in
/-- **(b) on matrices**: if no row of `W` vanishes and `b_t → b₀`, then
`t (N_ε(t W + b_t) - N_0(W)) → (rayLim (W r) (b₀ r))_r`. -/
private theorem tendsto_smul_rmsNorm_ray (ε : ℝ) {W : Matrix T d ℝ} (hW : ∀ r, W r ≠ 0)
    {b : ℝ → Matrix T d ℝ} {b₀ : Matrix T d ℝ} (hb : Tendsto b atTop (𝓝 b₀)) :
    Tendsto (fun t : ℝ => t • (rmsNorm ε (t • W + b t) - rmsNorm 0 W)) atTop
      (𝓝 (Matrix.of fun r => rayLim (W r) (b₀ r))) := by
  refine tendsto_pi_nhds.2 fun r => ?_
  exact tendsto_smul_rmsRow_ray ε (hW r) (tendsto_pi_nhds.1 hb r)

omit [DecidableEq d] in
/-- **(a) on matrices**: if no row of `W` vanishes and `b_t → b₀`, then `N_ε(t W + b_t) → N_0(W)`. -/
private theorem tendsto_rmsNorm_ray (ε : ℝ) {W : Matrix T d ℝ} (hW : ∀ r, W r ≠ 0)
    {b : ℝ → Matrix T d ℝ} {b₀ : Matrix T d ℝ} (hb : Tendsto b atTop (𝓝 b₀)) :
    Tendsto (fun t : ℝ => rmsNorm ε (t • W + b t)) atTop (𝓝 (rmsNorm 0 W)) :=
  tendsto_of_tendsto_smul_sub' (tendsto_smul_rmsNorm_ray ε hW hb)

/-! ### Matrices: right multiplication, inverses -/

/-- Limits are kept by right multiplication with a fixed matrix. -/
private theorem tendsto_mul_right_matrix {α : Type*} {l : Filter α} {m n : Type*} [Fintype m]
    [Fintype n] {f : α → Matrix T n ℝ} {a : Matrix T n ℝ} (h : Tendsto f l (𝓝 a))
    (M : Matrix n m ℝ) : Tendsto (fun x => f x * M) l (𝓝 (a * M)) :=
  ((lipschitzWith_mul_right M).continuous.tendsto a).comp h

/-- A matrix of rank its number of columns has a left inverse (copy of a private lemma of
`Depth/SuffixRMS.lean`). -/
private theorem exists_left_inverse_of_rank' {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (M : Matrix m n ℝ) (hM : M.rank = Fintype.card n) :
    ∃ B : Matrix n m ℝ, B * M = 1 :=
  Matrix.vecMul_surjective_iff_exists_left_inverse.1
    (Matrix.vecMul_surjective_iff_rank_eq_card.2 hM)

/-- If `D` has rank `d` (its number of rows), then `P D = 0` implies `P = 0`. -/
private theorem eq_zero_of_mul_eq_zero_of_rank {m : Type*} {P : Matrix m d ℝ}
    {D : Matrix d dOut ℝ} (hD : D.rank = Fintype.card d) (h : P * D = 0) : P = 0 := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1
    (Matrix.mulVec_surjective_iff_rank_eq_card.2 hD)
  rw [← Matrix.mul_one P, ← hR, ← Matrix.mul_assoc, h, Matrix.zero_mul]

omit [Fintype T] [DecidableEq d] in
/-- `N_0(n) = n` when every row of `n` has `n_r · n_r = d > 0`. -/
private theorem rmsNorm_zero_eq_self {n : Matrix T d ℝ} (hd : (0 : ℝ) < Fintype.card d)
    (hn : ∀ r, n r ⬝ᵥ n r = Fintype.card d) : rmsNorm 0 n = n := by
  ext r j
  show rmsRow 0 (n r) j = n r j
  unfold rmsRow
  rw [hn r, div_self hd.ne', add_zero, Real.sqrt_one, inv_one, one_smul]

/-! ### The residual network along a ray -/

/-- `β_k(n) = ∑_{ℓ < k} f_ℓ(n W_read^ℓ) W_write^ℓ`: the sum of the outputs of the first `k` blocks
at the state `n`. -/
private noncomputable def betaPart (A : Arch T d L) (θ : Params A dIn dOut) (n : Matrix T d ℝ)
    (k : Fin (L + 1)) : Matrix T d ℝ :=
  ∑ ℓ : Fin L, if (ℓ : ℕ) < (k : ℕ) then A.f ℓ (n * θ.read ℓ) * θ.write ℓ else 0

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem betaPart_zero (A : Arch T d L) (θ : Params A dIn dOut) (n : Matrix T d ℝ) :
    betaPart A θ n 0 = 0 := by
  simp [betaPart]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem betaPart_succ (A : Arch T d L) (θ : Params A dIn dOut) (n : Matrix T d ℝ)
    (k : Fin L) :
    betaPart A θ n k.succ = betaPart A θ n k.castSucc + A.f k (n * θ.read k) * θ.write k := by
  unfold betaPart
  have hterm : ∀ ℓ : Fin L,
      (if (ℓ : ℕ) < (k.succ : ℕ) then A.f ℓ (n * θ.read ℓ) * θ.write ℓ else 0)
        = (if (ℓ : ℕ) < (k.castSucc : ℕ) then A.f ℓ (n * θ.read ℓ) * θ.write ℓ else 0)
          + (if k = ℓ then A.f ℓ (n * θ.read ℓ) * θ.write ℓ else 0) := by
    intro ℓ
    simp only [Fin.val_succ, Fin.val_castSucc]
    rcases lt_trichotomy (ℓ : ℕ) k with h | h | h
    · have h' : k ≠ ℓ := Fin.ne_of_val_ne h.ne'
      simp [h, h', Nat.lt_succ_of_lt h]
    · have h' : k = ℓ := (Fin.ext h).symm
      subst h'
      simp
    · have h' : k ≠ ℓ := Fin.ne_of_val_ne h.ne
      have h2 : ¬ (ℓ : ℕ) < k + 1 := by omega
      have h3 : ¬ (ℓ : ℕ) < k := by omega
      simp [h2, h3, h']
  rw [Finset.sum_congr rfl fun ℓ _ => hterm ℓ, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
private theorem betaPart_last (A : Arch T d L) (θ : Params A dIn dOut) (n : Matrix T d ℝ) :
    betaPart A θ n (Fin.last L) = ∑ ℓ, A.f ℓ (n * θ.read ℓ) * θ.write ℓ := by
  unfold betaPart
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp [ℓ.isLt]

omit [Fintype dOut] in
/-- **(a) The residual hidden states along a ray**: if no row of `W = X E` vanishes, then
`h_k(t X) - t W → β_k(N_0(W))` as `t → ∞` (for any `ε`). -/
private theorem tendsto_hidden_residual_ray (A : Arch T d L) {ε : ℝ} (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Continuous (A.f ℓ)) (θ : Params A dIn dOut) {X : Matrix T dIn ℝ}
    (hX : ∀ r, (X * θ.E) r ≠ 0) (k : Fin (L + 1)) :
    Tendsto (fun t : ℝ => hidden A 1 θ (t • X) k - t • (X * θ.E)) atTop
      (𝓝 (betaPart A θ (rmsNorm 0 (X * θ.E)) k)) := by
  induction k using Fin.induction with
  | zero =>
    rw [betaPart_zero]
    refine tendsto_const_nhds.congr fun t => ?_
    rw [hidden_zero, Matrix.smul_mul, sub_self]
  | succ k ih =>
    -- `χ(h_k(t X)) → N_0(W)`, so the output of block `k` tends to `f_k(N_0(W) W_read) W_write`
    have hN : Tendsto (fun t : ℝ => A.χ (hidden A 1 θ (t • X) k.castSucc)) atTop
        (𝓝 (rmsNorm 0 (X * θ.E))) := by
      rw [hχ]
      refine (tendsto_rmsNorm_ray ε hX ih).congr fun t => ?_
      rw [add_sub_cancel]
    have hB : Tendsto (fun t : ℝ =>
        A.f k (A.χ (hidden A 1 θ (t • X) k.castSucc) * θ.read k) * θ.write k) atTop
        (𝓝 (A.f k (rmsNorm 0 (X * θ.E) * θ.read k) * θ.write k)) :=
      tendsto_mul_right_matrix (((hf k).tendsto _).comp (tendsto_mul_right_matrix hN _)) _
    rw [betaPart_succ]
    refine (ih.add hB).congr fun t => ?_
    rw [hidden_succ, Pi.one_apply, Matrix.mul_one]
    abel

/-- **(c) The residual output along a ray**: if no row of `W = X E` vanishes, then
`t (F(t X) - N_0(W) D) → P D`, where row `r` of `P` is `rayLim W_r β_r` and
`β = ∑_ℓ f_ℓ(N_0(W) W_read^ℓ) W_write^ℓ`. -/
private theorem tendsto_smul_eval_residual_ray (A : Arch T d L) {ε : ℝ} (hχ : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Continuous (A.f ℓ)) (θ : Params A dIn dOut) {X : Matrix T dIn ℝ}
    (hX : ∀ r, (X * θ.E) r ≠ 0) :
    Tendsto (fun t : ℝ => t • (eval A 1 θ (t • X) - rmsNorm 0 (X * θ.E) * θ.D)) atTop
      (𝓝 ((Matrix.of fun r => rayLim ((X * θ.E) r)
        ((∑ ℓ, A.f ℓ (rmsNorm 0 (X * θ.E) * θ.read ℓ) * θ.write ℓ) r)) * θ.D)) := by
  have h := tendsto_hidden_residual_ray A hχ hf θ hX (Fin.last L)
  rw [betaPart_last] at h
  refine (tendsto_mul_right_matrix (tendsto_smul_rmsNorm_ray ε hX h) θ.D).congr fun t => ?_
  simp only [eval, hχ, add_sub_cancel, Matrix.smul_mul, Matrix.sub_mul]

/-! ### The skipless network along a ray, for `ε > 0` -/

/-- If `t (x_t - c) → 0` and `g` is locally Lipschitz, then `t (g(x_t) - g(c)) → 0`. -/
private theorem tendsto_smul_sub_comp_of_locallyLipschitz {M N : Type*} [NormedAddCommGroup M]
    [NormedSpace ℝ M] [NormedAddCommGroup N] [NormedSpace ℝ N] {g : M → N}
    (hg : LocallyLipschitz g) {x : ℝ → M} {c : M}
    (hx : Tendsto (fun t : ℝ => t • (x t - c)) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => t • (g (x t) - g c)) atTop (𝓝 0) := by
  obtain ⟨K, U, hU, hK⟩ := hg c
  have hxc : Tendsto x atTop (𝓝 c) := tendsto_of_tendsto_smul_sub' hx
  have hb : Tendsto (fun t : ℝ => (K : ℝ) * ‖t • (x t - c)‖) atTop (𝓝 0) := by
    have := hx.norm.const_mul (K : ℝ)
    rwa [norm_zero, mul_zero] at this
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [hxc hU] with t ht
  rw [norm_smul, norm_smul]
  calc ‖t‖ * ‖g (x t) - g c‖ ≤ ‖t‖ * (K * ‖x t - c‖) :=
        mul_le_mul_of_nonneg_left (hK.norm_sub_le ht (mem_of_mem_nhds hU)) (norm_nonneg _)
    _ = K * (‖t‖ * ‖x t - c‖) := by ring

/-- `√` is analytic at a positive number (copy of a private lemma of `Depth/SuffixRMS.lean`). -/
private theorem analyticAt_sqrt_of_pos' {x : ℝ} (hx : 0 < x) : AnalyticAt ℝ Real.sqrt x := by
  have h : AnalyticAt ℝ (Real.exp ∘ fun y => Real.log y * (1 / 2)) x :=
    ((analyticAt_log hx).mul analyticAt_const).rexp
  refine h.congr ?_
  filter_upwards [lt_mem_nhds hx] with y hy
  show Real.exp (Real.log y * (1 / 2)) = Real.sqrt y
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]

/-- An entry of a matrix is an analytic (linear) function of the matrix (copy of a private lemma
of `Depth/SuffixRMS.lean`). -/
private theorem analyticOnNhd_entry' {m n : Type*} [Fintype m] [Fintype n] (t : m) (i : n) :
    AnalyticOnNhd ℝ (fun M : Matrix m n ℝ => M t i) Set.univ :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : n => ℝ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : m => n → ℝ) t)).analyticOnNhd _

omit [DecidableEq d] in
/-- `N_ε` with `ε > 0` is analytic (copy of `analyticOnNhd_rmsNorm` of `Depth/SuffixRMS.lean`,
which this file does not import). -/
private theorem analyticOnNhd_rmsNorm' {ε : ℝ} (hε : 0 < ε) :
    AnalyticOnNhd ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) Set.univ := by
  show AnalyticOnNhd ℝ (fun h : Matrix T d ℝ => fun t => fun i =>
    (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε))⁻¹ * h t i) Set.univ
  refine AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun i => fun h _ => ?_
  have hq : AnalyticAt ℝ (fun h : Matrix T d ℝ => (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε) h :=
    (((Finset.analyticOnNhd_fun_sum _ fun j _ =>
      (analyticOnNhd_entry' t j).mul (analyticOnNhd_entry' t j)) h
        (Set.mem_univ _)).div_const).add analyticAt_const
  have hpos : 0 < (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε := by
    have : 0 ≤ (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) :=
      div_nonneg (Finset.sum_nonneg fun j _ => mul_self_nonneg (h t j)) (Nat.cast_nonneg _)
    linarith
  exact (((analyticAt_sqrt_of_pos' hpos).comp
    (f := fun h : Matrix T d ℝ => (h t ⬝ᵥ h t) / (Fintype.card d : ℝ) + ε) hq).inv
      (Real.sqrt_pos.2 hpos).ne').mul (analyticOnNhd_entry' t i h (Set.mem_univ _))

omit [DecidableEq d] in
/-- `N_ε` with `ε > 0` is locally Lipschitz (it is analytic, hence strictly differentiable). -/
private theorem locallyLipschitz_rmsNorm {ε : ℝ} (hε : 0 < ε) :
    LocallyLipschitz (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) := fun h =>
  (analyticOnNhd_rmsNorm' hε h (Set.mem_univ h)).hasStrictFDerivAt.exists_lipschitzOnWith

omit [Fintype T] [DecidableEq d] in
/-- `t (N_ε(t Y) - N_0(Y)) → 0`: a zero row stays zero, and for a nonzero row this is (b) with
`b = 0`. -/
private theorem tendsto_smul_rmsNorm_smul_sub (ε : ℝ) (Y : Matrix T d ℝ) :
    Tendsto (fun t : ℝ => t • (rmsNorm ε (t • Y) - rmsNorm 0 Y)) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun r => ?_
  by_cases hY : Y r = 0
  · refine tendsto_const_nhds.congr fun t => ?_
    show (0 : d → ℝ) = t • (rmsRow ε (t • Y r) - rmsRow 0 (Y r))
    rw [hY, smul_zero]
    unfold rmsRow
    simp
  · have h := tendsto_smul_rmsRow_ray ε hY (tendsto_const_nhds (x := (0 : d → ℝ)))
    rw [rayLim_zero] at h
    refine h.congr fun t => ?_
    rw [add_zero]
    rfl

omit [DecidableEq d] [Fintype dOut] in
/-- **(d) The skipless hidden states along a ray**, for `ε > 0`: for every `k` there is `c` with
`t (χ(h_k(t X)) - c) → 0`. -/
private theorem exists_tendsto_smul_chi_skipless_ray (A : Arch T d L) {ε : ℝ} (hε : 0 < ε)
    (hχ : A.χ = rmsNorm ε) (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ)) (θ : Params A dIn dOut)
    (X : Matrix T dIn ℝ) (k : Fin (L + 1)) :
    ∃ c, Tendsto (fun t : ℝ => t • (A.χ (hidden A 0 θ (t • X) k) - c)) atTop (𝓝 0) := by
  induction k using Fin.induction with
  | zero =>
    refine ⟨rmsNorm 0 (X * θ.E), (tendsto_smul_rmsNorm_smul_sub ε (X * θ.E)).congr fun t => ?_⟩
    rw [hidden_zero, hχ, Matrix.smul_mul]
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    -- `χ(h_{k+1}) = G_k(χ(h_k))` with `G_k(u) = χ(f_k(u W_read) W_write)`, locally Lipschitz
    have hG : LocallyLipschitz
        (fun u : Matrix T d ℝ => A.χ (A.f k (u * θ.read k) * θ.write k)) := by
      rw [hχ]
      exact (locallyLipschitz_rmsNorm hε).comp
        ((lipschitzWith_mul_right (θ.write k)).locallyLipschitz.comp
          ((hf k).comp (lipschitzWith_mul_right (θ.read k)).locallyLipschitz))
    refine ⟨A.χ (A.f k (c * θ.read k) * θ.write k),
      (tendsto_smul_sub_comp_of_locallyLipschitz hG hc).congr fun t => ?_⟩
    rw [hidden_succ, Pi.zero_apply, Matrix.mul_zero, zero_add]

omit [DecidableEq d] in
/-- **(d) The skipless output along a ray**, for `ε > 0`: there is `G` with
`t (F'(t X) - G) → 0`. -/
private theorem exists_tendsto_smul_eval_skipless_ray (A : Arch T d L) {ε : ℝ} (hε : 0 < ε)
    (hχ : A.χ = rmsNorm ε) (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ)) (θ : Params A dIn dOut)
    (X : Matrix T dIn ℝ) :
    ∃ G, Tendsto (fun t : ℝ => t • (eval A 0 θ (t • X) - G)) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := exists_tendsto_smul_chi_skipless_ray A hε hχ hf θ X (Fin.last L)
  refine ⟨c * θ.D, ?_⟩
  have h := tendsto_mul_right_matrix hc θ.D
  rw [Matrix.zero_mul] at h
  refine h.congr fun t => ?_
  simp only [eval, Matrix.smul_mul, Matrix.sub_mul]

/-! ### Theorem 4.3 for `ε > 0` -/

/-- **Theorem 4.3 for `ε > 0`, under the conditions of the proof.** A pre-RMSNorm residual network
with locally Lipschitz blocks whose weights satisfy `TurnGeneric` equals no pre-RMSNorm skipless
network with locally Lipschitz blocks, whatever its depth, its model dimension, its widths, its
kinds of blocks and its constant `ε' > 0`: the two differ at some input. -/
theorem exists_ne_skipless_rmsNorm_of_turn {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    (A : Arch T d L) (hχ : A.χ = rmsNorm ε) (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ))
    (θ : Params A dIn dOut) (hθ : TurnGeneric A θ)
    {L' : ℕ} {d' : Type*} [Fintype d'] (A' : Arch T d' L')
    (hχ' : A'.χ = rmsNorm ε') (hf' : ∀ ℓ, LocallyLipschitz (A'.f ℓ))
    (θ' : Params A' dIn dOut) :
    ∃ X : Matrix T dIn ℝ, eval A 1 θ X ≠ eval A' 0 θ' X := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n, hn, r₀, hturn⟩ := hθ.turn
  -- `d` is not empty (else every row is `0 = 0 • n_r`), so the rows of `n` do not vanish
  have hd : (0 : ℝ) < Fintype.card d := by
    rcases (Fintype.card d).eq_zero_or_pos with h0 | h0
    · have : IsEmpty d := Fintype.card_eq_zero_iff.1 h0
      exact absurd (funext fun j => isEmptyElim j) (hturn 0)
    · exact Nat.cast_pos.2 h0
  have hnr : ∀ r, n r ≠ 0 := fun r h0 => by
    have h1 := hn r
    rw [h0, zero_dotProduct] at h1
    exact hd.ne h1
  have hnn : rmsNorm 0 n = n := rmsNorm_zero_eq_self hd hn
  -- the input `X₀ = n B` with `B E = 1` has `X₀ E = n`
  obtain ⟨B, hB⟩ := exists_left_inverse_of_rank' θ.E hθ.rank_E
  have hX₀ : n * B * θ.E = n := by rw [Matrix.mul_assoc, hB, Matrix.mul_one]
  -- residual network: `t (F(t X₀) - n D) → P D`
  have hres := tendsto_smul_eval_residual_ray A hχ (fun ℓ => (hf ℓ).continuous) θ
    (X := n * B) (by rw [hX₀]; exact hnr)
  rw [hX₀, hnn] at hres
  -- skipless network: `t (F'(t X₀) - G) → 0`
  obtain ⟨G, hG⟩ := exists_tendsto_smul_eval_skipless_ray A' hε' hχ' hf' θ' (n * B)
  -- the outputs are equal, so their limits are: `n D = G`, then `P D = 0`
  have hGn : n * θ.D = G := tendsto_nhds_unique (tendsto_of_tendsto_smul_sub' hres)
    ((tendsto_of_tendsto_smul_sub' hG).congr fun t => (hcon _).symm)
  have hPD : (Matrix.of fun r => rayLim (n r) ((∑ ℓ, A.f ℓ (n * θ.read ℓ) * θ.write ℓ) r))
      * θ.D = 0 := by
    refine tendsto_nhds_unique hres (hG.congr fun t => ?_)
    rw [hcon, hGn]
  -- `D` has rank `d`, so `P = 0`; row `r₀` makes `β_{r₀}` a multiple of `n_{r₀}`
  have hP := eq_zero_of_mul_eq_zero_of_rank hθ.rank_D hPD
  have h0 : rayLim (n r₀) ((∑ ℓ, A.f ℓ (n * θ.read ℓ) * θ.write ℓ) r₀) = 0 := congrFun hP r₀
  obtain ⟨c, hc⟩ := exists_eq_smul_of_rayLim_eq_zero (hnr r₀) h0
  exact hturn c hc

/-! ### Theorem 4.3 for `ε = 0` -/

/-- Finitely many positive numbers have a positive lower bound (copy of a private lemma of
`Absorb/Limits.lean`). -/
private theorem exists_pos_le_of_finite' {ι : Type*} [Finite ι] (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) : ∃ ρ > 0, ∀ i, ρ ≤ a i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min a
    exact ⟨a i₀, ha i₀, hi₀⟩

omit [DecidableEq d] in
/-- `N_0` is continuous at a state without zero rows. -/
private theorem continuousAt_rmsNorm_zero {z : Matrix T d ℝ} (hz : ∀ r, z r ≠ 0) :
    ContinuousAt (rmsNorm 0) z := by
  obtain ⟨ρ, hρ, hρz⟩ := exists_pos_le_of_finite' (fun r => ‖z r‖)
    (fun r => norm_pos_iff.2 (hz r))
  refine continuousAt_of_locally_lipschitz one_pos (2 * Fintype.card d / ρ) fun y _ => ?_
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_rmsNorm_zero_sub_le hρ hρz y

omit [DecidableEq d] [Fintype dOut] in
/-- For `χ = N_0` and continuous `f_ℓ`, every hidden state is continuous at an input at which the
network is defined. -/
private theorem continuousAt_hidden_of_definedAt (A : Arch T d L) (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, Continuous (A.f ℓ)) (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)
    {X : Matrix T dIn ℝ} (hX : DefinedAt A S θ X) (k : Fin (L + 1)) :
    ContinuousAt (fun X => hidden A S θ X k) X := by
  induction k using Fin.induction with
  | zero =>
    simp only [hidden_zero]
    exact (lipschitzWith_mul_right θ.E).continuous.continuousAt
  | succ k ih =>
    simp only [hidden_succ, hχ]
    have hN : ContinuousAt (fun X => rmsNorm 0 (hidden A S θ X k.castSucc)) X :=
      ContinuousAt.comp (f := fun X => hidden A S θ X k.castSucc)
        (continuousAt_rmsNorm_zero (hX k.castSucc)) ih
    exact ((lipschitzWith_mul_right (S k)).continuous.continuousAt.comp ih).add
      ((lipschitzWith_mul_right (θ.write k)).continuous.continuousAt.comp
        ((hf k).continuousAt.comp
          ((lipschitzWith_mul_right (θ.read k)).continuous.continuousAt.comp hN)))

omit [DecidableEq d] in
/-- **(a)** For `χ = N_0` and continuous `f_ℓ`, the output is continuous at an input at which the
network is defined. -/
private theorem continuousAt_eval_of_definedAt (A : Arch T d L) (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, Continuous (A.f ℓ)) (S : Fin L → Matrix d d ℝ) (θ : Params A dIn dOut)
    {X : Matrix T dIn ℝ} (hX : DefinedAt A S θ X) : ContinuousAt (eval A S θ) X := by
  have hN : ContinuousAt (fun X => rmsNorm 0 (hidden A S θ X (Fin.last L))) X :=
    ContinuousAt.comp (f := fun X => hidden A S θ X (Fin.last L))
      (continuousAt_rmsNorm_zero (hX (Fin.last L)))
      (continuousAt_hidden_of_definedAt A hχ hf S θ hX (Fin.last L))
  show ContinuousAt (fun X => A.χ (hidden A S θ X (Fin.last L)) * θ.D) X
  rw [hχ]
  exact (lipschitzWith_mul_right θ.D).continuous.continuousAt.comp hN

/-- Two maps continuous at `x` that agree on a dense set agree at `x`. -/
private theorem eq_of_continuousAt_of_dense {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [T2Space β] {f g : α → β} {S : Set α} (hS : Dense S)
    (hfg : ∀ y ∈ S, f y = g y) {x : α} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    f x = g x := by
  have : (𝓝[S] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hS x)
  refine tendsto_nhds_unique (l := 𝓝[S] x) (hf.tendsto.mono_left nhdsWithin_le_nhds) ?_
  exact (hg.tendsto.mono_left nhdsWithin_le_nhds).congr'
    (eventually_nhdsWithin_of_forall fun y hy => (hfg y hy).symm)

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
/-- **(b) Scale invariance of the skipless network** (`χ = N_0`): for `c > 0`, `h_0(c X) = c h_0(X)`
and `h_k(c X) = h_k(X)` for `k ≥ 1`. -/
private theorem exists_hidden_skipless_smul (A : Arch T d L) (hχ : A.χ = rmsNorm 0)
    (θ : Params A dIn dOut) (X : Matrix T dIn ℝ) {c : ℝ} (hc : 0 < c) (k : Fin (L + 1)) :
    ∃ c' : ℝ, 0 < c' ∧ hidden A 0 θ (c • X) k = c' • hidden A 0 θ X k := by
  induction k using Fin.induction with
  | zero => exact ⟨c, hc, by rw [hidden_zero, hidden_zero, Matrix.smul_mul]⟩
  | succ k ih =>
    obtain ⟨c', hc', h⟩ := ih
    refine ⟨1, one_pos, ?_⟩
    simp only [hidden_succ, h, hχ, rmsNorm_zero_smul hc', one_smul, Pi.zero_apply,
      Matrix.mul_zero, zero_add]

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
private theorem definedAt_skipless_smul (A : Arch T d L) (hχ : A.χ = rmsNorm 0)
    (θ : Params A dIn dOut) {X : Matrix T dIn ℝ} (hX : DefinedAt A 0 θ X) {c : ℝ}
    (hc : 0 < c) : DefinedAt A 0 θ (c • X) := by
  intro k r
  obtain ⟨c', hc', h⟩ := exists_hidden_skipless_smul A hχ θ X hc k
  rw [h]
  exact smul_ne_zero hc'.ne' (hX k r)

omit [Fintype T] [DecidableEq d] [Fintype dOut] in
private theorem eval_skipless_smul (A : Arch T d L) (hχ : A.χ = rmsNorm 0)
    (θ : Params A dIn dOut) (X : Matrix T dIn ℝ) {c : ℝ} (hc : 0 < c) :
    eval A 0 θ (c • X) = eval A 0 θ X := by
  obtain ⟨c', hc', h⟩ := exists_hidden_skipless_smul A hχ θ X hc (Fin.last L)
  unfold eval
  rw [h, hχ, rmsNorm_zero_smul hc']

/-- If `x_t - t W → β`, then `x_t / t → W`. -/
private theorem tendsto_inv_smul_of_tendsto_sub_smul {M : Type*} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {x : ℝ → M} {W β : M}
    (h : Tendsto (fun t : ℝ => x t - t • W) atTop (𝓝 β)) :
    Tendsto (fun t : ℝ => t⁻¹ • x t) atTop (𝓝 W) := by
  have h1 : Tendsto (fun t : ℝ => W + t⁻¹ • (x t - t • W)) atTop (𝓝 (W + (0 : ℝ) • β)) :=
    tendsto_const_nhds.add (tendsto_inv_atTop_zero.smul h)
  rw [zero_smul, add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_sub_cancel]

omit [Fintype dOut] in
/-- **(c)** If no row of `X E` vanishes, the residual network is defined at `t X` for all large
`t` (`h_k(t X) / t → X E`). -/
private theorem eventually_definedAt_residual_ray (A : Arch T d L) {ε : ℝ}
    (hχ : A.χ = rmsNorm ε) (hf : ∀ ℓ, Continuous (A.f ℓ)) (θ : Params A dIn dOut)
    {X : Matrix T dIn ℝ} (hX : ∀ r, (X * θ.E) r ≠ 0) :
    ∀ᶠ t : ℝ in atTop, DefinedAt A 1 θ (t • X) := by
  have h : ∀ k r, ∀ᶠ t : ℝ in atTop, (t⁻¹ • hidden A 1 θ (t • X) k) r ≠ 0 := fun k r =>
    (tendsto_pi_nhds.1 (tendsto_inv_smul_of_tendsto_sub_smul
      (tendsto_hidden_residual_ray A hχ hf θ hX k)) r).eventually_ne (hX r)
  filter_upwards [eventually_all.2 fun k => eventually_all.2 fun r => h k r] with t ht k r h0
  refine ht k r ?_
  show t⁻¹ • hidden A 1 θ (t • X) k r = 0
  rw [h0, smul_zero]

/-- **(c)** If the two networks agree wherever both are defined, then at every input `X` at which
the skipless network is defined and `X E` has no zero row, every row of `β(N_0(X E))` is a
multiple of the same row of `X E`. -/
private theorem exists_eq_smul_row_of_agree (A : Arch T d L) (hχ : A.χ = rmsNorm 0)
    (hf : ∀ ℓ, Continuous (A.f ℓ)) (θ : Params A dIn dOut) (hD : θ.D.rank = Fintype.card d)
    {L' : ℕ} {d' : Type*} [Fintype d'] (A' : Arch T d' L') (hχ' : A'.χ = rmsNorm 0)
    (θ' : Params A' dIn dOut)
    (hagree : ∀ X, DefinedAt A 1 θ X → DefinedAt A' 0 θ' X → eval A 1 θ X = eval A' 0 θ' X)
    {X : Matrix T dIn ℝ} (hX' : DefinedAt A' 0 θ' X) (hX : ∀ r, (X * θ.E) r ≠ 0) (r : T) :
    ∃ c : ℝ, (∑ ℓ, A.f ℓ (rmsNorm 0 (X * θ.E) * θ.read ℓ) * θ.write ℓ) r = c • (X * θ.E) r := by
  have hres := tendsto_smul_eval_residual_ray A hχ hf θ hX
  -- for large `t` both networks are defined at `t X`, and the skipless output there is `F'(X)`
  have hev : ∀ᶠ t : ℝ in atTop, eval A 1 θ (t • X) = eval A' 0 θ' X := by
    filter_upwards [eventually_definedAt_residual_ray A hχ hf θ hX, eventually_gt_atTop 0]
      with t hdef ht
    rw [hagree _ hdef (definedAt_skipless_smul A' hχ' θ' hX' ht), eval_skipless_smul A' hχ' θ' X ht]
  -- so the limit of the residual output is `F'(X)`, and then `P D = 0`
  have hG : eval A' 0 θ' X = rmsNorm 0 (X * θ.E) * θ.D :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm))
      (tendsto_of_tendsto_smul_sub' hres)
  have hPD : (Matrix.of fun r => rayLim ((X * θ.E) r)
      ((∑ ℓ, A.f ℓ (rmsNorm 0 (X * θ.E) * θ.read ℓ) * θ.write ℓ) r)) * θ.D = 0 := by
    refine tendsto_nhds_unique hres (tendsto_const_nhds.congr' (hev.mono fun t ht => ?_))
    dsimp only
    rw [ht, hG, sub_self, smul_zero]
  have hP := eq_zero_of_mul_eq_zero_of_rank hD hPD
  exact exists_eq_smul_of_rayLim_eq_zero (hX r) (congrFun hP r)

omit [DecidableEq d] in
/-- The dot product of two maps continuous at `x` is continuous at `x`. -/
private theorem continuousAt_dotProduct' {α : Type*} [TopologicalSpace α] {f g : α → d → ℝ}
    {x : α} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun y => f y ⬝ᵥ g y) x :=
  ContinuousAt.comp (f := fun y => (f y, g y)) (x := x)
    (continuous_fst.dotProduct continuous_snd).continuousAt (hf.prodMk hg)

omit [DecidableEq d] [Fintype dOut] in
/-- `X ↦ β(N_0(X E)) = ∑_ℓ f_ℓ(N_0(X E) W_read^ℓ) W_write^ℓ` is continuous at an input `X₀` such
that `X₀ E` has no zero row. -/
private theorem continuousAt_betaSum (A : Arch T d L) (hf : ∀ ℓ, Continuous (A.f ℓ))
    (θ : Params A dIn dOut) {X₀ : Matrix T dIn ℝ} (hX₀ : ∀ r, (X₀ * θ.E) r ≠ 0) :
    ContinuousAt (fun X : Matrix T dIn ℝ =>
      ∑ ℓ, A.f ℓ (rmsNorm 0 (X * θ.E) * θ.read ℓ) * θ.write ℓ) X₀ := by
  have hN : ContinuousAt (fun X : Matrix T dIn ℝ => rmsNorm 0 (X * θ.E)) X₀ :=
    ContinuousAt.comp (f := fun X : Matrix T dIn ℝ => X * θ.E) (x := X₀)
      (continuousAt_rmsNorm_zero hX₀) (lipschitzWith_mul_right θ.E).continuous.continuousAt
  refine tendsto_finsetSum (f := fun ℓ X => A.f ℓ (rmsNorm 0 (X * θ.E) * θ.read ℓ) * θ.write ℓ)
    _ fun ℓ _ => ?_
  exact (lipschitzWith_mul_right (θ.write ℓ)).continuous.continuousAt.comp
    ((hf ℓ).continuousAt.comp ((lipschitzWith_mul_right (θ.read ℓ)).continuous.continuousAt.comp hN))

/-- **Theorem 4.3 for `ε = 0`, under the conditions of the proof.** A pre-RMSNorm residual network
with `ε = 0` and locally Lipschitz blocks whose weights satisfy `TurnGeneric` equals no
pre-RMSNorm skipless network with `ε = 0` and continuous blocks, in the paper's sense of equality
for `ε = 0`: there is no dense set of inputs at which both networks are defined and agree. -/
theorem not_dense_eq_skipless_rmsNorm_zero_of_turn
    (A : Arch T d L) (hχ : A.χ = rmsNorm 0) (hf : ∀ ℓ, LocallyLipschitz (A.f ℓ))
    (θ : Params A dIn dOut) (hθ : TurnGeneric A θ)
    {L' : ℕ} {d' : Type*} [Fintype d'] (A' : Arch T d' L')
    (hχ' : A'.χ = rmsNorm 0) (hf' : ∀ ℓ, Continuous (A'.f ℓ))
    (θ' : Params A' dIn dOut) :
    ¬ ∃ S : Set (Matrix T dIn ℝ), Dense S ∧
      ∀ X ∈ S, DefinedAt A 1 θ X ∧ DefinedAt A' 0 θ' X ∧ eval A 1 θ X = eval A' 0 θ' X := by
  rintro ⟨S, hS, hSX⟩
  have hfc : ∀ ℓ, Continuous (A.f ℓ) := fun ℓ => (hf ℓ).continuous
  -- (a) both outputs are continuous where defined, so they agree wherever both are defined
  have hagree : ∀ X, DefinedAt A 1 θ X → DefinedAt A' 0 θ' X → eval A 1 θ X = eval A' 0 θ' X :=
    fun X h1 h2 => eq_of_continuousAt_of_dense hS (fun Y hY => (hSX Y hY).2.2)
      (continuousAt_eval_of_definedAt A hχ hfc 1 θ h1)
      (continuousAt_eval_of_definedAt A' hχ' hf' 0 θ' h2)
  obtain ⟨n, hn, r₀, hturn⟩ := hθ.turn
  -- `d` is not empty, the rows of `n` do not vanish, `N_0(n) = n`, and `X₀ = n B` has `X₀ E = n`
  have hd : (0 : ℝ) < Fintype.card d := by
    rcases (Fintype.card d).eq_zero_or_pos with h0 | h0
    · have : IsEmpty d := Fintype.card_eq_zero_iff.1 h0
      exact absurd (funext fun j => isEmptyElim j) (hturn 0)
    · exact Nat.cast_pos.2 h0
  have hnr : ∀ r, n r ≠ 0 := fun r h0 => by
    have h1 := hn r
    rw [h0, zero_dotProduct] at h1
    exact hd.ne h1
  have hnn : rmsNorm 0 n = n := rmsNorm_zero_eq_self hd hn
  obtain ⟨B, hB⟩ := exists_left_inverse_of_rank' θ.E hθ.rank_E
  have hX₀ : n * B * θ.E = n := by rw [Matrix.mul_assoc, hB, Matrix.mul_one]
  -- (d) the defect `V(X) = (w·w) β - (β·w) w` with `w = (X E)_{r₀}`, `β = β(N_0(X E))_{r₀}`
  obtain ⟨V, hV⟩ : ∃ V : Matrix T dIn ℝ → d → ℝ, ∀ X, V X =
      ((X * θ.E) r₀ ⬝ᵥ (X * θ.E) r₀) •
        (∑ ℓ, A.f ℓ (rmsNorm 0 (X * θ.E) * θ.read ℓ) * θ.write ℓ) r₀ -
      ((∑ ℓ, A.f ℓ (rmsNorm 0 (X * θ.E) * θ.read ℓ) * θ.write ℓ) r₀ ⬝ᵥ (X * θ.E) r₀) •
        (X * θ.E) r₀ := ⟨_, fun X => rfl⟩
  -- `V` is continuous at `X₀`, and `V(X₀) ≠ 0` by `turn`
  have hVc : ContinuousAt V (n * B) := by
    rw [show V = _ from funext hV]
    have hβ : ContinuousAt (fun X : Matrix T dIn ℝ =>
        (∑ ℓ, A.f ℓ (rmsNorm 0 (X * θ.E) * θ.read ℓ) * θ.write ℓ) r₀) (n * B) :=
      (continuous_apply r₀).continuousAt.comp
        (continuousAt_betaSum A hfc θ (X₀ := n * B) (by rw [hX₀]; exact hnr))
    have hw : ContinuousAt (fun X : Matrix T dIn ℝ => (X * θ.E) r₀) (n * B) :=
      ((continuous_apply r₀).comp (lipschitzWith_mul_right θ.E).continuous).continuousAt
    exact ((continuousAt_dotProduct' hw hw).smul hβ).sub
      ((continuousAt_dotProduct' hβ hw).smul hw)
  have hV0 : V (n * B) ≠ 0 := by
    intro h0
    rw [hV, hX₀, hnn, hn r₀, sub_eq_zero] at h0
    apply hturn (((∑ ℓ, A.f ℓ (n * θ.read ℓ) * θ.write ℓ) r₀ ⬝ᵥ n r₀) / Fintype.card d)
    rw [div_eq_inv_mul, ← smul_smul, ← h0, smul_smul, inv_mul_cancel₀ hd.ne', one_smul]
  -- near `X₀`, `V ≠ 0` and no row of `X E` vanishes; the dense set `S` meets this neighbourhood
  have hrows : ∀ᶠ X in 𝓝 (n * B), ∀ r, (X * θ.E) r ≠ 0 :=
    eventually_all.2 fun r =>
      (((continuous_apply r).comp (lipschitzWith_mul_right θ.E).continuous).continuousAt).eventually_ne
        (by show (n * B * θ.E) r ≠ 0; rw [hX₀]; exact hnr r)
  obtain ⟨X, hXS, hXV, hXr⟩ := hS.inter_nhds_nonempty ((hVc.eventually_ne hV0).and hrows)
  -- (c) at such an `X`, row `r₀` of `β` is a multiple of `(X E)_{r₀}`, so `V(X) = 0`
  obtain ⟨c, hc⟩ := exists_eq_smul_row_of_agree A hχ hfc θ hθ.rank_D A' hχ' θ' hagree
    (hSX X hXS).2.1 hXr r₀
  apply hXV
  rw [hV, hc, smul_dotProduct, smul_eq_mul, smul_smul, mul_comm, sub_self]

end Skips
