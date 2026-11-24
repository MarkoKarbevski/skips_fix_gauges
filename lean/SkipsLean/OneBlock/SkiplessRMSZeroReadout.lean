import SkipsLean.Depth.SuffixZero

/-!
# The final normalization with `ε = 0` and the readout: what a flat direction does to a hidden state

Paper (skips paper), proof of Theorem B.1 (iv), "The skipless network: equality": "As in the case
`ε = 0` of part (iii), `η_D = −Y D` with `Y` antisymmetric, since `h_1` takes all values in an
open set, and `D_θ h_1 η = h_1 Y + μ h_1` with a number `μ(x)` at each input of `Ω`." The case
`ε = 0` of part (iii) says: "Now `N_ε` maps onto the sphere of radius `√d_model`", and the kernel
of the derivative of `N_0` at a row `h ≠ 0` is the line `ℝ h`.

Here this step as one statement on the map `(h, D) ↦ N_0(h) D`, with no network in it: let `g i`
be hidden states with no zero row and `k i` their variations, for `i` in any index set (the inputs
of a network), and let `δ` be a variation of the readout `D` of rank `d`. If the output
`N_0(g i) D` does not move to first order, `𝐃N_0(g i)[k i] D + N_0(g i) δ = 0` for every `i`, and
the rows of the `g i` fill a nonempty open set of rows, then `δ = −Y D` for an antisymmetric `Y`,
and every row of `k i` is the row of `g i` times `Y` plus a multiple of the row of `g i`; the
multiple is `⟨g, k⟩ / ⟨g, g⟩`.

It is used for the skipless network of one ReLU or ReLU² block
(`OneBlock/SkiplessHomogeneousRMSZeroEq.lean`), where `g` is the output of the block without the
normalization before it.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dOut]

omit [DecidableEq d] in
/-- Helper: `⟨v, v⟩ > 0` and `⟨v, v⟩ / d > 0` for a row `v ≠ 0`. -/
private theorem dot_self_pos_srr {v : d → ℝ} (hv : v ≠ 0) :
    0 < v ⬝ᵥ v ∧ 0 < (v ⬝ᵥ v) / (Fintype.card d : ℝ) := by
  have h1 : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (v j))
      (fun h => hv (dotProduct_self_eq_zero.1 h.symm))
  obtain ⟨j, -⟩ := Function.ne_iff.1 hv
  have h2 : (0 : ℝ) < Fintype.card d := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩)
  exact ⟨h1, div_pos h1 h2⟩

/-- Helper: the real identity behind the rows of Step 3: from
`ρ⁻¹ a − (K/n) ρ⁻³ c = ρ⁻¹ b` with `ρ² = H/n` follows `a = b + (K/H) c`. -/
private theorem real_row_srr {a b c K H n ρ : ℝ} (hρ : 0 < ρ) (hH : 0 < H) (hn : 0 < n)
    (h2 : ρ ^ 2 = H / n) (e : ρ⁻¹ * a - (K / n * ρ⁻¹ ^ 3) * c = ρ⁻¹ * b) :
    a = b + K / H * c := by
  have hρn : ρ ^ 2 * n = H := by rw [h2]; field_simp
  have e1 : ρ ^ 2 * n * a - K * c = ρ ^ 2 * n * b := by
    have e2 := congrArg (fun z => z * (ρ ^ 3 * n)) e
    simp only [sub_mul] at e2
    field_simp at e2
    linear_combination e2
  rw [hρn] at e1
  field_simp
  linear_combination e1

omit [DecidableEq d] in
/-- Helper (Step 3): at `h` without a zero row, `𝐃N_0(h) k = N_0(h) M` gives, row by row,
`k_t = h_t M + μ_t h_t` with `μ_t = ⟨h_t, k_t⟩ / ⟨h_t, h_t⟩`. -/
private theorem row_of_fderiv_rmsNorm_zero_srr {h k : Matrix T d ℝ} (hh : ∀ t, h t ≠ 0)
    {M : Matrix d d ℝ}
    (e : fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) h k = rmsNorm 0 h * M) (t : T) :
    k t = h t ᵥ* M + ((h t ⬝ᵥ k t) / (h t ⬝ᵥ h t)) • h t := by
  rw [fderiv_rmsNorm_zero_apply h k hh] at e
  obtain ⟨hH, hq⟩ := dot_self_pos_srr (hh t)
  have hn : (0 : ℝ) < Fintype.card d := by
    obtain ⟨j, -⟩ := Function.ne_iff.1 (hh t)
    exact Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨j⟩)
  have hs2 := Real.sq_sqrt hq.le
  have hs := Real.sqrt_pos.2 hq
  funext i
  have ei := congrFun (congrFun e t) i
  have hR : (rmsNorm 0 h * M) t i
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ * (h t ᵥ* M) i := by
    rw [Matrix.mul_apply_eq_vecMul]
    show (rmsRow 0 (h t) ᵥ* M) i = _
    rw [rmsRow, add_zero, Matrix.smul_vecMul]
    rfl
  rw [hR] at ei
  simp only [Matrix.of_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ei
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact real_row_srr hs hH hn hs2 ei

omit [DecidableEq d] in
/-- Helper (Step 4): if `k = h M + μ h` with `h ≠ 0`, then `⟨h M, h⟩ = 0`. -/
private theorem quad_of_row_srr {h k : d → ℝ} (hh : h ≠ 0) {M : Matrix d d ℝ}
    (e : k = h ᵥ* M + ((h ⬝ᵥ k) / (h ⬝ᵥ h)) • h) : h ᵥ* M ⬝ᵥ h = 0 := by
  have hH := (dot_self_pos_srr hh).1
  have e1 := congrArg (fun v => h ⬝ᵥ v) e
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at e1
  rw [div_mul_cancel₀ _ hH.ne'] at e1
  rw [dotProduct_comm]
  linarith

omit [Fintype T] [DecidableEq d] in
/-- Helper (Step 2): `N_0(h) Z = 0` implies `h Z = 0` at `h` without a zero row (each row is
rescaled by a positive number). -/
private theorem mul_eq_zero_of_rmsNorm_zero_mul_srr {m : Type*} [Fintype m]
    {h : Matrix T d ℝ} (hh : ∀ t, h t ≠ 0) (Z : Matrix d m ℝ) (hZ : rmsNorm 0 h * Z = 0) :
    h * Z = 0 := by
  funext t
  have hq := (dot_self_pos_srr (hh t)).2
  have hrow : (rmsNorm 0 h * Z) t
      = (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ • (h t ᵥ* Z) := by
    rw [Matrix.mul_apply_eq_vecMul]
    show rmsRow 0 (h t) ᵥ* Z = _
    rw [rmsRow, add_zero, Matrix.smul_vecMul]
  have h0 : (Real.sqrt ((h t ⬝ᵥ h t) / (Fintype.card d : ℝ)))⁻¹ • (h t ᵥ* Z) = 0 := by
    rw [← hrow]
    exact congrFun hZ t
  rw [Matrix.mul_apply_eq_vecMul]
  exact (smul_eq_zero.1 h0).resolve_left (inv_ne_zero (Real.sqrt_pos.2 hq).ne')

omit [Fintype d] [DecidableEq d] in
/-- Helper: a point `v₀` of an open set `O` of rows and a direction `u` give a `δ > 0` with
`v₀ ± δ u ∈ O`. -/
private theorem exists_add_sub_mem_srr {O : Set (d → ℝ)} (hO : IsOpen O) {v₀ : d → ℝ}
    (hv₀ : v₀ ∈ O) (u : d → ℝ) : ∃ δ : ℝ, 0 < δ ∧ v₀ + δ • u ∈ O ∧ v₀ - δ • u ∈ O := by
  have hc : Continuous fun δ : ℝ => v₀ + δ • u :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : (fun δ : ℝ => v₀ + δ • u) ⁻¹' O ∈ nhds (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hv₀)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hmem
  have hr2 := half_pos hr
  refine ⟨r / 2, hr2, hball ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hr2]
    linarith
  · have h := hball (show -(r / 2) ∈ Metric.ball (0 : ℝ) r by
      rw [Metric.mem_ball, dist_zero_right, norm_neg, Real.norm_eq_abs, abs_of_pos hr2]
      linarith)
    rwa [Set.mem_preimage, neg_smul, ← sub_eq_add_neg] at h

/-- Helper (Step 2): a matrix `Z` with `v Z = 0` for every row `v` of a nonempty open set is
`0`. -/
private theorem eq_zero_of_vecMul_on_srr {m : Type*} [Fintype m] {O : Set (d → ℝ)}
    (hO : IsOpen O) (hne : O.Nonempty) {Z : Matrix d m ℝ} (h : ∀ v ∈ O, v ᵥ* Z = 0) :
    Z = 0 := by
  obtain ⟨v₀, hv₀⟩ := hne
  have hu : ∀ u : d → ℝ, u ᵥ* Z = 0 := by
    intro u
    obtain ⟨δ, hδ, hp, -⟩ := exists_add_sub_mem_srr hO hv₀ u
    have e := h _ hp
    rw [Matrix.add_vecMul, Matrix.smul_vecMul, h v₀ hv₀, zero_add] at e
    exact (smul_eq_zero.1 e).resolve_left hδ.ne'
  ext a j
  have e := congrFun (hu (Pi.single a 1)) j
  rw [Matrix.single_one_vecMul] at e
  exact e

omit [DecidableEq d] in
/-- Helper (Step 4): a quadratic form `u ↦ ⟨u Y, u⟩` that vanishes on a nonempty open set
vanishes everywhere. -/
private theorem quad_zero_on_srr {O : Set (d → ℝ)} (hO : IsOpen O) (hne : O.Nonempty)
    {Y : Matrix d d ℝ} (h : ∀ v ∈ O, v ᵥ* Y ⬝ᵥ v = 0) (u : d → ℝ) : u ᵥ* Y ⬝ᵥ u = 0 := by
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨δ, hδ, hp, hm⟩ := exists_add_sub_mem_srr hO hv₀ u
  have e0 := h v₀ hv₀
  have ep := h _ hp
  have em := h _ hm
  simp only [Matrix.add_vecMul, Matrix.sub_vecMul, Matrix.smul_vecMul, dotProduct_add,
    add_dotProduct, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul] at ep em
  have e : (2 * δ ^ 2) * (u ᵥ* Y ⬝ᵥ u) = 0 := by
    linear_combination ep + em - 2 * e0
  have hδ2 : 2 * δ ^ 2 ≠ 0 := by positivity
  exact (mul_eq_zero.1 e).resolve_left hδ2

/-- Helper (Step 4): a matrix `Y` with `⟨u Y, u⟩ = 0` for every row `u` is antisymmetric. -/
private theorem transpose_eq_neg_srr {Y : Matrix d d ℝ} (h : ∀ u : d → ℝ, u ᵥ* Y ⬝ᵥ u = 0) :
    Yᵀ = -Y := by
  ext i j
  have hii := h (Pi.single i 1)
  have hjj := h (Pi.single j 1)
  have hij := h (Pi.single i 1 + Pi.single j 1)
  simp only [Matrix.add_vecMul, dotProduct_add, Matrix.single_one_vecMul,
    dotProduct_single_one, Pi.add_apply, Matrix.row_apply] at hii hjj hij
  simp only [Matrix.transpose_apply, Matrix.neg_apply]
  linarith

/-- **Proof of Theorem B.1 (iv) of the skips paper, the final normalization (equation (18)):** if
`𝐃N_0(g i)[k i] D + N_0(g i) δ = 0` for all `i`, the readout `D` has rank `d`, no row of a `g i`
is zero and the rows of the `g i` fill a nonempty open set, then `δ = −Y D` with `Y`
antisymmetric, and each row of `k i` is the row of `g i` times `Y` plus `⟨g, k⟩ / ⟨g, g⟩` times
the row of `g i`. -/
theorem exists_antisymm_of_fderiv_rmsNorm_zero_mul {ι : Type*} (g k : ι → Matrix T d ℝ)
    (D δ : Matrix d dOut ℝ) (hD : D.rank = Fintype.card d)
    (hg : ∀ i t, g i t ≠ 0)
    (hO : ∃ O : Set (d → ℝ), IsOpen O ∧ O.Nonempty ∧ ∀ v ∈ O, ∃ i t, g i t = v)
    (h : ∀ i, fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (g i) (k i) * D
      + rmsNorm 0 (g i) * δ = 0) :
    ∃ Y : Matrix d d ℝ, Yᵀ = -Y ∧ δ = -(Y * D) ∧
      ∀ i t, k i t = g i t ᵥ* Y + ((g i t ⬝ᵥ k i t) / (g i t ⬝ᵥ g i t)) • g i t := by
  obtain ⟨O, hOo, hOne, hOg⟩ := hO
  -- Step 1: a right inverse `D⁺` of `D`, `Y := −δ D⁺`, and `𝐃N_0(g i)[k i] = N_0(g i) Y`
  obtain ⟨Dp, hDp⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1
    (Matrix.mulVec_surjective_iff_rank_eq_card.2 hD)
  set Y : Matrix d d ℝ := -(δ * Dp) with hYdef
  have step1 : ∀ i, fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (g i) (k i)
      = rmsNorm 0 (g i) * Y := by
    intro i
    have e := congrArg (· * Dp) (h i)
    simp only [Matrix.add_mul, Matrix.mul_assoc, hDp, Matrix.mul_one, Matrix.zero_mul] at e
    rw [hYdef, Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left e
  -- Step 3: the rows `k = h Y + (⟨h, k⟩ / ⟨h, h⟩) h`
  have step3 : ∀ i t, k i t = g i t ᵥ* Y + ((g i t ⬝ᵥ k i t) / (g i t ⬝ᵥ g i t)) • g i t :=
    fun i t => row_of_fderiv_rmsNorm_zero_srr (hg i) (step1 i) t
  -- Step 2: `N_0(g i) (Y D + δ) = 0`, so `v (Y D + δ) = 0` on `O`, so `Y D + δ = 0`
  have step2 : Y * D + δ = 0 := by
    refine eq_zero_of_vecMul_on_srr hOo hOne fun v hv => ?_
    obtain ⟨i, t, rfl⟩ := hOg v hv
    have e : rmsNorm 0 (g i) * (Y * D + δ) = 0 := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc, ← step1 i]
      exact h i
    have e2 := congrFun (mul_eq_zero_of_rmsNorm_zero_mul_srr (hg i) _ e) t
    rw [Matrix.mul_apply_eq_vecMul] at e2
    exact e2
  -- Step 4: `⟨h Y, h⟩ = 0` on `O`, so `Y` is antisymmetric
  have hq : ∀ v ∈ O, v ᵥ* Y ⬝ᵥ v = 0 := by
    intro v hv
    obtain ⟨i, t, rfl⟩ := hOg v hv
    exact quad_of_row_srr (hg i t) (step3 i t)
  refine ⟨Y, transpose_eq_neg_srr (quad_zero_on_srr hOo hOne hq),
    eq_neg_of_add_eq_zero_right step2, step3⟩

end Skips
