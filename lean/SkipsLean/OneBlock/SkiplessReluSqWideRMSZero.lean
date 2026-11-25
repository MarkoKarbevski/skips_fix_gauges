import SkipsLean.OneBlock.SkiplessHomogeneousRMSZeroEq
import SkipsLean.OneBlock.SkiplessReluWideRMSZero
import SkipsLean.OneBlock.UnitsGeneralPositionSq

/-!
# One skipless ReLU² block of width at least `d` under pre-RMSNorm with `ε = 0`: the equality

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`, and the skipless
network at most `P − d_model² − d_model (d_model − 1)/2 − 1 − s`, with equality for ReLU and ReLU²
blocks. So the skip raises the functional dimension by at least `d_model²`, and by exactly
`d_model²` for ReLU and ReLU² blocks."

Here "with equality" and "by exactly `d_model²`" **for a ReLU² block of width at least
`d_model`** (`OneBlock/SkiplessHomogeneousRMSZeroEq.lean` has width exactly `d_model`;
`OneBlock/SkiplessReluWideRMSZero.lean` the ReLU block of width at least `d_model`):

* at almost every parameter of a block of width at least `d ≥ 2` the hidden units are in general
  position in the sense for ReLU² (`UnitsGeneralPositionSq`,
  `OneBlock/UnitsGeneralPositionSq.lean`), one statement for each of its conditions;
* then the statements at one parameter (`OneBlock/SkiplessHomogeneousRMSZeroEqAt.lean`) apply.

The paper's proof of "for generic parameters `h_1 ≠ 0` there" uses the resultant of `d_model`
quadratic forms, and it does not show that "two entries `h_a` and `h_b` of `h_1` have no common
factor" holds for generic parameters. The Lean route: the parameters at which the output of the
block vanishes at a row with an active unit lie in the image of a map of the parameter space
into itself whose derivative is nowhere invertible (one row `a_i` is solved for, and the map is
homogeneous of degree `0` in the row that takes its place), a set of measure zero; and the
condition on two entries is a resultant of two polynomials in one variable, on one line, which
is not zero for almost every parameter.

The functional dimension: the value of Lean's `funDim`, and a finite batch of the paper's inputs
(no normalized row vanishes, no hidden unit at its kink) with this rank; the two together are the
paper's statement.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

omit [Fintype d] [DecidableEq d] in
/-- Helper: an entry of a matrix that depends linearly on `y` is analytic in `y`. -/
private theorem analyticOnNhd_entry_ssq {P m n : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (F : P →ₗ[ℝ] Matrix m n ℝ) (a : m) (b : n) :
    AnalyticOnNhd ℝ (fun y => F y a b) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ a b).comp F)

omit [DecidableEq d] in
/-- Helper: `u w_i` is analytic in `y` when `W_read` is linear in `y`. -/
private theorem analyticOnNhd_dot_ssq {P q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (R : P →ₗ[ℝ] Matrix d q ℝ) (u : d → ℝ) (i : q) :
    AnalyticOnNhd ℝ (fun y => u ⬝ᵥ (R y)ᵀ i) Set.univ := by
  simp only [dotProduct, transpose_apply]
  exact Finset.analyticOnNhd_fun_sum _ fun a _ =>
    analyticOnNhd_const.mul (analyticOnNhd_entry_ssq R a i)

omit [DecidableEq d] in
/-- Helper: `w_i w_j` is analytic in `y` when `W_read` is linear in `y`. -/
private theorem analyticOnNhd_colDot_ssq {P q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (R : P →ₗ[ℝ] Matrix d q ℝ) (i j : q) :
    AnalyticOnNhd ℝ (fun y => (R y)ᵀ i ⬝ᵥ (R y)ᵀ j) Set.univ := by
  simp only [dotProduct, transpose_apply]
  exact Finset.analyticOnNhd_fun_sum _ fun a _ =>
    (analyticOnNhd_entry_ssq R a i).mul (analyticOnNhd_entry_ssq R a j)

omit [Fintype d] [DecidableEq d] in
/-- Helper: the resultant of two quadratics whose coefficients are analytic in `y` is analytic
in `y` (a polynomial in the six coefficients). -/
private theorem analyticOnNhd_quadRes_ssq {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {p₀ p₁ p₂ r₀ r₁ r₂ : P → ℝ} (h₀ : AnalyticOnNhd ℝ p₀ Set.univ)
    (h₁ : AnalyticOnNhd ℝ p₁ Set.univ) (h₂ : AnalyticOnNhd ℝ p₂ Set.univ)
    (h₃ : AnalyticOnNhd ℝ r₀ Set.univ) (h₄ : AnalyticOnNhd ℝ r₁ Set.univ)
    (h₅ : AnalyticOnNhd ℝ r₂ Set.univ) :
    AnalyticOnNhd ℝ (fun y => quadRes (p₀ y) (p₁ y) (p₂ y) (r₀ y) (r₁ y) (r₂ y)) Set.univ := by
  simp only [quadRes]
  exact (((h₀.mul h₅).sub (h₂.mul h₃)).pow 2).sub
    (((h₀.mul h₄).sub (h₁.mul h₃)).mul ((h₁.mul h₅).sub (h₂.mul h₄)))

omit [DecidableEq d] in
/-- Helper: the point `u₀ = |w_i|² w_j − (w_i w_j) w_i` of the hyperplane of the unit `i`, for
the columns `w` of `M`. -/
private def kinkPt_ssq {q : Type*} (M : Matrix d q ℝ) (i j : q) : d → ℝ :=
  (Mᵀ i ⬝ᵥ Mᵀ i) • Mᵀ j - (Mᵀ i ⬝ᵥ Mᵀ j) • Mᵀ i

omit [DecidableEq d] in
/-- Helper: `u₀ w_l = |w_i|² (w_j w_l) − (w_i w_j) (w_i w_l)`. -/
private theorem kinkPt_dot_ssq {q : Type*} (M : Matrix d q ℝ) (i j l : q) :
    kinkPt_ssq M i j ⬝ᵥ Mᵀ l
      = (Mᵀ i ⬝ᵥ Mᵀ i) * (Mᵀ j ⬝ᵥ Mᵀ l) - (Mᵀ i ⬝ᵥ Mᵀ j) * (Mᵀ i ⬝ᵥ Mᵀ l) := by
  simp only [kinkPt_ssq, sub_dotProduct, smul_dotProduct, smul_eq_mul]

omit [Fintype d] [DecidableEq d] in
/-- Helper: the determinant of a square matrix whose entries are analytic in `y` is analytic in
`y` (a finite sum of signed finite products of entries). -/
private theorem analyticOnNhd_det_ssq {P n : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [Fintype n] [DecidableEq n] (N : P → Matrix n n ℝ)
    (h : ∀ a b, AnalyticOnNhd ℝ (fun y => N y a b) Set.univ) :
    AnalyticOnNhd ℝ (fun y => (N y).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ => h (σ i) i)

omit [DecidableEq d] in
/-- Helper: the entries of `∑_{i∈S} 2 (u w_i) w_i a_i`. -/
private theorem sum_two_dot_apply_ssq {q : Type*} (u : d → ℝ) (R : Matrix d q ℝ)
    (W : Matrix q d ℝ) (S : Finset q) (b c : d) :
    (∑ i ∈ S, (2 * (u ⬝ᵥ Rᵀ i)) • vecMulVec (Rᵀ i) (W i)) b c
      = ∑ i ∈ S, 2 * (u ⬝ᵥ Rᵀ i) * (R b i * W i c) := by
  rw [Matrix.sum_apply]
  rfl

omit [Fintype d] [DecidableEq d] in
/-- Helper: `2 max(z, 0) M` is `2 z M` if `z > 0` and `0` otherwise. -/
private theorem reluSqDeriv_smul_ssq (z : ℝ) (M : Matrix d d ℝ) :
    reluSqDeriv z • M = if 0 < z then (2 * z) • M else 0 := by
  unfold reluSqDeriv
  split_ifs with h
  · rw [max_eq_left h.le]
  · rw [max_eq_right (not_lt.1 h), mul_zero, zero_smul]

section Generic

variable {P q : Type*} [Fintype q] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P] (μ : Measure P) [μ.IsAddHaarMeasure]
  (R : P →ₗ[ℝ] Matrix d q ℝ) (W : P →ₗ[ℝ] Matrix q d ℝ)

/-- Helper, condition 5: for two coordinates `e ≠ f`, at almost every `y` the resultant on the
line `t ↦ e_e + t e_f` of the entries `e`, `f` is not zero, for every set `S` of at least two
units. It is a polynomial in `y`, equal to `quadRes 1 0 0 0 0 1 = 1` where `w_p = a_p = e_e`,
`w_r = a_r = e_f` for two units `p ≠ r` of `S` and all other weights are `0`. -/
private theorem ae_quadRes_ssq (hRW : ∀ R₀ W₀, ∃ y, R y = R₀ ∧ W y = W₀) {e f : d}
    (hef : e ≠ f) :
    ∀ᵐ y ∂μ, ∀ S : Finset q, 2 ≤ S.card →
      quadRes (∑ i ∈ S, (Pi.single e 1 ⬝ᵥ (R y)ᵀ i) ^ 2 * W y i e)
        (2 * ∑ i ∈ S, (Pi.single e 1 ⬝ᵥ (R y)ᵀ i) * (Pi.single f 1 ⬝ᵥ (R y)ᵀ i) * W y i e)
        (∑ i ∈ S, (Pi.single f 1 ⬝ᵥ (R y)ᵀ i) ^ 2 * W y i e)
        (∑ i ∈ S, (Pi.single e 1 ⬝ᵥ (R y)ᵀ i) ^ 2 * W y i f)
        (2 * ∑ i ∈ S, (Pi.single e 1 ⬝ᵥ (R y)ᵀ i) * (Pi.single f 1 ⬝ᵥ (R y)ᵀ i) * W y i f)
        (∑ i ∈ S, (Pi.single f 1 ⬝ᵥ (R y)ᵀ i) ^ 2 * W y i f) ≠ 0 := by
  classical
  refine ae_all_iff.2 fun S => ?_
  by_cases hS : 2 ≤ S.card
  swap
  · exact Filter.Eventually.of_forall fun _ h => absurd h hS
  -- two units `p ≠ r` of `S`
  obtain ⟨p, hp, r, hr, hpr⟩ := Finset.one_lt_card.1 hS
  -- the point `w_p = a_p = e_e`, `w_r = a_r = e_f`, all other weights `0`
  obtain ⟨y₀, hR₀, hW₀⟩ :=
    hRW (Matrix.of fun a l => if (a = e ∧ l = p) ∨ (a = f ∧ l = r) then 1 else 0)
      (Matrix.of fun l b => if (l = p ∧ b = e) ∨ (l = r ∧ b = f) then 1 else 0)
  have hne : quadRes (∑ i ∈ S, (Pi.single e 1 ⬝ᵥ (R y₀)ᵀ i) ^ 2 * W y₀ i e)
        (2 * ∑ i ∈ S, (Pi.single e 1 ⬝ᵥ (R y₀)ᵀ i) * (Pi.single f 1 ⬝ᵥ (R y₀)ᵀ i) * W y₀ i e)
        (∑ i ∈ S, (Pi.single f 1 ⬝ᵥ (R y₀)ᵀ i) ^ 2 * W y₀ i e)
        (∑ i ∈ S, (Pi.single e 1 ⬝ᵥ (R y₀)ᵀ i) ^ 2 * W y₀ i f)
        (2 * ∑ i ∈ S, (Pi.single e 1 ⬝ᵥ (R y₀)ᵀ i) * (Pi.single f 1 ⬝ᵥ (R y₀)ᵀ i) * W y₀ i f)
        (∑ i ∈ S, (Pi.single f 1 ⬝ᵥ (R y₀)ᵀ i) ^ 2 * W y₀ i f) ≠ 0 := by
    rw [hR₀, hW₀]
    simp only [single_dotProduct, one_mul, transpose_apply, of_apply, hef, Ne.symm hef,
      true_and, false_and, and_true, and_false, or_false, false_or]
    simp only [quadRes, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hp, ↓reduceIte, hr, hpr, Ne.symm hpr,
      sub_zero, sub_self, one_ne_zero]
  -- the resultant is a polynomial in `y`
  have hu := analyticOnNhd_dot_ssq R (Pi.single e 1)
  have hv := analyticOnNhd_dot_ssq R (Pi.single f 1)
  have han : AnalyticOnNhd ℝ (fun y => quadRes (∑ i ∈ S, (Pi.single e 1 ⬝ᵥ (R y)ᵀ i) ^ 2 * W y i e)
        (2 * ∑ i ∈ S, (Pi.single e 1 ⬝ᵥ (R y)ᵀ i) * (Pi.single f 1 ⬝ᵥ (R y)ᵀ i) * W y i e)
        (∑ i ∈ S, (Pi.single f 1 ⬝ᵥ (R y)ᵀ i) ^ 2 * W y i e)
        (∑ i ∈ S, (Pi.single e 1 ⬝ᵥ (R y)ᵀ i) ^ 2 * W y i f)
        (2 * ∑ i ∈ S, (Pi.single e 1 ⬝ᵥ (R y)ᵀ i) * (Pi.single f 1 ⬝ᵥ (R y)ᵀ i) * W y i f)
        (∑ i ∈ S, (Pi.single f 1 ⬝ᵥ (R y)ᵀ i) ^ 2 * W y i f)) Set.univ :=
    analyticOnNhd_quadRes_ssq
    (Finset.analyticOnNhd_fun_sum _ fun i _ => ((hu i).pow 2).mul (analyticOnNhd_entry_ssq W i e))
    (analyticOnNhd_const.mul (Finset.analyticOnNhd_fun_sum _ fun i _ =>
      ((hu i).mul (hv i)).mul (analyticOnNhd_entry_ssq W i e)))
    (Finset.analyticOnNhd_fun_sum _ fun i _ => ((hv i).pow 2).mul (analyticOnNhd_entry_ssq W i e))
    (Finset.analyticOnNhd_fun_sum _ fun i _ => ((hu i).pow 2).mul (analyticOnNhd_entry_ssq W i f))
    (analyticOnNhd_const.mul (Finset.analyticOnNhd_fun_sum _ fun i _ =>
      ((hu i).mul (hv i)).mul (analyticOnNhd_entry_ssq W i f)))
    (Finset.analyticOnNhd_fun_sum _ fun i _ => ((hv i).pow 2).mul (analyticOnNhd_entry_ssq W i f))
  -- a polynomial that is not identically zero is nonzero at almost every `y`
  filter_upwards [ae_ne_zero_of_analytic μ han ⟨y₀, hne⟩] with y hy _
  exact hy

omit [DecidableEq d] in
/-- Helper, condition 4: for two units `i ≠ j` and two coordinates `e ≠ f`, at almost every `y`
the point `u₀ = |w_i|² w_j − (w_i w_j) w_i` of the hyperplane of `i` is on no other hyperplane,
and for every set `S ∋ j` of units without `i` the minor `e`, `f` of `a_i` and
`∑_{l∈S} (u₀ w_l)² a_l` is not zero. Both are polynomials in `y`, nonzero where `w_i = a_i = e_e`,
`w_l = e_f` for `l ≠ i`, `a_j = e_f` and the other rows of the write are `0`: there `u₀ = e_f`. -/
private theorem ae_kink_ssq (hRW : ∀ R₀ W₀, ∃ y, R y = R₀ ∧ W y = W₀) {e f : d} (hef : e ≠ f)
    {i j : q} (hij : i ≠ j) :
    ∀ᵐ y ∂μ, (∀ l, l ≠ i → kinkPt_ssq (R y) i j ⬝ᵥ (R y)ᵀ l ≠ 0) ∧
      ∀ S : Finset q, j ∈ S → i ∉ S →
        W y i e * ∑ l ∈ S, (kinkPt_ssq (R y) i j ⬝ᵥ (R y)ᵀ l) ^ 2 * W y l f
          - W y i f * ∑ l ∈ S, (kinkPt_ssq (R y) i j ⬝ᵥ (R y)ᵀ l) ^ 2 * W y l e ≠ 0 := by
  classical
  obtain ⟨y₀, hR₀, hW₀⟩ :=
    hRW (Matrix.of fun a l => if l = i then (if a = e then 1 else 0) else (if a = f then 1 else 0))
      (Matrix.of fun l b => if (l = i ∧ b = e) ∨ (l = j ∧ b = f) then 1 else 0)
  -- at this point `u₀ w_l = 1` for every `l ≠ i`
  have hk : ∀ l, l ≠ i → kinkPt_ssq (R y₀) i j ⬝ᵥ (R y₀)ᵀ l = 1 := by
    intro l hl
    rw [kinkPt_dot_ssq, hR₀]
    simp only [dotProduct, transpose_apply, of_apply, ↓reduceIte, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, Ne.symm hij, hl, Ne.symm hef, sub_zero]
  have han_k : ∀ l, AnalyticOnNhd ℝ (fun y => kinkPt_ssq (R y) i j ⬝ᵥ (R y)ᵀ l) Set.univ := by
    intro l
    simp only [kinkPt_dot_ssq]
    exact ((analyticOnNhd_colDot_ssq R i i).mul (analyticOnNhd_colDot_ssq R j l)).sub
      ((analyticOnNhd_colDot_ssq R i j).mul (analyticOnNhd_colDot_ssq R i l))
  have h1 : ∀ᵐ y ∂μ, ∀ l, l ≠ i → kinkPt_ssq (R y) i j ⬝ᵥ (R y)ᵀ l ≠ 0 := by
    refine ae_all_iff.2 fun l => ?_
    by_cases hl : l = i
    · exact Filter.Eventually.of_forall fun _ h => absurd hl h
    filter_upwards [ae_ne_zero_of_analytic μ (han_k l)
      ⟨y₀, by rw [hk l hl]; exact one_ne_zero⟩] with y hy _
    exact hy
  have h2 : ∀ᵐ y ∂μ, ∀ S : Finset q, j ∈ S → i ∉ S →
      W y i e * ∑ l ∈ S, (kinkPt_ssq (R y) i j ⬝ᵥ (R y)ᵀ l) ^ 2 * W y l f
        - W y i f * ∑ l ∈ S, (kinkPt_ssq (R y) i j ⬝ᵥ (R y)ᵀ l) ^ 2 * W y l e ≠ 0 := by
    refine ae_all_iff.2 fun S => ?_
    by_cases hS : j ∈ S ∧ i ∉ S
    swap
    · exact Filter.Eventually.of_forall fun _ h h' => absurd ⟨h, h'⟩ hS
    -- at the point, `∑_{l∈S} (u₀ w_l)² a_l = a_j = e_f`
    have hs : ∀ b, ∑ l ∈ S, (kinkPt_ssq (R y₀) i j ⬝ᵥ (R y₀)ᵀ l) ^ 2 * W y₀ l b = W y₀ j b := by
      intro b
      rw [Finset.sum_eq_single_of_mem j hS.1]
      · rw [hk j (Ne.symm hij), one_pow, one_mul]
      · intro l hl hlj
        have hli : l ≠ i := fun h => hS.2 (h ▸ hl)
        rw [hW₀]
        simp only [of_apply, hli, false_and, hlj, or_self, ↓reduceIte, mul_zero]
    have hne : W y₀ i e * ∑ l ∈ S, (kinkPt_ssq (R y₀) i j ⬝ᵥ (R y₀)ᵀ l) ^ 2 * W y₀ l f
        - W y₀ i f * ∑ l ∈ S, (kinkPt_ssq (R y₀) i j ⬝ᵥ (R y₀)ᵀ l) ^ 2 * W y₀ l e ≠ 0 := by
      rw [hs, hs, hW₀]
      simp only [of_apply, and_self, hij, hef, or_false, ↓reduceIte, Ne.symm hij, Ne.symm hef,
        or_true, mul_one, and_false, and_true, or_self, mul_zero, sub_zero, ne_eq, one_ne_zero,
        not_false_eq_true]
    have han : AnalyticOnNhd ℝ (fun y =>
        W y i e * ∑ l ∈ S, (kinkPt_ssq (R y) i j ⬝ᵥ (R y)ᵀ l) ^ 2 * W y l f
          - W y i f * ∑ l ∈ S, (kinkPt_ssq (R y) i j ⬝ᵥ (R y)ᵀ l) ^ 2 * W y l e) Set.univ :=
      ((analyticOnNhd_entry_ssq W i e).mul (Finset.analyticOnNhd_fun_sum _ fun l _ =>
        ((han_k l).pow 2).mul (analyticOnNhd_entry_ssq W l f))).sub
      ((analyticOnNhd_entry_ssq W i f).mul (Finset.analyticOnNhd_fun_sum _ fun l _ =>
        ((han_k l).pow 2).mul (analyticOnNhd_entry_ssq W l e)))
    filter_upwards [ae_ne_zero_of_analytic μ han ⟨y₀, hne⟩] with y hy _ _
    exact hy
  filter_upwards [h1, h2] with y hy1 hy2
  exact ⟨hy1, hy2⟩

/-- Helper, condition 6, for `d` nonempty: at almost every `y` there is a point `u` on no
hyperplane at which `∑_i 2 max(u w_i, 0) w_i a_i` is invertible. -/
private theorem ae_isUnit_det_ssq [Nonempty d] (hRW : ∀ R₀ W₀, ∃ y, R y = R₀ ∧ W y = W₀)
    (hq : Fintype.card d ≤ Fintype.card q) :
    ∀ᵐ y ∂μ, ∃ u : d → ℝ, (∀ i, u ⬝ᵥ (R y)ᵀ i ≠ 0) ∧
      IsUnit (∑ i, reluSqDeriv (u ⬝ᵥ (R y)ᵀ i) • vecMulVec ((R y)ᵀ i) (W y i)).det := by
  classical
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hq
  -- (A) the columns `ρ` of `W_read` are independent: the witness `w_{ρ a} = e_a`
  have hA : ∀ᵐ y ∂μ, ((R y).submatrix id ρ).det ≠ 0 := by
    obtain ⟨y₀, hR₀, -⟩ := hRW (Matrix.of fun a l => if l = ρ a then 1 else 0) 0
    have h1 : (R y₀).submatrix id ρ = 1 := by
      ext a b
      simp only [hR₀, submatrix_apply, id_eq, of_apply, ρ.injective.eq_iff, Matrix.one_apply]
      exact if_congr eq_comm rfl rfl
    exact ae_ne_zero_of_analytic μ (analyticOnNhd_det_ssq (fun y => (R y).submatrix id ρ)
      fun a b => analyticOnNhd_entry_ssq R a (ρ b)) ⟨y₀, by rw [h1, det_one]; exact one_ne_zero⟩
  -- (B) no column of `W_read` is zero: an entry, with the witness `W_read = 1`
  have hB : ∀ᵐ y ∂μ, ∀ i, (R y)ᵀ i ≠ 0 := by
    obtain ⟨y₀, hR₀, -⟩ := hRW (Matrix.of fun _ _ => 1) 0
    refine ae_all_iff.2 fun i => ?_
    filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_entry_ssq R (Classical.arbitrary d) i)
      ⟨y₀, by rw [hR₀]; exact one_ne_zero⟩] with y hy h0
    exact hy (congrFun h0 (Classical.arbitrary d))
  -- (C) for every `S ⊇ ρ(d)`, `det ∑_{i∈S} 2 (1 w_i) w_i a_i ≠ 0`: the witness `w_{ρ a} = a_{ρ a}
  -- = e_a`, the other weights `0`, where the matrix is `2`
  have hC : ∀ᵐ y ∂μ, ∀ S : Finset q, (∀ a, ρ a ∈ S) →
      (∑ i ∈ S, (2 * ((1 : d → ℝ) ⬝ᵥ (R y)ᵀ i)) • vecMulVec ((R y)ᵀ i) (W y i)).det ≠ 0 := by
    refine ae_all_iff.2 fun S => ?_
    by_cases hS : ∀ a, ρ a ∈ S
    swap
    · exact Filter.Eventually.of_forall fun _ h => absurd h hS
    obtain ⟨y₀, hR₀, hW₀⟩ := hRW (Matrix.of fun a l => if l = ρ a then 1 else 0)
      (Matrix.of fun l a => if l = ρ a then 1 else 0)
    have h2 : ∑ i ∈ S, (2 * ((1 : d → ℝ) ⬝ᵥ (R y₀)ᵀ i)) • vecMulVec ((R y₀)ᵀ i) (W y₀ i)
        = (2 : ℝ) • (1 : Matrix d d ℝ) := by
      ext b c
      rw [sum_two_dot_apply_ssq, Finset.sum_eq_single_of_mem (ρ b) (hS b)]
      · simp only [dotProduct, Pi.one_apply, hR₀, transpose_apply, of_apply, ρ.injective.eq_iff,
          mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, hW₀,
          Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      · intro i _ hne
        simp only [hR₀, transpose_of, of_apply, hne, ↓reduceIte, hW₀, mul_ite, mul_one, mul_zero,
          ite_self]
    have han := analyticOnNhd_det_ssq (fun y =>
      ∑ i ∈ S, (2 * ((1 : d → ℝ) ⬝ᵥ (R y)ᵀ i)) • vecMulVec ((R y)ᵀ i) (W y i)) fun b c => by
        simp only [sum_two_dot_apply_ssq]
        exact Finset.analyticOnNhd_fun_sum _ fun i _ =>
          (analyticOnNhd_const.mul (analyticOnNhd_dot_ssq R 1 i)).mul
            ((analyticOnNhd_entry_ssq R b i).mul (analyticOnNhd_entry_ssq W i c))
    filter_upwards [ae_ne_zero_of_analytic μ han ⟨y₀, by
      rw [h2, det_smul, det_one, mul_one]; exact pow_ne_zero _ two_ne_zero⟩] with y hy _
    exact hy
  filter_upwards [hA, hB, hC] with y hA hB hC
  -- for this `y`, the functions `u ↦ u c` and `D_S(u) = det ∑_{i∈S} 2 (u w_i) w_i a_i`
  have hlin : ∀ c : d → ℝ, AnalyticOnNhd ℝ (fun u : d → ℝ => u ⬝ᵥ c) Set.univ := fun c =>
    analyticOnNhd_linear
      { toFun := fun u => u ⬝ᵥ c
        map_add' := fun u v => add_dotProduct u v c
        map_smul' := fun r u => smul_dotProduct r u c }
  have hD : ∀ S : Finset q, AnalyticOnNhd ℝ (fun u : d → ℝ =>
      (∑ i ∈ S, (2 * (u ⬝ᵥ (R y)ᵀ i)) • vecMulVec ((R y)ᵀ i) (W y i)).det) Set.univ :=
    fun S => analyticOnNhd_det_ssq _ fun b c => by
      simp only [sum_two_dot_apply_ssq]
      exact Finset.analyticOnNhd_fun_sum _ fun i _ =>
        (analyticOnNhd_const.mul (hlin _)).mul analyticOnNhd_const
  -- at almost every `u`: no `u w_i` is zero (`w_i ≠ 0`), and `D_S(u) ≠ 0` (`D_S(1) ≠ 0`)
  have hgood : ∀ᵐ u ∂(volume : Measure (d → ℝ)), (∀ i, u ⬝ᵥ (R y)ᵀ i ≠ 0) ∧
      ∀ S : Finset q, (∀ a, ρ a ∈ S) →
        (∑ i ∈ S, (2 * (u ⬝ᵥ (R y)ᵀ i)) • vecMulVec ((R y)ᵀ i) (W y i)).det ≠ 0 := by
    have h1 : ∀ᵐ u ∂(volume : Measure (d → ℝ)), ∀ i, u ⬝ᵥ (R y)ᵀ i ≠ 0 :=
      ae_all_iff.2 fun i => ae_ne_zero_of_analytic _ (hlin _)
        ⟨(R y)ᵀ i, fun h => hB i (dotProduct_self_eq_zero.1 h)⟩
    have h2 : ∀ᵐ u ∂(volume : Measure (d → ℝ)), ∀ S : Finset q, (∀ a, ρ a ∈ S) →
        (∑ i ∈ S, (2 * (u ⬝ᵥ (R y)ᵀ i)) • vecMulVec ((R y)ᵀ i) (W y i)).det ≠ 0 := by
      refine ae_all_iff.2 fun S => ?_
      by_cases hS : ∀ a, ρ a ∈ S
      swap
      · exact Filter.Eventually.of_forall fun _ h => absurd h hS
      filter_upwards [ae_ne_zero_of_analytic _ (hD S) ⟨1, hC S hS⟩] with u hu _
      exact hu
    exact h1.and h2
  -- the open cone `V` where the units `ρ a` are active is not empty: `u* w_{ρ a} = 1`
  set V := ⋂ a, {u : d → ℝ | 0 < u ⬝ᵥ (R y)ᵀ (ρ a)}
  have hV : IsOpen V := isOpen_iInter_of_finite fun a =>
    isOpen_lt continuous_const (continuousOn_univ.1 (hlin _).continuousOn)
  have hVne : V.Nonempty := by
    refine ⟨(1 : d → ℝ) ᵥ* ((R y).submatrix id ρ)⁻¹, Set.mem_iInter.2 fun a => ?_⟩
    have h1 : (1 : d → ℝ) ᵥ* ((R y).submatrix id ρ)⁻¹ ᵥ* (R y).submatrix id ρ = 1 := by
      rw [vecMul_vecMul, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hA), vecMul_one]
    show 0 < ((1 : d → ℝ) ᵥ* ((R y).submatrix id ρ)⁻¹ ᵥ* (R y).submatrix id ρ) a
    rw [h1]
    exact one_pos
  -- a good `u` in `V`; its active set `S` contains `ρ(d)`
  have : (ae ((volume : Measure (d → ℝ)).restrict V)).NeBot :=
    ae_neBot.2 (by rw [Ne, Measure.restrict_eq_zero]; exact hV.measure_ne_zero volume hVne)
  obtain ⟨u, huV, hu1, hu2⟩ :=
    ((ae_restrict_mem hV.measurableSet).and (ae_restrict_of_ae hgood)).exists
  refine ⟨u, hu1, ?_⟩
  have hS : ∀ a, ρ a ∈ Finset.univ.filter fun i => 0 < u ⬝ᵥ (R y)ᵀ i :=
    fun a => Finset.mem_filter.2 ⟨Finset.mem_univ _, Set.mem_iInter.1 huV a⟩
  -- there `2 max(u w_i, 0) = 2 u w_i` on `S` and `0` off `S`
  have heq : ∑ i, reluSqDeriv (u ⬝ᵥ (R y)ᵀ i) • vecMulVec ((R y)ᵀ i) (W y i)
      = ∑ i ∈ Finset.univ.filter (fun i => 0 < u ⬝ᵥ (R y)ᵀ i),
        (2 * (u ⬝ᵥ (R y)ᵀ i)) • vecMulVec ((R y)ᵀ i) (W y i) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun i _ => reluSqDeriv_smul_ssq _ _
  rw [heq]
  exact isUnit_iff_ne_zero.2 (hu2 _ hS)

end Generic

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read and the write of the block take every value, at the parameter with
`E = D = 0`. -/
private theorem exists_params_ssq {σ : ℝ → ℝ} (R₀ : Matrix d (hid 0) ℝ)
    (W₀ : Matrix (hid 0) d ℝ) :
    ∃ θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut,
      Params.linRead 0 θ = R₀ ∧ Params.linWrite 0 θ = W₀ :=
  ⟨⟨0, Pi.single (M := fun ℓ => Matrix d (hid ℓ) ℝ) 0 R₀,
      Pi.single (M := fun ℓ => Matrix (hid ℓ) d ℝ) 0 W₀, 0⟩,
    Pi.single_eq_same (M := fun ℓ => Matrix d (hid ℓ) ℝ) 0 R₀,
    Pi.single_eq_same (M := fun ℓ => Matrix (hid ℓ) d ℝ) 0 W₀⟩

omit [Fintype d] [DecidableEq d] in
/-- Helper: `max(z, 0)² a` is `z² a` if `z > 0` and `0` otherwise. -/
private theorem reluSq_smul_ssq (z : ℝ) (a : d → ℝ) :
    reluSq z • a = if 0 < z then z ^ 2 • a else 0 := by
  unfold reluSq
  split_ifs with h
  · rw [max_eq_left h.le]
  · rw [max_eq_right (not_lt.1 h), zero_pow two_ne_zero, zero_smul]

omit [Fintype d] [DecidableEq d] in
/-- Helper: `∑_i max(u w_i, 0)² a_i = ∑_{i∈S} (u w_i)² a_i` for the set `S` of units active at
`u`. -/
private theorem sum_reluSq_eq_ssq {q : Type*} [Fintype q] (z : q → ℝ) (a : q → d → ℝ) :
    ∑ i, reluSq (z i) • a i = ∑ i ∈ Finset.univ.filter (fun i => 0 < z i), z i ^ 2 • a i := by
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun i _ => reluSq_smul_ssq (z i) (a i)

/-! ### `h_1 ≠ 0` where a unit is active: the image of a map with a degenerate derivative -/

/-- Helper: the parameter whose only nonzero weight is the row `i₀` of the write, equal to
`v`. -/
private def rowParam_ssq {σ : ℝ → ℝ} [DecidableEq (hid 0)] (i₀ : hid 0) :
    (d → ℝ) →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut where
  toFun v := ⟨0, 0, Pi.single (M := fun ℓ => Matrix (hid ℓ) d ℝ) 0
    (Matrix.of fun l => if l = i₀ then v else 0), 0⟩
  map_add' v v' := by
    refine Params.ext' (add_zero 0).symm (fun _ => (add_zero 0).symm) (fun ℓ => ?_)
      (add_zero 0).symm
    obtain rfl := Subsingleton.elim ℓ 0
    show Pi.single (M := fun ℓ => Matrix (hid ℓ) d ℝ) 0
        (Matrix.of fun l => if l = i₀ then v + v' else 0) 0
      = Pi.single (M := fun ℓ => Matrix (hid ℓ) d ℝ) 0
          (Matrix.of fun l => if l = i₀ then v else 0) 0
        + Pi.single (M := fun ℓ => Matrix (hid ℓ) d ℝ) 0
          (Matrix.of fun l => if l = i₀ then v' else 0) 0
    simp only [Pi.single_eq_same (M := fun ℓ => Matrix (hid ℓ) d ℝ)]
    ext l b
    by_cases h : l = i₀ <;>
      simp only [Fin.isValue, h, of_apply, ↓reduceIte, Pi.add_apply, Matrix.add_apply,
        Pi.zero_apply, add_zero]
  map_smul' c v := by
    refine Params.ext' (smul_zero c).symm (fun _ => (smul_zero c).symm) (fun ℓ => ?_)
      (smul_zero c).symm
    obtain rfl := Subsingleton.elim ℓ 0
    show Pi.single (M := fun ℓ => Matrix (hid ℓ) d ℝ) 0
        (Matrix.of fun l => if l = i₀ then c • v else 0) 0
      = c • Pi.single (M := fun ℓ => Matrix (hid ℓ) d ℝ) 0
        (Matrix.of fun l => if l = i₀ then v else 0) 0
    simp only [Pi.single_eq_same (M := fun ℓ => Matrix (hid ℓ) d ℝ)]
    ext l b
    by_cases h : l = i₀ <;>
      simp only [Fin.isValue, h, of_apply, ↓reduceIte, Pi.smul_apply, smul_eq_mul,
        Matrix.smul_apply, Pi.zero_apply, mul_zero]

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: adding `rowParam_ssq i₀ v` does not change the read. -/
private theorem read_add_rowParam_ssq {σ : ℝ → ℝ} [DecidableEq (hid 0)] (i₀ : hid 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (v : d → ℝ) :
    (θ + rowParam_ssq i₀ v).read 0 = θ.read 0 :=
  add_zero _

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: adding `rowParam_ssq i₀ v` adds `v` to the row `i₀` of the write. -/
private theorem write_add_rowParam_ssq {σ : ℝ → ℝ} [DecidableEq (hid 0)] (i₀ : hid 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (v : d → ℝ)
    (l : hid 0) :
    (θ + rowParam_ssq i₀ v).write 0 l = θ.write 0 l + if l = i₀ then v else 0 := by
  show θ.write 0 l + Pi.single (M := fun ℓ => Matrix (hid ℓ) d ℝ) 0
    (Matrix.of fun l => if l = i₀ then v else 0) 0 l = _
  rw [Pi.single_eq_same (M := fun ℓ => Matrix (hid ℓ) d ℝ)]
  rfl

/-- Helper: `−∑_{i∈S, i≠i₀} (u w_i)² a_i`, with `u` the row `i₀` of the write. -/
private def solveRow_ssq {σ : ℝ → ℝ} [DecidableEq (hid 0)] (S : Finset (hid 0)) (i₀ : hid 0)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) : d → ℝ :=
  -∑ i ∈ S.erase i₀, (θ.write 0 i₀ ⬝ᵥ (θ.read 0)ᵀ i) ^ 2 • θ.write 0 i

/-- Helper: the map `Ψ_{S,i₀}` of the parameters that puts `solveRow_ssq` in the row `i₀` of the
write. -/
private noncomputable def solveMap_ssq {σ : ℝ → ℝ} [DecidableEq (hid 0)] (S : Finset (hid 0))
    (i₀ : hid 0) (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) :
    Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut :=
  θ + rowParam_ssq i₀ (solveRow_ssq S i₀ θ - θ.write 0 i₀)

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `u w_i`, with `u` the row `i₀` of the write, is analytic in the parameters. -/
private theorem analyticOnNhd_rowDot_ssq {σ : ℝ → ℝ} (i₀ i : hid 0) :
    AnalyticOnNhd ℝ (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
      θ.write 0 i₀ ⬝ᵥ (θ.read 0)ᵀ i) Set.univ := by
  simp only [dotProduct, transpose_apply]
  exact Finset.analyticOnNhd_fun_sum _ fun a _ =>
    (analyticOnNhd_entry_ssq (Params.linWrite (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid)
      (dIn := dIn) (dOut := dOut) 0) i₀ a).mul
      (analyticOnNhd_entry_ssq (Params.linRead (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid)
        (dIn := dIn) (dOut := dOut) 0) a i)

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: `Ψ_{S,i₀}` is differentiable (a polynomial map). -/
private theorem differentiable_solveMap_ssq {σ : ℝ → ℝ} [DecidableEq (hid 0)]
    (S : Finset (hid 0)) (i₀ : hid 0) :
    Differentiable ℝ
      (solveMap_ssq (T := T) (d := d) (σ := σ) (dIn := dIn) (dOut := dOut) S i₀) := by
  -- the rows of the write
  have hrow : ∀ l, Differentiable ℝ
      (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut => θ.write 0 l) :=
    fun l => differentiable_pi.2 fun b => differentiableOn_univ.1
      (analyticOnNhd_entry_ssq (Params.linWrite (A := Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid)
        (dIn := dIn) (dOut := dOut) 0) l b).differentiableOn
  have hdot : ∀ i, Differentiable ℝ
      (fun θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut =>
        θ.write 0 i₀ ⬝ᵥ (θ.read 0)ᵀ i) :=
    fun i => differentiableOn_univ.1 (analyticOnNhd_rowDot_ssq i₀ i).differentiableOn
  have hsolve : Differentiable ℝ
      (solveRow_ssq (T := T) (d := d) (σ := σ) (dIn := dIn) (dOut := dOut) S i₀) :=
    (Differentiable.fun_sum fun i _ => ((hdot i).fun_pow 2).fun_smul (hrow i)).fun_neg
  have hι := (LinearMap.toContinuousLinearMap
    (rowParam_ssq (T := T) (d := d) (σ := σ) (dIn := dIn) (dOut := dOut) i₀)).differentiable
  have hc := hι.comp (hsolve.sub (hrow i₀))
  exact differentiable_id.add hc

omit [Fintype T] [Nonempty T] [DecidableEq d] in
/-- Helper: the parameters with `u w_{i₀} = 1`, for `u` the row `i₀` of the write, are a null
set (the zero set of a polynomial that is `−1` at `0`). -/
private theorem measure_levelSet_ssq {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (i₀ : hid 0) :
    μ {θ | θ.write 0 i₀ ⬝ᵥ (θ.read 0)ᵀ i₀ - 1 = 0} = 0 :=
  measure_zeroSet_of_analytic μ ((analyticOnNhd_rowDot_ssq i₀ i₀).sub analyticOnNhd_const)
    ⟨0, by
      show (0 : d → ℝ) ⬝ᵥ 0 - 1 ≠ 0
      rw [zero_dotProduct]
      norm_num⟩

/-- **"For generic parameters `h_1 ≠ 0` there", for ReLU² units:** at almost every parameter of
one MLP block, `∑_i max(u w_i, 0)² a_i ≠ 0` at every `u` at which a unit is active. -/
theorem ae_forall_sum_reluSq_ne_zero {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ u : d → ℝ, (∃ i, 0 < u ⬝ᵥ (θ.read 0)ᵀ i) →
      ∑ i, reluSq (u ⬝ᵥ (θ.read 0)ᵀ i) • θ.write 0 i ≠ 0 := by
  classical
  rw [ae_iff]
  -- the bad parameters lie in the union of the images of the null sets `u w_{i₀} = 1` under the
  -- differentiable maps `Ψ_{S,i₀}`
  refine measure_mono_null (fun θ' hθ' => ?_) (measure_iUnion_null fun p : Finset (hid 0) × hid 0 =>
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ
      (differentiable_solveMap_ssq p.1 p.2).differentiableOn (measure_levelSet_ssq μ p.2))
  simp only [Set.mem_ofPred_eq, not_forall, not_not] at hθ'
  obtain ⟨u, ⟨i₀, hi₀⟩, hsum⟩ := hθ'
  set w := (θ'.read 0)ᵀ with hw
  set S := Finset.univ.filter fun i => 0 < u ⬝ᵥ w i
  set c := u ⬝ᵥ w i₀
  -- the point `u' = u / (u w_{i₀})`, with `u' w_{i₀} = 1` and the same active units
  set u' := c⁻¹ • u
  have hu' : ∀ i, u' ⬝ᵥ w i = c⁻¹ * (u ⬝ᵥ w i) := fun i => by rw [smul_dotProduct, smul_eq_mul]
  have hu'₀ : u' ⬝ᵥ w i₀ = 1 := by rw [hu']; exact inv_mul_cancel₀ hi₀.ne'
  -- `∑_{i∈S} (u' w_i)² a_i = 0`, so `a_{i₀} = −∑_{i∈S, i≠i₀} (u' w_i)² a_i`
  have hS : ∑ i ∈ S, (u ⬝ᵥ w i) ^ 2 • θ'.write 0 i = 0 :=
    (sum_reluSq_eq_ssq (q := hid 0) (fun i => u ⬝ᵥ w i) (fun i => θ'.write 0 i)).symm.trans hsum
  have hS' : ∑ i ∈ S, (u' ⬝ᵥ w i) ^ 2 • θ'.write 0 i = 0 := by
    simp only [hu', mul_pow, mul_smul]
    rw [← Finset.smul_sum, hS, smul_zero]
  have hi₀S : i₀ ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi₀⟩
  have ha : -∑ i ∈ S.erase i₀, (u' ⬝ᵥ w i) ^ 2 • θ'.write 0 i = θ'.write 0 i₀ := by
    rw [← Finset.add_sum_erase S _ hi₀S, hu'₀, one_pow, one_smul] at hS'
    exact (eq_neg_of_add_eq_zero_left hS').symm
  -- `θ'` is `Ψ_{S,i₀}(θ)` for `θ = θ'` with the row `i₀` of the write replaced by `u'`
  set θ := θ' + rowParam_ssq i₀ (u' - θ'.write 0 i₀)
  have hθr : θ.read 0 = θ'.read 0 := read_add_rowParam_ssq i₀ θ' _
  have hθw₀ : θ.write 0 i₀ = u' := by
    rw [write_add_rowParam_ssq, ite_eq_left rfl]
    abel
  have hθw : ∀ i, i ≠ i₀ → θ.write 0 i = θ'.write 0 i := fun i hi => by
    rw [write_add_rowParam_ssq, ite_eq_right hi, add_zero]
  refine Set.mem_iUnion.2 ⟨(S, i₀), θ, ?_, ?_⟩
  · show θ.write 0 i₀ ⬝ᵥ (θ.read 0)ᵀ i₀ - 1 = 0
    rw [hθw₀, hθr, hu'₀, sub_self]
  · have hrow : solveRow_ssq S i₀ θ = θ'.write 0 i₀ := by
      rw [← ha, solveRow_ssq, hθw₀, hθr]
      refine congrArg Neg.neg (Finset.sum_congr rfl fun i hi => ?_)
      rw [hθw i (Finset.ne_of_mem_erase hi)]
    show θ + rowParam_ssq i₀ (solveRow_ssq S i₀ θ - θ.write 0 i₀) = θ'
    rw [hrow, hθw₀, add_assoc, ← map_add, sub_add_sub_cancel, sub_self, map_zero, add_zero]

/-- **"`h_1(x_0)` is not parallel to `a_i`", for ReLU² units:** at almost every parameter of one
MLP block with at least two hidden units and `d ≥ 2`, every unit `i` has a point `u_0` of its
hyperplane, on no other hyperplane, at which `∑_j max(u_0 w_j, 0)² a_j` is not a multiple of
`a_i`. -/
theorem ae_exists_kink_point_reluSq {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hq : 2 ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∀ i, ∃ u₀ : d → ℝ, u₀ ⬝ᵥ (θ.read 0)ᵀ i = 0 ∧
      (∀ j, j ≠ i → u₀ ⬝ᵥ (θ.read 0)ᵀ j ≠ 0) ∧
      ∀ r : ℝ, ∑ j, reluSq (u₀ ⬝ᵥ (θ.read 0)ᵀ j) • θ.write 0 j ≠ r • θ.write 0 i := by
  classical
  obtain ⟨e, f, hef⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  -- for every unit `i` another unit `J i`
  have hJ : ∀ i : hid 0, ∃ j, j ≠ i := fun i => Fintype.exists_ne_of_one_lt_card (by omega) i
  choose J hJ using hJ
  have hae : ∀ᵐ θ ∂μ, ∀ i,
      (∀ l, l ≠ i → kinkPt_ssq (θ.read 0) i (J i) ⬝ᵥ (θ.read 0)ᵀ l ≠ 0) ∧
      ∀ S : Finset (hid 0), J i ∈ S → i ∉ S →
        θ.write 0 i e * ∑ l ∈ S, (kinkPt_ssq (θ.read 0) i (J i) ⬝ᵥ (θ.read 0)ᵀ l) ^ 2
            * θ.write 0 l f
          - θ.write 0 i f * ∑ l ∈ S, (kinkPt_ssq (θ.read 0) i (J i) ⬝ᵥ (θ.read 0)ᵀ l) ^ 2
            * θ.write 0 l e ≠ 0 :=
    ae_all_iff.2 fun i =>
      ae_kink_ssq (q := hid 0) μ _ _ (exists_params_ssq (σ := σ)) hef (hJ i).symm
  filter_upwards [hae] with θ hθ i
  obtain ⟨h1, h2⟩ := hθ i
  -- `u₀` or `-u₀`, the sign chosen so that the unit `J i` is active
  set u₀ := kinkPt_ssq (θ.read 0) i (J i)
  set w := (θ.read 0)ᵀ
  set c : ℝ := if 0 < u₀ ⬝ᵥ w (J i) then 1 else -1 with hc
  have hc2 : c ^ 2 = 1 := by rw [hc]; split_ifs <;> norm_num
  have hc0 : c ≠ 0 := by rw [hc]; split_ifs <;> norm_num
  have hdot : ∀ l, (c • u₀) ⬝ᵥ w l = c * (u₀ ⬝ᵥ w l) := fun l => by
    rw [smul_dotProduct, smul_eq_mul]
  have hi : u₀ ⬝ᵥ w i = 0 := by
    rw [kinkPt_dot_ssq, dotProduct_comm (w (J i)) (w i)]
    ring
  have hj : 0 < (c • u₀) ⬝ᵥ w (J i) := by
    rw [hdot, hc]
    split_ifs with h
    · rwa [one_mul]
    · have := h1 (J i) (hJ i)
      have : u₀ ⬝ᵥ w (J i) < 0 := lt_of_le_of_ne (not_lt.1 h) this
      linarith
  refine ⟨c • u₀, by rw [hdot, hi, mul_zero], fun l hl => by
    rw [hdot]; exact mul_ne_zero hc0 (h1 l hl), fun r hr => ?_⟩
  -- the active set `S` at `c u₀` contains `J i` and not `i`
  set S := Finset.univ.filter (fun l => 0 < (c • u₀) ⬝ᵥ w l)
  have hjS : J i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩
  have hiS : i ∉ S := fun h => by
    have := (Finset.mem_filter.1 h).2
    rw [hdot, hi, mul_zero] at this
    exact lt_irrefl 0 this
  have hr' : ∑ l ∈ S, ((c • u₀) ⬝ᵥ w l) ^ 2 • θ.write 0 l = r • θ.write 0 i :=
    (sum_reluSq_eq_ssq (q := hid 0) (fun l => (c • u₀) ⬝ᵥ w l) (fun l => θ.write 0 l)).symm.trans
      hr
  -- the entries `e`, `f` of `h_1 = r a_i`
  have hb : ∀ b, ∑ l ∈ S, (u₀ ⬝ᵥ w l) ^ 2 * θ.write 0 l b = r * θ.write 0 i b := by
    intro b
    have := congrFun hr' b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hdot, mul_pow, hc2, one_mul] at this
    exact this
  apply h2 S hjS hiS
  rw [hb e, hb f]
  ring

/-- **"Two entries `h_a` and `h_b` of `h_1` have no common factor", for ReLU² units, on a line:**
at almost every parameter of one MLP block with `d ≥ 2`, for every set `S` of at least two units
there are a line `t ↦ u + t v` and two entries `e`, `f` for which the resultant of the
polynomials `t ↦ ∑_{i∈S} ((u + t v) w_i)² a_{i e}` and `t ↦ ∑_{i∈S} ((u + t v) w_i)² a_{i f}` is
not zero. -/
theorem ae_exists_quadRes_ne_zero {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ∀ S : Finset (hid 0), 2 ≤ S.card → ∃ (u v : d → ℝ) (e f : d),
      quadRes (∑ i ∈ S, (u ⬝ᵥ (θ.read 0)ᵀ i) ^ 2 * θ.write 0 i e)
        (2 * ∑ i ∈ S, (u ⬝ᵥ (θ.read 0)ᵀ i) * (v ⬝ᵥ (θ.read 0)ᵀ i) * θ.write 0 i e)
        (∑ i ∈ S, (v ⬝ᵥ (θ.read 0)ᵀ i) ^ 2 * θ.write 0 i e)
        (∑ i ∈ S, (u ⬝ᵥ (θ.read 0)ᵀ i) ^ 2 * θ.write 0 i f)
        (2 * ∑ i ∈ S, (u ⬝ᵥ (θ.read 0)ᵀ i) * (v ⬝ᵥ (θ.read 0)ᵀ i) * θ.write 0 i f)
        (∑ i ∈ S, (v ⬝ᵥ (θ.read 0)ᵀ i) ^ 2 * θ.write 0 i f) ≠ 0 := by
  -- two coordinates `e ≠ f`, and the line `t ↦ e_e + t e_f` for every `S`
  obtain ⟨e, f, hef⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  filter_upwards [ae_quadRes_ssq (q := hid 0) μ _ _ (exists_params_ssq (σ := σ)) hef]
    with θ hθ S hS
  exact ⟨Pi.single e 1, Pi.single f 1, e, f, hθ S hS⟩

omit [Fintype T] [Nonempty T] in
/-- Helper: condition 6 at almost every parameter, for `d` nonempty. (For `d` empty and at least
one hidden unit the statement below is false: `u ⬝ᵥ w_i = 0` for every `u`.) -/
private theorem ae_exists_isUnit_det_reluSqDeriv_ssq [Nonempty d] {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∃ u : d → ℝ, (∀ i, u ⬝ᵥ (θ.read 0)ᵀ i ≠ 0) ∧
      IsUnit (∑ i, reluSqDeriv (u ⬝ᵥ (θ.read 0)ᵀ i)
        • Matrix.vecMulVec ((θ.read 0)ᵀ i) (θ.write 0 i)).det := by
  have h := ae_isUnit_det_ssq (q := hid 0) μ _ _ (exists_params_ssq (σ := σ)) hcard
  exact h

/-- **"`h_1` takes all values in an open set", for ReLU² units, the derivative:** at almost every
parameter of one MLP block of width at least `d`, there is a point `u` on no hyperplane at which
the derivative `v ↦ ∑_i 2 max(u w_i, 0) (v w_i) a_i` of the map of the block is invertible. -/
theorem ae_exists_isUnit_det_reluSqDeriv {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∃ u : d → ℝ, (∀ i, u ⬝ᵥ (θ.read 0)ᵀ i ≠ 0) ∧
      IsUnit (∑ i, reluSqDeriv (u ⬝ᵥ (θ.read 0)ᵀ i)
        • Matrix.vecMulVec ((θ.read 0)ᵀ i) (θ.write 0 i)).det := by
  sorry

/-- **The conditions "for generic parameters" of the proof of Theorem B.1 (iv), "The skipless
network: equality", for ReLU²:** for one MLP block with at least `d ≥ 2` hidden units, at almost
every parameter the hidden units are in general position in the sense for ReLU². -/
theorem ae_unitsGeneralPositionSq {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, UnitsGeneralPositionSq (θ.read 0) (θ.write 0) := by
  -- the first two conditions are among those for ReLU; the other four are the statements above
  filter_upwards [ae_unitsGeneralPosition μ hd hcard, ae_forall_sum_reluSq_ne_zero μ,
    ae_exists_kink_point_reluSq μ hd (hd.trans hcard), ae_exists_quadRes_ne_zero μ hd,
    ae_exists_isUnit_det_reluSqDeriv μ hcard] with θ hG h3 h4 h5 h6
  refine ⟨hG.1, fun i h0 => ?_, h3, h4, h5, h6⟩
  -- one row of `W_write` is a linearly independent family, so it is not zero
  have hli := hG.2.1 {i} (by rw [Finset.card_singleton]; omega)
  exact hli.ne_zero ⟨i, Finset.mem_singleton_self i⟩ h0

omit [Nonempty T] in
/-- Helper: at almost every parameter `E` and `D` have rank `d` (`d_in, d_out ≥ d`, width at
least `d`); a copy of `ae_rank_E_D_srw`. -/
private theorem ae_rank_E_D_ssq {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d ∧ θ.D.rank = Fintype.card d := by
  obtain ⟨ρD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  filter_upwards [ae_rank_E_write μ hdIn
      (fun ℓ => by obtain rfl := Subsingleton.elim ℓ 0; exact hcard),
    ae_isUnit_det_submatrix μ] with θ h1 h2
  exact ⟨h1.1, rank_eq_card_of_isUnit_det θ.D ρD (h2.2.1 ρD)⟩

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, "with equality", for one ReLU²
block of width at least `d`:** for `d_in, d_out ≥ d ≥ 2` and at least `d` hidden units, at almost
every parameter `funDim = P − d² − (d(d−1)/2 + 1) − s`. -/
theorem ae_funDim_reluSq_oneBlock_skipless_rmsNorm_zero_of_le
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_D_ssq μ hdIn hdOut hcard,
    ae_unitsGeneralPositionSq μ hd hcard] with θ hθ hG
  obtain ⟨hR, hW, hc⟩ := rank_of_unitsGeneralPositionSq hd hG
  exact funDim_mlp_oneBlock_rescale_skipless_rmsNorm_zero_of_unitsParallelAt
    (fun z _ => hasDerivAt_reluSq z) reluSq_homogeneous θ hd hθ.1 hθ.2 hR hW hc
    (reluSq_unitsParallelAt_of_unitsGeneralPositionSq θ.E hd hθ.1 hG)
    (exists_open_reluSq_of_unitsGeneralPositionSq θ.E hθ.1 hG)

/-- **The same in the paper's own sense:** at almost every parameter a finite batch of inputs at
which no normalized row vanishes and no hidden unit sits at its kink, on which the Jacobian has
the rank `P − d² − d(d−1)/2 − 1 − s`. -/
theorem ae_exists_jacobianRank_reluSq_oneBlock_skipless_rmsNorm_zero_of_le
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ skiplessZeroDomain (Arch.mlp reluSq (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp reluSq (rmsNorm 0) hid) 0 X θ
          + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
            + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_D_ssq μ hdIn hdOut hcard,
    ae_unitsGeneralPositionSq μ hd hcard] with θ hθ hG
  obtain ⟨hR, hW, hc⟩ := rank_of_unitsGeneralPositionSq hd hG
  exact exists_jacobianRank_mlp_oneBlock_rescale_skipless_rmsNorm_zero_of_unitsParallelAt
    (fun z _ => hasDerivAt_reluSq z) reluSq_homogeneous θ hd hθ.1 hθ.2 hR hW hc
    (reluSq_unitsParallelAt_of_unitsGeneralPositionSq θ.E hd hθ.1 hG)
    (exists_open_reluSq_of_unitsGeneralPositionSq θ.E hθ.1 hG)

/-- **Theorem B.1 (iv) of the skips paper, "by exactly `d_model²` for ReLU and ReLU² blocks", for
one ReLU² block of width at least `d`:** at almost every parameter `funDim` of the residual
network is `funDim` of the skipless network plus `d²`. -/
theorem ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero_eq_add_of_le
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 1 θ
      = funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ + Fintype.card d ^ 2 := by
  have : Nonempty (hid 0) := Fintype.card_pos_iff.1 (by omega)
  filter_upwards [ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero μ hd hdIn hdOut,
    ae_funDim_reluSq_oneBlock_skipless_rmsNorm_zero_of_le μ hd hdIn hdOut hcard] with θ h1 h0
  omega

end Skips
