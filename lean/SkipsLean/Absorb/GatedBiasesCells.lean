import SkipsLean.Absorb.BiasesConstructions
import SkipsLean.Absorb.SameWidth

/-!
# Gated blocks with biases along rays: the two identities of Lemma C.8

Paper (absorb paper), Appendix C.2. "For a unit `j` of a gated block with biases, let
`Δ_j = (b^g_j v_j + b^v_j g_j) ŵ_j`, a `d_model × d_model` matrix of rank at most one."

Proof of Lemma C.8 (Gated blocks with biases), "Outline. Along rays `x = t u` with `t → ∞`, every
gate becomes a ReLU gate. The terms of order `t²` and `t` of (2) then split hyperplane by
hyperplane […]. Expansion along rays. […] For `x ∉ H` and `t → ∞`,
`σ(t x g + b^g) = t η ReLU(s x ν) + b^g [s x ν > 0] + o(1/t)`, exactly for large `t` when `σ` is
ReLU, and up to terms that decay exponentially in `t` when `σ` is SiLU or GELU. So the unit
contributes `t² ReLU(s x ν) (x v) η ŵ + t (ReLU(s x ν) η b^v ŵ + [s x ν > 0] (x v) b^g ŵ) + O(1)`,
and a unit with gate read `0` contributes `t σ(b^g) (x v) ŵ + O(1)`. Put `t x` into (2) and compare
the coefficients of `t²` and of `t` at each `x` off all the hyperplanes."

Here this step is stated in the following form. At an input `x` off the hyperplanes `x g_j = 0` of
the units with a nonzero gate read (of both blocks), a unit whose gate is open at `x` (`x g_j > 0`)
contributes `t² (x g_j)(x v_j) ŵ_j + t x Δ_j + O(1)` at `t x`, a unit whose gate is closed
contributes `O(1)`, and a unit with gate read `0` contributes `t σ(b^g_j) (x v_j) ŵ_j + O(1)`. The
set of open gates is the same at all inputs near `x`, so the coefficients of `t` and of `t²` give
an identity of matrices and an identity of quadratic maps:

* `M + Λ_θ(x) = Λ_{θ′}(x)`, with `Λ_θ(x)` the sum of the `Δ_j` over the units open at `x`, plus
  the sum of `σ(b^g_j) v_j ŵ_j` over the units with gate read `0` (`gateLinear`);
* `Q_θ(x, y) = Q_{θ′}(x, y)` for every `y`, with `Q_θ(x, y)` the sum of `(y g_j)(y v_j) ŵ_j` over
  the units open at `x` (`gateQuadratic`).

The paper's two identities (sums over the hyperplanes of `ReLU(±x ν)` terms) are these, read on
the two sides of each hyperplane. What the step uses of the gate is that it is at a distance
`O(1/|z|)` from ReLU (`NearReLU`): ReLU, SiLU and GELU are. `NearReLU`, `gateLinear` and
`gateQuadratic` are not notions of the paper.
-/

namespace Skips

open Matrix

variable {p q m m' : Type*} [Fintype p] [Fintype m] [Fintype m']

/-- **A gate at a distance `O(1/|z|)` from ReLU:** `(1 + |z|) |σ(z) − ReLU(z)|` is bounded. (ReLU,
SiLU and GELU: for the last two the distance decays exponentially.) -/
def NearReLU (σ : ℝ → ℝ) : Prop := ∃ K : ℝ, ∀ z, (1 + |z|) * |σ z - relu z| ≤ K

/-- ReLU is at a distance `O(1/|z|)` from ReLU. -/
theorem nearReLU_relu : NearReLU relu := by
  refine ⟨0, fun z => ?_⟩
  rw [sub_self, abs_zero, mul_zero]

/-- `|SiLU(z) − ReLU(z)| = |z| / (1 + e^{|z|})`. -/
private theorem abs_silu_sub_relu_gbc (z : ℝ) :
    |silu z - relu z| = |z| / (1 + Real.exp |z|) := by
  have hE := Real.exp_pos |z|
  rcases le_total 0 z with hz | hz
  · -- `z ≥ 0`: `SiLU(z) − z = −z/(1 + e^z)`
    have e : silu z - relu z = -(z / (1 + Real.exp z)) := by
      rw [relu, max_eq_left hz, silu, Real.exp_neg]
      have := Real.exp_pos z
      field_simp
      ring
    rw [e, abs_neg, abs_of_nonneg hz, abs_of_nonneg (div_nonneg hz (by positivity))]
  · -- `z ≤ 0`: `SiLU(z) = z/(1 + e^{−z})`
    rw [relu, max_eq_right hz, sub_zero, silu, abs_of_nonpos hz, abs_div,
      abs_of_nonpos hz, abs_of_pos (by positivity)]

/-- SiLU is at a distance `O(1/|z|)` from ReLU: `|SiLU(z) − ReLU(z)| = |z| / (1 + e^{|z|})`. -/
theorem nearReLU_silu : NearReLU silu := by
  refine ⟨2, fun z => ?_⟩
  rw [abs_silu_sub_relu_gbc]
  -- `(1 + y) y ≤ 2 (1 + y + y²/2) ≤ 2 e^y < 2 (1 + e^y)` for `y = |z| ≥ 0`
  have hy := abs_nonneg z
  have hE := Real.quadratic_le_exp_of_nonneg hy
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

/-- `|z| |GELU(z) − ReLU(z)| ≤ 1`: with `y = |z|`, `y · y Φ(−y) ≤ y φ(y) ≤ y e^{−y²/2} ≤ 1`. -/
private theorem abs_mul_gelu_sub_relu_le_gbc (z : ℝ) :
    |z| * |gelu z - relu z| ≤ 1 := by
  rw [gelu_sub_relu, abs_neg]
  rcases (abs_nonneg z).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    exact zero_le_one
  · rw [abs_of_pos (mul_pos hpos (gaussCdf_pos _)), gaussCdf_neg]
    -- `1 − Φ(y) ≤ φ(y)/y`, and `y φ(y) ≤ y e^{−y²/2} ≤ 1` since `e^{y²/2} ≥ 1 + y²/2 + y⁴/8`
    have h1 := one_sub_gaussCdf_le hpos
    have h2 : |z| * gaussPdf |z| ≤ 1 := by
      have hs1 : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
      have hE := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ |z| ^ 2 / 2)
      have hE' : Real.exp (-|z| ^ 2 / 2) * Real.exp (|z| ^ 2 / 2) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      have hEp := Real.exp_pos (-|z| ^ 2 / 2)
      have hyE : |z| * Real.exp (-|z| ^ 2 / 2) ≤ 1 := by
        nlinarith [sq_nonneg (|z| - 1)]
      rw [gaussPdf, mul_div_assoc', div_le_one (by linarith)]
      linarith
    calc |z| * (|z| * (1 - gaussCdf |z|)) ≤ |z| * (|z| * (gaussPdf |z| / |z|)) := by gcongr
      _ = |z| * gaussPdf |z| := by field_simp
      _ ≤ 1 := h2

/-- GELU is at a distance `O(1/|z|)` from ReLU: `|GELU(z) − ReLU(z)| = |z| Φ(−|z|)`. -/
theorem nearReLU_gelu : NearReLU gelu := by
  -- `|GELU(z) − ReLU(z)| ≤ 1` and `|z| |GELU(z) − ReLU(z)| ≤ 1`
  refine ⟨2, fun z => ?_⟩
  have h1 := abs_gelu_sub_relu_le z
  have h2 := abs_mul_gelu_sub_relu_le_gbc z
  linarith

/-- **The matrix `Δ_j = (b^g_j v_j + b^v_j g_j) ŵ_j` of a unit of a gated block with biases**
(absorb paper, Appendix C.2), of rank at most one: the column `b^g_j v_j + b^v_j g_j` times the
row `ŵ_j`. -/
def gateDelta (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ)
    (Ww : Matrix m q ℝ) (j : m) : Matrix p q ℝ :=
  Matrix.of fun a o => (bg j * Wv a j + bv j * Wg a j) * Ww j o

open scoped Classical in
/-- **The coefficient of `t` of a gated block with biases at `t x`,** for `x` off the hyperplanes,
as a matrix `Λ` with coefficient `x Λ`: the sum of the `Δ_j` over the units whose gate is open at
`x` (`x g_j > 0`), plus the sum of `σ(b^g_j) v_j ŵ_j` over the units with gate read `0`. -/
noncomputable def gateLinear (σ : ℝ → ℝ) (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ)
    (bv : m → ℝ) (Ww : Matrix m q ℝ) (x : p → ℝ) : Matrix p q ℝ :=
  (∑ j, if 0 < (x ᵥ* Wg) j then gateDelta Wg bg Wv bv Ww j else 0)
    + ∑ j, if Wgᵀ j = 0 then Matrix.of (fun a o => σ (bg j) * Wv a j * Ww j o) else 0

open scoped Classical in
/-- **The coefficient of `t²` of a gated block with biases at `t y`,** for `y` in the cell of `x`:
the sum of `(y g_j)(y v_j) ŵ_j` over the units whose gate is open at `x`. -/
noncomputable def gateQuadratic (Wg Wv : Matrix p m ℝ) (Ww : Matrix m q ℝ) (x y : p → ℝ) :
    q → ℝ :=
  ∑ j, if 0 < (x ᵥ* Wg) j then ((y ᵥ* Wg) j * (y ᵥ* Wv) j) • Ww j else 0

/-! ### Helpers for Lemma C.8: one ray, one point -/

omit [Fintype m] in
/-- A unit with gate read `0` reads `0` at every input. -/
private theorem vecMul_eq_zero_of_col_gbc (Wg : Matrix p m ℝ) {j : m} (hg : Wgᵀ j = 0)
    (z : p → ℝ) : (z ᵥ* Wg) j = 0 := by
  simp only [Matrix.vecMul, dotProduct]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 : Wg i j = 0 := congrFun hg i
  rw [h1, mul_zero]

/-- An output coordinate of a gated block with biases at `t y`. -/
private theorem gatedBlockB_smul_apply_gbc (σ : ℝ → ℝ) (Wg : Matrix p m ℝ) (bg : m → ℝ)
    (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ) (t : ℝ) (y : p → ℝ)
    (o : q) :
    gatedBlockB σ Wg bg Wv bv Ww c (t • y) o
      = ∑ j, σ (t * (y ᵥ* Wg) j + bg j) * (t * (y ᵥ* Wv) j + bv j) * Ww j o + c o := by
  simp only [gatedBlockB, Pi.add_apply, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]
  rfl

/-- An output coordinate of `gateQuadratic`. -/
private theorem gateQuadratic_apply_gbc (Wg Wv : Matrix p m ℝ) (Ww : Matrix m q ℝ)
    (x y : p → ℝ) (o : q) :
    gateQuadratic Wg Wv Ww x y o
      = ∑ j, (if 0 < (x ᵥ* Wg) j then (y ᵥ* Wg) j * (y ᵥ* Wv) j else 0) * Ww j o := by
  unfold gateQuadratic
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

open scoped Classical in
/-- An output coordinate of `y Λ(x)`. -/
private theorem vecMul_gateLinear_apply_gbc (σ : ℝ → ℝ) (Wg : Matrix p m ℝ) (bg : m → ℝ)
    (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ) (x y : p → ℝ) (o : q) :
    (y ᵥ* gateLinear σ Wg bg Wv bv Ww x) o
      = ∑ j, ((if 0 < (x ᵥ* Wg) j then bg j * (y ᵥ* Wv) j + bv j * (y ᵥ* Wg) j else 0)
          + (if Wgᵀ j = 0 then σ (bg j) * (y ᵥ* Wv) j else 0)) * Ww j o := by
  have hA : ∀ a, gateLinear σ Wg bg Wv bv Ww x a o
      = ∑ j, ((if 0 < (x ᵥ* Wg) j then bg j * Wv a j + bv j * Wg a j else 0)
          + (if Wgᵀ j = 0 then σ (bg j) * Wv a j else 0)) * Ww j o := by
    intro a
    simp only [gateLinear, Matrix.add_apply, Matrix.sum_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [gateDelta]
    ring
  have e : (y ᵥ* gateLinear σ Wg bg Wv bv Ww x) o
      = ∑ a, y a * gateLinear σ Wg bg Wv bv Ww x a o := rfl
  rw [e]
  simp only [hA, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;>
    simp only [Matrix.vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum, ←
      Finset.sum_add_distrib, zero_add, add_zero, mul_zero, zero_mul, Finset.sum_const_zero] <;>
    refine Finset.sum_congr rfl fun a _ => by ring

/-- `|σ(z) − ReLU(z)| |t c + γ| ≤ (|c/a| + |γ − c β/a|) K` for `z = t a + β`: write
`t c + γ = (c/a) z + (γ − c β/a)` and use `(1 + |z|) |σ(z) − ReLU(z)| ≤ K`. -/
private theorem near_bound_gbc {σ : ℝ → ℝ} {K : ℝ} (hK : ∀ z, (1 + |z|) * |σ z - relu z| ≤ K)
    {a : ℝ} (ha : a ≠ 0) (β c γ t : ℝ) :
    |σ (t * a + β) - relu (t * a + β)| * |t * c + γ| ≤ (|c / a| + |γ - c * β / a|) * K := by
  have e : t * c + γ = c / a * (t * a + β) + (γ - c * β / a) := by
    field_simp
    ring
  have h1 : |t * c + γ| ≤ |c / a| * |t * a + β| + |γ - c * β / a| := by
    rw [e, ← abs_mul]
    exact abs_add_le _ _
  have hD := abs_nonneg (σ (t * a + β) - relu (t * a + β))
  have hP := abs_nonneg (c / a)
  have hQ := abs_nonneg (γ - c * β / a)
  have hz := abs_nonneg (t * a + β)
  calc |σ (t * a + β) - relu (t * a + β)| * |t * c + γ|
      ≤ |σ (t * a + β) - relu (t * a + β)| * (|c / a| * |t * a + β| + |γ - c * β / a|) :=
        mul_le_mul_of_nonneg_left h1 hD
    _ ≤ ((1 + |t * a + β|) * |σ (t * a + β) - relu (t * a + β)|) * (|c / a| + |γ - c * β / a|) := by
        nlinarith [mul_nonneg hD hP, mul_nonneg (mul_nonneg hD hQ) hz]
    _ ≤ K * (|c / a| + |γ - c * β / a|) := mul_le_mul_of_nonneg_right (hK _) (by positivity)
    _ = _ := mul_comm _ _

/-- **One unit with a nonzero gate read `a`, along the ray** (step (a)): for `t ≥ |β|/|a|`,
`σ(t a + β)(t c + γ) w` is `[a > 0] (t² a c + t (β c + γ a)) w` up to a bounded term. -/
private theorem unit_gbc {σ : ℝ → ℝ} {K : ℝ} (hK : ∀ z, (1 + |z|) * |σ z - relu z| ≤ K)
    {a : ℝ} (ha : a ≠ 0) (β c γ w : ℝ) :
    ∃ C, ∀ᶠ t in Filter.atTop, |σ (t * a + β) * (t * c + γ) * w
      - (t ^ 2 * (if 0 < a then a * c else 0) + t * (if 0 < a then β * c + γ * a else 0)) * w|
        ≤ C := by
  refine ⟨((|c / a| + |γ - c * β / a|) * K + |β * γ|) * |w|, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (|β| / |a|)] with t ht
  have hapos : 0 < |a| := abs_pos.2 ha
  have hta : |β| ≤ t * |a| := (div_le_iff₀ hapos).1 ht
  -- for such `t`, `ReLU(t a + β) = [a > 0] (t a + β)`
  have e : σ (t * a + β) * (t * c + γ) * w
      - (t ^ 2 * (if 0 < a then a * c else 0) + t * (if 0 < a then β * c + γ * a else 0)) * w
      = (σ (t * a + β) - relu (t * a + β)) * (t * c + γ) * w
        + (if 0 < a then β * γ else 0) * w := by
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · have hz : t * a + β ≤ 0 := by
        rw [abs_of_neg hneg] at hta
        linarith [le_abs_self β]
      rw [relu, max_eq_right hz]
      simp only [show ¬ (0 < a) from not_lt.2 hneg.le, ↓reduceIte]
      ring
    · have hz : 0 ≤ t * a + β := by
        rw [abs_of_pos hpos] at hta
        linarith [neg_abs_le β]
      rw [relu, max_eq_left hz]
      simp only [hpos, ↓reduceIte]
      ring
  rw [e]
  have hb := near_bound_gbc hK ha β c γ t
  have hβγ : |(if 0 < a then β * γ else 0)| ≤ |β * γ| := by
    split_ifs
    · exact le_rfl
    · rw [abs_zero]
      exact abs_nonneg _
  calc _ ≤ |(σ (t * a + β) - relu (t * a + β)) * (t * c + γ) * w|
        + |(if 0 < a then β * γ else 0) * w| := abs_add_le _ _
    _ ≤ (|c / a| + |γ - c * β / a|) * K * |w| + |β * γ| * |w| := by
        rw [abs_mul, abs_mul, abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right hb (abs_nonneg w))
          (mul_le_mul_of_nonneg_right hβγ (abs_nonneg w))
    _ = _ := by ring

omit [Fintype m] in
open scoped Classical in
/-- **One unit of a block along the ray `t y`** (step (a)), with `y` off the hyperplane of the
unit if its gate read is nonzero. A unit with gate read `0` contributes `σ(b^g) (t c + γ) ŵ`. -/
private theorem unit_block_gbc {σ : ℝ → ℝ} {K : ℝ}
    (hK : ∀ z, (1 + |z|) * |σ z - relu z| ≤ K) (Wg : Matrix p m ℝ) (bg : m → ℝ)
    (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ) (y : p → ℝ)
    (hy : ∀ j, (y ᵥ* Wg) j = 0 → Wgᵀ j = 0) (o : q) (j : m) :
    ∃ C, ∀ᶠ t in Filter.atTop, |σ (t * (y ᵥ* Wg) j + bg j) * (t * (y ᵥ* Wv) j + bv j) * Ww j o
      - (t ^ 2 * (if 0 < (y ᵥ* Wg) j then (y ᵥ* Wg) j * (y ᵥ* Wv) j else 0)
        + t * ((if 0 < (y ᵥ* Wg) j then bg j * (y ᵥ* Wv) j + bv j * (y ᵥ* Wg) j else 0)
          + (if Wgᵀ j = 0 then σ (bg j) * (y ᵥ* Wv) j else 0))) * Ww j o| ≤ C := by
  by_cases hg : Wgᵀ j = 0
  · -- gate read `0`: the difference is the constant `σ(b^g) γ ŵ`
    have ha := vecMul_eq_zero_of_col_gbc Wg hg y
    refine ⟨|σ (bg j) * bv j * Ww j o|, Filter.Eventually.of_forall fun t => le_of_eq ?_⟩
    rw [ha]
    simp only [lt_irrefl, ↓reduceIte, hg, mul_zero, zero_add]
    congr 1
    ring
  · have ha : (y ᵥ* Wg) j ≠ 0 := fun h0 => hg (hy j h0)
    obtain ⟨C, hC⟩ := unit_gbc hK ha (bg j) ((y ᵥ* Wv) j) (bv j) (Ww j o)
    refine ⟨C, hC.mono fun t ht => ?_⟩
    simp only [hg, ↓reduceIte, add_zero]
    exact ht

open scoped Classical in
/-- **A block along the ray `t y`** (step (b)): for `y` off the hyperplanes,
`B(t y) = t² Q(y, y) + t y Λ(y) + O(1)`, coordinate by coordinate. -/
private theorem expansion_gbc {σ : ℝ → ℝ} {K : ℝ}
    (hK : ∀ z, (1 + |z|) * |σ z - relu z| ≤ K) (Wg : Matrix p m ℝ) (bg : m → ℝ)
    (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ) (y : p → ℝ)
    (hy : ∀ j, (y ᵥ* Wg) j = 0 → Wgᵀ j = 0) (o : q) :
    ∃ C, ∀ᶠ t in Filter.atTop, |gatedBlockB σ Wg bg Wv bv Ww c (t • y) o
      - t ^ 2 * gateQuadratic Wg Wv Ww y y o
      - t * (y ᵥ* gateLinear σ Wg bg Wv bv Ww y) o| ≤ C := by
  choose C hC using unit_block_gbc hK Wg bg Wv bv Ww y hy o
  refine ⟨∑ j, C j + |c o|, (Filter.eventually_all.2 hC).mono fun t ht => ?_⟩
  have hsum := (Finset.abs_sum_le_sum_abs _ Finset.univ).trans
    (Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => ht j)
  rw [gatedBlockB_smul_apply_gbc, gateQuadratic_apply_gbc, vecMul_gateLinear_apply_gbc]
  rw [Finset.sum_sub_distrib] at hsum
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hsum ⊢
  rw [abs_le] at hsum ⊢
  constructor <;> linarith [neg_abs_le (c o), le_abs_self (c o)]


/-- A multiple `t B` that is bounded for all large `t` is `0`. -/
private theorem eq_zero_of_mul_le_gbc {t₀ B C : ℝ} (h : ∀ t, t₀ ≤ t → |t * B| ≤ C) : B = 0 := by
  by_contra hB
  have hBpos : 0 < |B| := abs_pos.2 hB
  -- at `T = max t₀ 0 + (|C| + 1)/|B|`: `|T B| ≥ |C| + 1 > C`
  obtain ⟨T, hT⟩ : ∃ T, T = max t₀ 0 + (|C| + 1) / |B| := ⟨_, rfl⟩
  have h0 : 0 ≤ (|C| + 1) / |B| := div_nonneg (by positivity) hBpos.le
  have hT0 : t₀ ≤ T := by linarith [le_max_left t₀ 0]
  have hTn : 0 ≤ T := by linarith [le_max_right t₀ 0]
  have hTB : |C| + 1 ≤ T * |B| := by
    rw [hT, add_mul, div_mul_cancel₀ _ hBpos.ne']
    linarith [mul_nonneg (le_max_right t₀ 0) hBpos.le]
  have h1 := h T hT0
  rw [abs_mul, abs_of_nonneg hTn] at h1
  linarith [le_abs_self C]

/-- **Step (c):** a polynomial `t² A + t B` that is bounded for all large `t` has `A = 0` and
`B = 0`. -/
private theorem poly_gbc {A B : ℝ} (h : ∃ C, ∀ᶠ t in Filter.atTop, |t ^ 2 * A + t * B| ≤ C) :
    A = 0 ∧ B = 0 := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.1 hC
  -- for `t ≥ 1`: `|t A + B| ≤ t |t A + B| = |t² A + t B| ≤ C`, so `|t A| ≤ |C| + |B|`
  have hA : A = 0 := by
    refine eq_zero_of_mul_le_gbc (t₀ := max t₀ 1) (C := |C| + |B|) fun t ht => ?_
    have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
    have h1 := ht₀ t (le_trans (le_max_left _ _) ht)
    have e : t ^ 2 * A + t * B = t * (t * A + B) := by ring
    rw [e, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)] at h1
    have h2 : |t * A + B| ≤ t * |t * A + B| := le_mul_of_one_le_left (abs_nonneg _) ht1
    have h3 : |t * A| ≤ |t * A + B| + |B| := by
      have := abs_sub (t * A + B) B
      rwa [add_sub_cancel_right] at this
    linarith [le_abs_self C]
  refine ⟨hA, eq_zero_of_mul_le_gbc (t₀ := t₀) (C := C) fun t ht => ?_⟩
  have h1 := ht₀ t ht
  rwa [hA, mul_zero, zero_add] at h1

open scoped Classical in
/-- **Step (c) at a point `y` off the hyperplanes of both blocks:** the coefficients of `t` and of
`t²` of `t y M + B_θ(t y) = B_{θ′}(t y)` agree. -/
private theorem at_point_gbc {σ : ℝ → ℝ} (hσ : NearReLU σ)
    (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (Wg' : Matrix p m' ℝ) (bg' : m' → ℝ) (Wv' : Matrix p m' ℝ) (bv' : m' → ℝ)
    (Ww' : Matrix m' q ℝ) (c' : q → ℝ) (M : Matrix p q ℝ)
    (h : ∀ x : p → ℝ, x ᵥ* M + gatedBlockB σ Wg bg Wv bv Ww c x
      = gatedBlockB σ Wg' bg' Wv' bv' Ww' c' x)
    (y : p → ℝ) (hy : ∀ j, (y ᵥ* Wg) j = 0 → Wgᵀ j = 0)
    (hy' : ∀ j, (y ᵥ* Wg') j = 0 → Wg'ᵀ j = 0) :
    y ᵥ* M + y ᵥ* gateLinear σ Wg bg Wv bv Ww y = y ᵥ* gateLinear σ Wg' bg' Wv' bv' Ww' y ∧
      gateQuadratic Wg Wv Ww y y = gateQuadratic Wg' Wv' Ww' y y := by
  obtain ⟨K, hK⟩ := hσ
  have hall : ∀ o, (y ᵥ* M) o + (y ᵥ* gateLinear σ Wg bg Wv bv Ww y) o
      = (y ᵥ* gateLinear σ Wg' bg' Wv' bv' Ww' y) o ∧
        gateQuadratic Wg Wv Ww y y o = gateQuadratic Wg' Wv' Ww' y y o := by
    intro o
    obtain ⟨C₁, h₁⟩ := expansion_gbc hK Wg bg Wv bv Ww c y hy o
    obtain ⟨C₂, h₂⟩ := expansion_gbc hK Wg' bg' Wv' bv' Ww' c' y hy' o
    -- `t² (Q − Q′) + t y (M + Λ − Λ′)` is the difference of the two remainders
    have hp := poly_gbc (A := gateQuadratic Wg Wv Ww y y o - gateQuadratic Wg' Wv' Ww' y y o)
      (B := (y ᵥ* M) o + (y ᵥ* gateLinear σ Wg bg Wv bv Ww y) o
        - (y ᵥ* gateLinear σ Wg' bg' Wv' bv' Ww' y) o)
      ⟨C₁ + C₂, (h₁.and h₂).mono fun t ht => ?_⟩
    · exact ⟨by linarith [hp.2], by linarith [hp.1]⟩
    · have e := congrFun (h (t • y)) o
      rw [Pi.add_apply, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul] at e
      obtain ⟨ht1, ht2⟩ := ht
      rw [abs_le] at ht1 ht2 ⊢
      constructor <;> nlinarith [ht1.1, ht1.2, ht2.1, ht2.2]
  exact ⟨funext fun o => (hall o).1, funext fun o => (hall o).2⟩

/-- **Proof of Lemma C.8 of the absorb paper, "Expansion along rays", with the comparison of the
coefficients of `t²` and of `t`:** let the gate `σ` be at a distance `O(1/|z|)` from ReLU, and let
gated blocks with biases `B_θ` and `B_{θ′}`, of any widths, satisfy `x M + B_θ(x) = B_{θ′}(x)` for
all `x`. Then at every `x` off the hyperplanes `x g_j = 0` of the units of both blocks with a
nonzero gate read: `M + Λ_θ(x) = Λ_{θ′}(x)`, and `Q_θ(x, y) = Q_{θ′}(x, y)` for every `y`. -/
theorem gateLinear_gateQuadratic_of_gatedBlockB_absorb {σ : ℝ → ℝ} (hσ : NearReLU σ)
    (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (Wg' : Matrix p m' ℝ) (bg' : m' → ℝ) (Wv' : Matrix p m' ℝ) (bv' : m' → ℝ)
    (Ww' : Matrix m' q ℝ) (c' : q → ℝ) (M : Matrix p q ℝ)
    (h : ∀ x : p → ℝ, x ᵥ* M + gatedBlockB σ Wg bg Wv bv Ww c x
      = gatedBlockB σ Wg' bg' Wv' bv' Ww' c' x)
    (x : p → ℝ) (hx : ∀ j, (x ᵥ* Wg) j = 0 → Wgᵀ j = 0)
    (hx' : ∀ j, (x ᵥ* Wg') j = 0 → Wg'ᵀ j = 0) :
    M + gateLinear σ Wg bg Wv bv Ww x = gateLinear σ Wg' bg' Wv' bv' Ww' x ∧
      ∀ y : p → ℝ, gateQuadratic Wg Wv Ww x y = gateQuadratic Wg' Wv' Ww' x y := by
  sorry

end Skips
