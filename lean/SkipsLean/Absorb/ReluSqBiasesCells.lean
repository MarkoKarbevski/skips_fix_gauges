import SkipsLean.Absorb.BiasesConstructions

/-!
# ReLU² blocks with biases: the polynomial of a cell

Paper (absorb paper), Appendix C.2, proof of Theorem C.2 (iii): "let `B_{θ′}`, with `n` more units
than `B_θ`, satisfy (2), and let `r(z) = max(z, 0)²`. Squares. Group the units of both blocks with
a nonzero read by the hyperplane `H = {x : x ω + ω_0 = 0}` on which their argument vanishes […].
By (2), `B_{θ′} − B_θ` is a polynomial. Near a point of `H` on no other hyperplane, the terms of
`H` are `μ_+ r(z) + μ_− r(−z)`, with `z = x ω + ω_0` […]."

A unit of a ReLU² block with biases computes `r(x w_i + b_i) ŵ_i`, which is the polynomial
`(x w_i + b_i)² ŵ_i` where its argument is positive and `0` where it is negative. So on the cell of
an input `x₀` (the inputs at which the arguments of all units have the signs they have at `x₀`)
the block is the polynomial `y ↦ ∑_{i : x₀ w_i + b_i > 0} (y w_i + b_i)² ŵ_i + c` (`reluSqCell`).
If `x₀` lies on no hyperplane `x w + b = 0` of a unit with a nonzero read, of either block, the
cell contains a neighbourhood of `x₀`, and an equality of the blocks on it is an equality of
polynomials. This is the form in which the proof uses "`B_{θ′} − B_θ` is a polynomial": here (2)
becomes, for every such `x₀`, an identity in `y` between the polynomials of the two cells.
`reluSqCell` is not a notion of the paper.
-/

namespace Skips

open Matrix

variable {p q m m' : Type*} [Fintype p] [Fintype m] [Fintype m']

open scoped Classical in
/-- **The polynomial of a ReLU² block with biases on the cell of `x₀`:**
`y ↦ ∑_{i : x₀ w_i + b_i > 0} (y w_i + b_i)² ŵ_i + c`. -/
noncomputable def reluSqCell (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ)
    (x₀ y : p → ℝ) : q → ℝ :=
  (∑ i, if 0 < (x₀ ᵥ* Wr) i + b i then ((y ᵥ* Wr) i + b i) ^ 2 • Ww i else 0) + c

/-- `reluSq z = z²` where `z > 0` and `0` elsewhere. -/
private theorem reluSq_eq_ite_rsc (z : ℝ) : reluSq z = if 0 < z then z ^ 2 else 0 := by
  unfold reluSq
  split_ifs with hz
  · rw [max_eq_left hz.le]
  · rw [max_eq_right (not_lt.mp hz)]; norm_num

/-- At every input, a ReLU² block with biases is the polynomial of the cell of that input. -/
theorem vanillaBlockB_reluSq_eq_reluSqCell (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (x : p → ℝ) :
    vanillaBlockB reluSq Wr b Ww c x = reluSqCell Wr b Ww c x x := by
  classical
  -- unit by unit, `reluSq z` is `z²` or `0`, and `f ᵥ* Ww = ∑ i, f i • Ww i`
  funext o
  simp only [vanillaBlockB, reluSqCell, Pi.add_apply, vecMul, dotProduct, Finset.sum_apply,
    reluSq_eq_ite_rsc]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- A coordinate of the polynomial of a cell. -/
private theorem reluSqCell_apply_rsc (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (x₀ y : p → ℝ) (o : q) :
    reluSqCell Wr b Ww c x₀ y o
      = ∑ i, (if 0 < (x₀ ᵥ* Wr) i + b i then ((y ᵥ* Wr) i + b i) ^ 2 * Ww i o else 0)
        + c o := by
  classical
  simp only [reluSqCell, Pi.add_apply, Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- The polynomial of a cell depends on `x₀` only through the signs of the arguments. -/
private theorem reluSqCell_congr_rsc (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (x₀ x₁ y : p → ℝ)
    (hs : ∀ i, (0 < (x₁ ᵥ* Wr) i + b i ↔ 0 < (x₀ ᵥ* Wr) i + b i)) :
    reluSqCell Wr b Ww c x₁ y = reluSqCell Wr b Ww c x₀ y := by
  classical
  funext o
  rw [reluSqCell_apply_rsc, reluSqCell_apply_rsc]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [if_congr (hs i) rfl rfl]

omit [Fintype m] in
/-- An argument on the line `x₀ + s • u`. -/
private theorem arg_line_rsc (Wr : Matrix p m ℝ) (b : m → ℝ) (x₀ u : p → ℝ) (s : ℝ) (i : m) :
    ((x₀ + s • u) ᵥ* Wr) i + b i = ((x₀ ᵥ* Wr) i + b i) + s * (u ᵥ* Wr) i := by
  rw [Matrix.add_vecMul, Matrix.smul_vecMul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A sum of squares of affine functions of `s`, unit by unit, is quadratic in `s`. -/
private theorem sum_ite_sq_rsc {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (a k w : ι → ℝ) (s : ℝ) :
    ∑ i, (if P i then (a i + s * k i) ^ 2 * w i else 0)
      = ∑ i, (if P i then a i ^ 2 * w i else 0)
        + s * ∑ i, (if P i then 2 * a i * k i * w i else 0)
        + s ^ 2 * ∑ i, (if P i then k i ^ 2 * w i else 0) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

/-- A coordinate of the polynomial of a cell on the line `x₀ + s • u` is quadratic in `s`. -/
private theorem reluSqCell_line_rsc (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (x₀ u : p → ℝ) (o : q) : ∃ α β γ : ℝ, ∀ s : ℝ,
    reluSqCell Wr b Ww c x₀ (x₀ + s • u) o = α + s * β + s ^ 2 * γ := by
  classical
  refine ⟨∑ i, (if 0 < (x₀ ᵥ* Wr) i + b i then ((x₀ ᵥ* Wr) i + b i) ^ 2 * Ww i o else 0) + c o,
    ∑ i, (if 0 < (x₀ ᵥ* Wr) i + b i
      then 2 * ((x₀ ᵥ* Wr) i + b i) * (u ᵥ* Wr) i * Ww i o else 0),
    ∑ i, (if 0 < (x₀ ᵥ* Wr) i + b i then (u ᵥ* Wr) i ^ 2 * Ww i o else 0), fun s => ?_⟩
  rw [reluSqCell_apply_rsc]
  simp only [arg_line_rsc]
  rw [sum_ite_sq_rsc (fun i => 0 < (x₀ ᵥ* Wr) i + b i) (fun i => (x₀ ᵥ* Wr) i + b i)
    (fun i => (u ᵥ* Wr) i) (fun i => Ww i o) s]
  ring

/-- Near `s = 0`, the sign of `a + s k` is that of `a`, if `a ≠ 0` or `k = 0`. -/
private theorem eventually_pos_iff_rsc (a k : ℝ) (h : a ≠ 0 ∨ k = 0) :
    ∀ᶠ s in nhds (0 : ℝ), (0 < a + s * k ↔ 0 < a) := by
  rcases h with ha | hk
  · have ht : Filter.Tendsto (fun s : ℝ => a + s * k) (nhds 0) (nhds a) := by
      have hc : Continuous fun s : ℝ => a + s * k := by fun_prop
      have h1 := hc.tendsto 0
      simp only [zero_mul, add_zero] at h1
      exact h1
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · filter_upwards [ht.eventually (gt_mem_nhds hneg)] with s hs
      exact ⟨fun h1 => by linarith, fun h1 => by linarith⟩
    · filter_upwards [ht.eventually (lt_mem_nhds hpos)] with s hs
      exact ⟨fun _ => hpos, fun _ => hs⟩
  · exact Filter.Eventually.of_forall fun s => by rw [hk, mul_zero, add_zero]

/-- Near `s = 0`, every unit of a block keeps on the line `x₀ + s • u` the sign it has at `x₀`. -/
private theorem eventually_signs_rsc (Wr : Matrix p m ℝ) (b : m → ℝ) (x₀ u : p → ℝ)
    (hx : ∀ i, (x₀ ᵥ* Wr) i + b i = 0 → Wrᵀ i = 0) :
    ∀ᶠ s in nhds (0 : ℝ), ∀ i,
      (0 < ((x₀ + s • u) ᵥ* Wr) i + b i ↔ 0 < (x₀ ᵥ* Wr) i + b i) := by
  rw [Filter.eventually_all]
  intro i
  simp only [arg_line_rsc]
  refine eventually_pos_iff_rsc _ _ ?_
  by_cases ha : (x₀ ᵥ* Wr) i + b i = 0
  · -- a unit on its hyperplane has the read `0`, so its argument is constant
    right
    have h0 := hx i ha
    simp only [vecMul, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h1 : Wr j i = 0 := by
      have h2 := congrFun h0 j
      simpa using h2
    rw [h1, mul_zero]
  · exact Or.inl ha

/-- A quadratic polynomial that vanishes near `0` vanishes at `1`. -/
private theorem quad_rsc (α β γ : ℝ) (h : ∀ᶠ s in nhds (0 : ℝ), α + s * β + s ^ 2 * γ = 0) :
    α + β + γ = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
  have h0 := hball (y := 0) (by simpa using hε)
  have hp := hball (y := ε / 2) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have hm := hball (y := -(ε / 2)) (by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith)
  have hα : α = 0 := by simpa using h0
  have ht : ε / 2 ≠ 0 := by positivity
  have hγ : γ = 0 := by
    have h1 : (ε / 2) ^ 2 * γ = 0 := by nlinarith
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (pow_ne_zero 2 ht)
    · exact h2
  have hβ : β = 0 := by
    have h1 : (ε / 2) * β = 0 := by rw [hα, hγ] at hp; linarith
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 ht
    · exact h2
  rw [hα, hβ, hγ]; norm_num

/-- **Proof of Theorem C.2 (iii) of the absorb paper, "`B_{θ′} − B_θ` is a polynomial", cell by
cell:** let ReLU² blocks with biases `B_θ` and `B_{θ′}`, of any widths, satisfy
`x M + B_θ(x) = B_{θ′}(x)` for all `x`. Then for every `x₀` on no hyperplane `x w + b = 0` of a
unit with a nonzero read, of either block, the polynomials of the cell of `x₀` satisfy the same
equation at every `y`. -/
theorem reluSqCell_eq_of_vanillaBlockB_absorb (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (Wr' : Matrix p m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' q ℝ) (c' : q → ℝ)
    (M : Matrix p q ℝ)
    (h : ∀ x : p → ℝ,
      x ᵥ* M + vanillaBlockB reluSq Wr b Ww c x = vanillaBlockB reluSq Wr' b' Ww' c' x)
    (x₀ : p → ℝ) (hx : ∀ i, (x₀ ᵥ* Wr) i + b i = 0 → Wrᵀ i = 0)
    (hx' : ∀ j, (x₀ ᵥ* Wr') j + b' j = 0 → Wr'ᵀ j = 0) :
    ∀ y : p → ℝ, y ᵥ* M + reluSqCell Wr b Ww c x₀ y = reluSqCell Wr' b' Ww' c' x₀ y := by
  classical
  intro y
  -- the line `x_s = x₀ + s • u` through `x₀` and `y = x_1`
  set u := y - x₀ with hu
  have hy : y = x₀ + (1 : ℝ) • u := by rw [one_smul, hu, add_sub_cancel]
  -- (a) near `s = 0` every unit of either block keeps its sign at `x₀`
  have hs := (eventually_signs_rsc Wr b x₀ u hx).and (eventually_signs_rsc Wr' b' x₀ u hx')
  -- (b) there, the equation of the blocks is the equation of the polynomials of the cell of `x₀`
  have he : ∀ᶠ s in nhds (0 : ℝ), (x₀ + s • u) ᵥ* M + reluSqCell Wr b Ww c x₀ (x₀ + s • u)
      = reluSqCell Wr' b' Ww' c' x₀ (x₀ + s • u) := by
    filter_upwards [hs] with s hs1
    have h1 := h (x₀ + s • u)
    rw [vanillaBlockB_reluSq_eq_reluSqCell, vanillaBlockB_reluSq_eq_reluSqCell,
      reluSqCell_congr_rsc Wr b Ww c x₀ _ _ hs1.1,
      reluSqCell_congr_rsc Wr' b' Ww' c' x₀ _ _ hs1.2] at h1
    exact h1
  -- (c) coordinate by coordinate, both sides are quadratic in `s`, so they agree at `s = 1`
  funext o
  obtain ⟨α, β, γ, hc⟩ := reluSqCell_line_rsc Wr b Ww c x₀ u o
  obtain ⟨α', β', γ', hc'⟩ := reluSqCell_line_rsc Wr' b' Ww' c' x₀ u o
  have hM : ∀ s : ℝ, ((x₀ + s • u) ᵥ* M) o = (x₀ ᵥ* M) o + s * (u ᵥ* M) o := fun s => by
    rw [Matrix.add_vecMul, Matrix.smul_vecMul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hq := quad_rsc ((x₀ ᵥ* M) o + α - α') ((u ᵥ* M) o + β - β') (γ - γ') (by
    filter_upwards [he] with s hs1
    have h1 := congrFun hs1 o
    rw [Pi.add_apply, hM, hc, hc'] at h1
    linear_combination h1)
  rw [Pi.add_apply, hy, hM, hc, hc']
  linear_combination hq

end Skips
