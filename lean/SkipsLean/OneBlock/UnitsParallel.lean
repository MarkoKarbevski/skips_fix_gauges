import SkipsLean.OneBlock.UnitsReLU

/-!
# A direction that keeps the output of ReLU or ReLU² units parallel: a scale and rescalings

Paper (skips paper), proof of Theorem B.1 (iv), "The skipless network: equality", for
`σ(z) = max(z, 0)^k`, `k = 1` or `2`, with `h_1 = ∑_i σ(x c_i) a_i`: equation (18),

`J(x) := ∑_i [σ(x c_i) (ψa_i − a_i Y) + σ'(x c_i) (x ψc_i) a_i] = μ(x) h_1(x)` on `Ω`,

then "The kinks stay": "In both cases `x_0 ψc_i = 0` on an open subset of the hyperplane, so
`ψc_i = λ_i c_i` for a number `λ_i`", and "One scale": "Hence `μ = c` on `Ω` for one number `c`".
With `β_i = ψa_i − a_i Y` the two steps say: `ψc_i = λ_i c_i` and `β_i = (c − k λ_i) a_i`.

Here these two steps as one statement on vectors, with no network in it (the twin of Lemma B.3,
`UnitsRescale` in `OneBlock/Rescale.lean`, with a multiple `μ(x)` of the output on the right side
in place of `0`), **for units whose columns `c_i` are linearly independent and whose rows `a_i`
are linearly independent** (a block of width exactly `d_model` at generic parameters), and at
least two units. Then every pattern of active units occurs, and the argument is elementary:

* ReLU: across the kink of unit `i`, at a point where another unit is active, `J` jumps by
  `(x ψc_i) a_i` and `h_1` does not jump; `a_i` is not parallel to `h_1(x)`, so `x ψc_i = 0` on the
  hyperplane `x c_i = 0`. Where all units are active, `J` and `h_1` are linear in `x` and
  parallel, and `h_1` has rank at least `2`, so `J = c h_1`.
* ReLU²: where all units are active, `J` and `h_1` are quadratic, and comparing coefficients in
  the independent linear forms `x c_i` gives both conclusions.

The clause "at least two units" is part of the definition: without it the statement is false for
one unit when the input has at least two coordinates (`ψc` is then arbitrary). The paper's
argument for blocks wider than `d_model` (a resultant, and entries of `h_1` without a common
factor) is not stated here. Numeric check of the dimension `q + 1` of the solutions:
`units_parallel_check_2026-11-24.py`.
-/

namespace Skips

open Matrix

/-- **The kinks stay, and one scale (proof of Theorem B.1 (iv) of the skips paper), as a property
of an activation `σ` with derivative `σ'` off the kink and degree `k`:** for at least two hidden
units with linearly independent columns `c_i` and linearly independent rows `a_i`, if at every
input `x` off the kinks at which the output `∑_i σ(x c_i) a_i` is not zero the vector
`∑_i [σ(x c_i) β_i + σ'(x c_i) (x ψc_i) a_i]` is a multiple of the output, then there are numbers
`c₀` and `λ_i` with `ψc_i = λ_i c_i` and `β_i = (c₀ − k λ_i) a_i`. Rows of the input are indexed
by `n`, the coordinates of the output by `m`, the hidden units by `q`. -/
def UnitsParallel (σ σ' : ℝ → ℝ) (k : ℕ) (n m q : Type*) [Fintype n] [Fintype m] [Fintype q] :
    Prop :=
  ∀ (c : q → n → ℝ) (a : q → m → ℝ) (ψc : q → n → ℝ) (β : q → m → ℝ),
    LinearIndependent ℝ c → LinearIndependent ℝ a → 2 ≤ Fintype.card q →
    (∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, σ (x ⬝ᵥ c i) • a i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = μ • ∑ i, σ (x ⬝ᵥ c i) • a i) →
    ∃ (c₀ : ℝ) (lam : q → ℝ), ∀ i, ψc i = lam i • c i ∧ β i = (c₀ - (k : ℝ) * lam i) • a i

/-- Linearly independent columns `c_i`: the values `x c_i` can be prescribed. -/
private lemma exists_dot_eq_upl {n q : Type*} [Fintype n] [Fintype q] {c : q → n → ℝ}
    (hc : LinearIndependent ℝ c) (y : q → ℝ) : ∃ x : n → ℝ, ∀ i, x ⬝ᵥ c i = y i := by
  obtain ⟨x, hx⟩ := LinearIndependent.mulVec_surjective (M := Matrix.of c) hc y
  refine ⟨x, fun i => ?_⟩
  rw [← hx, dotProduct_comm]
  rfl

/-- A vector is determined by its dot products with all `x`. -/
private lemma eq_smul_of_dot_upl {n : Type*} [Fintype n] {v w : n → ℝ} {l : ℝ}
    (h : ∀ x : n → ℝ, x ⬝ᵥ v = l * (x ⬝ᵥ w)) : v = l • w := by
  classical
  funext o
  have e := h (Pi.single o 1)
  simp only [single_one_dotProduct] at e
  simp only [Pi.smul_apply, smul_eq_mul]
  exact e

/-- **The coefficients of the `a_i`.** If `β_i = r_i a_i`, then at a point off the kinks where
unit `j` is active, `J = μ b` reads `u_i r_i + κ (x ψc_i) = μ u_i` for every active unit `i`
(`u_i = x c_i`): the `a_i` are independent, and `σ'(u) u = κ σ(u)`, `σ(u) > 0` for `u > 0`. -/
private lemma coeff_upl {n m q : Type*} [Fintype n] [Fintype m] [Fintype q] {σ σ' : ℝ → ℝ}
    {κ : ℝ} (hpos : ∀ u : ℝ, 0 < u → 0 < σ u ∧ σ' u * u = κ * σ u)
    {c ψc : q → n → ℝ} {a β : q → m → ℝ} {r : q → ℝ} (ha : LinearIndependent ℝ a)
    (hβ : ∀ i, β i = r i • a i)
    (h : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, σ (x ⬝ᵥ c i) • a i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = μ • ∑ i, σ (x ⬝ᵥ c i) • a i)
    {x : n → ℝ} (hx : ∀ i, x ⬝ᵥ c i ≠ 0) {j : q} (hj : 0 < x ⬝ᵥ c j) :
    ∃ μ : ℝ, ∀ i, 0 < x ⬝ᵥ c i → (x ⬝ᵥ c i) * r i + κ * (x ⬝ᵥ ψc i) = μ * (x ⬝ᵥ c i) := by
  -- the output is not zero: its coefficient on `a_j` is `σ(u_j) > 0`
  have hb : ∑ i, σ (x ⬝ᵥ c i) • a i ≠ 0 := fun h0 =>
    (hpos _ hj).1.ne' (Fintype.linearIndependent_iff.1 ha _ h0 j)
  obtain ⟨μ, hμ⟩ := h x hx hb
  -- `J - μ b = ∑_i [σ(u_i) r_i + σ'(u_i) (x ψc_i) - μ σ(u_i)] a_i = 0`
  have hsum : ∑ i, (σ (x ⬝ᵥ c i) * r i + σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)
      - μ * σ (x ⬝ᵥ c i)) • a i = 0 := by
    refine Eq.trans ?_ (sub_eq_zero.2 hμ)
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hβ i]
    ext o
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hco := Fintype.linearIndependent_iff.1 ha _ hsum
  refine ⟨μ, fun i hi => ?_⟩
  obtain ⟨h0, h1⟩ := hpos _ hi
  have e := hco i
  -- multiply by `u_i` and divide by `σ(u_i)`
  have key : σ (x ⬝ᵥ c i) * ((x ⬝ᵥ c i) * r i + κ * (x ⬝ᵥ ψc i) - μ * (x ⬝ᵥ c i)) = 0 := by
    linear_combination (x ⬝ᵥ c i) * e - (x ⬝ᵥ ψc i) * h1
  exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left h0.ne')

/-- **`β_j` is a multiple of `a_j`:** at a point where unit `j` alone is active, `b = σ(1) a_j`
and `J = σ(1) β_j + σ'(1) (x ψc_j) a_j`. -/
private lemma exists_beta_eq_upl {n m q : Type*} [Fintype n] [Fintype m] [Fintype q]
    {σ σ' : ℝ → ℝ} (hneg : ∀ u : ℝ, u < 0 → σ u = 0 ∧ σ' u = 0) (h1 : σ 1 ≠ 0)
    {c ψc : q → n → ℝ} {a β : q → m → ℝ} (hc : LinearIndependent ℝ c)
    (ha : LinearIndependent ℝ a)
    (h : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, σ (x ⬝ᵥ c i) • a i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = μ • ∑ i, σ (x ⬝ᵥ c i) • a i)
    (j : q) : ∃ r : ℝ, β j = r • a j := by
  classical
  obtain ⟨x, hx⟩ := exists_dot_eq_upl hc (fun i => if i = j then 1 else -1)
  have hxj : x ⬝ᵥ c j = 1 := by rw [hx]; simp only [↓reduceIte]
  have hxi : ∀ i, i ≠ j → x ⬝ᵥ c i = -1 := fun i hi => by
    rw [hx]; simp only [hi, ↓reduceIte]
  have hz : ∀ i, i ≠ j → σ (x ⬝ᵥ c i) = 0 ∧ σ' (x ⬝ᵥ c i) = 0 := fun i hi => by
    rw [hxi i hi]; exact hneg (-1) (by norm_num)
  have hx0 : ∀ i, x ⬝ᵥ c i ≠ 0 := fun i => by
    by_cases hi : i = j
    · rw [hi, hxj]; exact one_ne_zero
    · rw [hxi i hi]; norm_num
  -- only unit `j` contributes
  have hb : ∑ i, σ (x ⬝ᵥ c i) • a i = σ 1 • a j := by
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [(hz i hi).1, zero_smul])
      (fun hj => absurd (Finset.mem_univ j) hj), hxj]
  have hJ : ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
      = σ 1 • β j + (σ' 1 * (x ⬝ᵥ ψc j)) • a j := by
    rw [Finset.sum_eq_single j (fun i _ hi => by
      rw [(hz i hi).1, (hz i hi).2, zero_smul, zero_mul, zero_smul, add_zero])
      (fun hj => absurd (Finset.mem_univ j) hj), hxj]
  have hb0 : ∑ i, σ (x ⬝ᵥ c i) • a i ≠ 0 := by
    rw [hb]; exact smul_ne_zero h1 (ha.ne_zero j)
  obtain ⟨μ, hμ⟩ := h x hx0 hb0
  rw [hJ, hb] at hμ
  refine ⟨(μ * σ 1 - σ' 1 * (x ⬝ᵥ ψc j)) / σ 1, funext fun o => ?_⟩
  have e := congrFun hμ o
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  rw [div_mul_eq_mul_div, eq_div_iff h1]
  linear_combination e

/-- **The kinks stay.** Let `y` lie on the kink of unit `i` (`y c_i = 0`), with unit `j` active
and the other units not. On the points `y + s e_i` (`s > 0`, `e_i c_l = δ_il`) units `i` and `j`
are active; eliminating `μ` from their two coefficients gives a quadratic in `s` whose value at
`s = 0` is `κ (y c_j) (y ψc_i)`; it vanishes at `s = 1, 2, 3`, so `y ψc_i = 0`. -/
private lemma kink_upl {n m q : Type*} [Fintype n] [Fintype m] [Fintype q] {σ σ' : ℝ → ℝ}
    {κ : ℝ} (hκ : κ ≠ 0) (hpos : ∀ u : ℝ, 0 < u → 0 < σ u ∧ σ' u * u = κ * σ u)
    {c ψc : q → n → ℝ} {a β : q → m → ℝ} {r : q → ℝ} (ha : LinearIndependent ℝ a)
    (hβ : ∀ i, β i = r i • a i)
    (h : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, σ (x ⬝ᵥ c i) • a i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = μ • ∑ i, σ (x ⬝ᵥ c i) • a i)
    {i j : q} (hij : i ≠ j) {e : n → ℝ} (hei : e ⬝ᵥ c i = 1) (hel : ∀ l, l ≠ i → e ⬝ᵥ c l = 0)
    {y : n → ℝ} (hyi : y ⬝ᵥ c i = 0) (hyj : 0 < y ⬝ᵥ c j)
    (hyl : ∀ l, l ≠ i → l ≠ j → y ⬝ᵥ c l < 0) : y ⬝ᵥ ψc i = 0 := by
  -- at `y + s e_i`: `U s r_i + U κ L_i - s (U r_j + κ L_j) = 0` with `U = y c_j`
  have key : ∀ s : ℝ, 0 < s → (y ⬝ᵥ c j) * s * r i
      + (y ⬝ᵥ c j) * κ * (y ⬝ᵥ ψc i + s * (e ⬝ᵥ ψc i))
      - s * ((y ⬝ᵥ c j) * r j + κ * (y ⬝ᵥ ψc j + s * (e ⬝ᵥ ψc j))) = 0 := by
    intro s hs
    have hu : ∀ l, (y + s • e) ⬝ᵥ c l = y ⬝ᵥ c l + s * (e ⬝ᵥ c l) := fun l => by
      rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
    have hui : (y + s • e) ⬝ᵥ c i = s := by rw [hu, hyi, hei, zero_add, mul_one]
    have huj : (y + s • e) ⬝ᵥ c j = y ⬝ᵥ c j := by
      rw [hu, hel j hij.symm, mul_zero, add_zero]
    have hx : ∀ l, (y + s • e) ⬝ᵥ c l ≠ 0 := fun l => by
      by_cases hli : l = i
      · rw [hli, hui]; exact hs.ne'
      by_cases hlj : l = j
      · rw [hlj, huj]; exact hyj.ne'
      rw [hu, hel l hli, mul_zero, add_zero]; exact (hyl l hli hlj).ne
    obtain ⟨μ, hμ⟩ := coeff_upl hpos ha hβ h hx (j := i) (by rw [hui]; exact hs)
    have e1 := hμ i (by rw [hui]; exact hs)
    have e2 := hμ j (by rw [huj]; exact hyj)
    rw [hui, add_dotProduct, smul_dotProduct, smul_eq_mul] at e1
    rw [huj, add_dotProduct, smul_dotProduct, smul_eq_mul] at e2
    linear_combination (y ⬝ᵥ c j) * e1 - s * e2
  -- the value at `s = 0` of a quadratic is `3 f(1) - 3 f(2) + f(3)`
  have h0 : (y ⬝ᵥ c j) * κ * (y ⬝ᵥ ψc i) = 0 := by
    linear_combination 3 * key 1 one_pos - 3 * key 2 two_pos + key 3 three_pos
  exact (mul_eq_zero.1 h0).resolve_left (mul_ne_zero hyj.ne' hκ)

/-- **`x ψc_i = 0` on the whole hyperplane `x c_i = 0`.** Take another unit `j`, a point `y₀` of
the hyperplane with `y₀ c_j = 1` and `y₀ c_l = -1` for the other units, and a large `M`: then
`y₀` and `M y₀ + w` are points of the hyperplane as in `kink_upl`. -/
private lemma dot_psi_eq_zero_upl {n m q : Type*} [Fintype n] [Fintype m] [Fintype q]
    {σ σ' : ℝ → ℝ} {κ : ℝ} (hκ : κ ≠ 0) (hpos : ∀ u : ℝ, 0 < u → 0 < σ u ∧ σ' u * u = κ * σ u)
    {c ψc : q → n → ℝ} {a β : q → m → ℝ} {r : q → ℝ} (hc : LinearIndependent ℝ c)
    (ha : LinearIndependent ℝ a) (hcard : 2 ≤ Fintype.card q) (hβ : ∀ i, β i = r i • a i)
    (h : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i ≠ 0) → ∑ i, σ (x ⬝ᵥ c i) • a i ≠ 0 →
      ∃ μ : ℝ, ∑ i, (σ (x ⬝ᵥ c i) • β i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
        = μ • ∑ i, σ (x ⬝ᵥ c i) • a i)
    (i : q) {w : n → ℝ} (hw : w ⬝ᵥ c i = 0) : w ⬝ᵥ ψc i = 0 := by
  classical
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
  obtain ⟨e, he⟩ := exists_dot_eq_upl hc (Pi.single i 1)
  obtain ⟨y₀, hy₀⟩ := exists_dot_eq_upl hc (fun l => if l = i then 0 else if l = j then 1 else -1)
  -- the points of the hyperplane where `j` is active and the other units are not
  have hA : ∀ y : n → ℝ, y ⬝ᵥ c i = 0 → 0 < y ⬝ᵥ c j →
      (∀ l, l ≠ i → l ≠ j → y ⬝ᵥ c l < 0) → y ⬝ᵥ ψc i = 0 := fun y h1 h2 h3 =>
    kink_upl hκ hpos ha hβ h hji.symm (by rw [he, Pi.single_eq_same])
      (fun l hl => by rw [he, Pi.single_eq_of_ne hl]) h1 h2 h3
  have h0 : y₀ ⬝ᵥ ψc i = 0 :=
    hA y₀ (by rw [hy₀]; simp only [↓reduceIte])
      (by rw [hy₀]; simp only [hji, ↓reduceIte, zero_lt_one])
      (fun l hli hlj => by
        rw [hy₀]; simp only [hli, hlj, ↓reduceIte, Left.neg_neg_iff, zero_lt_one])
  -- `M > |w c_l|` for every `l`
  set M := 1 + ∑ l, |w ⬝ᵥ c l|
  have hM : ∀ l, |w ⬝ᵥ c l| < M := fun l => by
    have := Finset.single_le_sum (fun l _ => abs_nonneg (w ⬝ᵥ c l)) (Finset.mem_univ l)
    linarith
  have hu : ∀ l, (M • y₀ + w) ⬝ᵥ c l = M * (y₀ ⬝ᵥ c l) + w ⬝ᵥ c l := fun l => by
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
  have h1 := hA (M • y₀ + w) (by rw [hu, hy₀, hw]; simp only [↓reduceIte, mul_zero, add_zero])
    (by rw [hu, hy₀]; simp only [hji, ite_true, ite_false]; linarith [(abs_lt.1 (hM j)).1])
    (fun l hli hlj => by
      rw [hu, hy₀]; simp only [hli, hlj, ite_false]; linarith [(abs_lt.1 (hM l)).2])
  rw [add_dotProduct, smul_dotProduct, h0, smul_zero, zero_add] at h1
  exact h1

/-- **The kinks stay, and one scale, for an activation `σ` that vanishes with `σ'` on the negative
numbers and has `σ > 0`, `σ'(u) u = k σ(u)` on the positive numbers** (`k ≠ 0`). -/
private lemma unitsParallel_upl {σ σ' : ℝ → ℝ} {k : ℕ} (hk : k ≠ 0)
    (hneg : ∀ u : ℝ, u < 0 → σ u = 0 ∧ σ' u = 0)
    (hpos : ∀ u : ℝ, 0 < u → 0 < σ u ∧ σ' u * u = k * σ u)
    (n m q : Type*) [Fintype n] [Fintype m] [Fintype q] : UnitsParallel σ σ' k n m q := by
  classical
  intro c a ψc β hc ha hcard h
  have hκ : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  -- `β_i = r_i a_i`
  choose r hβ using exists_beta_eq_upl hneg (hpos 1 one_pos).1.ne' hc ha h
  -- the kinks stay: `x ψc_i = (e_i ψc_i) (x c_i)`, with `e_i c_l = δ_il`
  choose e he using fun i => exists_dot_eq_upl hc (Pi.single i 1)
  have hψ : ∀ i, ψc i = (e i ⬝ᵥ ψc i) • c i := fun i => eq_smul_of_dot_upl fun x => by
    have hw := dot_psi_eq_zero_upl hκ hpos hc ha hcard hβ h i (w := x - (x ⬝ᵥ c i) • e i)
      (by rw [sub_dotProduct, smul_dotProduct, he, Pi.single_eq_same, smul_eq_mul, mul_one,
        sub_self])
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, sub_eq_zero] at hw
    rw [hw, mul_comm]
  -- one scale: at a point where all units are active, `r_i + k λ_i = μ`
  obtain ⟨x₁, hx₁⟩ := exists_dot_eq_upl hc (fun _ => 1)
  obtain ⟨j₀⟩ : Nonempty q := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨μ, hμ⟩ := coeff_upl hpos ha hβ h (x := x₁) (fun i => by rw [hx₁]; exact one_ne_zero)
    (j := j₀) (by rw [hx₁]; exact one_pos)
  refine ⟨μ, fun i => e i ⬝ᵥ ψc i, fun i => ⟨hψ i, ?_⟩⟩
  have e1 := hμ i (by rw [hx₁]; exact one_pos)
  rw [hψ i, dotProduct_smul, smul_eq_mul, hx₁] at e1
  rw [hβ i]
  congr 1
  linarith

/-- **The kinks stay, and one scale, for ReLU units** (`k = 1`). -/
theorem relu_unitsParallel (n m q : Type*) [Fintype n] [Fintype m] [Fintype q] :
    UnitsParallel relu reluDeriv 1 n m q := by
  -- on `u < 0`: `relu u = reluDeriv u = 0`; on `u > 0`: `relu u = u > 0`, `reluDeriv u = 1`
  exact unitsParallel_upl (σ := relu) (σ' := reluDeriv) one_ne_zero
    (fun u hu => ⟨max_eq_right hu.le, by simp only [reluDeriv, not_lt.2 hu.le, ite_false]⟩)
    (fun u hu => ⟨by simp only [relu, max_eq_left hu.le]; exact hu,
      by simp only [relu, reluDeriv, max_eq_left hu.le, hu, ite_true, Nat.cast_one, one_mul]⟩)
    n m q

/-- **The kinks stay, and one scale, for ReLU² units** (`k = 2`). -/
theorem reluSq_unitsParallel (n m q : Type*) [Fintype n] [Fintype m] [Fintype q] :
    UnitsParallel reluSq reluSqDeriv 2 n m q := by
  -- on `u < 0`: `reluSq u = reluSqDeriv u = 0`; on `u > 0`: `reluSq u = u² > 0`, derivative `2u`
  exact unitsParallel_upl (σ := reluSq) (σ' := reluSqDeriv) two_ne_zero
    (fun u hu => ⟨by rw [reluSq, max_eq_right hu.le]; norm_num,
      by rw [reluSqDeriv, max_eq_right hu.le, mul_zero]⟩)
    (fun u hu => ⟨by rw [reluSq, max_eq_left hu.le]; positivity,
      by rw [reluSq, reluSqDeriv, max_eq_left hu.le]; push_cast; ring⟩)
    n m q

end Skips
