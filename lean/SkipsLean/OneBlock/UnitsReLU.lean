import SkipsLean.Activations.ReLU

/-!
# A flat direction of ReLU or ReLU² hidden units only rescales them

Paper (dimension paper): Lemma C.3, the cases of ReLU and of ReLU², in the generality in which the
paper states it: with a linear term `x M`, a constant `γ` and biases `β_i`.

The function is `G(φ, x) = x M + γ + ∑_i σ(z_i) a_i` with `z_i = x c_i + β_i`, where `c_i` is the
read column of hidden unit `i` and `a_i` its write row. A direction
`ψ = (ψ_M, ψ_γ, ψ_{c_i}, ψ_{β_i}, ψ_{a_i})` of these weights is flat if the derivative of `G`
along it vanishes at every input `x` at which no hidden unit sits at its kink, `z_i ≠ 0` for all `i`:

  `x ψ_M + ψ_γ + ∑_i [ σ(z_i) ψ_{a_i} + σ'(z_i) (x ψ_{c_i} + ψ_{β_i}) a_i ] = 0`.

If every `a_i` is nonzero and the `c_i` are nonzero and pairwise non-collinear, then `ψ_M = 0`,
`ψ_γ = 0`, and for every unit `i` there is a number `λ_i` with
`(ψ_{c_i}, ψ_{β_i}) = λ_i (c_i, β_i)` and `ψ_{a_i} = -λ_i a_i` for ReLU, `ψ_{a_i} = -2 λ_i a_i` for
ReLU²: the direction of the rescaling `(c_i, β_i, a_i) ↦ (λ c_i, λ β_i, a_i / λ)` of the unit,
resp. `a_i / λ²`.

The proof of the paper works at the hyperplanes `H_i = {x : z_i = 0}`, which are pairwise
different: near a point of `H_i` that lies on no other `H_k`, only the terms of unit `i` fail to be
smooth across `H_i`.
-/

namespace Skips

open Matrix Filter Topology

/-! ### Polynomials of degree at most two along lines -/

/-- `f` is a polynomial of degree at most `2` along every line: `f(x + t v) = f(x) + t A + t² B`. -/
private def QuadAlong {n k : Type*} (f : (n → ℝ) → k → ℝ) : Prop :=
  ∀ x v : n → ℝ, ∃ A B : k → ℝ, ∀ t : ℝ, f (x + t • v) = f x + t • A + t ^ 2 • B

private lemma quadAlong_add {n k : Type*} {f g : (n → ℝ) → k → ℝ} (hf : QuadAlong f)
    (hg : QuadAlong g) : QuadAlong (fun x => f x + g x) := by
  intro x v
  obtain ⟨A, B, h1⟩ := hf x v
  obtain ⟨A', B', h2⟩ := hg x v
  refine ⟨A + A', B + B', fun t => ?_⟩
  dsimp only
  rw [h1, h2, smul_add, smul_add]
  abel

private lemma quadAlong_sum {n k ι : Type*} (s : Finset ι) (f : ι → (n → ℝ) → k → ℝ)
    (hf : ∀ i, QuadAlong (f i)) : QuadAlong (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact fun x v => ⟨0, 0, fun t => by simp only [Finset.sum_empty, smul_zero, add_zero]⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact quadAlong_add (hf i) ih

/-- `x ↦ x W + b` is a polynomial along lines. -/
private lemma quadAlong_affine {n k : Type*} [Fintype n] (W : Matrix n k ℝ) (b : k → ℝ) :
    QuadAlong (fun x => x ᵥ* W + b) := by
  intro x v
  refine ⟨v ᵥ* W, 0, fun t => ?_⟩
  dsimp only
  rw [add_vecMul, smul_vecMul, smul_zero, add_zero]
  abel

/-- `x ↦ (x c + β) u` is a polynomial along lines. -/
private lemma quadAlong_lin_smul {n k : Type*} [Fintype n] (c : n → ℝ) (β : ℝ) (u : k → ℝ) :
    QuadAlong (fun x => (x ⬝ᵥ c + β) • u) := by
  intro x v
  refine ⟨(v ⬝ᵥ c) • u, 0, fun t => ?_⟩
  ext o
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_dotProduct, smul_dotProduct,
    Pi.zero_apply]
  ring

/-- A polynomial of degree at most `2` along lines that vanishes near a point vanishes
everywhere: on the line through `p` and `y`, a quadratic in `t` with zeros at `0`, `t₀`, `-t₀`
(`t₀ ≠ 0`) is zero. -/
private lemma quadAlong_eq_zero {n k : Type*} [Fintype n] {f : (n → ℝ) → k → ℝ}
    (hf : QuadAlong f) {p : n → ℝ} (hp : ∀ᶠ x in 𝓝 p, f x = 0) (y : n → ℝ) : f y = 0 := by
  obtain ⟨A, B, hAB⟩ := hf p (y - p)
  have hline : ∀ s : ℝ, Tendsto (fun t : ℝ => p + (s * t) • (y - p)) (𝓝 0) (𝓝 p) := fun s => by
    have hcont : Continuous (fun t : ℝ => p + (s * t) • (y - p)) := by fun_prop
    simpa using hcont.tendsto 0
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ := ((((hline 1).eventually hp).and
    ((hline (-1)).eventually hp)).filter_mono nhdsWithin_le_nhds |>.and
      (eventually_mem_nhdsWithin (s := Set.Ioi 0))).exists
  have hp0 : f p = 0 := hp.self_of_nhds
  have ht0 : t ≠ 0 := (Set.mem_Ioi.1 ht).ne'
  rw [hAB, hp0] at h1 h2
  have hy : f y = f (p + (1 : ℝ) • (y - p)) := by rw [one_smul, add_sub_cancel]
  rw [hy, hAB, hp0]
  ext o
  have e1 := congrFun h1 o
  have e2 := congrFun h2 o
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
  have hA : A o = 0 := by
    have : t * A o = 0 := by linear_combination (e1 - e2) / 2
    exact (mul_eq_zero.1 this).resolve_left ht0
  have hB : B o = 0 := by
    have : t ^ 2 * B o = 0 := by linear_combination (e1 + e2) / 2
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 ht0)
  rw [hA, hB]
  ring

/-! ### The hyperplanes of the hidden units -/

/-- Near a point off the hyperplane `x c + β = 0`, the sign of `x c + β` does not change. -/
private lemma eventually_sign {n : Type*} [Fintype n] (c : n → ℝ) (β : ℝ) {p : n → ℝ}
    (hp : p ⬝ᵥ c + β ≠ 0) :
    ∀ᶠ x in 𝓝 p, x ⬝ᵥ c + β ≠ 0 ∧ (0 < x ⬝ᵥ c + β ↔ 0 < p ⬝ᵥ c + β) := by
  have hcont : Continuous fun x : n → ℝ => x ⬝ᵥ c + β := by fun_prop
  rcases hp.lt_or_gt with hneg | hpos
  · filter_upwards [(hcont.tendsto p).eventually (eventually_lt_nhds hneg)] with x hx
    exact ⟨hx.ne, iff_of_false (not_lt.2 hx.le) (not_lt.2 hneg.le)⟩
  · filter_upwards [(hcont.tendsto p).eventually (eventually_gt_nhds hpos)] with x hx
    exact ⟨hx.ne', iff_of_true hx hpos⟩

/-- A direction `v` with `v c_j = 0` and `v c_i ≠ 0` for `i ≠ j`: a real vector space is not a
finite union of proper subspaces (as in `UnitsTanh.lean`). -/
private lemma exists_perp_dir {n q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ)
    (hc : ∀ i, c i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) (j : q) :
    ∃ v : n → ℝ, v ⬝ᵥ c j = 0 ∧ ∀ i, i ≠ j → v ⬝ᵥ c i ≠ 0 := by
  have hjj : c j ⬝ᵥ c j ≠ 0 := dotProduct_self_eq_zero.not.2 (hc j)
  -- `r i`: the component of `c i` orthogonal to `c j`; it is nonzero for `i ≠ j`
  set r : q → n → ℝ := fun i => c i - ((c j ⬝ᵥ c i) / (c j ⬝ᵥ c j)) • c j with hr_def
  have hr : ∀ i, i ≠ j → r i ≠ 0 := fun i hi h0 =>
    hcol i j hi _ (sub_eq_zero.1 h0)
  -- the kernels of `ν ↦ ν r_i` are proper subspaces, so some `ν` avoids all of them
  let K : {i // i ≠ j} → Submodule ℝ (n → ℝ) := fun i =>
    { carrier := {ν | ν ⬝ᵥ r i = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢; rw [add_dotProduct, hx, hy, add_zero]
      zero_mem' := by simp
      smul_mem' := fun s x hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢; rw [smul_dotProduct, hx, smul_zero] }
  obtain ⟨ν, hν⟩ : ∃ ν : n → ℝ, ∀ i, i ≠ j → ν ⬝ᵥ r i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ (p := K) (by
      ext ν
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      obtain ⟨i, hij, h0⟩ := hcon ν
      exact ⟨⟨i, hij⟩, h0⟩)
    have hmem : r i ∈ K i := hi ▸ Submodule.mem_top
    exact hr i.1 i.2 (dotProduct_self_eq_zero.1 hmem)
  -- `v = ν - (ν c_j / c_j c_j) c_j` has `v c_j = 0` and `v c_i = ν r_i`
  refine ⟨ν - ((ν ⬝ᵥ c j) / (c j ⬝ᵥ c j)) • c j, ?_, fun i hi => ?_⟩
  · rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    field_simp
    ring
  · have : (ν - ((ν ⬝ᵥ c j) / (c j ⬝ᵥ c j)) • c j) ⬝ᵥ c i = ν ⬝ᵥ r i := by
      rw [hr_def]
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    rw [this]; exact hν i hi

/-- **A point of `H_j` on no other `H_i`**: `x₀ c_j + β_j = 0` and `x₀ c_i + β_i ≠ 0` for
`i ≠ j`. Start at the point `x₁ = -(β_j / c_j c_j) c_j` of `H_j` and move along a direction `v`
of `H_j` that is transverse to every other `H_i`, avoiding the finitely many crossings. -/
private lemma exists_on_hyperplane {n q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ)
    (β : q → ℝ) (hc : ∀ i, c i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) (j : q) :
    ∃ x₀ : n → ℝ, x₀ ⬝ᵥ c j + β j = 0 ∧ ∀ i, i ≠ j → x₀ ⬝ᵥ c i + β i ≠ 0 := by
  classical
  have hjj : c j ⬝ᵥ c j ≠ 0 := dotProduct_self_eq_zero.not.2 (hc j)
  obtain ⟨v, hvj, hvi⟩ := exists_perp_dir c hc hcol j
  obtain ⟨x₁, h1⟩ : ∃ x₁ : n → ℝ, x₁ ⬝ᵥ c j + β j = 0 :=
    ⟨-(β j / (c j ⬝ᵥ c j)) • c j, by rw [smul_dotProduct, smul_eq_mul]; field_simp; ring⟩
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset
    (Finset.univ.image fun i => -(x₁ ⬝ᵥ c i + β i) / (v ⬝ᵥ c i))
  refine ⟨x₁ + s • v, ?_, fun i hi h0 => hs ?_⟩
  · rw [add_dotProduct, smul_dotProduct, hvj, smul_zero, add_zero, h1]
  · refine Finset.mem_image.2 ⟨i, Finset.mem_univ _, ?_⟩
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul] at h0
    rw [div_eq_iff (hvi i hi)]
    linarith

/-- **The two sides of `H_j`**: two points `p₁`, `p₂` on no hyperplane, with `z_j(p₁) > 0`,
`z_j(p₂) < 0`, and the same sign of `z_i` at both for every `i ≠ j`: the points `x₀ ± t c_j` for
a point `x₀` of `H_j` on no other `H_i` and a small `t > 0`. -/
private lemma exists_two_sides {n q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ)
    (β : q → ℝ) (hc : ∀ i, c i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) (j : q) :
    ∃ p₁ p₂ : n → ℝ, (∀ i, p₁ ⬝ᵥ c i + β i ≠ 0) ∧ (∀ i, p₂ ⬝ᵥ c i + β i ≠ 0) ∧
      0 < p₁ ⬝ᵥ c j + β j ∧ p₂ ⬝ᵥ c j + β j < 0 ∧
      ∀ i, i ≠ j → (0 < p₁ ⬝ᵥ c i + β i ↔ 0 < p₂ ⬝ᵥ c i + β i) := by
  obtain ⟨x₀, h0j, h0i⟩ := exists_on_hyperplane c β hc hcol j
  have hjj : 0 < c j ⬝ᵥ c j :=
    lt_of_le_of_ne (Finset.sum_nonneg fun m _ => mul_self_nonneg (c j m))
      (Ne.symm (dotProduct_self_eq_zero.not.2 (hc j)))
  -- near `x₀`, every other unit keeps its sign
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ i, i ≠ j →
      x ⬝ᵥ c i + β i ≠ 0 ∧ (0 < x ⬝ᵥ c i + β i ↔ 0 < x₀ ⬝ᵥ c i + β i) := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : i = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hi h
    · exact (eventually_sign (c i) (β i) (h0i i hi)).mono fun _ h _ => h
  have hline : ∀ s : ℝ, Tendsto (fun t : ℝ => x₀ + (s * t) • c j) (𝓝 0) (𝓝 x₀) := fun s => by
    have hcont : Continuous (fun t : ℝ => x₀ + (s * t) • c j) := by fun_prop
    simpa using hcont.tendsto 0
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ := ((((hline 1).eventually hev).and
    ((hline (-1)).eventually hev)).filter_mono nhdsWithin_le_nhds |>.and
      (eventually_mem_nhdsWithin (s := Set.Ioi 0))).exists
  have ht0 : 0 < t := ht
  -- `z_j(x₀ + s t c_j) = s t (c_j c_j)`
  have hz : ∀ s : ℝ, (x₀ + (s * t) • c j) ⬝ᵥ c j + β j = s * t * (c j ⬝ᵥ c j) := fun s => by
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
    linear_combination h0j
  have hz1 : 0 < (x₀ + (1 * t) • c j) ⬝ᵥ c j + β j := by
    rw [hz]; exact mul_pos (mul_pos one_pos ht0) hjj
  have hz2 : (x₀ + (-1 * t) • c j) ⬝ᵥ c j + β j < 0 := by
    rw [hz]; exact mul_neg_of_neg_of_pos (by linarith) hjj
  refine ⟨x₀ + (1 * t) • c j, x₀ + (-1 * t) • c j, fun i => ?_, fun i => ?_, hz1, hz2,
    fun i hi => (h1 i hi).2.trans (h2 i hi).2.symm⟩
  · by_cases hi : i = j
    · rw [hi]; exact hz1.ne'
    · exact (h1 i hi).1
  · by_cases hi : i = j
    · rw [hi]; exact hz2.ne
    · exact (h2 i hi).1

/-! ### The core of the argument, for any activation that is polynomial on both sides of `0` -/

/-- **Core of Lemma C.3 for piecewise polynomial activations.** Let the identity
`L(x) + ∑ᵢ termᵢ(x) = 0` hold at every input off the hyperplanes `H_i`, where `termᵢ = Tᵢ` on
`z_i > 0` and `termᵢ = 0` on `z_i < 0`, and `L`, `Tᵢ` are polynomials of degree at most `2` along
lines. Then every `Tᵢ` and `L` vanish identically. Near a point `p` off all hyperplanes, the
identity is the polynomial `L + ∑_{z_i(p) > 0} Tᵢ`, which therefore vanishes everywhere; on the two
sides of `H_j` these polynomials differ by `T_j` alone. -/
private lemma units_core {n k q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ) (β : q → ℝ)
    (hc : ∀ i, c i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j)
    (L : (n → ℝ) → k → ℝ) (hL : QuadAlong L) (term T : q → (n → ℝ) → k → ℝ)
    (hT : ∀ i, QuadAlong (T i))
    (hpos : ∀ i x, 0 < x ⬝ᵥ c i + β i → term i x = T i x)
    (hneg : ∀ i x, x ⬝ᵥ c i + β i < 0 → term i x = 0)
    (h : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i + β i ≠ 0) → L x + ∑ i, term i x = 0) :
    (∀ i x, T i x = 0) ∧ ∀ x, L x = 0 := by
  classical
  -- (1) near a point `p` off all hyperplanes the identity is a polynomial, which then vanishes
  have hA : ∀ p : n → ℝ, (∀ i, p ⬝ᵥ c i + β i ≠ 0) → ∀ y,
      L y + ∑ i ∈ Finset.univ.filter (fun i => 0 < p ⬝ᵥ c i + β i), T i y = 0 := by
    intro p hp y
    refine quadAlong_eq_zero (p := p) (quadAlong_add hL (quadAlong_sum _ T hT)) ?_ y
    filter_upwards [Filter.eventually_all.2 fun i => eventually_sign (c i) (β i) (hp i)]
      with x hx
    refine Eq.trans ?_ (h x fun i => (hx i).1)
    rw [Finset.sum_filter]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · exact (hpos i x ((hx i).2.2 hi)).symm
    · exact (hneg i x (lt_of_le_of_ne (not_lt.1 fun h' => hi ((hx i).2.1 h')) (hx i).1)).symm
  -- (2) each `T_j` vanishes: compare the two sides of `H_j`
  have hT0 : ∀ j y, T j y = 0 := by
    intro j y
    obtain ⟨p₁, p₂, hp₁, hp₂, hj₁, hj₂, hsame⟩ := exists_two_sides c β hc hcol j
    have hS : Finset.univ.filter (fun i => 0 < p₁ ⬝ᵥ c i + β i)
        = insert j (Finset.univ.filter (fun i => 0 < p₂ ⬝ᵥ c i + β i)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hi : i = j
      · rw [hi]; exact iff_of_true hj₁ (Or.inl rfl)
      · rw [hsame i hi]; exact ⟨Or.inr, fun h' => h'.resolve_left hi⟩
    have hj : j ∉ Finset.univ.filter (fun i => 0 < p₂ ⬝ᵥ c i + β i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      exact hj₂.le
    have e1 := hA p₁ hp₁ y
    rw [hS, Finset.sum_insert hj, add_left_comm, hA p₂ hp₂ y, add_zero] at e1
    exact e1
  -- (3) `L` vanishes: use any point off all hyperplanes
  refine ⟨hT0, fun y => ?_⟩
  obtain ⟨p, hp⟩ : ∃ p : n → ℝ, ∀ i, p ⬝ᵥ c i + β i ≠ 0 := by
    rcases isEmpty_or_nonempty q with hq | ⟨⟨j⟩⟩
    · exact ⟨0, fun i => isEmptyElim i⟩
    · obtain ⟨p₁, -, hp₁, -⟩ := exists_two_sides c β hc hcol j
      exact ⟨p₁, hp₁⟩
  have e := hA p hp y
  rwa [Finset.sum_eq_zero (fun i _ => hT0 i y), add_zero] at e

/-! ### Reading off the coefficients -/

/-- An affine function `x ↦ x c + β` with `c ≠ 0` takes a nonzero value. -/
private lemma exists_affine_ne_zero {n : Type*} [Fintype n] {c : n → ℝ} (hc : c ≠ 0) (β : ℝ) :
    ∃ x : n → ℝ, x ⬝ᵥ c + β ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h0 := hcon 0
  rw [zero_dotProduct, zero_add] at h0
  have h1 := hcon c
  rw [h0, add_zero] at h1
  exact hc (dotProduct_self_eq_zero.1 h1)

/-- Comparing the coefficients of two affine functions. -/
private lemma eq_of_affine_eq {n : Type*} [Fintype n] {u v : n → ℝ} {b b' : ℝ}
    (h : ∀ x : n → ℝ, x ⬝ᵥ u + b = x ⬝ᵥ v + b') : u = v ∧ b = b' := by
  classical
  have hb : b = b' := by simpa using h 0
  refine ⟨funext fun m => ?_, hb⟩
  simpa [hb] using h (Pi.single m 1)

/-- If `x ψ_c + ψ_β = l (x c + β)` for all `x`, then `ψ_c = l c` and `ψ_β = l β`. -/
private lemma coeffs_of_eq_mul {n : Type*} [Fintype n] {c ψc : n → ℝ} {β ψβ l : ℝ}
    (h : ∀ x : n → ℝ, x ⬝ᵥ ψc + ψβ = l * (x ⬝ᵥ c + β)) : ψc = l • c ∧ ψβ = l * β :=
  eq_of_affine_eq fun x => by rw [h x, dotProduct_smul, smul_eq_mul]; ring

/-- **One ReLU unit.** If `(x c + β) ψ_a + (x ψ_c + ψ_β) a = 0` for all `x`, with `a ≠ 0` and
`c ≠ 0`, then `(ψ_c, ψ_β) = l (c, β)` and `ψ_a = -l a`. -/
private lemma relu_unit_coeffs {n k : Type*} [Fintype n] {c ψc : n → ℝ} {β ψβ : ℝ}
    {a ψa : k → ℝ} (ha : a ≠ 0) (hc : c ≠ 0)
    (h : ∀ x : n → ℝ, (x ⬝ᵥ c + β) • ψa + (x ⬝ᵥ ψc + ψβ) • a = 0) :
    ∃ l : ℝ, ψc = l • c ∧ ψβ = l * β ∧ ψa = -l • a := by
  obtain ⟨o, ho⟩ := Function.ne_iff.1 ha
  rw [Pi.zero_apply] at ho
  set l := -(ψa o / a o) with hl
  have hl2 : l * a o = -ψa o := by rw [hl, neg_mul, div_mul_cancel₀ _ ho]
  -- the output `o` gives `x ψ_c + ψ_β = l (x c + β)`
  have hw : ∀ x : n → ℝ, x ⬝ᵥ ψc + ψβ = l * (x ⬝ᵥ c + β) := fun x => by
    have e := congrFun (h x) o
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e
    have key : a o * ((x ⬝ᵥ ψc + ψβ) - l * (x ⬝ᵥ c + β)) = 0 := by
      linear_combination e - (x ⬝ᵥ c + β) * hl2
    exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left ho)
  obtain ⟨hψc, hψβ⟩ := coeffs_of_eq_mul hw
  refine ⟨l, hψc, hψβ, funext fun o' => ?_⟩
  -- every output: `(x c + β) (ψ_a + l a) = 0`, at an `x` with `x c + β ≠ 0`
  obtain ⟨x, hx⟩ := exists_affine_ne_zero hc β
  have e := congrFun (h x) o'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hw x] at e
  have key : (x ⬝ᵥ c + β) * (ψa o' + l * a o') = 0 := by linear_combination e
  have := (mul_eq_zero.1 key).resolve_left hx
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith

/-- **Lemma C.3 for ReLU.** Rows are indexed by `n` (the coordinates of an input `x`), hidden
units by `q`, and the coordinates of the output by `k`. -/
theorem relu_units_flat {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψa : q → k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j)
    (h : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i + β i ≠ 0) →
      x ᵥ* ψM + ψγ + ∑ i, (relu (x ⬝ᵥ c i + β i) • ψa i
        + (reluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i)) • a i) = 0) :
    ψM = 0 ∧ ψγ = 0 ∧
      ∃ lam : q → ℝ, ∀ i, ψc i = lam i • c i ∧ ψβ i = lam i * β i ∧ ψa i = -(lam i) • a i := by
  classical
  -- on the side `z_i > 0` unit `i` contributes `z_i ψ_{a_i} + (x ψ_{c_i} + ψ_{β_i}) a_i`,
  -- on the side `z_i < 0` nothing
  obtain ⟨hT0, hL0⟩ := units_core c β hc hcol (fun x => x ᵥ* ψM + ψγ) (quadAlong_affine ψM ψγ)
    (fun i x => relu (x ⬝ᵥ c i + β i) • ψa i
      + (reluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i)) • a i)
    (fun i x => (x ⬝ᵥ c i + β i) • ψa i + (x ⬝ᵥ ψc i + ψβ i) • a i)
    (fun i => quadAlong_add (quadAlong_lin_smul _ _ _) (quadAlong_lin_smul _ _ _))
    (fun i x hz => by simp only [relu, reluDeriv, max_eq_left hz.le, hz, ite_true, one_mul])
    (fun i x hz => by
      simp only [relu, reluDeriv, max_eq_right hz.le, not_lt.2 hz.le, ite_false, zero_smul,
        zero_mul, add_zero])
    h
  -- `x ψ_M + ψ_γ = 0` for all `x`
  have hγ : ψγ = 0 := by simpa using hL0 0
  refine ⟨?_, hγ, ?_⟩
  · ext m o
    simpa [hγ] using congrFun (hL0 (Pi.single m 1)) o
  · choose lam hlam using fun i => relu_unit_coeffs (ha i) (hc i) (hT0 i)
    exact ⟨lam, hlam⟩

/-- **Lemma C.3 for ReLU².** -/
theorem reluSq_units_flat {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψa : q → k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j)
    (h : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i + β i ≠ 0) →
      x ᵥ* ψM + ψγ + ∑ i, (reluSq (x ⬝ᵥ c i + β i) • ψa i
        + (reluSqDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i)) • a i) = 0) :
    ψM = 0 ∧ ψγ = 0 ∧
      ∃ lam : q → ℝ, ∀ i, ψc i = lam i • c i ∧ ψβ i = lam i * β i ∧
        ψa i = -(2 * lam i) • a i := by
  sorry

end Skips
