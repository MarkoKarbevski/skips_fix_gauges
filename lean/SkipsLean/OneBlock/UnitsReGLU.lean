import SkipsLean.Activations.ReLU

/-!
# A flat direction of ReGLU hidden units only rescales them

Paper (dimension paper): Lemma C.3, the case of ReGLU, in the generality in which the paper states
it: with a linear term `x M`, a constant `γ` and biases `β_i`, `β'_i`.

A ReGLU hidden unit computes `σ(z_i) w_i a_i` with the gate `z_i = x c_i + β_i`, the value
`w_i = x e_i + β'_i` and `σ(z) = max(z, 0)`. The function is
`G(φ, x) = x M + γ + ∑_i σ(z_i) w_i a_i`, and a direction
`ψ = (ψ_M, ψ_γ, ψ_{c_i}, ψ_{β_i}, ψ_{e_i}, ψ_{β'_i}, ψ_{a_i})` of the weights is flat if the
derivative of `G` along it vanishes at every input `x` at which no gate sits at its kink,
`z_i ≠ 0` for all `i`:

  `x ψ_M + ψ_γ + ∑_i [ σ(z_i) w_i ψ_{a_i} + σ'(z_i) (x ψ_{c_i} + ψ_{β_i}) w_i a_i
      + σ(z_i) (x ψ_{e_i} + ψ_{β'_i}) a_i ] = 0`,

with `σ'(z) = 1[z > 0]`. If every `a_i` and every `e_i` is nonzero, the `c_i` are nonzero and
pairwise non-collinear, and `(e_i, β'_i)` is not proportional to `(c_i, β_i)`, then `ψ_M = 0`,
`ψ_γ = 0`, and for every unit `i` there are numbers `λ_i` and `α_i` with
`(ψ_{c_i}, ψ_{β_i}) = λ_i (c_i, β_i)`, `(ψ_{e_i}, ψ_{β'_i}) = -α_i (e_i, β'_i)` and
`ψ_{a_i} = (α_i - λ_i) a_i`: the directions of the two rescalings of the unit, of its gate and of
its value. Unlike for SwiGLU and GeGLU, the hypothesis on proportionality is needed here (a
numerical check gives a larger kernel without it).
-/

namespace Skips

open Matrix Filter Topology

/-! ### ReLU as a gate: `σ(z) = 1[z > 0] z` -/

/-- `σ(z) = σ'(z) z` for ReLU: the gate `1[z > 0]` times `z`. -/
private lemma relu_eq_reluDeriv_mul (z : ℝ) : relu z = reluDeriv z * z := by
  unfold relu reluDeriv
  split_ifs with hz
  · rw [one_mul, max_eq_left hz.le]
  · rw [zero_mul, max_eq_right (not_lt.1 hz)]

private lemma reluDeriv_of_pos {z : ℝ} (hz : 0 < z) : reluDeriv z = 1 := by
  simp only [reluDeriv, hz, ↓reduceIte]

private lemma reluDeriv_of_nonpos {z : ℝ} (hz : z ≤ 0) : reluDeriv z = 0 := by
  simp only [reluDeriv, not_lt.2 hz, ↓reduceIte]

/-- Near a point where a continuous `f` does not vanish, `f` keeps its sign, so `1[f > 0]` is
constant there. -/
private lemma eventually_reluDeriv {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) {x₀ : X} (h0 : f x₀ ≠ 0) :
    ∀ᶠ x in 𝓝 x₀, f x ≠ 0 ∧ reluDeriv (f x) = reluDeriv (f x₀) := by
  rcases h0.lt_or_gt with hneg | hpos
  · filter_upwards [hf.continuousAt.eventually_lt (g := fun _ => (0 : ℝ)) continuousAt_const
      hneg] with x hx
    exact ⟨hx.ne, by rw [reluDeriv_of_nonpos hx.le, reluDeriv_of_nonpos hneg.le]⟩
  · filter_upwards [(continuousAt_const (y := (0 : ℝ))).eventually_lt hf.continuousAt hpos]
      with x hx
    exact ⟨hx.ne', by rw [reluDeriv_of_pos hx, reluDeriv_of_pos hpos]⟩

/-! ### Polynomials of degree at most `2` along lines -/

/-- `F` is a polynomial of degree at most `2` along every line: `F(p + t v) = A + B t + C t²`. -/
private def QuadOnLines {n : Type*} (F : (n → ℝ) → ℝ) : Prop :=
  ∀ p v : n → ℝ, ∃ A B C : ℝ, ∀ t : ℝ, F (p + t • v) = A + B * t + C * t ^ 2

private lemma quad_add {n : Type*} {F G : (n → ℝ) → ℝ} (hF : QuadOnLines F)
    (hG : QuadOnLines G) : QuadOnLines fun x => F x + G x := fun p v => by
  obtain ⟨A, B, C, h⟩ := hF p v
  obtain ⟨A', B', C', h'⟩ := hG p v
  exact ⟨A + A', B + B', C + C', fun t => by dsimp only; rw [h, h']; ring⟩

private lemma quad_mul_const {n : Type*} {F : (n → ℝ) → ℝ} (hF : QuadOnLines F) (r : ℝ) :
    QuadOnLines fun x => F x * r := fun p v => by
  obtain ⟨A, B, C, h⟩ := hF p v
  exact ⟨A * r, B * r, C * r, fun t => by dsimp only; rw [h]; ring⟩

private lemma quad_const_mul {n : Type*} {F : (n → ℝ) → ℝ} (hF : QuadOnLines F) (r : ℝ) :
    QuadOnLines fun x => r * F x := fun p v => by
  obtain ⟨A, B, C, h⟩ := hF p v
  exact ⟨r * A, r * B, r * C, fun t => by dsimp only; rw [h]; ring⟩

private lemma quad_sum {n ι : Type*} (s : Finset ι) {F : ι → (n → ℝ) → ℝ}
    (hF : ∀ k, QuadOnLines (F k)) : QuadOnLines fun x => ∑ k ∈ s, F k x := fun p v => by
  choose A B C h using fun k => hF k p v
  exact ⟨∑ k ∈ s, A k, ∑ k ∈ s, B k, ∑ k ∈ s, C k, fun t => by
    simp only [h, Finset.sum_add_distrib, Finset.sum_mul]⟩

/-- An affine function `x c + β` is a polynomial of degree at most `2` along lines. -/
private lemma quad_affine {n : Type*} [Fintype n] (c : n → ℝ) (β : ℝ) :
    QuadOnLines fun x => x ⬝ᵥ c + β := fun p v =>
  ⟨p ⬝ᵥ c + β, v ⬝ᵥ c, 0, fun t => by
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]; ring⟩

/-- A product of two affine functions is a polynomial of degree at most `2` along lines. -/
private lemma quad_affine_mul {n : Type*} [Fintype n] (c : n → ℝ) (β : ℝ) (d : n → ℝ) (γ : ℝ) :
    QuadOnLines fun x => (x ⬝ᵥ c + β) * (x ⬝ᵥ d + γ) := fun p v =>
  ⟨(p ⬝ᵥ c + β) * (p ⬝ᵥ d + γ), (p ⬝ᵥ c + β) * (v ⬝ᵥ d) + (v ⬝ᵥ c) * (p ⬝ᵥ d + γ),
    (v ⬝ᵥ c) * (v ⬝ᵥ d), fun t => by
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]; ring⟩

/-- A polynomial `A + B t + C t²` that vanishes near `t = 0` has zero coefficients (use
`t = 0, ±ε/2`). -/
private lemma quad_coeffs_eq_zero {A B C : ℝ}
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), A + B * t + C * t ^ 2 = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  obtain ⟨ε, hε, hεt⟩ := Metric.eventually_nhds_iff.1 h
  have hε2 : 0 < ε / 2 := half_pos hε
  have h0 := hεt (y := 0) (by rw [dist_self]; exact hε)
  have h1 := hεt (y := ε / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos hε2]; linarith)
  have h2 := hεt (y := -(ε / 2))
    (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hε2]; linarith)
  have hC : C * (ε / 2) ^ 2 = 0 := by linear_combination (h1 + h2 - 2 * h0) / 2
  have hB : B * ε = 0 := by linear_combination h1 - h2
  exact ⟨by linear_combination h0, (mul_eq_zero.1 hB).resolve_right hε.ne',
    (mul_eq_zero.1 hC).resolve_right (pow_pos hε2 2).ne'⟩

/-- `(A₀ + t A₁)(B₀ + t B₁) = 0` for all `t` gives the three coefficients `0`. -/
private lemma affine_mul_coeffs {A₀ A₁ B₀ B₁ : ℝ}
    (h : ∀ t : ℝ, (A₀ + t * A₁) * (B₀ + t * B₁) = 0) :
    A₀ * B₀ = 0 ∧ A₀ * B₁ + A₁ * B₀ = 0 ∧ A₁ * B₁ = 0 :=
  quad_coeffs_eq_zero (Eventually.of_forall fun t => by linear_combination h t)

/-- **A polynomial of degree at most `2` along lines that vanishes near a point vanishes
everywhere**: on the line through that point and `y` it is `A + B t + C t²`, zero near `t = 0`. -/
private lemma quad_eq_zero_of_eventually {n : Type*} [Fintype n] {F : (n → ℝ) → ℝ}
    (hF : QuadOnLines F) {x₁ : n → ℝ} (h : ∀ᶠ x in 𝓝 x₁, F x = 0) (y : n → ℝ) : F y = 0 := by
  obtain ⟨A, B, C, hABC⟩ := hF x₁ (y - x₁)
  have hlim : Tendsto (fun t : ℝ => x₁ + t • (y - x₁)) (𝓝 0) (𝓝 x₁) := by
    have := (show Continuous fun t : ℝ => x₁ + t • (y - x₁) by fun_prop).tendsto 0
    rwa [zero_smul, add_zero] at this
  obtain ⟨hA, hB, hC⟩ := quad_coeffs_eq_zero
    ((hlim.eventually h).mono fun t ht => (hABC t).symm.trans ht)
  have h1 := hABC 1
  rw [show x₁ + (1 : ℝ) • (y - x₁) = y by rw [one_smul]; abel] at h1
  rw [h1, hA, hB, hC]
  ring

/-! ### A point of one hyperplane off the others -/

/-- A direction `v` orthogonal to `c_j` and to no other `c_i` (as in `exists_good` of
`UnitsTanh.lean`: a real vector space is not a finite union of proper subspaces). -/
private lemma exists_perp {n q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ)
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
      zero_mem' := by simp only [ne_eq, Set.mem_ofPred_eq, zero_dotProduct]
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
  -- `v = ν - (ν c_j / c_j c_j) c_j`: `v c_j = 0` and `v c_i = ν r_i`
  refine ⟨ν - ((ν ⬝ᵥ c j) / (c j ⬝ᵥ c j)) • c j, ?_, fun i hi => ?_⟩
  · rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, div_mul_cancel₀ _ hjj, sub_self]
  · have : (ν - ((ν ⬝ᵥ c j) / (c j ⬝ᵥ c j)) • c j) ⬝ᵥ c i = ν ⬝ᵥ r i := by
      rw [hr_def]
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    rw [this]; exact hν i hi

/-- The hyperplane `{x c + β = 0}` of a `c ≠ 0` is not empty. -/
private lemma exists_zero_affine {n : Type*} [Fintype n] {c : n → ℝ} (hc : c ≠ 0) (β : ℝ) :
    ∃ x : n → ℝ, x ⬝ᵥ c + β = 0 :=
  ⟨-(β / (c ⬝ᵥ c)) • c, by
    rw [smul_dotProduct, smul_eq_mul, neg_mul,
      div_mul_cancel₀ _ (dotProduct_self_eq_zero.not.2 hc), neg_add_cancel]⟩

/-- **A point of `H_j` off the other hyperplanes.** With the `c_i` nonzero and pairwise
non-collinear, there is `x₀` with `x₀ c_j + β_j = 0` and `x₀ c_i + β_i ≠ 0` for `i ≠ j`: start
on `H_j` and move inside `H_j` along a `v ⊥ c_j` with `v c_i ≠ 0`, avoiding finitely many
values of the step. -/
private lemma exists_on_hyperplane {n q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ)
    (β : q → ℝ) (hc : ∀ i, c i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) (j : q) :
    ∃ x₀ : n → ℝ, x₀ ⬝ᵥ c j + β j = 0 ∧ ∀ i, i ≠ j → x₀ ⬝ᵥ c i + β i ≠ 0 := by
  classical
  obtain ⟨v, hvj, hvi⟩ := exists_perp c hc hcol j
  obtain ⟨x', hx'⟩ := exists_zero_affine (hc j) (β j)
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset
    (Finset.univ.image fun i => -(x' ⬝ᵥ c i + β i) / (v ⬝ᵥ c i))
  refine ⟨x' + s • v, ?_, fun i hi h0 => hs ?_⟩
  · rw [add_dotProduct, smul_dotProduct, hvj, smul_zero, add_zero, hx']
  · rw [Finset.mem_image]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul] at h0
    rw [div_eq_iff (hvi i hi)]
    linear_combination -h0

/-- **Both sides of a hyperplane.** If `P` holds near a point `x₀` of `{x c + β = 0}` (`c ≠ 0`),
then on each side of the hyperplane there is a point near which `P` holds and `x c + β` has that
sign: move from `x₀` a little along `±c`. -/
private lemma exists_sides {n : Type*} [Fintype n] (c : n → ℝ) (β : ℝ) (hc : c ≠ 0)
    {x₀ : n → ℝ} (hx₀ : x₀ ⬝ᵥ c + β = 0) {P : (n → ℝ) → Prop} (hP : ∀ᶠ x in 𝓝 x₀, P x) :
    (∃ y, ∀ᶠ x in 𝓝 y, P x ∧ 0 < x ⬝ᵥ c + β) ∧ (∃ y, ∀ᶠ x in 𝓝 y, P x ∧ x ⬝ᵥ c + β < 0) := by
  have hcc : 0 < c ⬝ᵥ c :=
    lt_of_le_of_ne (Finset.sum_nonneg fun m _ => mul_self_nonneg (c m))
      (Ne.symm (dotProduct_self_eq_zero.not.2 hc))
  have hz : Continuous fun x : n → ℝ => x ⬝ᵥ c + β := by fun_prop
  have hlim : Tendsto (fun δ : ℝ => x₀ + δ • c) (𝓝 0) (𝓝 x₀) := by
    have := (show Continuous fun δ : ℝ => x₀ + δ • c by fun_prop).tendsto 0
    rwa [zero_smul, add_zero] at this
  have hev := hlim.eventually hP.eventually_nhds
  -- the gate at `x₀ + δ c` is `δ (c c)`
  have hval : ∀ δ : ℝ, (x₀ + δ • c) ⬝ᵥ c + β = δ * (c ⬝ᵥ c) := fun δ => by
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul]; linear_combination hx₀
  constructor
  · obtain ⟨δ, hδ, hδ0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_nhdsWithin (s := Set.Ioi 0))).exists
    refine ⟨x₀ + δ • c, hδ.and ?_⟩
    have h0 : (0 : ℝ) < (x₀ + δ • c) ⬝ᵥ c + β := by rw [hval]; exact mul_pos hδ0 hcc
    exact (continuousAt_const (y := (0 : ℝ))).eventually_lt hz.continuousAt h0
  · obtain ⟨δ, hδ, hδ0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_nhdsWithin (s := Set.Iio 0))).exists
    refine ⟨x₀ + δ • c, hδ.and ?_⟩
    have h0 : (x₀ + δ • c) ⬝ᵥ c + β < 0 := by rw [hval]; exact mul_neg_of_neg_of_pos hδ0 hcc
    exact hz.continuousAt.eventually_lt (g := fun _ => (0 : ℝ)) continuousAt_const h0

/-! ### Removing the gates `1[z_i > 0]` -/

/-- **One region of linearity.** If near some point every gate is off its kink with
`1[z_k > 0] = s_k`, then `L + ∑ s_k T_k` vanishes near that point, hence everywhere. -/
private lemma pattern_eq_zero {n q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ)
    (β : q → ℝ) (L : (n → ℝ) → ℝ) (T : q → (n → ℝ) → ℝ) (hL : QuadOnLines L)
    (hT : ∀ i, QuadOnLines (T i))
    (h : ∀ x, (∀ i, x ⬝ᵥ c i + β i ≠ 0) → L x + ∑ i, reluDeriv (x ⬝ᵥ c i + β i) * T i x = 0)
    (s : q → ℝ) {y : n → ℝ}
    (hy : ∀ᶠ x in 𝓝 y, ∀ i, x ⬝ᵥ c i + β i ≠ 0 ∧ reluDeriv (x ⬝ᵥ c i + β i) = s i)
    (x : n → ℝ) : L x + ∑ i, s i * T i x = 0 :=
  quad_eq_zero_of_eventually (quad_add hL (quad_sum _ fun i => quad_const_mul (hT i) (s i)))
    (hy.mono fun x hx => by
      show L x + ∑ i, s i * T i x = 0
      rw [Finset.sum_congr rfl fun i _ => by rw [← (hx i).2]]
      exact h x fun i => (hx i).1) x

/-- **The jump across one hyperplane.** Near a point `x₀` of `H_i = {z_i = 0}` off the other
hyperplanes the other gates keep their values `s_k = 1[z_k(x₀) > 0]`; below `H_i` the identity
reads `L + ∑ s_k T_k = 0`, above it `L + ∑ s_k T_k + T_i = 0`, both on open sets, so both hold
everywhere, and `T_i = 0`. -/
private lemma unit_jump {n q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ) (β : q → ℝ)
    (hc : ∀ i, c i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j)
    (L : (n → ℝ) → ℝ) (T : q → (n → ℝ) → ℝ) (hL : QuadOnLines L) (hT : ∀ i, QuadOnLines (T i))
    (h : ∀ x, (∀ i, x ⬝ᵥ c i + β i ≠ 0) → L x + ∑ i, reluDeriv (x ⬝ᵥ c i + β i) * T i x = 0)
    (i : q) :
    ∃ s : q → ℝ, (∀ x, L x + ∑ k, s k * T k x = 0) ∧ ∀ x, T i x = 0 := by
  classical
  obtain ⟨x₀, hx₀i, hx₀k⟩ := exists_on_hyperplane c β hc hcol i
  -- the values of the gates at `x₀`, with `s_i = 1[0 > 0] = 0`
  obtain ⟨s, hs⟩ : ∃ s : q → ℝ, ∀ k, s k = reluDeriv (x₀ ⬝ᵥ c k + β k) := ⟨_, fun _ => rfl⟩
  have hsi : s i = 0 := by rw [hs, hx₀i]; exact reluDeriv_of_nonpos le_rfl
  -- near `x₀` the other gates keep their values
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ k, k ≠ i →
      x ⬝ᵥ c k + β k ≠ 0 ∧ reluDeriv (x ⬝ᵥ c k + β k) = s k := by
    refine Filter.eventually_all.2 fun k => ?_
    by_cases hk : k = i
    · exact Filter.Eventually.of_forall fun _ h' => absurd hk h'
    · exact (eventually_reluDeriv (f := fun x => x ⬝ᵥ c k + β k) (by fun_prop)
        (hx₀k k hk)).mono fun _ hx _ => ⟨hx.1, hx.2.trans (hs k).symm⟩
  obtain ⟨⟨yp, hyp⟩, ⟨ym, hym⟩⟩ := exists_sides (c i) (β i) (hc i) hx₀i hev
  -- below `H_i`: the values `s`
  have hQ : ∀ x, L x + ∑ k, s k * T k x = 0 :=
    pattern_eq_zero c β L T hL hT h s (hym.mono fun x hx k => by
      by_cases hk : k = i
      · subst hk; exact ⟨hx.2.ne, by rw [hsi]; exact reluDeriv_of_nonpos hx.2.le⟩
      · exact hx.1 k hk)
  -- above `H_i`: the values `s + 1_i`
  have hQ' : ∀ x, L x + ∑ k, (s k + if k = i then 1 else 0) * T k x = 0 :=
    pattern_eq_zero c β L T hL hT h _ (hyp.mono fun x hx k => by
      by_cases hk : k = i
      · subst hk
        exact ⟨hx.2.ne', by simp only [hsi, reluDeriv_of_pos hx.2, ↓reduceIte, zero_add]⟩
      · simp only [hk, ↓reduceIte, add_zero]; exact hx.1 k hk)
  refine ⟨s, hQ, fun x => ?_⟩
  have hdiff : ∑ k, (s k + if k = i then 1 else 0) * T k x = ∑ k, s k * T k x + T i x := by
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  linear_combination hQ' x - hQ x - hdiff

/-- **The gates `1[z_i > 0]` can be removed.** If `L + ∑_i 1[z_i > 0] T_i = 0` at every `x` off
the hyperplanes `z_i = 0`, where `L` and the `T_i` are polynomials of degree at most `2` along
lines and the `c_i` are nonzero and pairwise non-collinear, then every `T_i` and `L` vanish
identically. -/
private lemma gated_eq_zero {n q : Type*} [Fintype n] [Fintype q] (c : q → n → ℝ) (β : q → ℝ)
    (hc : ∀ i, c i ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j)
    (L : (n → ℝ) → ℝ) (T : q → (n → ℝ) → ℝ) (hL : QuadOnLines L) (hT : ∀ i, QuadOnLines (T i))
    (h : ∀ x, (∀ i, x ⬝ᵥ c i + β i ≠ 0) → L x + ∑ i, reluDeriv (x ⬝ᵥ c i + β i) * T i x = 0) :
    (∀ i x, T i x = 0) ∧ ∀ x, L x = 0 := by
  have hTi : ∀ i x, T i x = 0 := fun i => by
    obtain ⟨-, -, hT0⟩ := unit_jump c β hc hcol L T hL hT h i
    exact hT0
  refine ⟨hTi, ?_⟩
  rcases isEmpty_or_nonempty q with hq | ⟨⟨i⟩⟩
  · intro x
    simpa only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] using h x fun i => isEmptyElim i
  · obtain ⟨s, hs, -⟩ := unit_jump c β hc hcol L T hL hT h i
    intro x
    simpa only [hTi, mul_zero, Finset.sum_const_zero, add_zero] using hs x

/-! ### One unit: from `T_i = 0` to the two rescalings -/

/-- A vector `d` orthogonal to every `v ⊥ c` (`c ≠ 0`) is a multiple of `c`. -/
private lemma eq_smul_of_perp {n : Type*} [Fintype n] {c d : n → ℝ} (hc : c ≠ 0)
    (h : ∀ v : n → ℝ, v ⬝ᵥ c = 0 → v ⬝ᵥ d = 0) : d = (d ⬝ᵥ c / (c ⬝ᵥ c)) • c := by
  have hcc : c ⬝ᵥ c ≠ 0 := dotProduct_self_eq_zero.not.2 hc
  have hvc : (d - (d ⬝ᵥ c / (c ⬝ᵥ c)) • c) ⬝ᵥ c = 0 := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, div_mul_cancel₀ _ hcc, sub_self]
  have hvv : (d - (d ⬝ᵥ c / (c ⬝ᵥ c)) • c) ⬝ᵥ (d - (d ⬝ᵥ c / (c ⬝ᵥ c)) • c) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, h _ hvc, hvc, smul_zero, sub_zero]
  exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 hvv)

/-- On the hyperplane `{x c + β = 0}` (`c ≠ 0`) the affine function `x e + β'` does not vanish
identically unless `(e, β')` is a multiple of `(c, β)`. -/
private lemma exists_value_ne_zero {n : Type*} [Fintype n] {c e : n → ℝ} {β β' : ℝ}
    (hc : c ≠ 0) (hec : ∀ r : ℝ, (e, β') ≠ r • (c, β)) :
    ∃ x : n → ℝ, x ⬝ᵥ c + β = 0 ∧ x ⬝ᵥ e + β' ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨xs, hxs⟩ := exists_zero_affine hc β
  have hxse := hcon xs hxs
  -- `e ⊥ v` for every `v ⊥ c`, so `e = r c`
  have he : e = (e ⬝ᵥ c / (c ⬝ᵥ c)) • c := eq_smul_of_perp hc fun v hv => by
    have := hcon (xs + v) (by rw [add_dotProduct, hv, add_zero, hxs])
    rw [add_dotProduct] at this
    linear_combination this - hxse
  -- and `β' = -xs e = r β`
  refine hec (e ⬝ᵥ c / (c ⬝ᵥ c)) (Prod.ext he ?_)
  rw [Prod.smul_snd, smul_eq_mul]
  rw [he, dotProduct_smul, smul_eq_mul] at hxse
  linear_combination hxse - (e ⬝ᵥ c / (c ⬝ᵥ c)) * hxs

/-- **One unit only rescales its gate and its value.** Write `z = x c + β`, `w = x e + β'`,
`u = x ψc + ψβ`, `y = x ψe + ψβ'`. If `z w ψa + u w a + z y a = 0` for every `x` (in every
output coordinate), `a ≠ 0`, `c ≠ 0` and `(e, β')` is not a multiple of `(c, β)`, then
`(ψc, ψβ) = λ (c, β)`, `(ψe, ψβ') = -α (e, β')` and `ψa = (α - λ) a`. -/
private lemma unit_rescale {n k : Type*} [Fintype n] (c : n → ℝ) (β : ℝ) (e : n → ℝ) (β' : ℝ)
    (a : k → ℝ) (ψc : n → ℝ) (ψβ : ℝ) (ψe : n → ℝ) (ψβ' : ℝ) (ψa : k → ℝ)
    (ha : a ≠ 0) (hc : c ≠ 0) (hec : ∀ r : ℝ, (e, β') ≠ r • (c, β))
    (hT : ∀ x : n → ℝ, ∀ o, (x ⬝ᵥ c + β) * (x ⬝ᵥ e + β') * ψa o
      + (x ⬝ᵥ ψc + ψβ) * (x ⬝ᵥ e + β') * a o + (x ⬝ᵥ c + β) * (x ⬝ᵥ ψe + ψβ') * a o = 0) :
    ∃ lam α : ℝ, ψc = lam • c ∧ ψβ = lam * β ∧ ψe = -α • e ∧ ψβ' = -α * β' ∧
      ψa = (α - lam) • a := by
  classical
  have hcc : c ⬝ᵥ c ≠ 0 := dotProduct_self_eq_zero.not.2 hc
  obtain ⟨o₀, ho₀⟩ := Function.ne_iff.1 ha
  rw [Pi.zero_apply] at ho₀
  obtain ⟨x₁, hx₁c, hx₁e⟩ := exists_value_ne_zero hc hec
  -- (1) on `H = {z = 0}` the identity is `u w a = 0`; along `x₁ + t v` with `v ⊥ c` the product
  -- `u w` is `(u(x₁) + t v ψc)(w(x₁) + t v e)` with `w(x₁) ≠ 0`: `u(x₁) = 0` and `v ψc = 0`
  have hline : ∀ v : n → ℝ, v ⬝ᵥ c = 0 → x₁ ⬝ᵥ ψc + ψβ = 0 ∧ v ⬝ᵥ ψc = 0 := fun v hv => by
    have hprod : ∀ t : ℝ,
        ((x₁ ⬝ᵥ ψc + ψβ) + t * (v ⬝ᵥ ψc)) * ((x₁ ⬝ᵥ e + β') + t * (v ⬝ᵥ e)) = 0 := fun t => by
      have h1 := hT (x₁ + t • v) o₀
      have hz : (x₁ + t • v) ⬝ᵥ c + β = 0 := by
        rw [add_dotProduct, smul_dotProduct, hv, smul_zero, add_zero, hx₁c]
      rw [hz] at h1
      simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at h1
      have h2 : (((x₁ ⬝ᵥ ψc + ψβ) + t * (v ⬝ᵥ ψc)) * ((x₁ ⬝ᵥ e + β') + t * (v ⬝ᵥ e)))
          * a o₀ = 0 := by linear_combination h1
      exact (mul_eq_zero.1 h2).resolve_right ho₀
    obtain ⟨h0, h1, -⟩ := affine_mul_coeffs hprod
    have hu : x₁ ⬝ᵥ ψc + ψβ = 0 := (mul_eq_zero.1 h0).resolve_right hx₁e
    refine ⟨hu, ?_⟩
    rw [hu, zero_mul, zero_add] at h1
    exact (mul_eq_zero.1 h1).resolve_right hx₁e
  -- (2) so `ψc = λ c`, and `u(x₁) = 0` with `z(x₁) = 0` gives `ψβ = λ β`
  obtain ⟨lam, hψc⟩ : ∃ lam : ℝ, ψc = lam • c :=
    ⟨_, eq_smul_of_perp hc fun v hv => (hline v hv).2⟩
  have hψβ : ψβ = lam * β := by
    have := (hline 0 (zero_dotProduct c)).1
    rw [hψc, dotProduct_smul, smul_eq_mul] at this
    linear_combination this - lam * hx₁c
  -- (3) now the identity is `z (w (ψa + λ a) + y a) = 0`; along `x + t c` the factor `z` has
  -- slope `c c ≠ 0`, so `w (ψa + λ a) + y a = 0` everywhere
  have hB : ∀ x : n → ℝ, ∀ o,
      (x ⬝ᵥ e + β') * (ψa o + lam * a o) + (x ⬝ᵥ ψe + ψβ') * a o = 0 := fun x o => by
    have hprod : ∀ t : ℝ, ((x ⬝ᵥ c + β) + t * (c ⬝ᵥ c))
        * (((x ⬝ᵥ e + β') * (ψa o + lam * a o) + (x ⬝ᵥ ψe + ψβ') * a o)
          + t * ((c ⬝ᵥ e) * (ψa o + lam * a o) + (c ⬝ᵥ ψe) * a o)) = 0 := fun t => by
      have h1 := hT (x + t • c) o
      rw [hψc, hψβ] at h1
      simp only [add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h1
      linear_combination h1
    obtain ⟨-, h1, h2⟩ := affine_mul_coeffs hprod
    have hB1 := (mul_eq_zero.1 h2).resolve_left hcc
    rw [hB1, mul_zero, zero_add] at h1
    exact (mul_eq_zero.1 h1).resolve_left hcc
  -- (4) `α = (ψa(o₀) + λ a(o₀)) / a(o₀)`; at `x = 0` and `x = 1_m`: `ψβ' = -α β'`, `ψe = -α e`
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (ψa o₀ + lam * a o₀) / a o₀ := ⟨_, rfl⟩
  have hB0 : ∀ o, β' * (ψa o + lam * a o) + ψβ' * a o = 0 := fun o => by
    simpa only [zero_dotProduct, zero_add] using hB 0 o
  have hψβ' : ψβ' = -α * β' := by
    rw [hα, show -((ψa o₀ + lam * a o₀) / a o₀) * β' = -(β' * (ψa o₀ + lam * a o₀)) / a o₀ by
      ring, eq_div_iff ho₀]
    linear_combination hB0 o₀
  have hψe : ψe = -α • e := funext fun m => by
    have h1 := hB (Pi.single m 1) o₀
    simp only [single_dotProduct, one_mul] at h1
    rw [Pi.smul_apply, smul_eq_mul, hα,
      show -((ψa o₀ + lam * a o₀) / a o₀) * e m = -(e m * (ψa o₀ + lam * a o₀)) / a o₀ by ring,
      eq_div_iff ho₀]
    linear_combination h1 - hB0 o₀
  -- (5) at `x₁` (`w(x₁) ≠ 0`): `w(x₁) (ψa(o) - (α - λ) a(o)) = 0`, so `ψa = (α - λ) a`
  have hψa : ψa = (α - lam) • a := funext fun o => by
    have h1 := hB x₁ o
    rw [hψe, hψβ', dotProduct_smul, smul_eq_mul] at h1
    have h2 : (x₁ ⬝ᵥ e + β') * (ψa o - (α - lam) * a o) = 0 := by linear_combination h1
    rw [Pi.smul_apply, smul_eq_mul]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hx₁e)
  exact ⟨lam, α, hψc, hψβ, hψe, hψβ', hψa⟩

/-- **Lemma C.3 for ReGLU.** Rows are indexed by `n` (the coordinates of an input `x`), hidden
units by `q`, and the coordinates of the output by `k`. -/
theorem relu_gated_units_flat {n k q : Type*} [Fintype n] [Fintype k] [Fintype q]
    (c : q → n → ℝ) (β : q → ℝ) (e : q → n → ℝ) (β' : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψe : q → n → ℝ)
    (ψβ' : q → ℝ) (ψa : q → k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j)
    (he : ∀ i, e i ≠ 0) (hec : ∀ i, ∀ r : ℝ, (e i, β' i) ≠ r • (c i, β i))
    (h : ∀ x : n → ℝ, (∀ i, x ⬝ᵥ c i + β i ≠ 0) →
      x ᵥ* ψM + ψγ + ∑ i,
        ((relu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i)) • ψa i
          + (reluDeriv (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i)) • a i
          + (relu (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i)) • a i) = 0) :
    ψM = 0 ∧ ψγ = 0 ∧
      ∃ (lam α : q → ℝ), ∀ i, ψc i = lam i • c i ∧ ψβ i = lam i * β i ∧
        ψe i = -(α i) • e i ∧ ψβ' i = -(α i) * β' i ∧ ψa i = (α i - lam i) • a i := by
  classical
  -- in the output coordinate `o`, with `σ(z) = 1[z > 0] z`, the identity reads
  -- `L(x) + ∑_i 1[z_i > 0] T_i(x) = 0` off the kinks, with `L = x ψM + ψγ` and
  -- `T_i = z_i w_i ψa_i + u_i w_i a_i + z_i y_i a_i`; the gates can be removed
  have key : ∀ o : k, (∀ i x, (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i) * ψa i o
        + (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i) * a i o
        + (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i) * a i o = 0) ∧
      ∀ x : n → ℝ, (x ᵥ* ψM) o + ψγ o = 0 := fun o =>
    gated_eq_zero c β hc hcol (fun x => (x ᵥ* ψM) o + ψγ o)
      (fun i x => (x ⬝ᵥ c i + β i) * (x ⬝ᵥ e i + β' i) * ψa i o
        + (x ⬝ᵥ ψc i + ψβ i) * (x ⬝ᵥ e i + β' i) * a i o
        + (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψe i + ψβ' i) * a i o)
      (quad_affine (fun m => ψM m o) (ψγ o))
      (fun i => quad_add (quad_add (quad_mul_const (quad_affine_mul _ _ _ _) _)
        (quad_mul_const (quad_affine_mul _ _ _ _) _)) (quad_mul_const (quad_affine_mul _ _ _ _) _))
      (fun x hx => by
        have h1 := congrFun (h x hx) o
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
          relu_eq_reluDeriv_mul] at h1
        refine Eq.trans ?_ h1
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring)
  -- every unit only rescales its gate and its value
  choose lam α hlam using fun i => unit_rescale (c i) (β i) (e i) (β' i) (a i) (ψc i) (ψβ i)
    (ψe i) (ψβ' i) (ψa i) (ha i) (hc i) (hec i) fun x o => (key o).1 i x
  -- and `x ψM + ψγ = 0` for all `x`
  have hγ : ψγ = 0 := funext fun o => by
    simpa only [Pi.zero_apply, zero_vecMul, zero_add] using (key o).2 0
  refine ⟨?_, hγ, lam, α, hlam⟩
  ext m o
  simpa only [Matrix.zero_apply, single_vecMul, Pi.smul_apply, row_apply, smul_eq_mul, one_mul, hγ,
    Pi.zero_apply, add_zero] using (key o).2 (Pi.single m 1)

end Skips
