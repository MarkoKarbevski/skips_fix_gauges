import SkipsLean.Absorb.ReluSqBiasesCells

/-!
# ReLU² blocks with biases: squares, costs and dimensions

Paper (absorb paper), Appendix C.2, proof of Theorem C.2 (iii).

"Squares. […] a unit with read `λ ω` and bias `λ ω_0` computes `λ² r(±(x ω + ω_0))` times its
write, on side `±` as `λ ≷ 0`. Let `μ_±` be the sum of `λ²` times the write over the units of
`B_{θ′}` on side `±`, minus the same sum over the units of `B_θ`. […] So `μ_+ = μ_− =: μ_H`, the
terms of `H` are `μ_H z²`, and `∑_H μ_H (x ω_H + ω_{0,H})² = x M + const` (12).
Costs. For generic `θ` the units of `B_θ` have nonzero reads and writes and lie on distinct
hyperplanes. […] Let `S` and `U` be the sets of units `i` of `B_θ` with `μ_{H_i} = −ŵ_i` and with
`μ_{H_i} ∉ {0, −ŵ_i}`, and `N` the set of the other hyperplanes with `μ_H ≠ 0`. Then
`n ≥ |U| + 2|N|`.
Dimensions. Modulo constants, a polynomial of degree at most two is a pair of a quadratic form
and a linear part, in a space of dimension `d_model (d_model + 3)/2`, in which `(x ω + ω_0)²`
becomes `φ(ω, ω_0) = (ω ω^⊤, 2 ω_0 ω)`. For each output coordinate `o`, with `M_{:,o}` the column
`o` of `M`, (12) reads `∑_{i∈U} μ_{H_i,o} φ(w_i, b_i) + ∑_{H∈N} μ_{H,o} φ(ω_H, ω_{0,H}) = τ_o`,
where `τ_o = (0, M_{:,o}) + ∑_{i∈S} ŵ_{i,o} φ(w_i, b_i)`. So the vectors `τ_1, …, τ_{d_model}` and
`φ(w_i, b_i)`, `i ∈ U`, lie in the span of `|U| + |N|` vectors. […]
Conclusion. So `|U| + |N| ≥ min(d_model (d_model + 3)/2, d_model + |U|)`. If the minimum is
`d_model + |U|`, then `|N| ≥ d_model` and `n ≥ 2 d_model`. Otherwise
`|U| + |N| ≥ d_model (d_model + 3)/2 ≥ 2 d_model`, and again `n ≥ 2 d_model`. For `M ≠ 0` of any
rank, the same argument with `rank M` in place of `d_model` gives `n ≥ 2`."

Here: `φ` (`sqForm`, with values in pairs of a matrix and a row) and `τ_o` (`sqTarget`); the three
steps "Squares", "Costs" and "Dimensions" as one statement, from the identities of the cells
(`Absorb/ReluSqBiasesCells.lean`); and the "Conclusion" under the generic condition of the proof.

The statement of the three steps avoids the list of the hyperplanes that carry no unit of `B_θ`:
the units of `B_{θ′}` on these hyperplanes are split into those whose argument is positive far
away in a fixed direction (`F₁`) and those whose argument is positive far away in the opposite
direction (`F₂`), and each `τ_o` lies in the span of the `φ(w_i, b_i)`, `i ∈ U`, with the `φ` of
the units of `F₁`, and also with those of `F₂`. A hyperplane of the paper's set `N` has a unit in
`F₁` and one in `F₂`, so this contains "`τ_o` lies in the span of `|U| + |N|` vectors", and the
count `n ≥ |U| + |F₁| + |F₂|` contains `n ≥ |U| + 2|N|`.

The generic condition is used in the form: for disjoint `S`, `U` with `|U| < 2 d`, the vectors
`τ_o` and `φ(w_i, b_i)`, `i ∈ U`, are linearly independent (for `|U| ≥ 2 d` the count alone gives
`n ≥ 2 d`; `2 d − 1 ≤ d (d + 1)/2`, so the paper's minimum is `d + |U|` for these `U`). For the
same width and `M ≠ 0` the condition is: for every `S` some `τ_o` is nonzero.
-/

namespace Skips

open Matrix

variable {p q m m' : Type*} [Fintype p] [Fintype m] [Fintype m']

/-- **`φ(ω, ω_0) = (ω ω^⊤, 2 ω_0 ω)`:** the polynomial `(x ω + ω_0)²` modulo constants, as the pair
of its quadratic form and its linear part. -/
def sqForm (ω : p → ℝ) (ω₀ : ℝ) : Matrix p p ℝ × (p → ℝ) :=
  (Matrix.vecMulVec ω ω, (2 * ω₀) • ω)

/-- **`τ_o = (0, M_{:,o}) + ∑_{i∈S} ŵ_{i,o} φ(w_i, b_i)`.** -/
def sqTarget (M : Matrix p q ℝ) (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (S : Finset m) (o : q) : Matrix p p ℝ × (p → ℝ) :=
  ((0 : Matrix p p ℝ), fun a => M a o) + ∑ i ∈ S, Ww i o • sqForm (Wrᵀ i) (b i)

/-! ### Step 0: from the polynomials of the cells to the vectors `φ` -/

/-- A row of `x A` is `x` times a column of `A`. -/
private theorem vecMul_apply_rsn {n : Type*} (x : p → ℝ) (A : Matrix p n ℝ) (i : n) :
    (x ᵥ* A) i = x ⬝ᵥ Aᵀ i := rfl

/-- The coordinate `o` of the polynomial of a cell, with the open units as coefficients. -/
private theorem reluSqCell_apply_rsn (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (x y : p → ℝ) (o : q) :
    reluSqCell Wr b Ww c x y o
      = ∑ i, (if 0 < x ⬝ᵥ Wrᵀ i + b i then Ww i o else 0) * (y ⬝ᵥ Wrᵀ i + b i) ^ 2 + c o := by
  classical
  simp only [reluSqCell, Pi.add_apply, Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ite_apply, vecMul_apply_rsn, vecMul_apply_rsn]
  split_ifs
  · rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  · rw [Pi.zero_apply, zero_mul]

/-- The quadratic part of `∑ κ_i (y u_i + β_i)²`, by polarization at `y`, `z`, `y + z`. -/
private theorem sum_quad_rsn {ι : Type*} [Fintype ι] (κ : ι → ℝ) (u : ι → p → ℝ) (β : ι → ℝ)
    (y z : p → ℝ) :
    ∑ i, κ i * ((y + z) ⬝ᵥ u i + β i) ^ 2 + ∑ i, κ i * ((-(y + z)) ⬝ᵥ u i + β i) ^ 2
      - ∑ i, κ i * (y ⬝ᵥ u i + β i) ^ 2 - ∑ i, κ i * ((-y) ⬝ᵥ u i + β i) ^ 2
      - ∑ i, κ i * (z ⬝ᵥ u i + β i) ^ 2 - ∑ i, κ i * ((-z) ⬝ᵥ u i + β i) ^ 2
      + 2 * ∑ i, κ i * ((0 : p → ℝ) ⬝ᵥ u i + β i) ^ 2
      = 4 * ∑ i, κ i * ((y ⬝ᵥ u i) * (z ⬝ᵥ u i)) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [add_dotProduct, neg_dotProduct, zero_dotProduct]
  ring

/-- The linear part of `∑ κ_i (y u_i + β_i)²`, from `y` and `-y`. -/
private theorem sum_lin_rsn {ι : Type*} [Fintype ι] (κ : ι → ℝ) (u : ι → p → ℝ) (β : ι → ℝ)
    (y : p → ℝ) :
    ∑ i, κ i * (y ⬝ᵥ u i + β i) ^ 2 - ∑ i, κ i * ((-y) ⬝ᵥ u i + β i) ^ 2
      = 2 * ∑ i, κ i * (2 * β i * (y ⬝ᵥ u i)) := by
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [neg_dotProduct]
  ring

/-- **Step 0.** An identity `y ℓ + ∑ κ_i (y u_i + β_i)² + k = ∑ κ'_j (y u'_j + β'_j)² + k'` of
polynomials in `y` is an identity of their quadratic and linear parts:
`(0, ℓ) + ∑ κ_i φ(u_i, β_i) = ∑ κ'_j φ(u'_j, β'_j)`. -/
private theorem sqForm_sum_eq_rsn {ι ι' : Type*} [Fintype ι] [Fintype ι'] (κ : ι → ℝ)
    (u : ι → p → ℝ) (β : ι → ℝ) (κ' : ι' → ℝ) (u' : ι' → p → ℝ) (β' : ι' → ℝ) (ℓ : p → ℝ)
    (k k' : ℝ)
    (h : ∀ y : p → ℝ, y ⬝ᵥ ℓ + ∑ i, κ i * (y ⬝ᵥ u i + β i) ^ 2 + k
      = ∑ j, κ' j * (y ⬝ᵥ u' j + β' j) ^ 2 + k') :
    ((0 : Matrix p p ℝ), ℓ) + ∑ i, κ i • sqForm (u i) (β i)
      = ∑ j, κ' j • sqForm (u' j) (β' j) := by
  classical
  -- the quadratic parts agree (polarization)
  have hB : ∀ y z : p → ℝ, ∑ i, κ i * ((y ⬝ᵥ u i) * (z ⬝ᵥ u i))
      = ∑ j, κ' j * ((y ⬝ᵥ u' j) * (z ⬝ᵥ u' j)) := by
    intro y z
    have e1 := sum_quad_rsn κ u β y z
    have e2 := sum_quad_rsn κ' u' β' y z
    linarith [h (y + z), h (-(y + z)), h y, h (-y), h z, h (-z), h 0,
      neg_dotProduct (y + z) ℓ, neg_dotProduct y ℓ, neg_dotProduct z ℓ, zero_dotProduct ℓ]
  -- the linear parts agree (odd part)
  have hL : ∀ y : p → ℝ, y ⬝ᵥ ℓ + ∑ i, κ i * (2 * β i * (y ⬝ᵥ u i))
      = ∑ j, κ' j * (2 * β' j * (y ⬝ᵥ u' j)) := by
    intro y
    have e1 := sum_lin_rsn κ u β y
    have e2 := sum_lin_rsn κ' u' β' y
    linarith [h y, h (-y), neg_dotProduct y ℓ]
  -- read the entries at the coordinate vectors
  refine Prod.ext (Matrix.ext fun a a' => ?_) (funext fun a => ?_)
  · have e := hB (Pi.single a 1) (Pi.single a' 1)
    simp only [single_dotProduct, one_mul] at e
    simp only [Prod.fst_add, Prod.fst_sum, Matrix.add_apply, Matrix.sum_apply, Prod.smul_fst,
      Matrix.smul_apply, sqForm, vecMulVec_apply, smul_eq_mul, Matrix.zero_apply, zero_add]
    exact e
  · have e := hL (Pi.single a 1)
    simp only [single_dotProduct, one_mul] at e
    simp only [Prod.snd_add, Prod.snd_sum, Pi.add_apply, Finset.sum_apply, Prod.smul_snd,
      Pi.smul_apply, sqForm, smul_eq_mul]
    exact e

/-- **(C):** at an input `x` off all hyperplanes, the cell identity becomes, for every output `o`,
`(0, M_{:,o}) + ∑_{i open} ŵ_{i,o} φ_i = ∑_{j open} ŵ'_{j,o} φ'_j`. -/
private theorem cell_eq_rsn (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ)
    (Wr' : Matrix p m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' q ℝ) (c' : q → ℝ) (M : Matrix p q ℝ)
    (hcell : ∀ x₀ : p → ℝ, (∀ i, (x₀ ᵥ* Wr) i + b i ≠ 0) →
      (∀ j, (x₀ ᵥ* Wr') j + b' j = 0 → Wr'ᵀ j = 0) →
      ∀ y : p → ℝ, y ᵥ* M + reluSqCell Wr b Ww c x₀ y = reluSqCell Wr' b' Ww' c' x₀ y)
    (x : p → ℝ) (hx : ∀ i, x ⬝ᵥ Wrᵀ i + b i ≠ 0)
    (hx' : ∀ j, x ⬝ᵥ Wr'ᵀ j + b' j = 0 → Wr'ᵀ j = 0) (o : q) :
    ((0 : Matrix p p ℝ), fun a => M a o)
        + ∑ i, (if 0 < x ⬝ᵥ Wrᵀ i + b i then Ww i o else 0) • sqForm (Wrᵀ i) (b i)
      = ∑ j, (if 0 < x ⬝ᵥ Wr'ᵀ j + b' j then Ww' j o else 0) • sqForm (Wr'ᵀ j) (b' j) := by
  refine sqForm_sum_eq_rsn _ _ _ _ _ _ _ (c o) (c' o) fun y => ?_
  have h := congrFun (hcell x hx hx' y) o
  rw [Pi.add_apply, reluSqCell_apply_rsn, reluSqCell_apply_rsn, ← add_assoc] at h
  exact h

/-! ### The vectors `φ` -/

omit [Fintype p] in
private theorem sqForm_smul_rsn (r : ℝ) (w : p → ℝ) (β : ℝ) :
    sqForm (r • w) (r * β) = r ^ 2 • sqForm w β := by
  refine Prod.ext (Matrix.ext fun a a' => ?_) (funext fun a => ?_) <;>
    simp only [sqForm, Prod.smul_fst, Prod.smul_snd, Matrix.smul_apply, vecMulVec_apply,
      Pi.smul_apply, smul_eq_mul] <;> ring

omit [Fintype p] in
private theorem sqForm_zero_rsn (β : ℝ) : sqForm (0 : p → ℝ) β = 0 := by
  refine Prod.ext (Matrix.ext fun a a' => ?_) (funext fun a => ?_) <;>
    simp [sqForm]

omit [Fintype p] in
private theorem sqForm_ne_zero_rsn {w : p → ℝ} (hw : w ≠ 0) (β : ℝ) : sqForm w β ≠ 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hw
  intro h
  have e := congrArg (fun z : Matrix p p ℝ × (p → ℝ) => z.1 a a) h
  simp only [sqForm, vecMulVec_apply, Prod.fst_zero, Matrix.zero_apply] at e
  exact ha (mul_self_eq_zero.1 e)

/-! ### Points on and off hyperplanes -/

/-- A copy of `exists_dotProduct_eq_zero_and_ne_zero` (`Absorb/SameWidth.lean`, not imported
here): a point of the hyperplane `x c = 0` off finitely many hyperplanes `x u_k = 0` different
from it. -/
private theorem exists_dotProduct_eq_zero_and_ne_zero_rsn {n ι : Type*} [Fintype n] [Finite ι]
    (c : n → ℝ) (u : ι → n → ℝ) (hu : ∀ k, ∀ r : ℝ, u k ≠ r • c) :
    ∃ x : n → ℝ, x ⬝ᵥ c = 0 ∧ ∀ k, x ⬝ᵥ u k ≠ 0 := by
  -- `w k`: the component of `u k` orthogonal to `c`; it is nonzero
  obtain ⟨w, hw_def⟩ : ∃ w : ι → n → ℝ, ∀ k, w k = u k - ((c ⬝ᵥ u k) / (c ⬝ᵥ c)) • c :=
    ⟨_, fun _ => rfl⟩
  have hw : ∀ k, w k ≠ 0 := fun k h0 => hu k _ (sub_eq_zero.1 ((hw_def k).symm.trans h0))
  -- the kernels of `ν ↦ ν w_k` are proper subspaces, so some `ν` avoids all of them
  let K : ι → Submodule ℝ (n → ℝ) := fun k =>
    { carrier := {ν | ν ⬝ᵥ w k = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢; rw [add_dotProduct, hx, hy, add_zero]
      zero_mem' := by simp
      smul_mem' := fun s x hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢; rw [smul_dotProduct, hx, smul_zero] }
  obtain ⟨ν, hν⟩ : ∃ ν : n → ℝ, ∀ k, ν ⬝ᵥ w k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ (p := K) (by
      ext ν
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      obtain ⟨k, h0⟩ := hcon ν
      exact ⟨k, h0⟩)
    have hmem : w k ∈ K k := hk ▸ Submodule.mem_top
    exact hw k (dotProduct_self_eq_zero.1 hmem)
  rcases eq_or_ne c 0 with rfl | hc
  · -- `c = 0`: every `x` lies on its "hyperplane"
    exact ⟨ν, dotProduct_zero ν, fun k => by
      have := hν k
      rwa [hw_def, zero_dotProduct, zero_div, zero_smul, sub_zero] at this⟩
  · -- `x = ν - (ν c / c c) c` has `x c = 0` and `x u_k = ν w_k`
    have hcc : c ⬝ᵥ c ≠ 0 := dotProduct_self_eq_zero.not.2 hc
    refine ⟨ν - ((ν ⬝ᵥ c) / (c ⬝ᵥ c)) • c, ?_, fun k => ?_⟩
    · rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, div_mul_cancel₀ _ hcc, sub_self]
    · have : (ν - ((ν ⬝ᵥ c) / (c ⬝ᵥ c)) • c) ⬝ᵥ u k = ν ⬝ᵥ w k := by
        rw [hw_def]
        simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
          dotProduct_comm c (u k)]
        ring
      rw [this]
      exact hν k

/-- For finitely many `a_k ≠ 0`, every large `t > 0` has `|β_k| < t |a_k|`. -/
private theorem exists_large_rsn {ι : Type*} [Finite ι] (P : ι → Prop) (a β : ι → ℝ)
    (ha : ∀ k, P k → a k ≠ 0) : ∃ t : ℝ, 0 < t ∧ ∀ k, P k → |β k| < t * |a k| := by
  have h : ∀ᶠ t in Filter.atTop, ∀ k, P k → |β k| < t * |a k| := by
    refine Filter.eventually_all.2 fun k => ?_
    by_cases hk : P k
    · exact ((Filter.tendsto_id.atTop_mul_const (abs_pos.2 (ha k hk))).eventually_gt_atTop
        |β k|).mono fun t ht _ => ht
    · exact Filter.Eventually.of_forall fun t h => absurd h hk
  obtain ⟨t, ht0, ht⟩ := ((Filter.eventually_gt_atTop 0).and h).exists
  exact ⟨t, ht0, ht⟩

/-- **A point of an affine hyperplane off finitely many others.** If no `(u_k, γ_k)` with `P k`
is a multiple of `(c, β)`, some `x` has `x c + β = 0` and `x u_k + γ_k ≠ 0` for all these `k`. -/
private theorem exists_on_hyperplane_rsn {ι : Type*} [Fintype ι] (c : p → ℝ) (β : ℝ)
    (hc : c ≠ 0) (u : ι → p → ℝ) (γ : ι → ℝ) (P : ι → Prop)
    (hu : ∀ k, P k → ∀ r : ℝ, ¬ (u k = r • c ∧ γ k = r * β)) :
    ∃ x : p → ℝ, x ⬝ᵥ c + β = 0 ∧ ∀ k, P k → x ⬝ᵥ u k + γ k ≠ 0 := by
  classical
  have hcc : c ⬝ᵥ c ≠ 0 := dotProduct_self_eq_zero.not.2 hc
  -- a direction `v` of the hyperplane transverse to the hyperplanes not parallel to it
  obtain ⟨v, hvc, hv⟩ := exists_dotProduct_eq_zero_and_ne_zero_rsn c
    (fun k : {k // P k ∧ ∀ r : ℝ, u k ≠ r • c} => u k.1) (fun k => k.2.2)
  -- a point `x₁` of the hyperplane, then `x₁ + s v` for `s` off finitely many values
  obtain ⟨x₁, h1⟩ : ∃ x₁ : p → ℝ, x₁ ⬝ᵥ c + β = 0 :=
    ⟨-(β / (c ⬝ᵥ c)) • c, by
      rw [smul_dotProduct, smul_eq_mul, neg_mul, div_mul_cancel₀ _ hcc, neg_add_cancel]⟩
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset
    (Finset.univ.image fun k => -(x₁ ⬝ᵥ u k + γ k) / (v ⬝ᵥ u k))
  refine ⟨x₁ + s • v, ?_, fun k hk h0 => ?_⟩
  · rw [add_dotProduct, smul_dotProduct, hvc, smul_zero, add_zero, h1]
  · rw [add_dotProduct, smul_dotProduct, smul_eq_mul] at h0
    by_cases hpar : ∀ r : ℝ, u k ≠ r • c
    · have hvk : v ⬝ᵥ u k ≠ 0 := hv ⟨k, hk, hpar⟩
      exact hs (Finset.mem_image.2 ⟨k, Finset.mem_univ _, by rw [div_eq_iff hvk]; linarith⟩)
    · -- a parallel hyperplane with another offset does not meet the hyperplane
      push Not at hpar
      obtain ⟨r, hr⟩ := hpar
      refine hu k hk r ⟨hr, ?_⟩
      have e1 : x₁ ⬝ᵥ u k = r * (x₁ ⬝ᵥ c) := by rw [hr, dotProduct_smul, smul_eq_mul]
      have e2 : v ⬝ᵥ u k = r * (v ⬝ᵥ c) := by rw [hr, dotProduct_smul, smul_eq_mul]
      rw [hvc, mul_zero] at e2
      rw [e1, e2] at h0
      linear_combination h0 - r * h1

/-- If `|a| < t |g|` with `t > 0`, then `g ± a/t` are nonzero and have the sign of `g`. -/
private theorem sign_stable_rsn {g a t : ℝ} (hg : g ≠ 0) (h : |a| < t * |g|) (ht : 0 < t) :
    g + t⁻¹ * a ≠ 0 ∧ g - t⁻¹ * a ≠ 0 ∧ (0 < g + t⁻¹ * a ↔ 0 < g - t⁻¹ * a) := by
  have he : |t⁻¹ * a| < |g| := by
    rw [abs_mul, abs_inv, abs_of_pos ht, inv_mul_lt_iff₀ ht]; exact h
  obtain ⟨h1, h2⟩ := abs_lt.1 he
  rcases lt_or_gt_of_ne hg with hneg | hpos
  · rw [abs_of_neg hneg] at h1 h2
    exact ⟨(by linarith : g + t⁻¹ * a < 0).ne, (by linarith : g - t⁻¹ * a < 0).ne,
      iff_of_false (not_lt.2 (by linarith)) (not_lt.2 (by linarith))⟩
  · rw [abs_of_pos hpos] at h1 h2
    exact ⟨(by linarith : 0 < g + t⁻¹ * a).ne', (by linarith : 0 < g - t⁻¹ * a).ne',
      iff_of_true (by linarith) (by linarith)⟩

/-- **The two sides of an affine hyperplane:** two points `x₁`, `x₂` with `x c + β` positive at
`x₁` and negative at `x₂`, at which every `x u_k + γ_k` (`P k`) is nonzero with the same sign. -/
private theorem exists_two_sides_rsn {ι : Type*} [Fintype ι] (c : p → ℝ) (β : ℝ) (hc : c ≠ 0)
    (u : ι → p → ℝ) (γ : ι → ℝ) (P : ι → Prop)
    (hu : ∀ k, P k → ∀ r : ℝ, ¬ (u k = r • c ∧ γ k = r * β)) :
    ∃ x₁ x₂ : p → ℝ, 0 < x₁ ⬝ᵥ c + β ∧ x₂ ⬝ᵥ c + β < 0 ∧ ∀ k, P k →
      x₁ ⬝ᵥ u k + γ k ≠ 0 ∧ x₂ ⬝ᵥ u k + γ k ≠ 0 ∧
        (0 < x₁ ⬝ᵥ u k + γ k ↔ 0 < x₂ ⬝ᵥ u k + γ k) := by
  obtain ⟨x₀, h0, hk⟩ := exists_on_hyperplane_rsn c β hc u γ P hu
  have hcc : 0 < c ⬝ᵥ c :=
    lt_of_le_of_ne (Finset.sum_nonneg fun a _ => mul_self_nonneg (c a))
      (Ne.symm (dotProduct_self_eq_zero.not.2 hc))
  obtain ⟨t, ht0, ht⟩ := exists_large_rsn P (fun k => x₀ ⬝ᵥ u k + γ k) (fun k => c ⬝ᵥ u k) hk
  refine ⟨x₀ + t⁻¹ • c, x₀ - t⁻¹ • c, ?_, ?_, fun k hPk => ?_⟩
  · rw [add_dotProduct, smul_dotProduct, smul_eq_mul, add_right_comm, h0, zero_add]
    exact mul_pos (inv_pos.2 ht0) hcc
  · rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, sub_add_eq_add_sub, h0, zero_sub,
      neg_lt_zero]
    exact mul_pos (inv_pos.2 ht0) hcc
  · have e1 : (x₀ + t⁻¹ • c) ⬝ᵥ u k + γ k = (x₀ ⬝ᵥ u k + γ k) + t⁻¹ * (c ⬝ᵥ u k) := by
      rw [add_dotProduct, smul_dotProduct, smul_eq_mul]; ring
    have e2 : (x₀ - t⁻¹ • c) ⬝ᵥ u k + γ k = (x₀ ⬝ᵥ u k + γ k) - t⁻¹ * (c ⬝ᵥ u k) := by
      rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]; ring
    rw [e1, e2]
    exact sign_stable_rsn (hk k hPk) (ht k hPk) ht0

/-- If `|β| < t |a|`, the arguments `± t a + β` are nonzero and not both positive. -/
private theorem far_sign_rsn {a β t : ℝ} (h : |β| < t * |a|) :
    t * a + β ≠ 0 ∧ -t * a + β ≠ 0 ∧ ¬ (0 < t * a + β ∧ 0 < -t * a + β) := by
  obtain ⟨h1, h2⟩ := abs_lt.1 h
  rcases le_or_gt 0 a with ha | ha
  · rw [abs_of_nonneg ha] at h1 h2
    exact ⟨(by linarith : 0 < t * a + β).ne', (by linarith : -t * a + β < 0).ne,
      fun h3 => by linarith [h3.2]⟩
  · rw [abs_of_neg ha] at h1 h2
    exact ⟨(by linarith : t * a + β < 0).ne, (by linarith : 0 < -t * a + β).ne',
      fun h3 => by linarith [h3.1]⟩

/-- The sign of the argument of a unit of a class, on the positive side of `H_i`. -/
private theorem ite_mul_pos_rsn {l a w : ℝ} (hl : l ≠ 0) (ha : 0 < a) :
    (if 0 < l * a then w else 0) * l ^ 2 = if 0 < l then l ^ 2 * w else 0 := by
  rcases lt_or_gt_of_ne hl with hneg | hpos
  · simp only [not_lt.2 (mul_neg_of_neg_of_pos hneg ha).le, not_lt.2 hneg.le, ↓reduceIte,
      zero_mul]
  · simp only [mul_pos hpos ha, hpos, ↓reduceIte]; ring

/-- The sign of the argument of a unit of a class, on the negative side of `H_i`. -/
private theorem ite_mul_neg_rsn {l a w : ℝ} (hl : l ≠ 0) (ha : a < 0) :
    (if 0 < l * a then w else 0) * l ^ 2 = if 0 < l then 0 else l ^ 2 * w := by
  rcases lt_or_gt_of_ne hl with hneg | hpos
  · simp only [mul_pos_of_neg_of_neg hneg ha, not_lt.2 hneg.le, ↓reduceIte]; ring
  · simp only [not_lt.2 (mul_neg_of_pos_of_neg hpos ha).le, hpos, ↓reduceIte, zero_mul]

/-! ### Step 1: across the hyperplane of a unit -/

/-- **Step 1 (K).** Let `J` be the units of `B_{θ′}` whose read and bias are `λ_j` times those of
unit `i` (`λ_j ≠ 0`). Then `ŵ_i = ∑_{j ∈ J, λ_j > 0} λ_j² ŵ'_j − ∑_{j ∈ J, λ_j < 0} λ_j² ŵ'_j`:
compare (C) on the two sides of the hyperplane of `i`, near a point of it on no other hyperplane. -/
private theorem step1_rsn (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (Wr' : Matrix p m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' q ℝ) (M : Matrix p q ℝ)
    (hr : ∀ i, Wrᵀ i ≠ 0)
    (hH : ∀ i k, i ≠ k → ∀ r : ℝ, ¬ (Wrᵀ i = r • Wrᵀ k ∧ b i = r * b k))
    (hC : ∀ x : p → ℝ, (∀ i, x ⬝ᵥ Wrᵀ i + b i ≠ 0) →
      (∀ j, x ⬝ᵥ Wr'ᵀ j + b' j = 0 → Wr'ᵀ j = 0) → ∀ o,
      ((0 : Matrix p p ℝ), fun a => M a o)
          + ∑ i, (if 0 < x ⬝ᵥ Wrᵀ i + b i then Ww i o else 0) • sqForm (Wrᵀ i) (b i)
        = ∑ j, (if 0 < x ⬝ᵥ Wr'ᵀ j + b' j then Ww' j o else 0) • sqForm (Wr'ᵀ j) (b' j))
    (i : m) (J : Finset m') (lam : m' → ℝ)
    (hJ : ∀ j, j ∉ J → ∀ r : ℝ, r ≠ 0 → ¬ (Wr'ᵀ j = r • Wrᵀ i ∧ b' j = r * b i))
    (hlam : ∀ j ∈ J, lam j ≠ 0 ∧ Wr'ᵀ j = lam j • Wrᵀ i ∧ b' j = lam j * b i) (o : q) :
    Ww i o = ∑ j ∈ J, (if 0 < lam j then lam j ^ 2 * Ww' j o else 0)
      - ∑ j ∈ J, (if 0 < lam j then 0 else lam j ^ 2 * Ww' j o) := by
  classical
  -- the other units of `B_θ` and the units of `B_{θ′}` off the class are not multiples of `i`
  have hfam : ∀ k : m ⊕ m', Sum.elim (fun k => k ≠ i) (fun j => Wr'ᵀ j ≠ 0 ∧ j ∉ J) k →
      ∀ r : ℝ, ¬ (Sum.elim (fun k => Wrᵀ k) (fun j => Wr'ᵀ j) k = r • Wrᵀ i ∧
        Sum.elim b b' k = r * b i) := by
    rintro (k | j) hk r ⟨h1, h2⟩
    · simp only [Sum.elim_inl] at hk h1 h2
      rcases eq_or_ne r 0 with rfl | hr0
      · exact hr k (by rw [h1, zero_smul])
      · refine hH i k (Ne.symm hk) r⁻¹ ⟨?_, ?_⟩
        · rw [h1, smul_smul, inv_mul_cancel₀ hr0, one_smul]
        · rw [h2, ← mul_assoc, inv_mul_cancel₀ hr0, one_mul]
    · simp only [Sum.elim_inr] at hk h1 h2
      rcases eq_or_ne r 0 with rfl | hr0
      · exact hk.1 (by rw [h1, zero_smul])
      · exact hJ j hk.2 r hr0 ⟨h1, h2⟩
  -- two points `x₁`, `x₂` on the two sides of `H_i`, where all these units keep their signs
  obtain ⟨x₁, x₂, h1i, h2i, hs⟩ := exists_two_sides_rsn (Wrᵀ i) (b i) (hr i) _ _ _ hfam
  have hm : ∀ k, k ≠ i → x₁ ⬝ᵥ Wrᵀ k + b k ≠ 0 ∧ x₂ ⬝ᵥ Wrᵀ k + b k ≠ 0 ∧
      (0 < x₁ ⬝ᵥ Wrᵀ k + b k ↔ 0 < x₂ ⬝ᵥ Wrᵀ k + b k) := fun k hk => hs (Sum.inl k) hk
  have hm' : ∀ j, Wr'ᵀ j ≠ 0 → j ∉ J → x₁ ⬝ᵥ Wr'ᵀ j + b' j ≠ 0 ∧ x₂ ⬝ᵥ Wr'ᵀ j + b' j ≠ 0 ∧
      (0 < x₁ ⬝ᵥ Wr'ᵀ j + b' j ↔ 0 < x₂ ⬝ᵥ Wr'ᵀ j + b' j) :=
    fun j h1 h2 => hs (Sum.inr j) ⟨h1, h2⟩
  -- on a unit of the class the argument is `λ_j` times that of `i`
  have harg : ∀ j ∈ J, ∀ x : p → ℝ, x ⬝ᵥ Wr'ᵀ j + b' j = lam j * (x ⬝ᵥ Wrᵀ i + b i) := by
    intro j hj x
    rw [(hlam j hj).2.1, (hlam j hj).2.2, dotProduct_smul, smul_eq_mul]; ring
  -- `x₁` and `x₂` lie on no hyperplane
  have hadm : ∀ x : p → ℝ, x ⬝ᵥ Wrᵀ i + b i ≠ 0 → (∀ k, k ≠ i → x ⬝ᵥ Wrᵀ k + b k ≠ 0) →
      (∀ j, Wr'ᵀ j ≠ 0 → j ∉ J → x ⬝ᵥ Wr'ᵀ j + b' j ≠ 0) →
      (∀ k, x ⬝ᵥ Wrᵀ k + b k ≠ 0) ∧ (∀ j, x ⬝ᵥ Wr'ᵀ j + b' j = 0 → Wr'ᵀ j = 0) := by
    intro x hxi hxk hxj
    refine ⟨fun k => ?_, fun j h0 => ?_⟩
    · by_cases hk : k = i
      · rw [hk]; exact hxi
      · exact hxk k hk
    · by_contra hne
      by_cases hj : j ∈ J
      · rw [harg j hj x] at h0
        exact mul_ne_zero (hlam j hj).1 hxi h0
      · exact hxj j hne hj h0
  obtain ⟨ha1, ha1'⟩ := hadm x₁ h1i.ne' (fun k hk => (hm k hk).1) (fun j h1 h2 => (hm' j h1 h2).1)
  obtain ⟨ha2, ha2'⟩ := hadm x₂ h2i.ne (fun k hk => (hm k hk).2.1)
    (fun j h1 h2 => (hm' j h1 h2).2.1)
  have e1 := hC x₁ ha1 ha1' o
  have e2 := hC x₂ ha2 ha2' o
  -- on the side of `B_θ`, only unit `i` changes
  have hL : ∑ k, (if 0 < x₁ ⬝ᵥ Wrᵀ k + b k then Ww k o else 0) • sqForm (Wrᵀ k) (b k)
      - ∑ k, (if 0 < x₂ ⬝ᵥ Wrᵀ k + b k then Ww k o else 0) • sqForm (Wrᵀ k) (b k)
      = Ww i o • sqForm (Wrᵀ i) (b i) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp only [h1i, not_lt.2 h2i.le, ↓reduceIte, zero_smul, sub_zero]
    · intro k _ hk
      simp only [(hm k hk).2.2, sub_self]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- on the side of `B_{θ′}`, only the units of the class change
  have hR : ∑ j, (if 0 < x₁ ⬝ᵥ Wr'ᵀ j + b' j then Ww' j o else 0) • sqForm (Wr'ᵀ j) (b' j)
      - ∑ j, (if 0 < x₂ ⬝ᵥ Wr'ᵀ j + b' j then Ww' j o else 0) • sqForm (Wr'ᵀ j) (b' j)
      = (∑ j ∈ J, (if 0 < lam j then lam j ^ 2 * Ww' j o else 0)
          - ∑ j ∈ J, (if 0 < lam j then 0 else lam j ^ 2 * Ww' j o)) • sqForm (Wrᵀ i) (b i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_smul,
      ← Finset.sum_subset (Finset.subset_univ J)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      obtain ⟨hl0, hw', hb'⟩ := hlam j hj
      rw [harg j hj x₁, harg j hj x₂, hw', hb', sqForm_smul_rsn, smul_smul, smul_smul,
        ← sub_smul, ite_mul_pos_rsn hl0 h1i, ite_mul_neg_rsn hl0 h2i]
    · intro j _ hj
      by_cases hw0 : Wr'ᵀ j = 0
      · rw [hw0, sqForm_zero_rsn, smul_zero, smul_zero, sub_self]
      · simp only [(hm' j hw0 hj).2.2, sub_self]
  have key : Ww i o • sqForm (Wrᵀ i) (b i)
      = (∑ j ∈ J, (if 0 < lam j then lam j ^ 2 * Ww' j o else 0)
          - ∑ j ∈ J, (if 0 < lam j then 0 else lam j ^ 2 * Ww' j o)) • sqForm (Wrᵀ i) (b i) := by
    rw [← hL, ← hR, ← e1, ← e2, add_sub_add_left_eq_sub]
  exact smul_left_injective ℝ (sqForm_ne_zero_rsn (hr i) (b i)) key


/-! ### Step 2: the classes, and two opposite cells far away -/

/-- **The units of `B_{θ′}` by class:** a sum over the units, with zero terms on the units with
`Z j` (read `0`), is the sum over the disjoint classes `J_i` plus the sum over the other units. -/
private theorem sum_split_rsn {β : Type*} [AddCommMonoid β] (J : m → Finset m') (F : Finset m')
    (Z : m' → Prop) (hdisj : ∀ i i' j, j ∈ J i → j ∈ J i' → i = i')
    (hF : ∀ j, j ∈ F ↔ ¬ Z j ∧ ∀ i, j ∉ J i) (g : m' → β) (hg : ∀ j, Z j → g j = 0) :
    ∑ j, g j = ∑ i, ∑ j ∈ J i, g j + ∑ j ∈ F, g j := by
  classical
  have hpt : ∀ j, g j = ∑ i, (if j ∈ J i then g j else 0) + if j ∈ F then g j else 0 := by
    intro j
    by_cases hZ : Z j
    · simp [hg j hZ]
    by_cases hex : ∃ i, j ∈ J i
    · obtain ⟨i, hi⟩ := hex
      have hjF : j ∉ F := fun h => ((hF j).1 h).2 i hi
      rw [Finset.sum_eq_single i, ite_eq_left hi, ite_eq_right hjF, add_zero]
      · intro i' _ hi'
        exact ite_eq_right fun h => hi' (hdisj i' i j h hi)
      · intro h; exact absurd (Finset.mem_univ i) h
    · push Not at hex
      have hjF : j ∈ F := (hF j).2 ⟨hZ, hex⟩
      simp [hex, hjF]
  calc ∑ j, g j = ∑ j, (∑ i, (if j ∈ J i then g j else 0) + if j ∈ F then g j else 0) :=
        Finset.sum_congr rfl fun j _ => hpt j
    _ = ∑ i, ∑ j ∈ J i, g j + ∑ j ∈ F, g j := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_ite_mem, Finset.univ_inter]
        · rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **Step 2.** At an input `x` off all hyperplanes, (C) and (K) give
`(0, M_{:,o}) = ∑_i N_{i,o} φ_i + ∑_{j ∈ F open at x} ŵ'_{j,o} φ'_j`, with
`N_{i,o} = ∑_{j ∈ J_i, λ_j < 0} λ_j² ŵ'_{j,o}` (the `μ_i` of the paper): the units of the class of
`i` contribute `P_{i,o} φ_i` if `i` is open at `x` and `N_{i,o} φ_i` if not, and
`P_{i,o} − ŵ_{i,o} = N_{i,o}`. -/
private theorem step2_rsn (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (Wr' : Matrix p m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' q ℝ) (M : Matrix p q ℝ)
    (J : m → Finset m') (lam : m → m' → ℝ) (F : Finset m') (P N : m → q → ℝ)
    (hlam : ∀ i, ∀ j ∈ J i, lam i j ≠ 0 ∧ Wr'ᵀ j = lam i j • Wrᵀ i ∧ b' j = lam i j * b i)
    (hdisj : ∀ i i' j, j ∈ J i → j ∈ J i' → i = i')
    (hF : ∀ j, j ∈ F ↔ ¬ Wr'ᵀ j = 0 ∧ ∀ i, j ∉ J i)
    (hP : ∀ i o, P i o = ∑ j ∈ J i, (if 0 < lam i j then lam i j ^ 2 * Ww' j o else 0))
    (hN : ∀ i o, N i o = ∑ j ∈ J i, (if 0 < lam i j then 0 else lam i j ^ 2 * Ww' j o))
    (hK : ∀ i o, Ww i o = P i o - N i o)
    (x : p → ℝ) (hx : ∀ i, x ⬝ᵥ Wrᵀ i + b i ≠ 0) (o : q)
    (e : ((0 : Matrix p p ℝ), fun a => M a o)
          + ∑ i, (if 0 < x ⬝ᵥ Wrᵀ i + b i then Ww i o else 0) • sqForm (Wrᵀ i) (b i)
        = ∑ j, (if 0 < x ⬝ᵥ Wr'ᵀ j + b' j then Ww' j o else 0) • sqForm (Wr'ᵀ j) (b' j)) :
    ((0 : Matrix p p ℝ), fun a => M a o)
      = ∑ i, N i o • sqForm (Wrᵀ i) (b i)
        + ∑ j ∈ F.filter (fun j => 0 < x ⬝ᵥ Wr'ᵀ j + b' j), Ww' j o • sqForm (Wr'ᵀ j) (b' j) := by
  classical
  rw [sum_split_rsn J F (fun j => Wr'ᵀ j = 0) hdisj hF _
    (fun j hj => by simp only [hj, sqForm_zero_rsn, smul_zero])] at e
  -- the class of `i` contributes `P_{i,o} φ_i` or `N_{i,o} φ_i`, as `i` is open at `x` or not
  have hcls : ∀ i, ∑ j ∈ J i, (if 0 < x ⬝ᵥ Wr'ᵀ j + b' j then Ww' j o else 0)
        • sqForm (Wr'ᵀ j) (b' j)
      = (if 0 < x ⬝ᵥ Wrᵀ i + b i then P i o else N i o) • sqForm (Wrᵀ i) (b i) := by
    intro i
    have hterm : ∀ j ∈ J i, (if 0 < x ⬝ᵥ Wr'ᵀ j + b' j then Ww' j o else 0)
          • sqForm (Wr'ᵀ j) (b' j)
        = ((if 0 < lam i j * (x ⬝ᵥ Wrᵀ i + b i) then Ww' j o else 0) * lam i j ^ 2)
          • sqForm (Wrᵀ i) (b i) := by
      intro j hj
      obtain ⟨-, hw', hb'⟩ := hlam i j hj
      have harg : x ⬝ᵥ Wr'ᵀ j + b' j = lam i j * (x ⬝ᵥ Wrᵀ i + b i) := by
        rw [hw', hb', dotProduct_smul, smul_eq_mul]; ring
      rw [harg, hw', hb', sqForm_smul_rsn, smul_smul]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul]
    congr 1
    rcases lt_or_gt_of_ne (hx i) with hneg | hpos
    · rw [ite_eq_right (not_lt.2 hneg.le), hN]
      exact Finset.sum_congr rfl fun j hj => ite_mul_neg_rsn (hlam i j hj).1 hneg
    · rw [ite_eq_left hpos, hP]
      exact Finset.sum_congr rfl fun j hj => ite_mul_pos_rsn (hlam i j hj).1 hpos
  rw [Finset.sum_congr rfl fun i _ => hcls i] at e
  rw [eq_sub_of_add_eq e, add_sub_right_comm, ← Finset.sum_sub_distrib]
  congr 1
  · -- by (K), what is left of the class of `i` is `N_{i,o} φ_i`
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul]
    congr 1
    have := hK i o
    split_ifs <;> linarith
  · rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp

/-- **Two opposite cells far away:** `x₁ = t v` and `x₂ = −t v`, for a direction `v` seen by every
nonzero read and a large `t`, lie on no hyperplane, and no unit with a nonzero read is open at
both. -/
private theorem exists_far_rsn (Wr : Matrix p m ℝ) (b : m → ℝ) (Wr' : Matrix p m' ℝ)
    (b' : m' → ℝ) (hr : ∀ i, Wrᵀ i ≠ 0) :
    ∃ x₁ x₂ : p → ℝ,
      ((∀ i, x₁ ⬝ᵥ Wrᵀ i + b i ≠ 0) ∧ (∀ j, x₁ ⬝ᵥ Wr'ᵀ j + b' j = 0 → Wr'ᵀ j = 0)) ∧
      ((∀ i, x₂ ⬝ᵥ Wrᵀ i + b i ≠ 0) ∧ (∀ j, x₂ ⬝ᵥ Wr'ᵀ j + b' j = 0 → Wr'ᵀ j = 0)) ∧
      ∀ j, Wr'ᵀ j ≠ 0 → ¬ (0 < x₁ ⬝ᵥ Wr'ᵀ j + b' j ∧ 0 < x₂ ⬝ᵥ Wr'ᵀ j + b' j) := by
  classical
  -- a direction seen by every nonzero read
  obtain ⟨v, -, hv⟩ := exists_dotProduct_eq_zero_and_ne_zero_rsn (0 : p → ℝ)
    (Sum.elim (fun i => Wrᵀ i) (fun j : {j : m' // Wr'ᵀ j ≠ 0} => Wr'ᵀ j.1)) (by
      rintro (i | j) r h <;> rw [smul_zero] at h
      · exact hr i h
      · exact j.2 h)
  have hv1 : ∀ i, v ⬝ᵥ Wrᵀ i ≠ 0 := fun i => hv (Sum.inl i)
  have hv2 : ∀ j, Wr'ᵀ j ≠ 0 → v ⬝ᵥ Wr'ᵀ j ≠ 0 := fun j hj => hv (Sum.inr ⟨j, hj⟩)
  obtain ⟨t, -, ht⟩ := exists_large_rsn
    (Sum.elim (fun _ : m => True) (fun j : m' => Wr'ᵀ j ≠ 0))
    (Sum.elim (fun i => v ⬝ᵥ Wrᵀ i) (fun j => v ⬝ᵥ Wr'ᵀ j)) (Sum.elim b b') (by
      rintro (i | j) hk
      · exact hv1 i
      · exact hv2 j hk)
  have ht1 : ∀ i, |b i| < t * |v ⬝ᵥ Wrᵀ i| := fun i => ht (Sum.inl i) trivial
  have ht2 : ∀ j, Wr'ᵀ j ≠ 0 → |b' j| < t * |v ⬝ᵥ Wr'ᵀ j| := fun j hj => ht (Sum.inr j) hj
  have e1 : ∀ w : p → ℝ, (t • v) ⬝ᵥ w = t * (v ⬝ᵥ w) := fun w => by
    rw [smul_dotProduct, smul_eq_mul]
  have e2 : ∀ w : p → ℝ, ((-t) • v) ⬝ᵥ w = -t * (v ⬝ᵥ w) := fun w => by
    rw [smul_dotProduct, smul_eq_mul]
  refine ⟨t • v, (-t) • v, ⟨fun i => ?_, fun j h0 => ?_⟩, ⟨fun i => ?_, fun j h0 => ?_⟩,
    fun j hj => ?_⟩
  · rw [e1]; exact (far_sign_rsn (ht1 i)).1
  · by_contra hj; rw [e1] at h0; exact (far_sign_rsn (ht2 j hj)).1 h0
  · rw [e2]; exact (far_sign_rsn (ht1 i)).2.1
  · by_contra hj; rw [e2] at h0; exact (far_sign_rsn (ht2 j hj)).2.1 h0
  · rw [e1, e2]; exact (far_sign_rsn (ht2 j hj)).2.2

/-! ### Dimensions -/

/-- A linearly independent family in a subspace has at most its dimension many vectors. -/
private theorem card_le_finrank_of_mem_rsn {ι V : Type*} [Fintype ι] [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] {v : ι → V} (hv : LinearIndependent ℝ v)
    (W : Submodule ℝ V) (hW : ∀ k, v k ∈ W) : Fintype.card ι ≤ Module.finrank ℝ W :=
  (LinearIndependent.of_comp W.subtype (v := fun k => (⟨v k, hW k⟩ : W))
    hv).fintype_card_le_finrank

/-- The span of the images of `|s|` points has dimension at most `|s|`. -/
private theorem finrank_span_image_le_rsn {ι V : Type*} [AddCommGroup V] [Module ℝ V]
    (s : Finset ι) (f : ι → V) :
    Module.finrank ℝ (Submodule.span ℝ (f '' (s : Set ι))) ≤ s.card := by
  classical
  rw [← Finset.coe_image]
  exact (finrank_span_finset_le_card _).trans Finset.card_image_le

/-- **Proof of Theorem C.2 (iii) of the absorb paper, "Squares", "Costs" and "Dimensions":** let
the units of `B_θ` have nonzero reads and writes and lie on distinct hyperplanes, and let the
polynomials of the cells of the two blocks satisfy `y M + B_θ = B_{θ′}` at every `x₀` off the
hyperplanes. Then there are disjoint sets `S`, `U` of units of `B_θ` and disjoint sets `F₁`, `F₂`
of units of `B_{θ′}` such that `B_{θ′}` has at least `|U| + |F₁| + |F₂|` more units than `B_θ`,
and every `τ_o` lies in the span of the `φ(w_i, b_i)`, `i ∈ U`, with the `φ` of the units of
`F₁`, and in their span with the `φ` of the units of `F₂`. -/
theorem exists_sqTarget_mem_span_of_reluSqCell (Wr : Matrix p m ℝ) (b : m → ℝ)
    (Ww : Matrix m q ℝ) (c : q → ℝ) (Wr' : Matrix p m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' q ℝ)
    (c' : q → ℝ) (M : Matrix p q ℝ)
    (hr : ∀ i, Wrᵀ i ≠ 0) (hw : ∀ i, Ww i ≠ 0)
    (hH : ∀ i k, i ≠ k → ∀ r : ℝ, ¬ (Wrᵀ i = r • Wrᵀ k ∧ b i = r * b k))
    (hcell : ∀ x₀ : p → ℝ, (∀ i, (x₀ ᵥ* Wr) i + b i ≠ 0) →
      (∀ j, (x₀ ᵥ* Wr') j + b' j = 0 → Wr'ᵀ j = 0) →
      ∀ y : p → ℝ, y ᵥ* M + reluSqCell Wr b Ww c x₀ y = reluSqCell Wr' b' Ww' c' x₀ y) :
    ∃ (S U : Finset m) (F₁ F₂ : Finset m'), Disjoint S U ∧ Disjoint F₁ F₂ ∧
      Fintype.card m + U.card + F₁.card + F₂.card ≤ Fintype.card m' ∧
      ∀ o : q,
        sqTarget M Wr b Ww S o ∈
          Submodule.span ℝ ((fun i => sqForm (Wrᵀ i) (b i)) '' (U : Set m)) ⊔
            Submodule.span ℝ ((fun j => sqForm (Wr'ᵀ j) (b' j)) '' (F₁ : Set m')) ∧
        sqTarget M Wr b Ww S o ∈
          Submodule.span ℝ ((fun i => sqForm (Wrᵀ i) (b i)) '' (U : Set m)) ⊔
            Submodule.span ℝ ((fun j => sqForm (Wr'ᵀ j) (b' j)) '' (F₂ : Set m')) := by
  sorry

/-- **Proof of Theorem C.2 (iii) of the absorb paper, "Conclusion":** under the hypotheses of the
three steps, if for all disjoint sets `S`, `U` of units of `B_θ` with `|U| < 2 d` the vectors
`τ_o` (`o` an output) and `φ(w_i, b_i)`, `i ∈ U`, are linearly independent, then `B_{θ′}` has at
least `2 d` more units than `B_θ`, with `d` the number of outputs. -/
theorem card_add_two_mul_card_le_of_reluSqCell [Fintype q] (Wr : Matrix p m ℝ) (b : m → ℝ)
    (Ww : Matrix m q ℝ) (c : q → ℝ) (Wr' : Matrix p m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' q ℝ)
    (c' : q → ℝ) (M : Matrix p q ℝ)
    (hr : ∀ i, Wrᵀ i ≠ 0) (hw : ∀ i, Ww i ≠ 0)
    (hH : ∀ i k, i ≠ k → ∀ r : ℝ, ¬ (Wrᵀ i = r • Wrᵀ k ∧ b i = r * b k))
    (hG : ∀ S U : Finset m, Disjoint S U → U.card < 2 * Fintype.card q →
      LinearIndependent ℝ (Sum.elim (fun o : q => sqTarget M Wr b Ww S o)
        (fun i : U => sqForm (Wrᵀ (i : m)) (b i))))
    (hcell : ∀ x₀ : p → ℝ, (∀ i, (x₀ ᵥ* Wr) i + b i ≠ 0) →
      (∀ j, (x₀ ᵥ* Wr') j + b' j = 0 → Wr'ᵀ j = 0) →
      ∀ y : p → ℝ, y ᵥ* M + reluSqCell Wr b Ww c x₀ y = reluSqCell Wr' b' Ww' c' x₀ y) :
    Fintype.card m + 2 * Fintype.card q ≤ Fintype.card m' := by
  classical
  obtain ⟨S, U, F₁, F₂, hSU, -, hcount, hspan⟩ :=
    exists_sqTarget_mem_span_of_reluSqCell Wr b Ww c Wr' b' Ww' c' M hr hw hH hcell
  by_cases hU : 2 * Fintype.card q ≤ U.card
  · omega
  push Not at hU
  have hli := hG S U hSU hU
  -- `d + |U|` independent vectors in a span of `|U| + |F|` vectors: `d ≤ |F|`
  have hdim : ∀ F : Finset m', (∀ o, sqTarget M Wr b Ww S o ∈
      Submodule.span ℝ ((fun i => sqForm (Wrᵀ i) (b i)) '' (U : Set m)) ⊔
        Submodule.span ℝ ((fun j => sqForm (Wr'ᵀ j) (b' j)) '' (F : Set m'))) →
      Fintype.card q ≤ F.card := by
    intro F hF
    have hmem : ∀ k, Sum.elim (fun o : q => sqTarget M Wr b Ww S o)
        (fun i : U => sqForm (Wrᵀ (i : m)) (b i)) k ∈
          Submodule.span ℝ ((fun i => sqForm (Wrᵀ i) (b i)) '' (U : Set m)) ⊔
            Submodule.span ℝ ((fun j => sqForm (Wr'ᵀ j) (b' j)) '' (F : Set m')) := by
      rintro (o | i)
      · exact hF o
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, i.2, rfl⟩)
    have h1 := card_le_finrank_of_mem_rsn hli _ hmem
    have h2 := (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
      (add_le_add (finrank_span_image_le_rsn U fun i => sqForm (Wrᵀ i) (b i))
        (finrank_span_image_le_rsn F fun j => sqForm (Wr'ᵀ j) (b' j)))
    rw [Fintype.card_sum, Fintype.card_coe] at h1
    omega
  have h1 := hdim F₁ fun o => (hspan o).1
  have h2 := hdim F₂ fun o => (hspan o).2
  omega

/-- **Proof of Theorem C.2 (iii) of the absorb paper, last sentence, for the same width:** under
the hypotheses of the three steps, if for every set `S` of units of `B_θ` some `τ_o` is nonzero,
then `B_{θ′}` has more units than `B_θ`. -/
theorem card_lt_card_of_reluSqCell (Wr : Matrix p m ℝ) (b : m → ℝ)
    (Ww : Matrix m q ℝ) (c : q → ℝ) (Wr' : Matrix p m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' q ℝ)
    (c' : q → ℝ) (M : Matrix p q ℝ)
    (hr : ∀ i, Wrᵀ i ≠ 0) (hw : ∀ i, Ww i ≠ 0)
    (hH : ∀ i k, i ≠ k → ∀ r : ℝ, ¬ (Wrᵀ i = r • Wrᵀ k ∧ b i = r * b k))
    (hG : ∀ S : Finset m, ∃ o : q, sqTarget M Wr b Ww S o ≠ 0)
    (hcell : ∀ x₀ : p → ℝ, (∀ i, (x₀ ᵥ* Wr) i + b i ≠ 0) →
      (∀ j, (x₀ ᵥ* Wr') j + b' j = 0 → Wr'ᵀ j = 0) →
      ∀ y : p → ℝ, y ᵥ* M + reluSqCell Wr b Ww c x₀ y = reluSqCell Wr' b' Ww' c' x₀ y) :
    Fintype.card m < Fintype.card m' := by
  classical
  by_contra hle
  push Not at hle
  obtain ⟨S, U, F₁, F₂, -, -, hcount, hspan⟩ :=
    exists_sqTarget_mem_span_of_reluSqCell Wr b Ww c Wr' b' Ww' c' M hr hw hH hcell
  -- the count leaves no room: `U = F₁ = ∅`, so every `τ_o` is `0`
  have hU : U = ∅ := Finset.card_eq_zero.1 (by omega)
  have hF : F₁ = ∅ := Finset.card_eq_zero.1 (by omega)
  obtain ⟨o, ho⟩ := hG S
  have h := (hspan o).1
  rw [hU, hF, Finset.coe_empty, Finset.coe_empty, Set.image_empty, Set.image_empty,
    Submodule.span_empty, sup_bot_eq, Submodule.mem_bot] at h
  exact ho h

end Skips
