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
  sorry

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
  sorry

end Skips
