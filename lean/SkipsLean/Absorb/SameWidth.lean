import SkipsLean.Absorb.Block
import SkipsLean.OneBlock.Mlp

/-!
# Absorption at the same width: only by flipped reads

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Theorem 3.1 (i) and Proposition 3.2, with
Theorem A.4, Corollary A.9 and the reduction of GELU to ReLU along rays (proof of Theorem 4.5).

Let `σ` be ReLU or GELU and let the block `B(x) = σ(x W_read) W_write` be nondegenerate: the columns
of `W_read` are nonzero and pairwise non-collinear, and the rows of `W_write` are nonzero. A block of
the same width computes `x M + B(x)` if and only if some set `S` of hidden units has
`W_read[:,S] W_write[S,:] = -M` (Corollary A.9; the "if" is `vanillaBlock_flipCols_of_subProd`).
For `M ≠ 0` this holds only on a set of weights of measure zero.

The paper proves the "only if" for ReLU through the kinks of `|x w_i|` (Theorem A.4) and for GELU
through ridge functions (Theorem A.7). Here the case of GELU is obtained from the case of ReLU by
the paper's reduction along rays: `|GELU(t y)/t - ReLU(y)| ≤ κ/t`, so a GELU block equation implies
the ReLU block equation with the same weights.

Weights are rectangular (`p` inputs, `q` outputs), as in Corollary A.9. "Generic" refers to an
additive Haar measure on the pairs `(W_read, W_write)`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {p q m : Type*} [Fintype p] [Fintype m]

/-- A block is **nondegenerate** if the columns of `W_read` are nonzero and pairwise non-collinear
(no one of them is a scalar multiple of another) and the rows of `W_write` are nonzero. -/
structure Nondegenerate (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ) : Prop where
  col_ne_zero : ∀ i, Wrᵀ i ≠ 0
  col_not_collinear : ∀ i j, i ≠ j → ∀ r : ℝ, Wrᵀ i ≠ r • Wrᵀ j
  row_ne_zero : ∀ i, Ww i ≠ 0

/-! ### GELU and ReLU along rays -/

/-- `GELU(y) - ReLU(y) = -|y| Φ(-|y|)` (proof of Theorem 4.5). -/
theorem gelu_sub_relu (y : ℝ) : gelu y - relu y = -(|y| * gaussCdf (-|y|)) := by
  rcases le_total 0 y with hy | hy
  · -- `y ≥ 0`: `y Φ(y) - y = -y (1 - Φ(y)) = -y Φ(-y)`
    rw [abs_of_nonneg hy, gaussCdf_neg, gelu, relu, max_eq_left hy]
    ring
  · -- `y ≤ 0`: `y Φ(y) - 0 = -|y| Φ(-|y|)`, with `|y| = -y`
    rw [abs_of_nonpos hy, neg_neg, gelu, relu, max_eq_right hy]
    ring

/-- `φ(u) ≤ 1`: `e^{-u²/2} ≤ 1 ≤ √(2π)`. -/
private theorem gaussPdf_le_one (u : ℝ) : gaussPdf u ≤ 1 := by
  have h1 : Real.exp (-u ^ 2 / 2) ≤ 1 :=
    Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg u)) two_pos.le)
  have h2 : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  rw [gaussPdf, div_le_one (by linarith)]
  linarith

/-- `|GELU(y) - ReLU(y)|` is bounded. (The paper's bound is `κ < 0.17`; any bound serves.) -/
theorem abs_gelu_sub_relu_le (y : ℝ) : |gelu y - relu y| ≤ 1 := by
  rw [gelu_sub_relu, abs_neg]
  rcases (abs_nonneg y).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul, abs_zero]
    exact zero_le_one
  · -- `u Φ(-u) = u (1 - Φ(u)) ≤ φ(u) ≤ 1` for `u = |y| > 0`
    rw [abs_of_pos (mul_pos hpos (gaussCdf_pos _)), gaussCdf_neg]
    calc |y| * (1 - gaussCdf |y|) ≤ |y| * (gaussPdf |y| / |y|) :=
          mul_le_mul_of_nonneg_left (one_sub_gaussCdf_le hpos) hpos.le
      _ = gaussPdf |y| := by field_simp
      _ ≤ 1 := gaussPdf_le_one _

/-- An output coordinate of a vanilla block. -/
private theorem vanillaBlock_apply {k : Type*} [Fintype k] (σ : ℝ → ℝ) (W : Matrix p k ℝ)
    (V : Matrix k q ℝ) (z : p → ℝ) (o : q) :
    vanillaBlock σ W V z o = ∑ i, σ ((z ᵥ* W) i) * V i o := rfl

/-- ReLU is positively homogeneous: `ReLU(t y) = t ReLU(y)` for `t > 0`. -/
private theorem relu_mul_of_pos {t : ℝ} (ht : 0 < t) (y : ℝ) : relu (t * y) = t * relu y := by
  rw [relu, relu, mul_max_of_nonneg _ _ ht.le, mul_zero]

/-- `|∑ᵢ (GELU(t yᵢ) - t ReLU(yᵢ)) wᵢ| ≤ ∑ᵢ |wᵢ|` for `t > 0`. -/
private theorem abs_sum_gelu_sub_le {ι : Type*} [Fintype ι] {t : ℝ} (ht : 0 < t) (y w : ι → ℝ) :
    |∑ i, (gelu (t * y i) - t * relu (y i)) * w i| ≤ ∑ i, |w i| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, ← relu_mul_of_pos ht]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_gelu_sub_relu_le _)

/-- **GELU to ReLU along rays** (proof of Theorem 4.5, for one block): if a GELU block absorbs
`x M` into a GELU block, of any width, then the ReLU blocks with the same weights satisfy the same
equation. (Evaluate at `t x`, divide by `t`, and let `t → ∞`.) -/
theorem relu_absorb_of_gelu_absorb {m' : Type*} [Fintype m'] (Wr : Matrix p m ℝ)
    (Ww : Matrix m q ℝ) (Wr' : Matrix p m' ℝ) (Ww' : Matrix m' q ℝ) (M : Matrix p q ℝ)
    (h : ∀ x : p → ℝ, x ᵥ* M + vanillaBlock gelu Wr Ww x = vanillaBlock gelu Wr' Ww' x) :
    ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x := by
  intro x
  funext o
  -- the GELU equation at `t x`, coordinate `o`
  have hG : ∀ t : ℝ, t * (x ᵥ* M) o + ∑ i, gelu (t * (x ᵥ* Wr) i) * Ww i o
      = ∑ j, gelu (t * (x ᵥ* Wr') j) * Ww' j o := by
    intro t
    have h1 := congrFun (h (t • x)) o
    simpa only [Pi.add_apply, vanillaBlock_apply, Matrix.smul_vecMul, Pi.smul_apply,
      smul_eq_mul] using h1
  -- the defect `D` of the ReLU equation at `o` has `|t D| ≤ C` for all `t > 0`
  obtain ⟨D, hD⟩ : ∃ D, D = (x ᵥ* M) o + ∑ i, relu ((x ᵥ* Wr) i) * Ww i o
      - ∑ j, relu ((x ᵥ* Wr') j) * Ww' j o := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = ∑ i, |Ww i o| + ∑ j, |Ww' j o| := ⟨_, rfl⟩
  have hbound : ∀ t : ℝ, 0 < t → |t * D| ≤ C := by
    intro t ht
    -- `t D = ∑ⱼ (GELU(t y'ⱼ) - t ReLU(y'ⱼ)) ŵ'ⱼ - ∑ᵢ (GELU(t yᵢ) - t ReLU(yᵢ)) ŵᵢ`
    have e : t * D = ∑ j, (gelu (t * (x ᵥ* Wr') j) - t * relu ((x ᵥ* Wr') j)) * Ww' j o
        - ∑ i, (gelu (t * (x ᵥ* Wr) i) - t * relu ((x ᵥ* Wr) i)) * Ww i o := by
      simp only [sub_mul, Finset.sum_sub_distrib, hD, mul_add, mul_sub, Finset.mul_sum,
        mul_assoc]
      linarith [hG t]
    rw [e, hC]
    refine (abs_sub _ _).trans ?_
    linarith [abs_sum_gelu_sub_le ht (fun j => (x ᵥ* Wr') j) (fun j => Ww' j o),
      abs_sum_gelu_sub_le ht (fun i => (x ᵥ* Wr) i) (fun i => Ww i o)]
  -- hence `D = 0`: else `t = (C + 1)/|D|` gives `|t D| = C + 1`
  have hD0 : D = 0 := by
    by_contra hne
    have hC0 : 0 ≤ C := hC ▸ add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have hDpos : 0 < |D| := abs_pos.2 hne
    have ht : 0 < (C + 1) / |D| := div_pos (by linarith) hDpos
    have h1 := hbound _ ht
    rw [abs_mul, abs_of_pos ht, div_mul_cancel₀ _ hDpos.ne'] at h1
    linarith
  rw [Pi.add_apply, vanillaBlock_apply, vanillaBlock_apply]
  linarith

/-! ### Corollary A.9 and Theorem 3.1 (i) -/

/-- ReLU satisfies `σ(z) + σ(-z) = |z|`: the even part of ReLU is `|z|/2`. -/
private theorem relu_add_relu_neg (z : ℝ) : relu z + relu (-z) = |z| := by
  simp only [relu]
  rcases le_total z 0 with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h), abs_of_nonpos h]; ring
  · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h), abs_of_nonneg h]; ring

/-- **A point on a hyperplane and off finitely many others.** If no vector `u k` is a multiple of
`c`, some `x` has `x ⬝ᵥ c = 0` and `x ⬝ᵥ u k ≠ 0` for every `k`: the hyperplane `x c = 0` is not
contained in the union of the hyperplanes `x u_k = 0`, which are different from it (as
`exists_on_hyperplane` in `OneBlock/UnitsReLU.lean`, without the biases). The family `u` may
collect the columns of the reads of two blocks of different widths. -/
theorem exists_dotProduct_eq_zero_and_ne_zero {n ι : Type*} [Fintype n] [Finite ι]
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

/-- `|a + b| + |a - b| = 2 |a|` when `|b| ≤ |a|`: no sign change between `a - b` and `a + b`. -/
private theorem abs_add_add_abs_sub_of_le {a b : ℝ} (h : |b| ≤ |a|) :
    |a + b| + |a - b| = 2 * |a| := by
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha] at h ⊢
    obtain ⟨h1, h2⟩ := abs_le.1 h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    ring
  · rw [abs_of_nonpos ha] at h ⊢
    obtain ⟨h1, h2⟩ := abs_le.1 h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    ring

open Filter Topology in
/-- Near `s = 0`, `|s b| ≤ a` for `a > 0`. -/
private theorem eventually_abs_mul_le {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∀ᶠ s in 𝓝 (0 : ℝ), |s * b| ≤ a := by
  have hc : Continuous fun s : ℝ => |s * b| := by fun_prop
  have h0 : Tendsto (fun s : ℝ => |s * b|) (𝓝 0) (𝓝 0) := by simpa using hc.tendsto 0
  exact (h0.eventually (eventually_lt_nhds ha)).mono fun _ h => h.le

open Filter Topology in
/-- **The kink of one unit** (Theorem A.4, Steps 1 and 2, in the form of (★)). Let
`∑_k |x w_k| ŵ_k = ∑_j |x w'_j| ŵ'_j` for all `x`, for two blocks of widths `m` and `m'`, and let
the column `w_i` be nonzero and not collinear with any other column `w_k` of the first read. Let
`J` be the set of units `j` of the second block whose column `w'_j` is a multiple `r_j w_i` of `w_i`
(a zero column included). Then `ŵ_i = ∑_{j ∈ J} |r_j| ŵ'_j`. Proof: at a point `x₀` with
`x₀ w_i = 0` and on no other hyperplane of the two blocks, and a direction `v` with `v w_i = 1`,
the second difference `G(x₀ + s v) + G(x₀ - s v) - 2 G(x₀)` of both sides at a small `s > 0` keeps
only the terms on the hyperplane of `w_i`: `2 s ŵ_i` on the left, `2 s ∑_{j ∈ J} |r_j| ŵ'_j` on
the right. -/
theorem write_eq_sum_of_abs_eq {m' : Type*} [Fintype m'] (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ)
    (Wr' : Matrix p m' ℝ) (Ww' : Matrix m' q ℝ)
    (h : ∀ x : p → ℝ, (fun k => |(x ᵥ* Wr) k|) ᵥ* Ww = (fun j => |(x ᵥ* Wr') j|) ᵥ* Ww')
    (i : m) (hc : Wrᵀ i ≠ 0) (hcol : ∀ k, k ≠ i → ∀ r : ℝ, Wrᵀ k ≠ r • Wrᵀ i)
    (J : Finset m') (r : m' → ℝ) (hJ : ∀ j ∈ J, Wr'ᵀ j = r j • Wrᵀ i)
    (hJc : ∀ j ∉ J, ∀ t : ℝ, Wr'ᵀ j ≠ t • Wrᵀ i) :
    Ww i = ∑ j ∈ J, |r j| • Ww' j := by
  classical
  -- a point `x₀` of the hyperplane `x w_i = 0` on no other hyperplane of the two blocks
  obtain ⟨x₀, hx₀i, hx₀⟩ := exists_dotProduct_eq_zero_and_ne_zero (Wrᵀ i)
    (Sum.elim (fun k : {k // k ≠ i} => Wrᵀ k.1) (fun j : {j // j ∉ J} => Wr'ᵀ j.1))
    (by rintro (⟨k, hk⟩ | ⟨j, hj⟩) t; exacts [hcol k hk t, hJc j hj t])
  have hx₁ : ∀ k, k ≠ i → x₀ ⬝ᵥ Wrᵀ k ≠ 0 := fun k hk => hx₀ (Sum.inl ⟨k, hk⟩)
  have hx₂ : ∀ j, j ∉ J → x₀ ⬝ᵥ Wr'ᵀ j ≠ 0 := fun j hj => hx₀ (Sum.inr ⟨j, hj⟩)
  -- a direction `v` with `v w_i = 1`
  have hii : Wrᵀ i ⬝ᵥ Wrᵀ i ≠ 0 := dotProduct_self_eq_zero.not.2 hc
  obtain ⟨v, hv⟩ : ∃ v : p → ℝ, v ⬝ᵥ Wrᵀ i = 1 :=
    ⟨(Wrᵀ i ⬝ᵥ Wrᵀ i)⁻¹ • Wrᵀ i, by rw [smul_dotProduct, smul_eq_mul, inv_mul_cancel₀ hii]⟩
  -- a small `s > 0`: off the hyperplane of `w_i`, no term changes sign between `x₀ ± s v`
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), (∀ k, k ≠ i → |s * (v ⬝ᵥ Wrᵀ k)| ≤ |x₀ ⬝ᵥ Wrᵀ k|) ∧
      (∀ j, j ∉ J → |s * (v ⬝ᵥ Wr'ᵀ j)| ≤ |x₀ ⬝ᵥ Wr'ᵀ j|) := by
    refine (Filter.eventually_all.2 fun k => ?_).and (Filter.eventually_all.2 fun j => ?_)
    · by_cases hk : k = i
      · exact Filter.Eventually.of_forall fun _ h => absurd hk h
      · exact (eventually_abs_mul_le (abs_pos.2 (hx₁ k hk)) _).mono fun _ h _ => h
    · by_cases hj : j ∈ J
      · exact Filter.Eventually.of_forall fun _ h => absurd hj h
      · exact (eventually_abs_mul_le (abs_pos.2 (hx₂ j hj)) _).mono fun _ h _ => h
  obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin (s := Set.Ioi 0))).exists
  have hs0 : 0 < s := hs
  -- `δ u`: the second difference of `x ↦ |x u|` at `x₀` along `s v`
  obtain ⟨δ, hδ⟩ : ∃ δ : (p → ℝ) → ℝ, ∀ u, δ u =
      |(x₀ + s • v) ⬝ᵥ u| + |(x₀ - s • v) ⬝ᵥ u| - 2 * |x₀ ⬝ᵥ u| := ⟨_, fun _ => rfl⟩
  have hδ0 : ∀ u, |s * (v ⬝ᵥ u)| ≤ |x₀ ⬝ᵥ u| → δ u = 0 := by
    intro u hu
    rw [hδ, add_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul,
      abs_add_add_abs_sub_of_le hu, sub_self]
  have hδi : ∀ t : ℝ, δ (t • Wrᵀ i) = 2 * s * |t| := by
    intro t
    rw [hδ]
    simp only [add_dotProduct, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, hx₀i,
      hv, mul_zero, zero_add, zero_sub, mul_one, abs_neg, abs_zero, abs_mul, abs_of_pos hs0]
    ring
  -- the second difference of both sides, at the output coordinate `o`
  funext o
  have hsum : ∀ x : p → ℝ, ∑ k, |x ⬝ᵥ Wrᵀ k| * Ww k o = ∑ j, |x ⬝ᵥ Wr'ᵀ j| * Ww' j o :=
    fun x => congrFun (h x) o
  have hL : ∑ k, |(x₀ + s • v) ⬝ᵥ Wrᵀ k| * Ww k o + ∑ k, |(x₀ - s • v) ⬝ᵥ Wrᵀ k| * Ww k o
      - 2 * ∑ k, |x₀ ⬝ᵥ Wrᵀ k| * Ww k o = 2 * s * Ww i o := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      Finset.sum_eq_single i]
    · have := hδi 1
      rw [one_smul, abs_one, mul_one, hδ] at this
      rw [← this]
      ring
    · intro k _ hk
      have := hδ0 _ (hs1 k hk)
      rw [hδ] at this
      linear_combination (Ww k o) * this
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hR : ∑ j, |(x₀ + s • v) ⬝ᵥ Wr'ᵀ j| * Ww' j o + ∑ j, |(x₀ - s • v) ⬝ᵥ Wr'ᵀ j| * Ww' j o
      - 2 * ∑ j, |x₀ ⬝ᵥ Wr'ᵀ j| * Ww' j o = 2 * s * ∑ j ∈ J, |r j| * Ww' j o := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_subset (Finset.subset_univ J)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have := hδi (r j)
      rw [← hJ j hj, hδ] at this
      linear_combination (Ww' j o) * this
    · intro j _ hj
      have := hδ0 _ (hs2 j hj)
      rw [hδ] at this
      linear_combination (Ww' j o) * this
  have key : 2 * s * Ww i o = 2 * s * ∑ j ∈ J, |r j| * Ww' j o := by
    rw [← hL, ← hR, hsum, hsum, hsum]
  have h2s : (2 * s) ≠ 0 := by positivity
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_left_cancel₀ h2s key

variable [DecidableEq m]

/-- **Corollary A.9 / Theorem A.4, "only if", for ReLU.** Let the block be nondegenerate. If a
ReLU block of the same width computes `x M + B(x)`, then some set `S` of hidden units has
`W_read[:,S] W_write[S,:] = -M`. (The paper assumes `p ≥ 2`; the proof does not use it.) -/
theorem exists_subProd_eq_neg_of_relu_absorb (Wr : Matrix p m ℝ)
    (Ww : Matrix m q ℝ) (hnd : Nondegenerate Wr Ww) (M : Matrix p q ℝ) (Wr' : Matrix p m ℝ)
    (Ww' : Matrix m q ℝ)
    (h : ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x) :
    ∃ S : Finset m, subProd S Wr Ww = -M := by
  classical
  -- the equation at `x` and at `-x`, at the output coordinate `o`
  have hpre : ∀ (x : p → ℝ) (o : q), (x ᵥ* M) o + ∑ k, relu (x ⬝ᵥ Wrᵀ k) * Ww k o
      = ∑ j, relu (x ⬝ᵥ Wr'ᵀ j) * Ww' j o := fun x o => congrFun (h x) o
  have hpm : ∀ (x : p → ℝ) (o : q), -(x ᵥ* M) o + ∑ k, relu (-(x ⬝ᵥ Wrᵀ k)) * Ww k o
      = ∑ j, relu (-(x ⬝ᵥ Wr'ᵀ j)) * Ww' j o := by
    intro x o
    have h2 := hpre (-x) o
    simp only [Matrix.neg_vecMul, Pi.neg_apply, neg_dotProduct] at h2
    exact h2
  -- the even part (`ReLU(z) + ReLU(-z) = |z|`): `|x W_read| W_write = |x W_read'| W_write'`
  have hEven : ∀ x : p → ℝ,
      (fun k => |(x ᵥ* Wr) k|) ᵥ* Ww = (fun j => |(x ᵥ* Wr') j|) ᵥ* Ww' := by
    intro x
    funext o
    show ∑ k, |x ⬝ᵥ Wrᵀ k| * Ww k o = ∑ j, |x ⬝ᵥ Wr'ᵀ j| * Ww' j o
    simp only [← relu_add_relu_neg, add_mul, Finset.sum_add_distrib]
    linarith [hpre x o, hpm x o]
  -- the odd part (`ReLU(z) - ReLU(-z) = z`): `x W_read W_write + 2 x M = x W_read' W_write'`
  have hOdd : ∀ (x : p → ℝ) (o : q), 2 * (x ᵥ* M) o + ∑ k, (x ⬝ᵥ Wrᵀ k) * Ww k o
      = ∑ j, (x ⬝ᵥ Wr'ᵀ j) * Ww' j o := by
    intro x o
    have e1 : ∑ k, (x ⬝ᵥ Wrᵀ k) * Ww k o
        = ∑ k, relu (x ⬝ᵥ Wrᵀ k) * Ww k o - ∑ k, relu (-(x ⬝ᵥ Wrᵀ k)) * Ww k o := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [← sub_mul, relu_sub_relu_neg]
    have e2 : ∑ j, (x ⬝ᵥ Wr'ᵀ j) * Ww' j o
        = ∑ j, relu (x ⬝ᵥ Wr'ᵀ j) * Ww' j o - ∑ j, relu (-(x ⬝ᵥ Wr'ᵀ j)) * Ww' j o := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [← sub_mul, relu_sub_relu_neg]
    linarith [hpre x o, hpm x o]
  -- Steps 1 and 2 at unit `i`, with `J` the units `j` whose `w'_j` is a multiple `r_j w_i`
  have hJr : ∀ i, ∃ (J : Finset m) (r : m → ℝ), (∀ j ∈ J, Wr'ᵀ j = r j • Wrᵀ i) ∧
      (∀ j ∉ J, ∀ t : ℝ, Wr'ᵀ j ≠ t • Wrᵀ i) := by
    intro i
    have hr : ∀ j, ∃ t : ℝ, (∃ t' : ℝ, Wr'ᵀ j = t' • Wrᵀ i) → Wr'ᵀ j = t • Wrᵀ i := fun j => by
      by_cases hj : ∃ t' : ℝ, Wr'ᵀ j = t' • Wrᵀ i
      · obtain ⟨t', ht'⟩ := hj
        exact ⟨t', fun _ => ht'⟩
      · exact ⟨0, fun h' => absurd h' hj⟩
    choose r hr using hr
    exact ⟨Finset.univ.filter (fun j => ∃ t' : ℝ, Wr'ᵀ j = t' • Wrᵀ i), r,
      fun j hj => hr j (Finset.mem_filter.1 hj).2,
      fun j hj t ht => hj (Finset.mem_filter.2 ⟨Finset.mem_univ _, t, ht⟩)⟩
  have hstar : ∀ i (J : Finset m) (r : m → ℝ), (∀ j ∈ J, Wr'ᵀ j = r j • Wrᵀ i) →
      (∀ j ∉ J, ∀ t : ℝ, Wr'ᵀ j ≠ t • Wrᵀ i) → Ww i = ∑ j ∈ J, |r j| • Ww' j :=
    fun i J r hJ hJc => write_eq_sum_of_abs_eq Wr Ww Wr' Ww' hEven i (hnd.col_ne_zero i)
      (fun k hk t => hnd.col_not_collinear k i hk t) J r hJ hJc
  -- since `ŵ_i ≠ 0`, some `w'_j` is a nonzero multiple of `w_i`
  have hex : ∀ i, ∃ j, ∃ ρ : ℝ, ρ ≠ 0 ∧ Wr'ᵀ j = ρ • Wrᵀ i := by
    intro i
    obtain ⟨J, r, hJ, hJc⟩ := hJr i
    have hne : ∑ j ∈ J, |r j| • Ww' j ≠ 0 := hstar i J r hJ hJc ▸ hnd.row_ne_zero i
    obtain ⟨j, hj, hj0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact ⟨j, r j, fun h0 => hj0 (by rw [h0, abs_zero, zero_smul]), hJ j hj⟩
  choose f ρ hρ hf using hex
  -- two columns of the read that are collinear are the same column
  have hsame : ∀ a b (r₁ r₂ : ℝ), r₁ ≠ 0 → r₁ • Wrᵀ a = r₂ • Wrᵀ b → a = b := by
    intro a b r₁ r₂ h1 h12
    by_contra hab
    apply hnd.col_not_collinear a b hab (r₁⁻¹ * r₂)
    rw [mul_smul, ← h12, smul_smul, inv_mul_cancel₀ h1, one_smul]
  -- `i ↦ f i` is injective, hence a bijection of the units: each hyperplane gets one unit
  have hinj : Function.Injective f := by
    intro a b hab
    exact hsame a b (ρ a) (ρ b) (hρ a) (by rw [← hf a, ← hf b, hab])
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hinj
  -- a column `w'_j` that is a nonzero multiple of `w_i` is the column of `j = f i`
  have huniq : ∀ i j (t : ℝ), t ≠ 0 → Wr'ᵀ j = t • Wrᵀ i → j = f i := by
    intro i j t ht hj
    obtain ⟨i', rfl⟩ := hsurj j
    rw [hsame i i' t (ρ i') ht (by rw [← hj, hf])]
  -- (★) becomes `ŵ_i = |ρ_i| ŵ'_{f i}`: no kinks cancel
  have hw : ∀ i, Ww i = |ρ i| • Ww' (f i) := by
    intro i
    obtain ⟨J, r, hJ, hJc⟩ := hJr i
    have hfi : f i ∈ J := by
      by_contra hn
      exact hJc (f i) hn (ρ i) (hf i)
    have hr : r (f i) = ρ i :=
      smul_left_injective ℝ (hnd.col_ne_zero i) ((hJ (f i) hfi).symm.trans (hf i))
    rw [hstar i J r hJ hJc, Finset.sum_eq_single_of_mem (f i) hfi, hr]
    intro j hj hne
    have hr0 : r j = 0 := by
      by_contra h0
      exact hne (huniq i j (r j) h0 (hJ j hj))
    rw [hr0, abs_zero, zero_smul]
  -- Step 3, signs: `S` is the set of units whose read changes sign
  refine ⟨Finset.univ.filter (fun i => ρ i < 0), ?_⟩
  ext a o
  -- the odd part at the row `x = e_a`
  have hO := hOdd (Pi.single a 1) o
  have hxa : ∀ u : p → ℝ, Pi.single a (1 : ℝ) ⬝ᵥ u = u a := fun u => by
    rw [single_dotProduct, one_mul]
  have hxM : (Pi.single a (1 : ℝ) ᵥ* M) o = M a o := by
    rw [Matrix.single_one_vecMul]
    rfl
  simp only [hxa, hxM, Matrix.transpose_apply] at hO
  -- reindex the new units by `f`
  have hre : ∑ j, Wr' a j * Ww' j o = ∑ i, Wr' a (f i) * Ww' (f i) o :=
    ((Function.Bijective.sum_comp ⟨hinj, hsurj⟩ (fun j => Wr' a j * Ww' j o))).symm
  -- unit `f i` contributes `±` the term of unit `i`, with `-` exactly for `i ∈ S`
  have hterm : ∀ i, Wr' a (f i) * Ww' (f i) o - Wr a i * Ww i o
      = -2 * (Wr a i * (if ρ i < 0 then 1 else 0) * Ww i o) := by
    intro i
    have e1 : Wr' a (f i) = ρ i * Wr a i := congrFun (hf i) a
    have e2 : Ww i o = |ρ i| * Ww' (f i) o := congrFun (hw i) o
    rw [e1, e2]
    rcases lt_or_gt_of_ne (hρ i) with hneg | hpos
    · simp only [abs_of_neg hneg, hneg, ↓reduceIte]
      ring
    · simp only [abs_of_pos hpos, not_lt.2 hpos.le, ↓reduceIte]
      ring
  have hsum : ∑ i, Wr' a (f i) * Ww' (f i) o - ∑ i, Wr a i * Ww i o
      = -2 * ∑ i, Wr a i * (if ρ i < 0 then 1 else 0) * Ww i o := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hterm i
  have hsp : subProd (Finset.univ.filter (fun i => ρ i < 0)) Wr Ww a o
      = ∑ i, Wr a i * (if ρ i < 0 then 1 else 0) * Ww i o := by
    rw [subProd, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hsp, Matrix.neg_apply]
  linarith

/-- **Corollary A.9, "only if", for GELU.** -/
theorem exists_subProd_eq_neg_of_gelu_absorb (Wr : Matrix p m ℝ)
    (Ww : Matrix m q ℝ) (hnd : Nondegenerate Wr Ww) (M : Matrix p q ℝ) (Wr' : Matrix p m ℝ)
    (Ww' : Matrix m q ℝ)
    (h : ∀ x : p → ℝ, x ᵥ* M + vanillaBlock gelu Wr Ww x = vanillaBlock gelu Wr' Ww' x) :
    ∃ S : Finset m, subProd S Wr Ww = -M :=
  -- the ReLU blocks with the same weights satisfy the same equation
  exists_subProd_eq_neg_of_relu_absorb Wr Ww hnd M Wr' Ww'
    (relu_absorb_of_gelu_absorb Wr Ww Wr' Ww' M h)

/-- **Theorem 3.1 (i), first sentence, for ReLU** (Corollary A.9): a nondegenerate block absorbs
`x M` at the same width if and only if some set `S` of hidden units has
`W_read[:,S] W_write[S,:] = -M`. -/
theorem relu_absorb_same_width_iff (Wr : Matrix p m ℝ)
    (Ww : Matrix m q ℝ) (hnd : Nondegenerate Wr Ww) (M : Matrix p q ℝ) :
    (∃ (Wr' : Matrix p m ℝ) (Ww' : Matrix m q ℝ),
        ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x)
      ↔ ∃ S : Finset m, subProd S Wr Ww = -M := by
  constructor
  · rintro ⟨Wr', Ww', h⟩
    exact exists_subProd_eq_neg_of_relu_absorb Wr Ww hnd M Wr' Ww' h
  · -- flip the reads of the units of `S`
    rintro ⟨S, hS⟩
    exact ⟨flipCols S Wr, Ww, vanillaBlock_flipCols_of_subProd relu_sub_relu_neg S Wr Ww M hS⟩

/-- **Theorem 3.1 (i), first sentence, for GELU.** -/
theorem gelu_absorb_same_width_iff (Wr : Matrix p m ℝ)
    (Ww : Matrix m q ℝ) (hnd : Nondegenerate Wr Ww) (M : Matrix p q ℝ) :
    (∃ (Wr' : Matrix p m ℝ) (Ww' : Matrix m q ℝ),
        ∀ x : p → ℝ, x ᵥ* M + vanillaBlock gelu Wr Ww x = vanillaBlock gelu Wr' Ww' x)
      ↔ ∃ S : Finset m, subProd S Wr Ww = -M := by
  constructor
  · rintro ⟨Wr', Ww', h⟩
    exact exists_subProd_eq_neg_of_gelu_absorb Wr Ww hnd M Wr' Ww' h
  · -- flip the reads of the units of `S`
    rintro ⟨S, hS⟩
    exact ⟨flipCols S Wr, Ww, vanillaBlock_flipCols_of_subProd gelu_sub_gelu_neg S Wr Ww M hS⟩

variable [Fintype q]

/-- An entry of a product of two matrix-valued functions whose entries are analytic is
analytic. -/
private theorem analyticOnNhd_mul_entry {P a b c : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [Fintype b] {F : P → Matrix a b ℝ} {G : P → Matrix b c ℝ}
    (hF : ∀ i j, AnalyticOnNhd ℝ (fun y => F y i j) Set.univ)
    (hG : ∀ i j, AnalyticOnNhd ℝ (fun y => G y i j) Set.univ) (i : a) (j : c) :
    AnalyticOnNhd ℝ (fun y => (F y * G y) i j) Set.univ := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticOnNhd_fun_sum _ fun k _ => (hF i k).mul (hG k j)

omit [DecidableEq m] in
/-- An entry of the read is an analytic (linear) function of the weights. -/
private theorem analyticOnNhd_fst_apply (a : p) (i : m) :
    AnalyticOnNhd ℝ (fun W : Matrix p m ℝ × Matrix m q ℝ => W.1 a i) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ a i).comp
    (LinearMap.fst ℝ (Matrix p m ℝ) (Matrix m q ℝ)))

omit [DecidableEq m] in
/-- An entry of the write is an analytic (linear) function of the weights. -/
private theorem analyticOnNhd_snd_apply (i : m) (o : q) :
    AnalyticOnNhd ℝ (fun W : Matrix p m ℝ × Matrix m q ℝ => W.2 i o) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ i o).comp
    (LinearMap.snd ℝ (Matrix p m ℝ) (Matrix m q ℝ)))

omit [DecidableEq m] in
/-- An analytic function of the weights `(W_read, W_write)` that is not identically zero is nonzero
at generic weights. The Borel structure of the product is given explicitly: the measure sees the
topology of `Matrix`, the analytic function the one of the norm, and they agree only by
definition. -/
private theorem ae_ne_zero_of_analytic_prod
    (μ : Measure (Matrix p m ℝ × Matrix m q ℝ)) [μ.IsAddHaarMeasure]
    {g : Matrix p m ℝ × Matrix m q ℝ → ℝ} (hg : AnalyticOnNhd ℝ g Set.univ)
    (hne : ∃ y, g y ≠ 0) : ∀ᵐ W ∂μ, g W ≠ 0 := by
  have h1 : SecondCountableTopology (Matrix p m ℝ) :=
    inferInstanceAs (SecondCountableTopology (p → m → ℝ))
  have hB : BorelSpace (Matrix p m ℝ × Matrix m q ℝ) := Prod.borelSpace
  exact @ae_ne_zero_of_analytic _ _ _ _ _ hB μ ‹_› _ hg hne

/-- Generic blocks are nondegenerate (`p ≥ 2` inputs, at least one output). -/
theorem ae_nondegenerate (hp : 2 ≤ Fintype.card p) [Nonempty q]
    (μ : Measure (Matrix p m ℝ × Matrix m q ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, Nondegenerate W.1 W.2 := by
  classical
  obtain ⟨a₁, a₂, ha⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card p by omega)
  obtain ⟨o₀⟩ := ‹Nonempty q›
  -- the columns of the read are nonzero: their entries at `a₁` are
  have h1 : ∀ᵐ W ∂μ, ∀ i : m, W.1 a₁ i ≠ 0 := by
    refine ae_all_iff.2 fun i => ?_
    exact ae_ne_zero_of_analytic_prod μ (analyticOnNhd_fst_apply a₁ i)
      ⟨(Matrix.of fun _ _ => 1, 0), one_ne_zero⟩
  -- the rows of the write are nonzero: their entries at `o₀` are
  have h2 : ∀ᵐ W ∂μ, ∀ i : m, W.2 i o₀ ≠ 0 := by
    refine ae_all_iff.2 fun i => ?_
    exact ae_ne_zero_of_analytic_prod μ (analyticOnNhd_snd_apply i o₀)
      ⟨(0, Matrix.of fun _ _ => 1), one_ne_zero⟩
  -- two columns of the read are not collinear: a `2 × 2` minor does not vanish
  have h3 : ∀ᵐ W ∂μ, ∀ i j : m, i ≠ j →
      W.1 a₁ i * W.1 a₂ j - W.1 a₁ j * W.1 a₂ i ≠ 0 := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hij h
    · -- the read with the entries `(a₁, i)` and `(a₂, j)` equal to `1`, the others `0`
      let R : Matrix p m ℝ := Matrix.of fun a k =>
        if a = a₁ ∧ k = i then 1 else if a = a₂ ∧ k = j then 1 else 0
      have hR : R a₁ i * R a₂ j - R a₁ j * R a₂ i ≠ 0 := by
        simp only [R, Matrix.of_apply, ha, ha.symm, hij, Ne.symm hij, and_self, and_true,
          and_false, ↓reduceIte]
        norm_num
      have hg : AnalyticOnNhd ℝ (fun W : Matrix p m ℝ × Matrix m q ℝ =>
          W.1 a₁ i * W.1 a₂ j - W.1 a₁ j * W.1 a₂ i) Set.univ :=
        ((analyticOnNhd_fst_apply a₁ i).mul (analyticOnNhd_fst_apply a₂ j)).sub
          ((analyticOnNhd_fst_apply a₁ j).mul (analyticOnNhd_fst_apply a₂ i))
      exact (ae_ne_zero_of_analytic_prod μ hg ⟨(R, 0), hR⟩).mono fun _ h _ => h
  filter_upwards [h1, h2, h3] with W h1 h2 h3
  refine ⟨fun i hi => h1 i (congrFun hi a₁), fun i j hij r hr => ?_,
    fun i hi => h2 i (congrFun hi o₀)⟩
  -- if `w_i = r w_j`, the minor of the columns `i`, `j` vanishes
  have e1 : W.1 a₁ i = r * W.1 a₁ j := congrFun hr a₁
  have e2 : W.1 a₂ i = r * W.1 a₂ j := congrFun hr a₂
  apply h3 i j hij
  rw [e1, e2]
  ring

/-- For `M ≠ 0` the condition `W_read[:,S] W_write[S,:] = -M` fails for every `S` at generic
weights: it is polynomial in the weights and fails when the writes vanish. -/
theorem ae_forall_subProd_ne_neg (M : Matrix p q ℝ) (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × Matrix m q ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ∀ S : Finset m, subProd S W.1 W.2 ≠ -M := by
  -- an entry `(a, o)` with `M a o ≠ 0`
  obtain ⟨a, o, hao⟩ : ∃ a o, M a o ≠ 0 := by
    by_contra hc
    exact hM (Matrix.ext fun a o => by_contra fun h => hc ⟨a, o, h⟩)
  refine ae_all_iff.2 fun S => ?_
  -- `W ↦ (W_read Π_S W_write) a o + M a o` is a polynomial, equal to `M a o ≠ 0` at `W = 0`
  have hg : AnalyticOnNhd ℝ (fun W : Matrix p m ℝ × Matrix m q ℝ =>
      subProd S W.1 W.2 a o + M a o) Set.univ := by
    refine AnalyticOnNhd.add ?_ analyticOnNhd_const
    have h1 : ∀ a k, AnalyticOnNhd ℝ (fun W : Matrix p m ℝ × Matrix m q ℝ =>
        (W.1 * Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0)) a k) Set.univ :=
      analyticOnNhd_mul_entry (F := fun W : Matrix p m ℝ × Matrix m q ℝ => W.1)
        (G := fun _ => Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0))
        (fun a i => analyticOnNhd_fst_apply a i) (fun _ _ => analyticOnNhd_const)
    exact analyticOnNhd_mul_entry (F := fun W : Matrix p m ℝ × Matrix m q ℝ =>
        W.1 * Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0))
      (G := fun W => W.2) h1 (fun i o => analyticOnNhd_snd_apply i o) a o
  have h0 : subProd S (0 : Matrix p m ℝ × Matrix m q ℝ).1 (0 : Matrix p m ℝ × Matrix m q ℝ).2 a o
      + M a o ≠ 0 := by
    simpa only [subProd, Prod.fst_zero, Prod.snd_zero, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.zero_apply, zero_add] using hao
  filter_upwards [ae_ne_zero_of_analytic_prod μ hg ⟨0, h0⟩] with W hW hS
  apply hW
  rw [hS, Matrix.neg_apply, neg_add_cancel]

/-- **Theorem 3.1 (i), second sentence, for ReLU:** fix `M ≠ 0`. For generic `θ = (W_read, W_write)`
no ReLU block of the same width computes `x M + B_θ(x)`. -/
theorem ae_not_relu_absorb_same_width (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ) (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × Matrix m q ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ¬ ∃ (Wr' : Matrix p m ℝ) (Ww' : Matrix m q ℝ),
      ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu W.1 W.2 x = vanillaBlock relu Wr' Ww' x := by
  -- `q` is nonempty, since `M ≠ 0`
  have : Nonempty q := by
    by_contra hq
    exact hM (Matrix.ext fun _ o => (hq ⟨o⟩).elim)
  filter_upwards [ae_nondegenerate hp μ, ae_forall_subProd_ne_neg M hM μ] with W hnd hS
  rintro ⟨Wr', Ww', h⟩
  obtain ⟨S, hS'⟩ := exists_subProd_eq_neg_of_relu_absorb W.1 W.2 hnd M Wr' Ww' h
  exact hS S hS'

/-- **Theorem 3.1 (i), second sentence, for GELU.** -/
theorem ae_not_gelu_absorb_same_width (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ) (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × Matrix m q ℝ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ W ∂μ, ¬ ∃ (Wr' : Matrix p m ℝ) (Ww' : Matrix m q ℝ),
      ∀ x : p → ℝ, x ᵥ* M + vanillaBlock gelu W.1 W.2 x = vanillaBlock gelu Wr' Ww' x := by
  -- `q` is nonempty, since `M ≠ 0`
  have : Nonempty q := by
    by_contra hq
    exact hM (Matrix.ext fun _ o => (hq ⟨o⟩).elim)
  filter_upwards [ae_nondegenerate hp μ, ae_forall_subProd_ne_neg M hM μ] with W hnd hS
  rintro ⟨Wr', Ww', h⟩
  obtain ⟨S, hS'⟩ := exists_subProd_eq_neg_of_gelu_absorb W.1 W.2 hnd M Wr' Ww' h
  exact hS S hS'

/-! ### Proposition 3.2: networks of one block -/

section OneBlock

variable {T dIn dOut : Type*} {d : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

omit [Fintype T] [Fintype dOut] in
/-- A row of a residual network of one MLP block: `x E D + σ(x E W_read) W_write D`. -/
private theorem eval_residual_row (σ : ℝ → ℝ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (X : Matrix T dIn ℝ) (t : T) :
    eval (Arch.mlp σ id hid) 1 θ X t
      = X t ᵥ* (θ.E * θ.D) + vanillaBlock σ (θ.E * θ.read 0) (θ.write 0 * θ.D) (X t) := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.mlp (T := T) (d := d) σ id hid).χ = id := rfl
  have hf : (Arch.mlp (T := T) (d := d) σ id hid).f 0 = fun M => M.map σ := rfl
  -- `h_1 = h_0 + σ(h_0 W_read) W_write` with `h_0 = X E`
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hχ, hf]
  simp only [id_eq, Pi.one_apply, Matrix.mul_one]
  have e : (X * θ.E + (X * θ.E * θ.read 0).map σ * θ.write 0) * θ.D
      = X * (θ.E * θ.D) + (X * (θ.E * θ.read 0)).map σ * (θ.write 0 * θ.D) := by
    rw [Matrix.add_mul, Matrix.mul_assoc X θ.E θ.D, Matrix.mul_assoc X θ.E (θ.read 0),
      Matrix.mul_assoc]
  rw [e]
  exact congrArg₂ (· + ·) (Matrix.mul_apply_eq_vecMul X _ t)
    (map_mul_mul_row σ (θ.E * θ.read 0) (θ.write 0 * θ.D) X t)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dOut] in
/-- A row of a skipless network of one MLP block: `σ(x E' W_read') W_write' D'`. -/
private theorem eval_skipless_row (σ : ℝ → ℝ) {d' : Type*} [Fintype d']
    (θ' : Params (Arch.mlp (T := T) (d := d') σ id hid) dIn dOut) (X : Matrix T dIn ℝ) (t : T) :
    eval (Arch.mlp σ id hid) 0 θ' X t
      = vanillaBlock σ (θ'.E * θ'.read 0) (θ'.write 0 * θ'.D) (X t) := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.mlp (T := T) (d := d') σ id hid).χ = id := rfl
  have hf : (Arch.mlp (T := T) (d := d') σ id hid).f 0 = fun M => M.map σ := rfl
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hχ, hf]
  simp only [Pi.zero_apply, Matrix.mul_zero, zero_add, id_eq]
  rw [Matrix.mul_assoc X θ'.E (θ'.read 0), Matrix.mul_assoc _ (θ'.write 0) θ'.D]
  exact map_mul_mul_row σ _ _ X t

omit [Fintype T] [DecidableEq d] in
/-- At generic parameters of one MLP block, `E W_read[:,S] W_write[S,:] D ≠ -E D` for every set
`S` of units, if `E D` can be nonzero: an entry of the difference is a polynomial in the weights,
equal to `(E D)_{a o} ≠ 0` when the write vanishes. -/
private theorem ae_subProd_ne_neg_oneBlock {σ : ℝ → ℝ} [DecidableEq (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, ∀ S : Finset (hid 0),
      subProd S (θ.E * θ.read 0) (θ.write 0 * θ.D) ≠ -(θ.E * θ.D) := by
  obtain ⟨a⟩ : Nonempty dIn := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨o⟩ : Nonempty dOut := Fintype.card_pos_iff.1 (by omega)
  refine ae_all_iff.2 fun S => ?_
  -- the entry `(a, o)` of `E W_read Π_S W_write D + E D` is a polynomial in the parameters
  have hg : AnalyticOnNhd ℝ (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
      subProd S (θ.E * θ.read 0) (θ.write 0 * θ.D) a o + (θ.E * θ.D) a o) Set.univ := by
    have hED : AnalyticOnNhd ℝ (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        (θ.E * θ.D) a o) Set.univ :=
      analyticOnNhd_mul_apply (Params.linE (A := Arch.mlp (T := T) (d := d) σ id hid) (dIn := dIn) (dOut := dOut))
        Params.linD a o
    refine AnalyticOnNhd.add ?_ hED
    have h1 : ∀ a k, AnalyticOnNhd ℝ
        (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
          (θ.E * θ.read 0 * Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0)) a k)
        Set.univ :=
      analyticOnNhd_mul_entry
        (F := fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut => θ.E * θ.read 0)
        (G := fun _ => Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0))
        (fun a i => analyticOnNhd_E_mul_read (A := Arch.mlp (T := T) (d := d) σ id hid) (dOut := dOut) 0 a i)
        (fun _ _ => analyticOnNhd_const)
    exact analyticOnNhd_mul_entry
      (F := fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        θ.E * θ.read 0 * Matrix.diagonal (fun j => if j ∈ S then (1 : ℝ) else 0))
      (G := fun θ => θ.write 0 * θ.D) h1
      (fun i o => analyticOnNhd_write_mul_D (A := Arch.mlp (T := T) (d := d) σ id hid) (dIn := dIn) 0 i o) a o
  -- at the parameters with `W_write = 0` and `E`, `D` of ones it is `card d ≠ 0`
  let θ₀ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => 0, fun _ => 0, Matrix.of fun _ _ => 1⟩
  have h0 : subProd S (θ₀.E * θ₀.read 0) (θ₀.write 0 * θ₀.D) a o + (θ₀.E * θ₀.D) a o ≠ 0 := by
    simp only [θ₀, subProd, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_apply, zero_add]
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact sum_one_mul_one_ne_zero hd
  filter_upwards [ae_ne_zero_of_analytic μ hg ⟨θ₀, h0⟩] with θ hθ hS
  exact hθ (by rw [hS, Matrix.neg_apply, neg_add_cancel])

/-- Proposition 3.2 for an activation for which Corollary A.9 holds. -/
private theorem ae_ne_skipless_oneBlock_of {σ : ℝ → ℝ} [Nonempty T] [DecidableEq (hid 0)]
    (hσ : ∀ (Wr : Matrix dIn (hid 0) ℝ) (Ww : Matrix (hid 0) dOut ℝ), Nondegenerate Wr Ww →
      ∀ (M : Matrix dIn dOut ℝ) (Wr' : Matrix dIn (hid 0) ℝ) (Ww' : Matrix (hid 0) dOut ℝ),
        (∀ x : dIn → ℝ, x ᵥ* M + vanillaBlock σ Wr Ww x = vanillaBlock σ Wr' Ww' x) →
        ∃ S : Finset (hid 0), subProd S Wr Ww = -M)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∀ (d' : Type) [Fintype d']
      (θ' : Params (Arch.mlp (T := T) (d := d') σ id hid) dIn dOut),
      ∃ X : Matrix T dIn ℝ,
        eval (Arch.mlp σ id hid) 1 θ X ≠ eval (Arch.mlp σ id hid) 0 θ' X := by
  filter_upwards [ae_oneBlockGeneric μ hd hdIn hdOut hhid,
    ae_subProd_ne_neg_oneBlock μ hd hdIn hdOut] with θ hθ hS
  intro d' _ θ'
  by_contra hall
  have heq : ∀ X : Matrix T dIn ℝ,
      eval (Arch.mlp σ id hid) 1 θ X = eval (Arch.mlp σ id hid) 0 θ' X :=
    fun X => by_contra fun hne => hall ⟨X, hne⟩
  -- on an input whose rows all equal `x`, the networks are the blocks of Corollary A.9, with the
  -- reads `E W_read`, the writes `W_write D` and `M = E D`
  have hrow : ∀ x : dIn → ℝ, x ᵥ* (θ.E * θ.D)
      + vanillaBlock σ (θ.E * θ.read 0) (θ.write 0 * θ.D) x
      = vanillaBlock σ (θ'.E * θ'.read 0) (θ'.write 0 * θ'.D) x := by
    intro x
    have h := congrFun (heq (Matrix.of fun _ => x)) (Classical.arbitrary T)
    rwa [eval_residual_row, eval_skipless_row] at h
  obtain ⟨S, hS'⟩ := hσ _ _ ⟨hθ.col_ne_zero, hθ.col_not_collinear, hθ.row_ne_zero⟩ _ _ _ hrow
  exact hS S hS'

/-- **Proposition 3.2 for ReLU:** for almost every choice of weights, a residual network of one
ReLU block equals no skipless network of one ReLU block of the same width (with its own model
dimension, embedding, read, write and readout). Scope of the paper: `d_in, d_out, d_hidden ≥ d ≥ 2`. -/
theorem ae_ne_skipless_oneBlock_relu [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∀ (d' : Type) [Fintype d']
      (θ' : Params (Arch.mlp (T := T) (d := d') relu id hid) dIn dOut),
      ∃ X : Matrix T dIn ℝ,
        eval (Arch.mlp relu id hid) 1 θ X ≠ eval (Arch.mlp relu id hid) 0 θ' X := by
  classical
  -- Corollary A.9 with `p = d_in`
  exact ae_ne_skipless_oneBlock_of (fun Wr Ww hnd M Wr' Ww' h =>
    exists_subProd_eq_neg_of_relu_absorb Wr Ww hnd M Wr' Ww' h) μ hd hdIn hdOut hhid

/-- **Proposition 3.2 for GELU.** -/
theorem ae_ne_skipless_oneBlock_gelu [Nonempty T]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∀ (d' : Type) [Fintype d']
      (θ' : Params (Arch.mlp (T := T) (d := d') gelu id hid) dIn dOut),
      ∃ X : Matrix T dIn ℝ,
        eval (Arch.mlp gelu id hid) 1 θ X ≠ eval (Arch.mlp gelu id hid) 0 θ' X := by
  classical
  -- Corollary A.9 with `p = d_in`
  exact ae_ne_skipless_oneBlock_of (fun Wr Ww hnd M Wr' Ww' h =>
    exists_subProd_eq_neg_of_gelu_absorb Wr Ww hnd M Wr' Ww' h) μ hd hdIn hdOut hhid

end OneBlock

end Skips
