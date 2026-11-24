import SkipsLean.Depth.CondP
import SkipsLean.Activations.MillsC

/-!
# One GELU block that satisfies all conditions of the case (0)

Paper (dimension paper): Appendix D.6, "Parameters that satisfy all conditions, in the case (0)":
"We choose the blocks from the last to the first. Let `D` and the blocks `ℓ + 1, …, L` be chosen,
regular and with […] (P1) and (P2) for GELU. This fixes `κ_ℓ` (Lemma D.14). We choose
`(W, V) = (W_read^ℓ, W_write^ℓ)`. Conditions that fail on a set of measure zero of pairs `(W, V)`.
(R1), (S1), (S2) and (P1) are of this kind […]. (R2): […]. (R3): […]. Conditions that hold on a
nonempty open set of pairs. […] (P2): take a row `α` with positive entries, any `V` with
`αV ≠ 0`, and `W° = ξ₀ᵀ α`. For `W°` the left sides of the first two inequalities of (P2) vanish
and `ξ₀c°_j = α_j > 0`, so these two inequalities hold for all `W = λ (W° + W')` with `λ > 0` and
`W'` small. For fixed small `W'`, the third holds for large `λ` […]. A nonempty open set minus a
set of measure zero is not empty."

Stated here: for every `κ > 0` there is a pair `(W, V)` that satisfies the conditions of one GELU
block, for one row (the paper's one token): (R1) for the write, `V` has rank `d`; (R2)
`GELU(nW) V ≠ 0` for every row `n` on the sphere `‖n‖² = d`; (R3) at some such `n`, a `v ⊥ n` with
`𝐃g(n) v ∈ ℝ g(n)` is `0`, where `g(n) = GELU(nW) V`; (P1); (P2) for `κ`.

The existence needs one pair only, and the Lean proof may take an explicit one, with the hidden
units `d ⊕ Fin m`: the columns of `W` are `λ (𝟙 + ε e_i)` (`i ∈ d`, `𝟙` the row of ones) and
`λ μ_j 𝟙`, the rows of `V` are `e_i` and `η 𝟙`, with `ξ₀ = 𝟙/√d`, `ε` small, `λ` large, then `η`
small.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **The conditions on one GELU block in the case (0),** for the read `W` (columns `c_j`), the
write `V` (rows `a_j`) and `κ`: (R1) for `V`, (R2), (R3), (P1), and (P2) for `κ`. -/
structure GeluPathBlock {q : Type*} [Fintype q] (W : Matrix d q ℝ) (V : Matrix q d ℝ) (κ : ℝ) :
    Prop where
  /-- (R1) for the write: `V` has rank `d`. -/
  rank_write : V.rank = Fintype.card d
  /-- (R2): `g(n) = GELU(nW) V ≠ 0` for every row `n` on the sphere `‖n‖² = d`. -/
  ne_zero : ∀ n : d → ℝ, n ⬝ᵥ n = (Fintype.card d : ℝ) →
    (fun j : q => gelu ((n ᵥ* W) j)) ᵥ* V ≠ 0
  /-- (R3): at some `n` on the sphere, a `v ⊥ n` with `𝐃g(n) v ∈ ℝ g(n)` is `0`. -/
  deriv : ∃ n : d → ℝ, n ⬝ᵥ n = (Fintype.card d : ℝ) ∧ ∀ v : d → ℝ, v ⬝ᵥ n = 0 →
    (∃ a : ℝ,
      fderiv ℝ (fun n' : d → ℝ => (fun j : q => gelu ((n' ᵥ* W) j)) ᵥ* V) n v
        = a • ((fun j : q => gelu ((n ᵥ* W) j)) ᵥ* V)) →
    v = 0
  /-- (P1): the columns of `W` are pairwise different. -/
  cols_ne : ∀ i j : q, i ≠ j → (fun a : d => W a i) ≠ fun a : d => W a j
  /-- (P1): no row of `V` vanishes. -/
  rows_ne : ∀ j : q, V j ≠ 0
  /-- (P1): `W V` is invertible. -/
  det_unit : IsUnit (W * V).det
  /-- (P2) for `κ`: a unit row `ξ₀` such that the three inequalities hold with every unit row `ξ'`
  orthogonal to `ξ₀`. -/
  p2 : ∃ ξ₀ : d → ℝ, ξ₀ ⬝ᵥ ξ₀ = 1 ∧
    ∀ ξ' : d → ℝ, ξ' ⬝ᵥ ξ' = 1 → ξ₀ ⬝ᵥ ξ' = 0 → PathP2 W V κ ξ₀ ξ'

/-- The read of the pair: `W i (inl i') = λ (1 + ε δ_{ii'})`, `W i (inr j) = λ (j + 1)`. -/
private def readGpb (l ε : ℝ) (m : ℕ) : Matrix d (d ⊕ Fin m) ℝ :=
  Matrix.of fun i k => Sum.elim (fun i' : d => l * (1 + if i = i' then ε else 0))
    (fun j : Fin m => l * (((j : ℕ) : ℝ) + 1)) k

/-- The write of the pair: the row `inl i'` is `e_{i'}`, the row `inr j` is `η 𝟙`. -/
private def writeGpb (η : ℝ) (m : ℕ) : Matrix (d ⊕ Fin m) d ℝ :=
  Matrix.of fun k i => Sum.elim (fun i' : d => if i' = i then (1 : ℝ) else 0) (fun _ : Fin m => η) k

/-- Helper: `(xW)_{inl i} = λ (∑_a x_a + ε x_i)`. -/
private theorem vecMul_read_inl_gpb (l ε : ℝ) (m : ℕ) (x : d → ℝ) (i : d) :
    (x ᵥ* readGpb l ε m) (Sum.inl i) = l * (∑ a, x a + ε * x i) := by
  simp only [readGpb, Matrix.vecMul, dotProduct, Matrix.of_apply, Sum.elim_inl]
  have h : ∀ a, x a * (l * (1 + if a = i then ε else 0))
      = l * x a + if a = i then l * ε * x a else 0 := fun a => by
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_add_distrib, Finset.sum_ite_eq',
    ← Finset.mul_sum]
  simp only [Finset.mem_univ, ite_true]
  ring

/-- Helper: `(xW)_{inr j} = λ (j + 1) ∑_a x_a`. -/
private theorem vecMul_read_inr_gpb (l ε : ℝ) (m : ℕ) (x : d → ℝ) (j : Fin m) :
    (x ᵥ* readGpb l ε m) (Sum.inr j) = l * (((j : ℕ) : ℝ) + 1) * ∑ a, x a := by
  simp only [readGpb, Matrix.vecMul, dotProduct, Matrix.of_apply, Sum.elim_inr]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- Helper: `(wV)_b = w_{inl b} + η ∑_j w_{inr j}`. -/
private theorem vecMul_write_gpb (η : ℝ) (m : ℕ) (w : d ⊕ Fin m → ℝ) (b : d) :
    (w ᵥ* writeGpb η m) b = w (Sum.inl b) + η * ∑ j, w (Sum.inr j) := by
  simp only [writeGpb, Matrix.vecMul, dotProduct, Matrix.of_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  rw [Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)

/-- Helper: `(x W V)_b = λ ((1 + η S) ∑_a x_a + ε x_b)`, `S = ∑_j (j + 1)`. -/
private theorem vecMul_mul_gpb (l ε η : ℝ) (m : ℕ) (x : d → ℝ) (b : d) :
    (x ᵥ* (readGpb l ε m * writeGpb η m)) b
      = l * ((1 + η * ∑ j : Fin m, (((j : ℕ) : ℝ) + 1)) * ∑ a, x a + ε * x b) := by
  rw [← Matrix.vecMul_vecMul, vecMul_write_gpb, vecMul_read_inl_gpb]
  simp only [vecMul_read_inr_gpb]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

omit [DecidableEq d] in
/-- Helper: the derivative of `g(n) = GELU(nW) V` along `v`. -/
private theorem fderiv_gelu_vecMul_gpb {q : Type*} [Fintype q] (W : Matrix d q ℝ)
    (V : Matrix q d ℝ) (n v : d → ℝ) :
    fderiv ℝ (fun n' : d → ℝ => (fun j : q => gelu ((n' ᵥ* W) j)) ᵥ* V) n v
      = (fun k => (gaussCdf ((n ᵥ* W) k) + (n ᵥ* W) k * gaussPdf ((n ᵥ* W) k)) * (v ᵥ* W) k)
        ᵥ* V := by
  let L : (d → ℝ) →L[ℝ] (q → ℝ) := LinearMap.toContinuousLinearMap (Matrix.vecMulLinear W)
  let M : (q → ℝ) →L[ℝ] (d → ℝ) := LinearMap.toContinuousLinearMap (Matrix.vecMulLinear V)
  let D : (q → ℝ) →L[ℝ] (q → ℝ) := ContinuousLinearMap.pi fun k =>
    (gaussCdf ((n ᵥ* W) k) + (n ᵥ* W) k * gaussPdf ((n ᵥ* W) k)) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : q => ℝ) k
  have hΦ : HasFDerivAt (fun y : q → ℝ => fun k => gelu (y k)) D (n ᵥ* W) := by
    refine hasFDerivAt_pi.2 fun k => ?_
    have h := (hasDerivAt_gelu ((n ᵥ* W) k)).comp_hasFDerivAt (n ᵥ* W)
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : q => ℝ) k (n ᵥ* W))
    exact h
  have hg : HasFDerivAt (fun n' : d → ℝ => (fun j : q => gelu ((n' ᵥ* W) j)) ᵥ* V)
      (M.comp (D.comp L)) n := by
    have h1 := M.hasFDerivAt.comp n (hΦ.comp n L.hasFDerivAt)
    exact h1
  rw [hg.fderiv]
  rfl

/-- Helper (R1): the write has rank `d` (the rows `inl i` form the identity, `P V = 1`). -/
private theorem rank_write_gpb (η : ℝ) (m : ℕ) :
    (writeGpb (d := d) η m).rank = Fintype.card d := by
  -- the left inverse `P` picks the rows `inl i`
  let P : Matrix d (d ⊕ Fin m) ℝ :=
    Matrix.of fun i k => Sum.elim (fun i' : d => if i = i' then (1 : ℝ) else 0)
      (fun _ : Fin m => 0) k
  have hP : P * writeGpb (d := d) η m = 1 := by
    ext i i'
    simp [P, writeGpb, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  apply le_antisymm (Matrix.rank_le_card_width _)
  calc Fintype.card d = (1 : Matrix d d ℝ).rank := Matrix.rank_one.symm
    _ = (P * writeGpb (d := d) η m).rank := by rw [hP]
    _ ≤ (writeGpb η m).rank := Matrix.rank_mul_le_right _ _

omit [Fintype d] in
/-- Helper (P1): the columns `λ (𝟙 + ε e_i)` and `λ (j + 1) 𝟙` are pairwise different. -/
private theorem cols_ne_gpb [Nontrivial d] {l ε : ℝ} (m : ℕ) (hl : l ≠ 0) (hε : ε ≠ 0) :
    ∀ k k' : d ⊕ Fin m, k ≠ k' →
      (fun a : d => readGpb l ε m a k) ≠ fun a : d => readGpb l ε m a k' := by
  intro k k' hkk' h
  rcases k with i | j <;> rcases k' with i' | j'
  · -- `inl i`, `inl i'`: the entry `i`
    have hii' : i ≠ i' := fun e => hkk' (by rw [e])
    have h1 := congrFun h i
    simp only [readGpb, Matrix.of_apply, Sum.elim_inl, hii', ↓reduceIte, add_zero] at h1
    exact (mul_ne_zero hl hε) (by linear_combination h1)
  · -- `inl i`, `inr j'`: the entries `i` and `i' ≠ i`
    obtain ⟨i', hi'⟩ := exists_ne i
    have h1 := congrFun h i
    have h2 := congrFun h i'
    simp only [readGpb, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, hi', ↓reduceIte,
      add_zero] at h1 h2
    exact (mul_ne_zero hl hε) (by linear_combination h1 - h2)
  · obtain ⟨i, hi'⟩ := exists_ne i'
    have h1 := congrFun h i'
    have h2 := congrFun h i
    simp only [readGpb, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, hi', ↓reduceIte,
      add_zero] at h1 h2
    exact (mul_ne_zero hl hε) (by linear_combination h2 - h1)
  · -- `inr j`, `inr j'`: `λ (j + 1) = λ (j' + 1)`
    have hjj' : (((j : ℕ) : ℝ)) ≠ ((j' : ℕ) : ℝ) :=
      Nat.cast_injective.ne (Fin.val_injective.ne fun e => hkk' (by rw [e]))
    obtain ⟨a⟩ := (inferInstance : Nonempty d)
    have h1 := congrFun h a
    simp only [readGpb, Matrix.of_apply, Sum.elim_inr] at h1
    have h2 : l * ((((j : ℕ) : ℝ)) - ((j' : ℕ) : ℝ)) = 0 := by linear_combination h1
    exact hjj' (sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hl))

omit [Fintype d] in
/-- Helper (P1): no row of the write vanishes. -/
private theorem rows_ne_gpb [Nonempty d] {η : ℝ} (m : ℕ) (hη : η ≠ 0) :
    ∀ k : d ⊕ Fin m, writeGpb η m k ≠ 0 := by
  intro k h
  rcases k with i | j
  · have h1 := congrFun h i
    simp [writeGpb] at h1
  · obtain ⟨a⟩ := (inferInstance : Nonempty d)
    have h1 := congrFun h a
    simp only [writeGpb, Matrix.of_apply, Sum.elim_inr, Pi.zero_apply] at h1
    exact hη h1

/-- Helper (P1): `W V = λ ((1 + ηS) J + ε I)` is invertible: `x W V = 0` gives `∑_a x_a = 0`
(the sum of the entries), then `ε x = 0`. -/
private theorem det_unit_gpb {l ε η : ℝ} (m : ℕ) (hl : 0 < l) (hε : 0 < ε) (hη : 0 ≤ η) :
    IsUnit (readGpb (d := d) l ε m * writeGpb η m).det := by
  rw [isUnit_iff_ne_zero, ne_eq, ← Matrix.exists_vecMul_eq_zero_iff]
  rintro ⟨x, hx, h0⟩
  set c := 1 + η * ∑ j : Fin m, (((j : ℕ) : ℝ) + 1) with hc
  have hc0 : 0 ≤ c - 1 := by
    rw [hc, add_sub_cancel_left]
    exact mul_nonneg hη (Finset.sum_nonneg fun j _ => by positivity)
  have hb : ∀ b, l * (c * ∑ a, x a + ε * x b) = 0 := fun b => by
    rw [← vecMul_mul_gpb]
    exact congrFun h0 b
  -- the sum: `λ ((c D + ε) ∑_a x_a) = 0`
  have hsum : l * ((c * (Fintype.card d : ℝ) + ε) * ∑ a, x a) = 0 := by
    have h := Finset.sum_eq_zero (s := Finset.univ) fun b (_ : b ∈ Finset.univ) => hb b
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at h
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at h
    linear_combination h
  have hD : (0 : ℝ) ≤ Fintype.card d := Nat.cast_nonneg _
  have hs : ∑ a, x a = 0 := by
    rcases mul_eq_zero.1 hsum with h | h
    · exact absurd h hl.ne'
    · exact (mul_eq_zero.1 h).resolve_left (by nlinarith)
  apply hx
  funext b
  have h := hb b
  rw [hs, mul_zero, zero_add] at h
  simpa [hl.ne', hε.ne'] using h

/-- Helper: `|x| ≤ (x² + 1)/2`. -/
private theorem abs_le_gpb (x : ℝ) : |x| ≤ (x * x + 1) / 2 := by
  nlinarith [sq_nonneg (|x| - 1), abs_mul_abs_self x]

/-- Helper: `|GELU z| ≤ |z|` (`0 < Φ < 1`). -/
private theorem abs_gelu_le_gpb (z : ℝ) : |gelu z| ≤ |z| := by
  rw [gelu, abs_mul, abs_of_pos (gaussCdf_pos z)]
  exact mul_le_of_le_one_right (abs_nonneg z) (gaussCdf_lt_one z).le

/-- Helper: `|GELU z| ≥ z₀ Φ(−z₁)` for `z₀ ≤ |z| ≤ z₁` (`Φ` is increasing). -/
private theorem le_abs_gelu_gpb {z z₀ z₁ : ℝ} (h1 : z₀ ≤ |z|) (h2 : |z| ≤ z₁) :
    z₀ * gaussCdf (-z₁) ≤ |gelu z| := by
  rw [gelu, abs_mul, abs_of_pos (gaussCdf_pos z)]
  have hz : -z₁ ≤ z := by linarith [neg_abs_le z]
  exact mul_le_mul h1 (strictMono_gaussCdf.monotone hz) (gaussCdf_pos _).le (abs_nonneg z)

/-- Helper (R2): `g(n) ≠ 0` on the sphere: some `z_b = λ (s + ε n_b)` (`s = ∑_a n_a`) has
`λε/2 ≤ |z_b| ≤ 2λD`, so `|GELU z_b| ≥ (λε/2) Φ(−2λD)`, and the term `η ∑_j GELU(λ (j + 1) s)` is
at most `η λ S D` in absolute value. -/
private theorem ne_zero_gpb [Nonempty d] {l ε η : ℝ} (m : ℕ) (hl : 0 < l) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hη : 0 ≤ η)
    (hηm : η * (l * (∑ j : Fin m, (((j : ℕ) : ℝ) + 1)) * Fintype.card d)
      < l * ε / 2 * gaussCdf (-(2 * l * Fintype.card d)))
    (n : d → ℝ) (hn : n ⬝ᵥ n = (Fintype.card d : ℝ)) :
    (fun k => gelu ((n ᵥ* readGpb l ε m) k)) ᵥ* writeGpb η m ≠ 0 := by
  have hD1 : (1 : ℝ) ≤ Fintype.card d := by exact_mod_cast Fintype.card_pos
  obtain ⟨s, hs⟩ : ∃ s, s = ∑ a, n a := ⟨_, rfl⟩
  -- some `|n_i| ≥ 1`, otherwise `n ⬝ n < D`
  obtain ⟨i, hi⟩ : ∃ i, 1 ≤ |n i| := by
    by_contra h
    push Not at h
    have hlt : n ⬝ᵥ n < ∑ _i : d, (1 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => by
        have := (sq_lt_one_iff_abs_lt_one (n i)).2 (h i)
        nlinarith
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hlt
    linarith
  -- `|s| ≤ D` and `|n_b| ≤ D`
  have hsD : |s| ≤ Fintype.card d := by
    rw [hs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ a, |n a| ≤ ∑ a, (n a * n a + 1) / 2 :=
          Finset.sum_le_sum fun a _ => abs_le_gpb (n a)
      _ = (n ⬝ᵥ n + Fintype.card d) / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib]
          simp [dotProduct]
      _ = Fintype.card d := by rw [hn]; ring
  have hnD : ∀ b, |n b| ≤ Fintype.card d := fun b => by
    have h1 : n b * n b ≤ n ⬝ᵥ n :=
      Finset.single_le_sum (f := fun a => n a * n a) (fun a _ => mul_self_nonneg (n a))
        (Finset.mem_univ b)
    linarith [abs_le_gpb (n b)]
  -- some `|s + ε n_b| ≥ ε/2`: otherwise, summing, `|s| < ε/2`, and then `|s + ε n_i| > ε/2`
  obtain ⟨b, hb⟩ : ∃ b, ε / 2 ≤ |s + ε * n b| := by
    by_contra h
    push Not at h
    have hsum : |(Fintype.card d + ε) * s| < Fintype.card d * (ε / 2) := by
      have e : (Fintype.card d + ε) * s = ∑ a, (s + ε * n a) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hs]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
      rw [e]
      refine lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _) ?_
      have h' := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        fun a (_ : a ∈ Finset.univ) => h a
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h'
    have hs2 : |s| < ε / 2 := by
      rw [abs_mul, abs_of_pos (by linarith)] at hsum
      nlinarith [abs_nonneg s]
    have h3 := h i
    have h4 : ε ≤ |ε * n i| := by
      rw [abs_mul, abs_of_pos hε]
      nlinarith
    rw [abs_lt] at h3 hs2
    have h5 : |ε * n i| < ε := abs_lt.2 ⟨by linarith, by linarith⟩
    linarith
  intro h0
  have hc := congrFun h0 b
  simp only [vecMul_write_gpb, vecMul_read_inl_gpb, vecMul_read_inr_gpb, ← hs,
    Pi.zero_apply] at hc
  -- the term `inl b`: `|GELU z_b| ≥ (λε/2) Φ(−2λD)`
  have h1 : l * ε / 2 * gaussCdf (-(2 * l * Fintype.card d)) ≤ |gelu (l * (s + ε * n b))| := by
    have h2 : |s + ε * n b| ≤ 2 * Fintype.card d := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hε]
      nlinarith [hnD b, abs_nonneg (n b)]
    apply le_abs_gelu_gpb
    · rw [abs_mul, abs_of_pos hl]
      nlinarith
    · rw [abs_mul, abs_of_pos hl]
      nlinarith
  -- the terms `inr j`: at most `η λ S D`
  have h2 : |η * ∑ j : Fin m, gelu (l * (((j : ℕ) : ℝ) + 1) * s)|
      ≤ η * (l * (∑ j : Fin m, (((j : ℕ) : ℝ) + 1)) * Fintype.card d) := by
    rw [abs_mul, abs_of_nonneg hη]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) hη
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => (abs_gelu_le_gpb _).trans ?_
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hsD (by positivity)
  rw [add_eq_zero_iff_eq_neg] at hc
  rw [hc, abs_neg] at h1
  linarith

/-- Helper (R3) at `n₀ = 𝟙`: for `v ⊥ 𝟙`, `𝐃g(𝟙) v = GELU'(z) λ ε v`, and `g(𝟙)` is a positive
multiple of `𝟙`. -/
private theorem deriv_gpb [Nonempty d] {l ε η : ℝ} (m : ℕ) (hl : 0 < l) (hε : 0 < ε)
    (hη : 0 ≤ η) :
    ∃ n : d → ℝ, n ⬝ᵥ n = (Fintype.card d : ℝ) ∧ ∀ v : d → ℝ, v ⬝ᵥ n = 0 →
      (∃ a : ℝ,
        fderiv ℝ (fun n' : d → ℝ =>
            (fun j => gelu ((n' ᵥ* readGpb l ε m) j)) ᵥ* writeGpb η m) n v
          = a • ((fun j => gelu ((n ᵥ* readGpb l ε m) j)) ᵥ* writeGpb η m)) →
      v = 0 := by
  refine ⟨fun _ => 1, by simp [dotProduct], fun v hv ⟨a, ha⟩ => ?_⟩
  -- `∑_i v_i = 0`
  have hs : ∑ i, v i = 0 := by simpa [dotProduct] using hv
  rw [fderiv_gelu_vecMul_gpb] at ha
  obtain ⟨z, hz⟩ : ∃ z, z = l * (∑ _a : d, (1 : ℝ) + ε * 1) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = gelu z
      + η * ∑ j : Fin m, gelu (l * (((j : ℕ) : ℝ) + 1) * ∑ _a : d, (1 : ℝ)) := ⟨_, rfl⟩
  -- coordinate `i`: `GELU'(z) λ ε v_i = a G`
  have hi : ∀ i, (gaussCdf z + z * gaussPdf z) * (l * (ε * v i)) = a * G := by
    intro i
    have h := congrFun ha i
    simp only [vecMul_write_gpb, vecMul_read_inl_gpb, vecMul_read_inr_gpb, hs, mul_zero,
      zero_add, Finset.sum_const_zero, add_zero, Pi.smul_apply, smul_eq_mul, ← hz,
      ← hG] at h
    exact h
  have hz0 : 0 < z := by
    rw [hz]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos
    positivity
  -- `G > 0`
  have hG0 : 0 < G := by
    rw [hG]
    refine add_pos_of_pos_of_nonneg (mul_pos hz0 (gaussCdf_pos z))
      (mul_nonneg hη (Finset.sum_nonneg fun j _ => ?_))
    exact mul_nonneg (by positivity) (gaussCdf_pos _).le
  -- summing over `i`: `0 = a D G`, so `a = 0`
  have hsum : (gaussCdf z + z * gaussPdf z) * (l * ε) * ∑ i, v i
      = a * ∑ _i : d, G := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← hi i]; ring
  rw [hs, mul_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have ha0 : a = 0 := by
    have hc : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos
    rcases mul_eq_zero.1 hsum.symm with h | h
    · exact h
    · exact absurd h (mul_pos hc hG0).ne'
  -- then `GELU'(z) λ ε v_i = 0` with `GELU'(z) λ ε ≠ 0`
  funext i
  have h := hi i
  rw [ha0, zero_mul] at h
  have hc : (gaussCdf z + z * gaussPdf z) * (l * ε) ≠ 0 :=
    mul_ne_zero (add_pos (gaussCdf_pos z) (mul_pos hz0 (gaussPdf_pos z))).ne'
      (mul_pos hl hε).ne'
  have h' : (gaussCdf z + z * gaussPdf z) * (l * ε) * v i = 0 := by
    rw [← h]; ring
  simpa [hc] using h'

/-- Helper (P2) with `ξ₀ = 𝟙/√D`: for `ξ' ⊥ ξ₀` (so `∑_a ξ'_a = 0`), `ξ'W = (λ ε ξ', 0)`,
`ξ' W V = λ ε ξ'`, every `ξ₀ c_k ≥ λ √D` and every entry of `ξ₀ W V` is at least `λ √D`, so
`‖ξ₀ W V‖ ≥ λ D`; the left side of the third inequality is at most `(D + m) √D`. -/
private theorem p2_gpb (hd : 2 ≤ Fintype.card d) {l ε η κ : ℝ} (m : ℕ) (hκ : 0 < κ)
    (hl : 1 ≤ l) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεκ : ε ≤ κ / 2) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hlκ : (Fintype.card d : ℝ) + m < κ * l / 8) :
    ∃ ξ₀ : d → ℝ, ξ₀ ⬝ᵥ ξ₀ = 1 ∧ ∀ ξ' : d → ℝ, ξ' ⬝ᵥ ξ' = 1 → ξ₀ ⬝ᵥ ξ' = 0 →
      PathP2 (readGpb l ε m) (writeGpb η m) κ ξ₀ ξ' := by
  have hD2 : (2 : ℝ) ≤ Fintype.card d := by exact_mod_cast hd
  have hl0 : 0 < l := by linarith
  -- `r = √D`, `r r = D`, `r > 1`
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (Fintype.card d) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.2 (by linarith)
  have hrr : r * r = Fintype.card d := by rw [hr]; exact Real.mul_self_sqrt (by linarith)
  have hr1 : 1 < r := by nlinarith
  have hS : 0 ≤ η * ∑ j : Fin m, (((j : ℕ) : ℝ) + 1) :=
    mul_nonneg hη (Finset.sum_nonneg fun j _ => by positivity)
  -- `ξ₀ = r⁻¹ 𝟙`: `∑_a ξ₀_a = r`, `ξ₀ ⬝ ξ₀ = 1`
  have hsum0 : ∑ _a : d, r⁻¹ = r := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hrr]
    field_simp
  have hξ : (fun _ : d => r⁻¹) ⬝ᵥ (fun _ : d => r⁻¹) = 1 := by
    simp only [dotProduct, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hrr]
    field_simp
  refine ⟨fun _ => r⁻¹, hξ, fun ξ' h1 h0 => ?_⟩
  -- `∑_a ξ'_a = 0` and `|ξ'_a| ≤ 1`
  have hs' : ∑ a, ξ' a = 0 := by
    have h : r⁻¹ * ∑ a, ξ' a = 0 := by
      rw [Finset.mul_sum]
      simpa [dotProduct] using h0
    exact (mul_eq_zero.1 h).resolve_left (inv_ne_zero hr0.ne')
  have hξ'1 : ∀ a, |ξ' a| ≤ 1 := fun a => by
    have h : ξ' a * ξ' a ≤ ξ' ⬝ᵥ ξ' :=
      Finset.single_le_sum (f := fun b => ξ' b * ξ' b) (fun b _ => mul_self_nonneg (ξ' b))
        (Finset.mem_univ a)
    rw [h1] at h
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  -- `‖ξ₀ W V‖ ≥ λ D`: every entry is at least `λ r`
  have hN : l * Fintype.card d ≤ Real.sqrt (((fun _ : d => r⁻¹) ᵥ* (readGpb l ε m *
      writeGpb η m)) ⬝ᵥ ((fun _ : d => r⁻¹) ᵥ* (readGpb l ε m * writeGpb η m))) := by
    have hb : ∀ b, l * r ≤ ((fun _ : d => r⁻¹) ᵥ* (readGpb l ε m * writeGpb η m)) b :=
      fun b => by
        rw [vecMul_mul_gpb, hsum0]
        have h2 : 0 ≤ ε * r⁻¹ := by positivity
        have h3 : r ≤ (1 + η * ∑ j : Fin m, (((j : ℕ) : ℝ) + 1)) * r := by nlinarith
        exact mul_le_mul_of_nonneg_left (by linarith) hl0.le
    refine (Real.le_sqrt (by positivity) ?_).2 ?_
    · exact Finset.sum_nonneg fun b _ => mul_self_nonneg _
    calc (l * Fintype.card d) ^ 2 = ∑ _b : d, (l * r) * (l * r) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          linear_combination (-((Fintype.card d : ℝ) * l ^ 2)) * hrr
      _ ≤ _ := Finset.sum_le_sum fun b _ =>
          mul_self_le_mul_self (by positivity) (hb b)
  refine ⟨fun k => ?_, ?_, ?_⟩
  · -- `|ξ' c_k| < ξ₀ c_k`
    rcases k with i | j
    · simp only [vecMul_read_inl_gpb, hs', hsum0, zero_add]
      rw [abs_mul, abs_of_pos hl0, abs_mul, abs_of_pos hε]
      have h2 : ε * |ξ' i| ≤ 1 := by nlinarith [hξ'1 i, abs_nonneg (ξ' i)]
      have h3 : 0 ≤ ε * r⁻¹ := by positivity
      exact mul_lt_mul_of_pos_left (by linarith) hl0
    · simp only [vecMul_read_inr_gpb, hs', hsum0, mul_zero, abs_zero]
      positivity
  · -- `ξ' W V = λ ε ξ'`, of norm `λ ε ≤ λ κ/2 < κ λ ≤ (κ/2) λ D`
    have he : ξ' ᵥ* (readGpb l ε m * writeGpb η m) = (l * ε) • ξ' := by
      funext b
      rw [vecMul_mul_gpb, hs', Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, dotProduct_smul, smul_dotProduct, h1, smul_eq_mul, smul_eq_mul, mul_one,
      Real.sqrt_mul_self (by positivity)]
    have h2 : κ / 2 * (l * Fintype.card d) ≤ κ / 2 * Real.sqrt _ :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    have h3 : κ * l ≤ κ / 2 * (l * Fintype.card d) := by nlinarith
    have h4 : l * ε ≤ l * (κ / 2) := mul_le_mul_of_nonneg_left hεκ hl0.le
    nlinarith
  · -- the third: every `e^{…} ≤ 1` and `‖V_k‖ ≤ r`
    have hV : ∀ k, Real.sqrt (writeGpb η m k ⬝ᵥ writeGpb η m k) ≤ r := fun k => by
      rw [hr]
      apply Real.sqrt_le_sqrt
      calc writeGpb η m k ⬝ᵥ writeGpb η m k ≤ ∑ _b : d, (1 : ℝ) :=
            Finset.sum_le_sum fun b _ => by
              have h0 : 0 ≤ writeGpb η m k b ∧ writeGpb η m k b ≤ 1 := by
                rcases k with i | j
                · simp only [writeGpb, Matrix.of_apply, Sum.elim_inl]
                  split_ifs <;> norm_num
                · exact ⟨hη, hη1⟩
              nlinarith [h0.1, h0.2]
        _ = Fintype.card d := by simp
    have hL : ∑ k : d ⊕ Fin m, Real.exp (-((Fintype.card d : ℝ) *
        (((fun _ : d => r⁻¹) ᵥ* readGpb l ε m) k) ^ 2 / 2)) *
          Real.sqrt (writeGpb η m k ⬝ᵥ writeGpb η m k)
        ≤ ((Fintype.card d : ℝ) + m) * r := by
      calc _ ≤ ∑ _k : d ⊕ Fin m, r := Finset.sum_le_sum fun k _ => by
              have he : Real.exp (-((Fintype.card d : ℝ) *
                  (((fun _ : d => r⁻¹) ᵥ* readGpb l ε m) k) ^ 2 / 2)) ≤ 1 := by
                rw [Real.exp_le_one_iff, neg_nonpos]
                positivity
              exact (mul_le_of_le_one_left (Real.sqrt_nonneg _) he).trans (hV k)
        _ = ((Fintype.card d : ℝ) + m) * r := by
              simp [Fintype.card_sum]
    have h2 : κ * r / 8 * (l * Fintype.card d) ≤ κ * r / 8 * Real.sqrt _ :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    have h3 : κ * l / 8 * r ≤ κ * r / 8 * (l * Fintype.card d) := by
      have h5 : 0 ≤ κ * r * l / 8 := by positivity
      have h6 := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Fintype.card d by linarith) h5
      linarith
    have h4 : ((Fintype.card d : ℝ) + m) * r < κ * l / 8 * r :=
      mul_lt_mul_of_pos_right hlκ hr0
    rw [← hr]
    linarith

/-- **"Parameters that satisfy all conditions, in the case (0)", one GELU block:** for `d ≥ 2`, at
least `d` hidden units and every `κ > 0`, there are a read `W` and a write `V` that satisfy (R1)
for the write, (R2), (R3), (P1), and (P2) for `κ`. -/
theorem exists_geluPathBlock {q : Type*} [Fintype q] (hd : 2 ≤ Fintype.card d)
    (hq : Fintype.card d ≤ Fintype.card q) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (W : Matrix d q ℝ) (V : Matrix q d ℝ), GeluPathBlock W V κ := by
  sorry

end Skips
