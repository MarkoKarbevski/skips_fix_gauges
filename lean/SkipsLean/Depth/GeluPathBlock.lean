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

/-- **"Parameters that satisfy all conditions, in the case (0)", one GELU block:** for `d ≥ 2`, at
least `d` hidden units and every `κ > 0`, there are a read `W` and a write `V` that satisfy (R1)
for the write, (R2), (R3), (P1), and (P2) for `κ`. -/
theorem exists_geluPathBlock {q : Type*} [Fintype q] (hd : 2 ≤ Fintype.card d)
    (hq : Fintype.card d ≤ Fintype.card q) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (W : Matrix d q ℝ) (V : Matrix q d ℝ), GeluPathBlock W V κ := by
  sorry

end Skips
