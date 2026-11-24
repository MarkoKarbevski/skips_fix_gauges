import SkipsLean.Absorb.GatedBiasesCells

/-!
# Gated blocks with biases: one hyperplane at a time, and the count of Lemma C.8

Paper (absorb paper), Appendix C.2, proof of Lemma C.8 (Gated blocks with biases), after the
expansion along rays: "One hyperplane at a time. Near a point of `H` that lies on no other
hyperplane, the terms of the other hyperplanes are smooth. […] The terms of `H` are then `x Δ_H`,
with `Δ_H = G_− − ν a_− = G_+ + ν a_+`, and the second identity becomes `M = ∑_H Δ_H + Z`. As
`g = ±η ν` on side `±`, `G_± ± ν a_±` is the sum of the matrices `Δ_j` over the units of `B_{θ′}`
on side `±`, minus the same sum over the units of `B_θ`. […] So `A_+ + A_− = 0`.
Counting. Orient the hyperplane `H_i` of unit `i` of `B_θ` so that unit `i` lies on side `+`; no
other unit of `B_θ` lies on `H_i`. Let `J^±` be the sets of units of `B_{θ′}` on side `±` of `H_i`.
If both were empty, `A_+ + A_−` would be `−η_i v_i ŵ_i`, where `g_i = η_i ν`, which does not
vanish; so `H_i` carries `|J^+| + |J^−| − 1 ≥ 0` extra units. If `J^+` is empty, `Δ_{H_i} = −Δ_i`.
Otherwise `Δ_{H_i}` is the sum of the `Δ_j` over `J^−`, at most `|J^−| ≤ |J^+| + |J^−| − 1`
matrices of rank one. A hyperplane of no unit of `B_θ` carries `|J^+| + |J^−|` units of `B_{θ′}`,
with `J^±` defined in the same way, and `Δ_H` is a sum of at most that many matrices of rank one.
Each unit of `B_{θ′}` with gate read `0` adds one matrix of rank one to `Z`, and `B_θ` has no such
unit. With `S` the units `i` for which `J^+` is empty, `M + ∑_{i∈S} Δ_i` is therefore a sum of at
most `n` matrices of rank one."

Here this part of the proof is stated from the two identities of `Absorb/GatedBiasesCells.lean`
(`M + Λ_θ(x) = Λ_{θ′}(x)` and `Q_θ(x, ·) = Q_{θ′}(x, ·)` at every `x` off the hyperplanes). Two
inputs on the two sides of the hyperplane of a unit `i`, close to a point of it that lies on no
other hyperplane, give the two facts of "One hyperplane at a time": the sums of the `Δ` over the
units on the two sides agree, and the units of `B_{θ′}` on the hyperplane carry `v_i ŵ_i ≠ 0`.

"`M + ∑_{i∈S} Δ_i` is a sum of at most `n` matrices of rank one", with `n` the number of units
that `B_{θ′}` has more than `B_θ`, is stated as: its rank plus the number of units of `B_θ` is at
most the number of units of `B_{θ′}` (so `B_{θ′}` has at least as many units as `B_θ`).
-/

namespace Skips

open Matrix

variable {p q m m' : Type*} [Fintype p] [Fintype q] [Fintype m] [Fintype m']

omit [Fintype m] in
/-- `(x W)_k = x ⬝ᵥ` (column `k` of `W`). -/
private theorem vecMul_apply_gbn (x : p → ℝ) (W : Matrix p m ℝ)
    (k : m) : (x ᵥ* W) k = x ⬝ᵥ Wᵀ k := rfl

/-- **A row off finitely many hyperplanes** (`exists_dotProduct_eq_zero_and_ne_zero` with
`c = 0`). -/
private theorem exists_forall_dotProduct_ne_zero_gbn {n ι : Type*} [Fintype n] [Finite ι]
    (u : ι → n → ℝ) (hu : ∀ k, u k ≠ 0) : ∃ x : n → ℝ, ∀ k, x ⬝ᵥ u k ≠ 0 := by
  obtain ⟨x, -, hx⟩ := exists_dotProduct_eq_zero_and_ne_zero (0 : n → ℝ) u
    (fun k r => by rw [smul_zero]; exact hu k)
  exact ⟨x, hx⟩

open Filter Topology in
/-- Near `s = 0`, `α_k + s β_k` keeps the sign of `α_k`, for every `k` with `α_k ≠ 0`. -/
private theorem eventually_sign_gbn {ι : Type*} [Finite ι] (α β : ι → ℝ) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ k, α k ≠ 0 → 0 < α k * (α k + s * β k) := by
  rw [Filter.eventually_all]
  intro k
  by_cases hk : α k = 0
  · exact Filter.Eventually.of_forall fun _ h => absurd hk h
  · have hc : Continuous fun s : ℝ => α k * (α k + s * β k) := by fun_prop
    have h0 : 0 < α k * (α k + 0 * β k) := by
      rw [zero_mul, add_zero]; exact mul_self_pos.2 hk
    exact ((hc.tendsto 0).eventually (lt_mem_nhds h0)).mono fun s hs _ => hs

open Filter Topology in
/-- A property of all small `s` holds at some `s > 0` and at `-s`. -/
private theorem exists_pos_and_neg_gbn {P : ℝ → Prop} (h : ∀ᶠ s in 𝓝 (0 : ℝ), P s) :
    ∃ s : ℝ, 0 < s ∧ P s ∧ P (-s) := by
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨ε / 2, by positivity, hP ?_, hP ?_⟩
  · rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
  · rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)]; linarith

/-- `g ⬝ᵥ g > 0` for `g ≠ 0`. -/
private theorem dotProduct_self_pos_gbn {n : Type*} [Fintype n] {g : n → ℝ} (hg : g ≠ 0) :
    0 < g ⬝ᵥ g :=
  lt_of_le_of_ne (Finset.sum_nonneg fun a _ => mul_self_nonneg (g a))
    (Ne.symm (dotProduct_self_eq_zero.not.2 hg))

/-- **Two inputs across the hyperplane of unit `i`** (Step 1): `x_± = x₀ ± s g_i`, with `x₀` on
the hyperplane of `i` and off those of the other units of the first block and of the units of the
second block whose gate read is not a multiple of `g_i`. Unit `i` is open at `x_+` and closed at
`x_−`; every other unit of the first block, and every unit of the second block whose gate read is
not a multiple of `g_i`, is off its hyperplane at both and has the same gate at both. -/
private theorem exists_two_sides_gbn (Wg : Matrix p m ℝ) (Wg' : Matrix p m' ℝ) (hg : ∀ j, Wgᵀ j ≠ 0)
    (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, Wgᵀ i ≠ r • Wgᵀ j) (i : m) :
    ∃ xp xm : p → ℝ, (∀ k, (xp ᵥ* Wg) k ≠ 0) ∧ (∀ k, (xm ᵥ* Wg) k ≠ 0) ∧
      0 < (xp ᵥ* Wg) i ∧ (xm ᵥ* Wg) i < 0 ∧
      (∀ k, k ≠ i → (0 < (xp ᵥ* Wg) k ↔ 0 < (xm ᵥ* Wg) k)) ∧
      (∀ j, (∀ r : ℝ, Wg'ᵀ j ≠ r • Wgᵀ i) →
        (xp ᵥ* Wg') j ≠ 0 ∧ (xm ᵥ* Wg') j ≠ 0 ∧ (0 < (xp ᵥ* Wg') j ↔ 0 < (xm ᵥ* Wg') j)) := by
  -- `x₀` on the hyperplane of `i`, off the others that differ from it
  obtain ⟨x₀, h0, hne⟩ := exists_dotProduct_eq_zero_and_ne_zero (Wgᵀ i)
    (Sum.elim (fun k : {k : m // k ≠ i} => Wgᵀ k.1)
      (fun j : {j : m' // ∀ r : ℝ, Wg'ᵀ j ≠ r • Wgᵀ i} => Wg'ᵀ j.1))
    (by rintro (⟨k, hk⟩ | ⟨j, hj⟩) r; exacts [hcol k i hk r, hj r])
  -- for small `s > 0`, `x₀ ± s g_i` keeps the signs of the units off the hyperplane
  obtain ⟨s, hs, hP, hM⟩ := exists_pos_and_neg_gbn
    ((eventually_sign_gbn (fun k => x₀ ⬝ᵥ Wgᵀ k) (fun k => Wgᵀ i ⬝ᵥ Wgᵀ k)).and
      (eventually_sign_gbn (fun j => x₀ ⬝ᵥ Wg'ᵀ j) (fun j => Wgᵀ i ⬝ᵥ Wg'ᵀ j)))
  have hgg := dotProduct_self_pos_gbn (hg i)
  have hval : ∀ (t : ℝ) (w : p → ℝ), (x₀ + t • Wgᵀ i) ⬝ᵥ w = x₀ ⬝ᵥ w + t * (Wgᵀ i ⬝ᵥ w) :=
    fun t w => by rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hk0 : ∀ k, k ≠ i → x₀ ⬝ᵥ Wgᵀ k ≠ 0 := fun k hk => hne (Sum.inl ⟨k, hk⟩)
  have hj0 : ∀ j, (∀ r : ℝ, Wg'ᵀ j ≠ r • Wgᵀ i) → x₀ ⬝ᵥ Wg'ᵀ j ≠ 0 :=
    fun j hj => hne (Sum.inr ⟨j, hj⟩)
  have hpi : 0 < ((x₀ + s • Wgᵀ i) ᵥ* Wg) i := by
    rw [vecMul_apply_gbn, hval, h0, zero_add]; exact mul_pos hs hgg
  have hmi : ((x₀ + (-s) • Wgᵀ i) ᵥ* Wg) i < 0 := by
    rw [vecMul_apply_gbn, hval, h0, zero_add]; nlinarith
  refine ⟨x₀ + s • Wgᵀ i, x₀ + (-s) • Wgᵀ i, fun k => ?_, fun k => ?_, hpi, hmi,
    fun k hk => ?_, fun j hj => ?_⟩
  · rcases eq_or_ne k i with rfl | hk
    · exact hpi.ne'
    · rw [vecMul_apply_gbn, hval]; exact right_ne_zero_of_mul (hP.1 k (hk0 k hk)).ne'
  · rcases eq_or_ne k i with rfl | hk
    · exact hmi.ne
    · rw [vecMul_apply_gbn, hval]; exact right_ne_zero_of_mul (hM.1 k (hk0 k hk)).ne'
  · rw [vecMul_apply_gbn, vecMul_apply_gbn, hval, hval]
    exact (pos_iff_pos_of_mul_pos (hP.1 k (hk0 k hk))).symm.trans
      (pos_iff_pos_of_mul_pos (hM.1 k (hk0 k hk)))
  · rw [vecMul_apply_gbn, vecMul_apply_gbn, hval, hval]
    exact ⟨right_ne_zero_of_mul (hP.2 j (hj0 j hj)).ne',
      right_ne_zero_of_mul (hM.2 j (hj0 j hj)).ne',
      (pos_iff_pos_of_mul_pos (hP.2 j (hj0 j hj))).symm.trans
        (pos_iff_pos_of_mul_pos (hM.2 j (hj0 j hj)))⟩

/-- The difference of two sums of `if`s, as one sum with the coefficients `c_k`. -/
private theorem sum_ite_sub_gbn {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (P Q : ι → Prop) [DecidablePred P] [DecidablePred Q] (F : ι → V) (c : ι → ℝ)
    (hc : ∀ k, ((if P k then (1 : ℝ) else 0) - if Q k then 1 else 0) = c k) :
    ((∑ k, if P k then F k else 0) - ∑ k, if Q k then F k else 0) = ∑ k, c k • F k := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hc k]
  by_cases hp : P k <;> by_cases hq : Q k <;> simp [hp, hq]

/-- Subtracting two identities with the same `M` and the same constant terms. -/
private theorem sub_eq_sub_gbn {V : Type*} [AddCommGroup V] {M A B Z A' B' Z' : V}
    (h1 : M + (A + Z) = A' + Z') (h2 : M + (B + Z) = B' + Z') : A - B = A' - B' := by
  calc A - B = (M + (A + Z)) - (M + (B + Z)) := by abel
    _ = A' - B' := by rw [h1, h2]; abel

/-- **The identity of Steps 2 and 3**, in any module: from `M + ∑ o_k D_k = ∑ o'_j D'_j + ∑ Z_j`
and `D_i = ∑_j e_ij D'_j`, `M + ∑_{i ∈ S} D_i = ∑_j (c_j D'_j + Z_j)` with
`c_j = o'_j + ∑_i ([i ∈ S] − o_i) e_ij`. -/
private theorem sum_eq_gbn {ι κ V : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [AddCommGroup V] [Module ℝ V] (M : V) (D : ι → V) (D' Z : κ → V) (S : Finset ι)
    (o : ι → ℝ) (o' c : κ → ℝ) (e : ι → κ → ℝ)
    (hA : M + ∑ k, o k • D k = ∑ j, o' j • D' j + ∑ j, Z j)
    (hK : ∀ i, D i = ∑ j, e i j • D' j)
    (hc : ∀ j, c j = o' j + ∑ i, ((if i ∈ S then 1 else 0) - o i) * e i j) :
    M + ∑ i ∈ S, D i = ∑ j, (c j • D' j + Z j) := by
  have h1 : ∑ i, ((if i ∈ S then 1 else 0) - o i) • D i
      = ∑ j, (∑ i, ((if i ∈ S then 1 else 0) - o i) * e i j) • D' j := by
    simp only [hK, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h2 : ∑ i ∈ S, D i = ∑ i, o i • D i + ∑ i, ((if i ∈ S then 1 else 0) - o i) • D i := by
    have h3 : ∑ i ∈ S, D i = ∑ i, if i ∈ S then D i else 0 := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [← Finset.sum_add_distrib, h3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul, add_sub_cancel]
    split_ifs <;> simp
  rw [h2, ← add_assoc, hA, h1]
  simp only [hc, add_smul, Finset.sum_add_distrib]
  abel

/-- Rank is subadditive. -/
private theorem rank_add_le_gbn {a b : Type*} [Fintype a] [Fintype b] (A B : Matrix a b ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- The rank of a sum is at most the sum of the ranks. -/
private theorem rank_sum_le_gbn {a b ι : Type*} [Fintype a] [Fintype b] (s : Finset ι)
    (A : ι → Matrix a b ℝ) : (∑ j ∈ s, A j).rank ≤ ∑ j ∈ s, (A j).rank := by
  refine Finset.sum_hom_rel (r := fun (X : Matrix a b ℝ) (n : ℕ) => X.rank ≤ n) ?_ ?_
  · simp
  · intro j X n h
    exact (rank_add_le_gbn _ _).trans (Nat.add_le_add_left h _)

/-- **Proof of Lemma C.8 of the absorb paper, "One hyperplane at a time" and "Counting":** let the
gate reads of `B_θ` be nonzero and pairwise non-collinear, and its value reads and writes nonzero.
If the two identities of the expansion along rays hold at every `x` off the hyperplanes of both
blocks, then for some set `S` of units of `B_θ` the rank of `M + ∑_{i∈S} Δ_i` is at most the number
of units that `B_{θ′}` has more than `B_θ`. -/
theorem exists_rank_add_card_le_of_gateLinear_gateQuadratic (σ : ℝ → ℝ)
    (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ)
    (Wg' : Matrix p m' ℝ) (bg' : m' → ℝ) (Wv' : Matrix p m' ℝ) (bv' : m' → ℝ)
    (Ww' : Matrix m' q ℝ) (M : Matrix p q ℝ)
    (hg : ∀ j, Wgᵀ j ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, Wgᵀ i ≠ r • Wgᵀ j)
    (hv : ∀ j, Wvᵀ j ≠ 0) (hw : ∀ j, Ww j ≠ 0)
    (hcell : ∀ x : p → ℝ, (∀ j, (x ᵥ* Wg) j ≠ 0) → (∀ j, (x ᵥ* Wg') j = 0 → Wg'ᵀ j = 0) →
      M + gateLinear σ Wg bg Wv bv Ww x = gateLinear σ Wg' bg' Wv' bv' Ww' x ∧
        ∀ y : p → ℝ, gateQuadratic Wg Wv Ww x y = gateQuadratic Wg' Wv' Ww' x y) :
    ∃ S : Finset m, (M + ∑ i ∈ S, gateDelta Wg bg Wv bv Ww i).rank + Fintype.card m
      ≤ Fintype.card m' := by
  sorry

end Skips
