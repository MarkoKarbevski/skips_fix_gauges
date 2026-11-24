import SkipsLean.Depth.ComplexRMSNorm
import SkipsLean.Depth.RowsAux

/-!
# One `tanh` block that satisfies all conditions of the case (0)

Paper (dimension paper): Appendix D.6, "Parameters that satisfy all conditions, in the case (0)":
"We choose the blocks from the last to the first. Let `D` and the blocks `ℓ + 1, …, L` be chosen,
regular and with (S1) to (S3) for tanh […]. This fixes `κ_ℓ` (Lemma D.14). We choose
`(W, V) = (W_read^ℓ, W_write^ℓ)`. Conditions that fail on a set of measure zero of pairs `(W, V)`.
(R1), (S1), (S2) and (P1) are of this kind […]. (R2): […]. (R3): the determinant in the proof of
Lemma D.2 is real-analytic in `(n, W, V)`, so (R3) fails on a set of measure zero once it holds for
one pair. It holds for `W = [I | 0]` and `V` with the rows of `I` and zero rows, at any `n ∈ S`
with positive entries `n_i` […]. Conditions that hold on a nonempty open set of pairs. (S3): take
any `V` and `W°`, with the columns `c°_j`, and a unit row `ξ₀` with `ξ₀c°_j ≠ 0` and `s̄V ≠ 0` for
the row `s̄` of the signs. As `s̄V` is a real nonzero row, there is a `ρ` as in (S3). Then
`W = λW°` satisfies (S3) for large `λ > 0` […]. A nonempty open set minus a set of measure zero is
not empty."

Stated here: for every cone `C_κ`, `κ > 0`, there is a pair `(W, V)` that satisfies the conditions
of one `tanh` block, for one row (the paper's one token):
(R1) for the write, `V` has rank `d`; (R2) `tanh(nW) V ≠ 0` for every row `n` on the sphere
`‖n‖² = d`; (R3) at some such `n`, a `v ⊥ n` with `𝐃g(n) v ∈ ℝ g(n)` is `0`, where
`g(n) = tanh(nW) V`; (S1) any two rows of `V` are linearly independent; (S2) the columns of `W` are
linearly independent over `ℚ`; (S3) for `C_κ`.

The existence needs one pair only, and the Lean proof may take it in the family `V = Wᵀ` (the
paper's pair for (R3) is of this kind): there (R2) holds as soon as `W` has rank `d`, because
`⟨tanh(nW) Wᵀ, n⟩ = ∑_j tanh(n c_j) (n c_j) > 0`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {d : Type*} [Fintype d]

/-- **The conditions on one `tanh` block in the case (0),** for the read `W` (columns `c_j`), the
write `V` and the cone `C_κ`: (R1) for `V`, (R2), (R3), (S1), (S2), and (S3) for `C_κ`. -/
structure TanhPathBlock {q : Type*} [Fintype q] (W : Matrix d q ℝ) (V : Matrix q d ℝ) (κ : ℝ) :
    Prop where
  /-- (R1) for the write: `V` has rank `d`. -/
  rank_write : V.rank = Fintype.card d
  /-- (R2): `g(n) = tanh(nW) V ≠ 0` for every row `n` on the sphere `‖n‖² = d`. -/
  ne_zero : ∀ n : d → ℝ, n ⬝ᵥ n = (Fintype.card d : ℝ) →
    (fun j : q => Real.tanh ((n ᵥ* W) j)) ᵥ* V ≠ 0
  /-- (R3): at some `n` on the sphere, a `v ⊥ n` with `𝐃g(n) v ∈ ℝ g(n)` is `0`. -/
  deriv : ∃ n : d → ℝ, n ⬝ᵥ n = (Fintype.card d : ℝ) ∧ ∀ v : d → ℝ, v ⬝ᵥ n = 0 →
    (∃ a : ℝ,
      fderiv ℝ (fun n' : d → ℝ => (fun j : q => Real.tanh ((n' ᵥ* W) j)) ᵥ* V) n v
        = a • ((fun j : q => Real.tanh ((n ᵥ* W) j)) ᵥ* V)) →
    v = 0
  /-- (S1): any two rows of `V` are linearly independent. -/
  rows_indep : ∀ i j : q, i ≠ j → ∀ a c : ℝ, a • V i + c • V j = 0 → a = 0 ∧ c = 0
  /-- (S2): the columns of `W` are linearly independent over `ℚ`. -/
  cols_indep : LinearIndependent ℚ (fun j : q => fun i : d => W i j)
  /-- (S3) for `C_κ`: a unit row `ξ₀` and a `ρ ∈ (0, 1]` such that every `ξ₀c_j ≠ 0`, the rows
  `w̃V` with `|w̃_j − s_j| ≤ ρ` (`s_j` the sign of `ξ₀c_j`) lie in `C_κ`, and
  `e^{−2√d |ξ₀c_j|} < ρ/3`. -/
  saturated : ∃ (ξ₀ : d → ℝ) (ρ : ℝ), ξ₀ ⬝ᵥ ξ₀ = 1 ∧ 0 < ρ ∧ ρ ≤ 1 ∧
    (∀ j : q, (ξ₀ ᵥ* W) j ≠ 0) ∧
    (∀ w : q → ℂ, (∀ j, ‖w j - ((Real.sign ((ξ₀ ᵥ* W) j) : ℝ) : ℂ)‖ ≤ ρ) →
      w ᵥ* V.map (fun x : ℝ => (x : ℂ)) ∈ complexCone κ) ∧
    ∀ j : q, Real.exp (-(2 * (Real.sqrt (Fintype.card d) * |(ξ₀ ᵥ* W) j|))) < ρ / 3

/-- Helper: `tanh` is strictly increasing (its derivative `1 − tanh²` is positive). -/
private theorem strictMono_tanh_tpx : StrictMono Real.tanh :=
  strictMono_of_deriv_pos fun x => by
    rw [(hasDerivAt_tanh x).deriv]
    linarith [Real.tanh_sq_lt_one x]

/-- Helper: `tanh x > 0` for `x > 0`. -/
private theorem tanh_pos_tpx {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  have h := strictMono_tanh_tpx hx
  rwa [Real.tanh_zero] at h

/-- Helper: `tanh x ≥ 0` for `x ≥ 0`. -/
private theorem tanh_nonneg_tpx {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  have h := strictMono_tanh_tpx.monotone hx
  rwa [Real.tanh_zero] at h

/-- Helper: `|tanh x| = tanh |x|` (`tanh` is odd). -/
private theorem abs_tanh_tpx (x : ℝ) : |Real.tanh x| = Real.tanh |x| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (tanh_nonneg_tpx hx)]
  · rw [abs_of_neg hx, Real.tanh_neg, abs_of_neg]
    have h := tanh_pos_tpx (neg_pos.2 hx)
    rw [Real.tanh_neg] at h
    linarith

/-- The read of the pair: `W i (inl i') = λ δ_{ii'}`, `W i (inr j) = λ μ_j`. -/
private def readTpx [DecidableEq d] (l : ℝ) {m : ℕ} (μ : Fin m → ℝ) : Matrix d (d ⊕ Fin m) ℝ :=
  Matrix.of fun i k => Sum.elim (fun i' => if i = i' then l else 0) (fun j => l * μ j) k

/-- The write of the pair: the row `inl i'` is `e_{i'}`, the row `inr j` is `B_j`. -/
private def writeTpx [DecidableEq d] {m : ℕ} (B : Fin m → d → ℝ) : Matrix (d ⊕ Fin m) d ℝ :=
  Matrix.of fun k i => Sum.elim (fun i' => if i' = i then (1 : ℝ) else 0) (fun j => B j i) k

/-- Helper: `(ξW)_{inl i} = λ ξ_i`. -/
private theorem vecMul_read_inl_tpx [DecidableEq d] (l : ℝ) {m : ℕ} (μ : Fin m → ℝ) (ξ : d → ℝ)
    (i : d) : (ξ ᵥ* readTpx l μ) (Sum.inl i) = l * ξ i := by
  simp [readTpx, Matrix.vecMul, dotProduct, mul_comm]

/-- Helper: `(ξW)_{inr j} = λ μ_j ∑_i ξ_i`. -/
private theorem vecMul_read_inr_tpx [DecidableEq d] (l : ℝ) {m : ℕ} (μ : Fin m → ℝ) (ξ : d → ℝ)
    (j : Fin m) : (ξ ᵥ* readTpx l μ) (Sum.inr j) = l * μ j * ∑ i, ξ i := by
  simp only [readTpx, Matrix.vecMul, dotProduct, Matrix.of_apply, Sum.elim_inr]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Helper: `(xV)_i = x_{inl i} + ∑_j x_{inr j} B_{ji}`. -/
private theorem vecMul_write_tpx [DecidableEq d] {m : ℕ} (B : Fin m → d → ℝ)
    (x : d ⊕ Fin m → ℝ) (i : d) :
    (x ᵥ* writeTpx B) i = x (Sum.inl i) + ∑ j, x (Sum.inr j) * B j i := by
  simp [writeTpx, Matrix.vecMul, dotProduct, Fintype.sum_sum_type]

/-- Helper: the same for complex rows and the complex write. -/
private theorem vecMul_write_map_tpx [DecidableEq d] {m : ℕ} (B : Fin m → d → ℝ)
    (w : d ⊕ Fin m → ℂ) (i : d) :
    (w ᵥ* (writeTpx B).map (fun x : ℝ => (x : ℂ))) i
      = w (Sum.inl i) + ∑ j, w (Sum.inr j) * (B j i : ℂ) := by
  simp [writeTpx, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, apply_ite]

/-- Helper: the derivative of `g(n) = tanh(nW) V` along `v`. -/
private theorem fderiv_tanh_vecMul_tpx {q : Type*} [Fintype q] (W : Matrix d q ℝ)
    (V : Matrix q d ℝ) (n v : d → ℝ) :
    fderiv ℝ (fun n' : d → ℝ => (fun j : q => Real.tanh ((n' ᵥ* W) j)) ᵥ* V) n v
      = (fun k => (1 - Real.tanh ((n ᵥ* W) k) ^ 2) * (v ᵥ* W) k) ᵥ* V := by
  let L : (d → ℝ) →L[ℝ] (q → ℝ) := LinearMap.toContinuousLinearMap (Matrix.vecMulLinear W)
  let M : (q → ℝ) →L[ℝ] (d → ℝ) := LinearMap.toContinuousLinearMap (Matrix.vecMulLinear V)
  let D : (q → ℝ) →L[ℝ] (q → ℝ) := ContinuousLinearMap.pi fun k =>
    (1 - Real.tanh ((n ᵥ* W) k) ^ 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : q => ℝ) k
  have hΦ : HasFDerivAt (fun y : q → ℝ => fun k => Real.tanh (y k)) D (n ᵥ* W) := by
    refine hasFDerivAt_pi.2 fun k => ?_
    have h := (hasDerivAt_tanh ((n ᵥ* W) k)).comp_hasFDerivAt (n ᵥ* W)
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : q => ℝ) k (n ᵥ* W))
    exact h
  have hg : HasFDerivAt (fun n' : d → ℝ => (fun j : q => Real.tanh ((n' ᵥ* W) j)) ᵥ* V)
      (M.comp (D.comp L)) n := by
    have h1 := M.hasFDerivAt.comp n (hΦ.comp n L.hasFDerivAt)
    exact h1
  rw [hg.fderiv]
  rfl

/-- Helper (R1): the write has rank `d` (the rows `inl i` form the identity, `P V = 1`). -/
private theorem rank_write_tpx [DecidableEq d] {m : ℕ} (B : Fin m → d → ℝ) :
    (writeTpx B).rank = Fintype.card d := by
  -- the left inverse `P` picks the rows `inl i`
  let P : Matrix d (d ⊕ Fin m) ℝ :=
    Matrix.of fun i k => Sum.elim (fun i' => if i = i' then (1 : ℝ) else 0) (fun _ => 0) k
  have hP : P * writeTpx B = 1 := by
    ext i i'
    simp [P, writeTpx, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  apply le_antisymm (Matrix.rank_le_card_width _)
  calc Fintype.card d = (1 : Matrix d d ℝ).rank := Matrix.rank_one.symm
    _ = (P * writeTpx B).rank := by rw [hP]
    _ ≤ (writeTpx B).rank := Matrix.rank_mul_le_right _ _

/-- Helper (R2): `g(n) ≠ 0` on the sphere: a coordinate with `|n_i| ≥ 1` has
`|tanh(λn_i)| ≥ tanh 1`, and the other terms add up to less than `tanh 1 / 2`. -/
private theorem ne_zero_tpx [DecidableEq d] [Nonempty d] {m : ℕ} {l : ℝ} (hl : 1 ≤ l)
    (μ : Fin m → ℝ) (B : Fin m → d → ℝ) (hB : ∀ i, ∑ j, |B j i| < Real.tanh 1 / 2) (n : d → ℝ)
    (hn : n ⬝ᵥ n = (Fintype.card d : ℝ)) :
    (fun k => Real.tanh ((n ᵥ* readTpx l μ) k)) ᵥ* writeTpx B ≠ 0 := by
  -- some `|n_i| ≥ 1`, otherwise `n ⬝ n < d`
  obtain ⟨i, hi⟩ : ∃ i, 1 ≤ |n i| := by
    by_contra h
    push Not at h
    have hlt : n ⬝ᵥ n < ∑ _i : d, (1 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => by
        have := (sq_lt_one_iff_abs_lt_one (n i)).2 (h i)
        nlinarith
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hlt
    linarith
  intro h0
  have hc := congrFun h0 i
  simp only [vecMul_write_tpx, vecMul_read_inl_tpx, Pi.zero_apply] at hc
  -- the first term: `|tanh(λ n_i)| ≥ tanh 1`
  have h1 : Real.tanh 1 ≤ |Real.tanh (l * n i)| := by
    rw [abs_tanh_tpx, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < l)]
    exact strictMono_tanh_tpx.monotone (by nlinarith)
  -- the other terms: at most `∑_j |B_{ji}| < tanh 1 / 2`
  have h2 : |∑ j, Real.tanh ((n ᵥ* readTpx l μ) (Sum.inr j)) * B j i| < Real.tanh 1 / 2 := by
    refine lt_of_le_of_lt ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => ?_)) (hB i)
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_tanh_lt_one _).le
  have h3 : 0 < Real.tanh 1 := tanh_pos_tpx one_pos
  rw [add_eq_zero_iff_eq_neg] at hc
  rw [hc, abs_neg] at h1
  linarith

/-- Helper (R3) at `n₀ = (1, …, 1)`: for `v ⊥ n₀`, `𝐃g(n₀) v = λ(1 − tanh² λ) v`, and
`⟨g(n₀), n₀⟩ > 0`. -/
private theorem deriv_tpx [DecidableEq d] [Nonempty d] {m : ℕ} {l : ℝ} (hl : 0 < l)
    (μ : Fin m → ℝ) (hμ : ∀ j, 0 < μ j) (B : Fin m → d → ℝ) (hB : ∀ j i, 0 ≤ B j i) :
    ∃ n : d → ℝ, n ⬝ᵥ n = (Fintype.card d : ℝ) ∧ ∀ v : d → ℝ, v ⬝ᵥ n = 0 →
      (∃ a : ℝ,
        fderiv ℝ (fun n' : d → ℝ =>
            (fun j => Real.tanh ((n' ᵥ* readTpx l μ) j)) ᵥ* writeTpx B) n v
          = a • ((fun j => Real.tanh ((n ᵥ* readTpx l μ) j)) ᵥ* writeTpx B)) →
      v = 0 := by
  refine ⟨fun _ => 1, by simp [dotProduct], fun v hv ⟨a, ha⟩ => ?_⟩
  -- `∑_i v_i = 0`
  have hs : ∑ i, v i = 0 := by simpa [dotProduct] using hv
  rw [fderiv_tanh_vecMul_tpx] at ha
  -- coordinate `i`: `(1 − tanh² λ) λ v_i = a g(n₀)_i`
  have hi : ∀ i, (1 - Real.tanh l ^ 2) * (l * v i)
      = a * (Real.tanh l + ∑ j, Real.tanh (l * μ j * ∑ _i : d, (1 : ℝ)) * B j i) := by
    intro i
    have h := congrFun ha i
    simp only [vecMul_write_tpx, vecMul_read_inl_tpx, vecMul_read_inr_tpx, hs, mul_zero,
      zero_mul, Finset.sum_const_zero, add_zero, mul_one, Pi.smul_apply, smul_eq_mul] at h
    exact h
  -- `g(n₀)_i ≥ tanh λ > 0`
  have hG : ∀ i, 0 < Real.tanh l + ∑ j, Real.tanh (l * μ j * ∑ _i : d, (1 : ℝ)) * B j i :=
    fun i => add_pos_of_pos_of_nonneg (tanh_pos_tpx hl) (Finset.sum_nonneg fun j _ =>
      mul_nonneg (tanh_nonneg_tpx (mul_nonneg (mul_nonneg hl.le (hμ j).le)
        (Finset.sum_nonneg fun _ _ => zero_le_one))) (hB j i))
  -- summing over `i`: `0 = a ∑_i g(n₀)_i`, so `a = 0`
  have hsum : (1 - Real.tanh l ^ 2) * l * ∑ i, v i
      = a * ∑ i, (Real.tanh l + ∑ j, Real.tanh (l * μ j * ∑ _i : d, (1 : ℝ)) * B j i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← hi i]; ring
  rw [hs, mul_zero] at hsum
  have ha0 : a = 0 := by
    rcases mul_eq_zero.1 hsum.symm with h | h
    · exact h
    · exact absurd h (Finset.sum_pos (fun i _ => hG i) Finset.univ_nonempty).ne'
  -- then `(1 − tanh² λ) λ v_i = 0` with `(1 − tanh² λ) λ ≠ 0`
  funext i
  have h := hi i
  rw [ha0, zero_mul] at h
  have hc : (1 - Real.tanh l ^ 2) * l ≠ 0 :=
    mul_ne_zero (by linarith [Real.tanh_sq_lt_one l]) hl.ne'
  have h' : (1 - Real.tanh l ^ 2) * l * v i = 0 := by rw [mul_assoc]; exact h
  simpa [hc] using h'

/-- The rows `B_j = η a_j` of the write: `a_j i = j + 2` at `i = i₁`, and `1` elsewhere. -/
private def rowTpx [DecidableEq d] (η : ℝ) (i₁ : d) {m : ℕ} (j : Fin m) (i : d) : ℝ :=
  η * (if i = i₁ then ((j : ℕ) : ℝ) + 2 else 1)

omit [Fintype d] in
/-- Helper: the entries of the rows `η a_j` are positive. -/
private theorem rowTpx_pos [DecidableEq d] {η : ℝ} (hη : 0 < η) (i₁ : d) {m : ℕ} (j : Fin m)
    (i : d) : 0 < rowTpx η i₁ j i := by
  unfold rowTpx
  split_ifs <;> positivity

omit [Fintype d] in
/-- Helper: `η a_j i ≤ η (j + 2)`. -/
private theorem rowTpx_le [DecidableEq d] {η : ℝ} (hη : 0 < η) (i₁ : d) {m : ℕ} (j : Fin m)
    (i : d) : rowTpx η i₁ j i ≤ η * (((j : ℕ) : ℝ) + 2) := by
  unfold rowTpx
  apply mul_le_mul_of_nonneg_left _ hη.le
  split_ifs
  · exact le_refl _
  · linarith [(Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ _)]

omit [Fintype d] in
/-- Helper (S1): any two rows `e_i`, `η a_j` of the write are linearly independent. -/
private theorem rows_indep_tpx [DecidableEq d] {m : ℕ} {η : ℝ} (hη : 0 < η) {i₀ i₁ : d}
    (hi : i₀ ≠ i₁) :
    ∀ k k' : d ⊕ Fin m, k ≠ k' → ∀ a c : ℝ,
      a • writeTpx (rowTpx η i₁) k + c • writeTpx (rowTpx η i₁) k' = 0 → a = 0 ∧ c = 0 := by
  have : Nontrivial d := nontrivial_of_ne i₀ i₁ hi
  -- the coordinate `i` of `a V_k + c V_{k'} = 0`
  have hco : ∀ (k k' : d ⊕ Fin m) (a c : ℝ) (i : d),
      a • writeTpx (rowTpx η i₁) k + c • writeTpx (rowTpx η i₁) k' = 0 →
      a * writeTpx (rowTpx η i₁) k i + c * writeTpx (rowTpx η i₁) k' i = 0 :=
    fun k k' a c i h => by simpa using congrFun h i
  intro k k' hkk' a c h
  rcases k with i | j <;> rcases k' with i' | j'
  · -- `e_i`, `e_{i'}`, `i ≠ i'`: the coordinates `i` and `i'`
    have hii' : i ≠ i' := fun e => hkk' (by rw [e])
    have h1 := hco _ _ a c i h
    have h2 := hco _ _ a c i' h
    simp [writeTpx, hii', hii'.symm] at h1 h2
    exact ⟨h1, h2⟩
  · -- `e_i`, `η a_{j'}`: a coordinate `i' ≠ i` gives `c = 0`, then `i` gives `a = 0`
    obtain ⟨i', hi'⟩ := exists_ne i
    have h1 := hco _ _ a c i' h
    simp [writeTpx, hi'.symm, (rowTpx_pos hη i₁ j' i').ne'] at h1
    have h2 := hco _ _ a c i h
    simp [writeTpx, h1] at h2
    exact ⟨h2, h1⟩
  · -- `η a_j`, `e_{i'}`: the same
    obtain ⟨i, hi'⟩ := exists_ne i'
    have h1 := hco _ _ a c i h
    simp [writeTpx, hi'.symm, (rowTpx_pos hη i₁ j i).ne'] at h1
    have h2 := hco _ _ a c i' h
    simp [writeTpx, h1] at h2
    exact ⟨h1, h2⟩
  · -- `η a_j`, `η a_{j'}`, `j ≠ j'`: the coordinates `i₀` (`a + c = 0`) and `i₁`
    have hjj' : (((j : ℕ) : ℝ)) ≠ ((j' : ℕ) : ℝ) :=
      Nat.cast_injective.ne (Fin.val_injective.ne fun e => hkk' (by rw [e]))
    have h1 := hco _ _ a c i₀ h
    have h2 := hco _ _ a c i₁ h
    simp only [writeTpx, rowTpx, Matrix.of_apply, Sum.elim_inr, hi, ite_true, ite_false] at h1 h2
    have e0 : (a + c) * η = 0 := by linear_combination h1
    have e0' : a + c = 0 := (mul_eq_zero.1 e0).resolve_right hη.ne'
    have e1 : (a * (((j : ℕ) : ℝ) + 2) + c * (((j' : ℕ) : ℝ) + 2)) * η = 0 := by
      linear_combination h2
    have e1' := (mul_eq_zero.1 e1).resolve_right hη.ne'
    have e2 : a * (((j : ℕ) : ℝ) - ((j' : ℕ) : ℝ)) = 0 := by
      linear_combination e1' - (((j' : ℕ) : ℝ) + 2) * e0'
    have ha : a = 0 := (mul_eq_zero.1 e2).resolve_right (sub_ne_zero.2 hjj')
    exact ⟨ha, by linarith⟩

/-- Helper (S2): the columns `λ e_i` and `λ μ_j (1, …, 1)` of the read are linearly independent
over `ℚ`: at a coordinate `i`, a relation is `λ (κ_i + ∑_j κ'_j μ_j) = 0`. -/
private theorem cols_indep_tpx [DecidableEq d] [Nonempty d] {m : ℕ} {l : ℝ} (hl : l ≠ 0)
    (μ : Fin m → ℝ) (hμ : LinearIndependent ℚ (fun o : Option (Fin m) => Option.elim o 1 μ)) :
    LinearIndependent ℚ (fun k : d ⊕ Fin m => fun i : d => readTpx l μ i k) := by
  rw [Fintype.linearIndependent_iff] at hμ ⊢
  intro g hg
  have key : ∀ (i : d) (o : Option (Fin m)),
      Option.elim o (g (Sum.inl i)) (fun j => g (Sum.inr j)) = 0 := by
    intro i
    apply hμ
    have h := congrFun hg i
    simp only [Finset.sum_apply, Pi.smul_apply, Fintype.sum_sum_type, readTpx, Matrix.of_apply,
      Sum.elim_inl, Sum.elim_inr, Rat.smul_def, Pi.zero_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
    have h2 : l * ((g (Sum.inl i) : ℝ) + ∑ j, (g (Sum.inr j) : ℝ) * μ j) = 0 := by
      rw [← h, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun j _ => by ring
    rw [Fintype.sum_option]
    simp only [Option.elim_none, Option.elim_some, Rat.smul_def, mul_one]
    exact (mul_eq_zero.1 h2).resolve_left hl
  intro k
  rcases k with i | j
  · exact key i none
  · exact key (Classical.arbitrary d) (some j)

/-- Helper (S3), the cone: for `‖w_k − 1‖ ≤ ρ`, the row `wV` is in `C_κ` (`B ≥ 0`,
`ρ ≤ min (1/2) (κ/4)`): `Re (wV)_i ≥ (1 − ρ) A_i`, `|Im (wV)_i| ≤ ρ A_i`, `A_i = 1 + ∑_j B_{ji}`. -/
private theorem mem_complexCone_tpx [DecidableEq d] [Nonempty d] {m : ℕ} (B : Fin m → d → ℝ)
    (hB : ∀ j i, 0 ≤ B j i) {κ ρ : ℝ} (hκ : 0 < κ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hρκ : ρ ≤ κ / 4) (w : d ⊕ Fin m → ℂ) (hw : ∀ k, ‖w k - 1‖ ≤ ρ) :
    w ᵥ* (writeTpx B).map (fun x : ℝ => (x : ℂ)) ∈ complexCone κ := by
  set u := w ᵥ* (writeTpx B).map (fun x : ℝ => (x : ℂ)) with hu
  -- `|u_i − A_i| ≤ ρ A_i`
  have hdiff : ∀ i, ‖u i - ((1 + ∑ j, B j i : ℝ) : ℂ)‖ ≤ ρ * (1 + ∑ j, B j i) := by
    intro i
    have he : u i - ((1 + ∑ j, B j i : ℝ) : ℂ)
        = (w (Sum.inl i) - 1) + ∑ j, (w (Sum.inr j) - 1) * (B j i : ℂ) := by
      rw [hu, vecMul_write_map_tpx]
      push_cast
      simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
      ring
    rw [he, mul_add, mul_one, Finset.mul_sum]
    refine (norm_add_le _ _).trans (add_le_add (hw _)
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)))
    rw [norm_mul, Complex.norm_of_nonneg (hB j i)]
    exact mul_le_mul_of_nonneg_right (hw _) (hB j i)
  -- per coordinate: `(Im u_i)² < κ² (Re u_i)²`
  have hco : ∀ i, (u i).im * (u i).im < κ ^ 2 * ((u i).re * (u i).re) := by
    intro i
    have hA : 1 ≤ 1 + ∑ j, B j i :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hB j i)
    have hre := (Complex.abs_re_le_norm _).trans (hdiff i)
    have him := (Complex.abs_im_le_norm _).trans (hdiff i)
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
    have h1 := (abs_le.1 hre).1
    have hk : ρ < κ * (1 - ρ) := by nlinarith
    have h3 : ρ * (1 + ∑ j, B j i) < κ * (u i).re := by nlinarith
    calc (u i).im * (u i).im = |(u i).im| * |(u i).im| := (abs_mul_abs_self _).symm
      _ < (κ * (u i).re) * (κ * (u i).re) :=
          mul_self_lt_mul_self (abs_nonneg _) (him.trans_lt h3)
      _ = κ ^ 2 * ((u i).re * (u i).re) := by ring
  show (fun i => (u i).im) ⬝ᵥ (fun i => (u i).im)
    < κ ^ 2 * ((fun i => (u i).re) ⬝ᵥ (fun i => (u i).re))
  simp only [dotProduct]
  rw [Finset.mul_sum]
  exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hco i

/-- Helper (S3): with the unit row `ξ₀ = (1/√d, …, 1/√d)`, every `ξ₀ c_k > 0` (so every sign is
`1`), `√d ξ₀ c_k ≥ λ`, and the cone part gives (S3) for `ρ`. -/
private theorem saturated_tpx [DecidableEq d] [Nonempty d] {m : ℕ} {l : ℝ} (hl : 1 ≤ l)
    (μ : Fin m → ℝ) (hμ : ∀ j, 1 ≤ μ j) (B : Fin m → d → ℝ) (hB : ∀ j i, 0 ≤ B j i)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (hρκ : ρ ≤ κ / 4)
    (hexp : Real.exp (-(2 * l)) < ρ / 3) :
    ∃ (ξ₀ : d → ℝ) (ρ' : ℝ), ξ₀ ⬝ᵥ ξ₀ = 1 ∧ 0 < ρ' ∧ ρ' ≤ 1 ∧
      (∀ k, (ξ₀ ᵥ* readTpx l μ) k ≠ 0) ∧
      (∀ w : d ⊕ Fin m → ℂ,
        (∀ k, ‖w k - ((Real.sign ((ξ₀ ᵥ* readTpx l μ) k) : ℝ) : ℂ)‖ ≤ ρ') →
        w ᵥ* (writeTpx B).map (fun x : ℝ => (x : ℂ)) ∈ complexCone κ) ∧
      ∀ k, Real.exp (-(2 * (Real.sqrt (Fintype.card d) * |(ξ₀ ᵥ* readTpx l μ) k|))) < ρ' / 3 := by
  -- `s = √d > 0`, `s² = d ≥ 1`
  have hc : (1 : ℝ) ≤ Fintype.card d := by exact_mod_cast Fintype.card_pos
  set s := Real.sqrt (Fintype.card d) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hss : s * s = Fintype.card d := Real.mul_self_sqrt (by linarith)
  -- `ξ₀ ⬝ ξ₀ = d / s² = 1`
  have hξ : (fun _ : d => s⁻¹) ⬝ᵥ (fun _ : d => s⁻¹) = 1 := by
    simp only [dotProduct, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hss]
    field_simp
  -- `ξ₀ c_k > 0` and `s ξ₀ c_k ≥ λ`
  have hpos : ∀ k, 0 < ((fun _ : d => s⁻¹) ᵥ* readTpx l μ) k ∧
      l ≤ s * ((fun _ : d => s⁻¹) ᵥ* readTpx l μ) k := by
    intro k
    rcases k with i | j
    · rw [vecMul_read_inl_tpx]
      refine ⟨mul_pos (by linarith) (inv_pos.2 hs0), ?_⟩
      rw [show s * (l * s⁻¹) = l by field_simp]
    · rw [vecMul_read_inr_tpx]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hsinv : (Fintype.card d : ℝ) * s⁻¹ = s := by rw [← hss]; field_simp
      rw [hsinv]
      refine ⟨mul_pos (mul_pos (by linarith) (by linarith [hμ j])) hs0, ?_⟩
      rw [show s * (l * μ j * s) = l * (μ j * (s * s)) by ring, hss]
      exact le_mul_of_one_le_right (by linarith) (one_le_mul_of_one_le_of_one_le (hμ j) hc)
  refine ⟨fun _ => s⁻¹, ρ, hξ, hρ0, by linarith, fun k => (hpos k).1.ne', fun w hw => ?_,
    fun k => ?_⟩
  · -- all signs are `1`
    refine mem_complexCone_tpx B hB hκ hρ0 hρ1 hρκ w fun k => ?_
    have h := hw k
    rwa [Real.sign_of_pos (hpos k).1, Complex.ofReal_one] at h
  · -- the decay: `e^{−2 s ξ₀ c_k} ≤ e^{−2λ} < ρ/3`
    rw [abs_of_pos (hpos k).1]
    exact lt_of_le_of_lt (Real.exp_le_exp.2 (by linarith [(hpos k).2])) hexp

/-- Helper: a `λ ≥ 1` with `e^{−2λ} < ρ/3` (`λ = 1 + 3/ρ`, `e^x ≥ 1 + x`). -/
private theorem exists_lambda_tpx {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ l : ℝ, 1 ≤ l ∧ Real.exp (-(2 * l)) < ρ / 3 := by
  have h3 : 0 < 3 / ρ := div_pos three_pos hρ
  refine ⟨1 + 3 / ρ, by linarith, ?_⟩
  have h1 := Real.add_one_le_exp (2 * (1 + 3 / ρ))
  have h2 : ρ * (3 / ρ) = 3 := by field_simp
  rw [Real.exp_neg, inv_eq_one_div, div_lt_iff₀ (Real.exp_pos _)]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ ρ / 3)]

/-- Helper: an `η > 0` with `η ∑_j (j + 2) < tanh 1 / 2`. -/
private theorem exists_eta_tpx (m : ℕ) :
    ∃ η : ℝ, 0 < η ∧ η * ∑ j : Fin m, (((j : ℕ) : ℝ) + 2) < Real.tanh 1 / 2 := by
  have ht := tanh_pos_tpx one_pos
  have hS : 0 ≤ ∑ j : Fin m, (((j : ℕ) : ℝ) + 2) := Finset.sum_nonneg fun j _ => by positivity
  refine ⟨Real.tanh 1 / (2 * (∑ j : Fin m, (((j : ℕ) : ℝ) + 2) + 1)), by positivity, ?_⟩
  rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- Helper: over `ℚ`, the linear independence of `(u_j)_j` passes to `(c u_j)_j`, `c ≠ 0` real
(a copy of the private `linearIndependent_mul_szt`). -/
private theorem linearIndependent_mul_tpx {q : Type*} {u : q → ℝ} (hu : LinearIndependent ℚ u)
    {c : ℝ} (hc : c ≠ 0) : LinearIndependent ℚ (fun j => c * u j) :=
  hu.map' (LinearMap.mulLeft ℚ c) (LinearMap.ker_eq_bot.2 (mul_right_injective₀ hc))

/-- Helper: numbers `μ_j > 1` with `1, μ_0, …, μ_{m−1}` linearly independent over `ℚ`: a point
`x` of the dense set of rows with entries independent over `ℚ` (the columns of `1`) in the open set
`0 < x_∅ < x_j`, and `μ_j = x_j / x_∅`. -/
private theorem exists_mu_tpx (m : ℕ) :
    ∃ μ : Fin m → ℝ, (∀ j, 1 < μ j) ∧
      LinearIndependent ℚ (fun o : Option (Fin m) => Option.elim o 1 μ) := by
  classical
  -- the columns of `1` are linearly independent over `ℚ`
  have hcols : LinearIndependent ℚ (fun j : Option (Fin m) => fun i : Option (Fin m) =>
      (1 : Matrix (Option (Fin m)) (Option (Fin m)) ℝ) i j) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg o
    have h := congrFun hg o
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.one_apply, Rat.smul_def, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Pi.zero_apply] at h
    exact_mod_cast h
  have hD := dense_setOf_linearIndependent_vecMul _ hcols
  -- the open set `0 < x_∅ < x_j`
  let U : Set (Option (Fin m) → ℝ) :=
    {x | 0 < x none} ∩ ⋂ j : Fin m, {x | x none < x (some j)}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const (continuous_apply none)).inter
      (isOpen_iInter_of_finite fun j => isOpen_lt (continuous_apply none) (continuous_apply _))
  have hUne : U.Nonempty := ⟨fun o => Option.elim o 1 (fun _ => 2), by
    refine ⟨by simp, Set.mem_iInter.2 fun j => ?_⟩
    show (1 : ℝ) < 2
    norm_num⟩
  obtain ⟨x, hxD, hx0, hxj⟩ := hD.exists_mem_open hU hUne
  have hxj' : ∀ j, x none < x (some j) := fun j => Set.mem_iInter.1 hxj j
  have hx0' : 0 < x none := hx0
  refine ⟨fun j => x (some j) / x none, fun j => (one_lt_div hx0').2 (hxj' j), ?_⟩
  have h1 : LinearIndependent ℚ x := by
    have h := hxD
    simp only [Set.mem_ofPred_eq, Matrix.vecMul_one] at h
    exact h
  have h2 := linearIndependent_mul_tpx h1 (inv_ne_zero hx0'.ne')
  convert h2 using 1
  funext o
  cases o with
  | none => simp [hx0'.ne']
  | some j => simp [div_eq_inv_mul]

omit [Fintype d] in
/-- Helper: `(x ∘ e) (V reindexed) = x V` for a reindexing `e` of the hidden units. -/
private theorem comp_vecMul_submatrix_tpx {R : Type*} [CommSemiring R] {q q' : Type*}
    [Fintype q] [Fintype q'] (e : q' ≃ q) (M : Matrix q d R) (x : q → R) :
    (x ∘ e) ᵥ* M.submatrix e id = x ᵥ* M := by
  funext i
  simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, Function.comp_apply, id]
  exact e.sum_comp (fun k => x k * M k i)

/-- Helper: the six conditions do not depend on the order of the hidden units. -/
private theorem tanhPathBlock_submatrix_tpx {q q' : Type*} [Fintype q] [Fintype q'] (e : q' ≃ q)
    {W : Matrix d q ℝ} {V : Matrix q d ℝ} {κ : ℝ} (h : TanhPathBlock W V κ) :
    TanhPathBlock (W.submatrix id e) (V.submatrix e id) κ := by
  -- `g(n) = tanh(nW) V` is the same function
  have hpt : ∀ n : d → ℝ, (fun j => Real.tanh ((n ᵥ* W.submatrix id e) j)) ᵥ* V.submatrix e id
      = (fun j => Real.tanh ((n ᵥ* W) j)) ᵥ* V := fun n =>
    comp_vecMul_submatrix_tpx e V (fun j => Real.tanh ((n ᵥ* W) j))
  have hfun : (fun n : d → ℝ => (fun j => Real.tanh ((n ᵥ* W.submatrix id e) j)) ᵥ*
      V.submatrix e id) = fun n => (fun j => Real.tanh ((n ᵥ* W) j)) ᵥ* V := funext hpt
  refine ⟨?_, fun n hn => ?_, ?_, ?_, ?_, ?_⟩
  · exact (Matrix.rank_submatrix V e (Equiv.refl d)).trans h.rank_write
  · rw [hpt]
    exact h.ne_zero n hn
  · obtain ⟨n, hn, h3⟩ := h.deriv
    refine ⟨n, hn, fun v hv ha => h3 v hv ?_⟩
    rw [hfun, hpt] at ha
    exact ha
  · exact fun i j hij a c hac => h.rows_indep (e i) (e j) (e.injective.ne hij) a c hac
  · exact h.cols_indep.comp e e.injective
  · obtain ⟨ξ₀, ρ, h1, hρ0, hρ1, hne, hcone, hdec⟩ := h.saturated
    refine ⟨ξ₀, ρ, h1, hρ0, hρ1, fun j => hne (e j), fun w hw => ?_, fun j => hdec (e j)⟩
    have key := comp_vecMul_submatrix_tpx e (V.map (fun x : ℝ => (x : ℂ))) (w ∘ e.symm)
    simp only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] at key
    rw [show (V.submatrix e id).map (fun x : ℝ => (x : ℂ))
      = (V.map (fun x : ℝ => (x : ℂ))).submatrix e id from rfl, key]
    refine hcone _ fun j => ?_
    have hj := hw (e.symm j)
    have he : (ξ₀ ᵥ* W.submatrix id e) (e.symm j) = (ξ₀ ᵥ* W) j := by
      show (ξ₀ ᵥ* W) (e (e.symm j)) = _
      rw [e.apply_symm_apply]
    rw [he] at hj
    exact hj

/-- Helper: the theorem for the hidden units `d ⊕ Fin m`, with the explicit pair. -/
private theorem exists_tanhPathBlock_sum_tpx [DecidableEq d] (hd : 2 ≤ Fintype.card d) (m : ℕ)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ (W : Matrix d (d ⊕ Fin m) ℝ) (V : Matrix (d ⊕ Fin m) d ℝ), TanhPathBlock W V κ := by
  obtain ⟨i₀, i₁, hi⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card d)
  have : Nonempty d := ⟨i₀⟩
  -- the numbers `μ_j`, `ρ`, `λ`, `η`
  obtain ⟨μ, hμ1, hμQ⟩ := exists_mu_tpx m
  have hρ0 : 0 < min (1 / 2 : ℝ) (κ / 4) := lt_min (by norm_num) (by linarith)
  obtain ⟨l, hl, hexp⟩ := exists_lambda_tpx hρ0
  obtain ⟨η, hη, hη2⟩ := exists_eta_tpx m
  -- `∑_j |η a_j i| < tanh 1 / 2`
  have hB : ∀ i, ∑ j, |rowTpx η i₁ j i| < Real.tanh 1 / 2 := fun i => by
    refine lt_of_le_of_lt ?_ hη2
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_of_pos (rowTpx_pos hη i₁ j i)]
    exact rowTpx_le hη i₁ j i
  have hB0 : ∀ (j : Fin m) (i : d), 0 ≤ rowTpx η i₁ j i := fun j i => (rowTpx_pos hη i₁ j i).le
  refine ⟨readTpx l μ, writeTpx (rowTpx η i₁), rank_write_tpx _, ne_zero_tpx hl μ _ hB,
    deriv_tpx (by linarith) μ (fun j => by linarith [hμ1 j]) _ hB0,
    rows_indep_tpx hη hi, cols_indep_tpx (by linarith) μ hμQ,
    saturated_tpx hl μ (fun j => (hμ1 j).le) _ hB0 hκ hρ0 (min_le_left _ _) (min_le_right _ _)
      hexp⟩

/-- **"Parameters that satisfy all conditions, in the case (0)", one block:** for `d ≥ 2`, at least
`d` hidden units and every `κ > 0`, there are a read `W` and a write `V` that satisfy (R1) for the
write, (R2), (R3), (S1), (S2), and (S3) for the cone `C_κ`. -/
theorem exists_tanhPathBlock {q : Type*} [Fintype q] (hd : 2 ≤ Fintype.card d)
    (hq : Fintype.card d ≤ Fintype.card q) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (W : Matrix d q ℝ) (V : Matrix q d ℝ), TanhPathBlock W V κ := by
  classical
  -- the pair on `d ⊕ Fin m`, `m = q − d`, moved to `q` along `q ≃ d ⊕ Fin m`
  obtain ⟨W, V, h⟩ := exists_tanhPathBlock_sum_tpx hd (Fintype.card q - Fintype.card d) hκ
  have hcard : Fintype.card q = Fintype.card (d ⊕ Fin (Fintype.card q - Fintype.card d)) := by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  exact ⟨_, _, tanhPathBlock_submatrix_tpx (Fintype.equivOfCardEq hcard) h⟩

end Skips
