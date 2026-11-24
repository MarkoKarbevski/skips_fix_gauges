import SkipsLean.Absorb.BiasesConstructions
import Mathlib.Analysis.Real.Pi.Irrational

/-!
# Attention blocks with biases and rotary embeddings absorb a linear term

Paper (absorb paper), Appendix C. "Rotary embeddings. With rotary embeddings (Su et al., 2021),
the head dimension `d_h` is even, and the query and the key of the token at position `t` are
multiplied by `R^t`, where the `d_h × d_h` matrix `R` rotates `d_h/2` coordinate planes by fixed
angles. With `h_t` row `t` of `h`, the score of the query at position `t` against the key at
position `s` is then `(h_t W_{Q,i} + b_{Q,i}) R^{t−s} (h_s W_{K,i} + b_{K,i})^⊤ / √d_h`, which
depends on the two positions. Without biases, no such block absorbs a linear term (Theorem 3.4).
With biases, a head whose queries and keys are its biases attends by position alone, and such
heads add up to a skip."

Proposition C.6 (Rotary embeddings with biases): "Let attention blocks have biases and rotary
embeddings, with or without a causal mask, and let one of the rotary angles, `ϑ`, satisfy
`k ϑ ∉ 2πℤ` for `0 < k < T`. Then every attention block absorbs `h M`, for every `M`, with at most
`T² ⌈rank M / d_h⌉` more heads." After it: "The first angle of Su et al. (2021) is `ϑ = 1`, which
satisfies the condition for every `T`."

Here: the tokens are the positions `0, …, n − 1` (`Fin n`; `T = n`), the coordinate planes are an
index type `pl` and the head dimension is `pl × Fin 2`, so `d_h = 2 |pl|`; `R^k` rotates the plane
`c` by `k ϑ_c` (`rotaryPow`); the block is `attentionBlockRotaryB` (for the angles `0` it is the
block with biases of `Absorb/BiasesConstructions.lean`). The proof of the proposition uses the
mask through "Among them, `s = t`": every token sees itself. So the statement is for any such
mask, and the paper's two masks are stated by name. "With at most `k` more heads" is: a block
whose heads are the heads `H` of `B_θ` and a further finite type of at most `k` heads.
-/

namespace Skips

open Matrix

/-- **The power `R^k` of the rotary matrix:** on the head dimension `pl × Fin 2`, the plane `c`
is rotated by the angle `k ϑ_c`. -/
noncomputable def rotaryPow {pl : Type*} [DecidableEq pl] (ϑ : pl → ℝ) (k : ℤ) :
    Matrix (pl × Fin 2) (pl × Fin 2) ℝ :=
  Matrix.of fun x y =>
    if x.1 = y.1 then
      (if x.2 = y.2 then Real.cos (k * ϑ x.1)
        else if x.2 = 0 then -Real.sin (k * ϑ x.1) else Real.sin (k * ϑ x.1))
    else 0

/-- **An attention block with biases and rotary embeddings** on the positions `0, …, n − 1`: as
the block with biases, with the score of the query at position `t` against the key at position
`s` equal to `(h_t W_{Q,i} + b_{Q,i}) R^{t−s} (h_s W_{K,i} + b_{K,i})^⊤ / √d_h`. -/
noncomputable def attentionBlockRotaryB {n : ℕ} {d H pl : Type*} [Fintype d] [Fintype H]
    [Fintype pl] [DecidableEq pl] (sees : Fin n → Fin n → Prop) [DecidableRel sees] (ϑ : pl → ℝ)
    (WQ WK WV : H → Matrix d (pl × Fin 2) ℝ) (bQ bK bV : H → pl × Fin 2 → ℝ)
    (WO : H → Matrix (pl × Fin 2) d ℝ) (bO : d → ℝ) (h : Matrix (Fin n) d ℝ) :
    Matrix (Fin n) d ℝ :=
  (∑ i, attnWeights sees (Matrix.of fun t s =>
        (Real.sqrt (Fintype.card (pl × Fin 2)))⁻¹ *
          (((h t ᵥ* WQ i + bQ i) ᵥ* rotaryPow ϑ ((t : ℤ) - (s : ℤ))) ⬝ᵥ (h s ᵥ* WK i + bK i)))
      * (h * WV i + Matrix.of fun _ => bV i) * WO i)
    + Matrix.of fun _ => bO

/-- **A rank factorization** (as `exists_mul_eq_rank_bc` of `Absorb/BiasesConstructions.lean`):
`M = A B` with `rank M` columns in `A`. -/
private theorem exists_mul_eq_rank_rot {p q : Type*} [Fintype p] [Fintype q] (M : Matrix p q ℝ) :
    ∃ (A : Matrix p (Fin M.rank) ℝ) (B : Matrix (Fin M.rank) q ℝ), M = A * B := by
  classical
  set W := Submodule.span ℝ (Set.range M.row) with hW
  let β : Module.Basis (Fin M.rank) ℝ W :=
    Module.finBasisOfFinrankEq ℝ W (M.rank_eq_finrank_span_row).symm
  have hmem : ∀ i, M i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  refine ⟨Matrix.of fun i l => β.repr ⟨M i, hmem i⟩ l, Matrix.of fun l => (β l : q → ℝ), ?_⟩
  funext i o
  have h := β.sum_repr ⟨M i, hmem i⟩
  have h2 := congrArg (fun v : W => (v : q → ℝ) o) h
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h2
  rw [Matrix.mul_apply]
  simpa only [Matrix.of_apply] using h2.symm

/-- **Chunks of `M`:** if `rank M ≤ N d_h`, then `M = ∑_{i < N} V_i O_i` with `V_i` of `d_h`
columns and `O_i` of `d_h` rows: the inner indices of a rank factorization embed into
`Fin N × D`. -/
private theorem exists_chunks_rot {d D : Type*} [Fintype d] [Fintype D] (N : ℕ)
    (M : Matrix d d ℝ) (hN : M.rank ≤ N * Fintype.card D) :
    ∃ (V : Fin N → Matrix d D ℝ) (O : Fin N → Matrix D d ℝ), ∑ i, V i * O i = M := by
  obtain ⟨A, B, hAB⟩ := exists_mul_eq_rank_rot M
  -- the `rank M` inner indices embed into `Fin N × D`
  obtain ⟨ι⟩ : Nonempty (Fin M.rank ↪ Fin N × D) :=
    Function.Embedding.nonempty_of_card_le
      (by simpa only [Fintype.card_fin, Fintype.card_prod] using hN)
  refine ⟨fun i => Matrix.of fun a x => Function.extend ι (A a) 0 (i, x),
    fun i => Matrix.of fun x o => Function.extend ι (fun c => B c o) 0 (i, x), ?_⟩
  ext a o
  have hM : M a o = (A * B) a o := congrFun (congrFun hAB a) o
  rw [hM, Matrix.sum_apply, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.of_apply]
  calc _ = ∑ p : Fin N × D, Function.extend ι (A a) 0 p
        * Function.extend ι (fun c => B c o) 0 p := (Fintype.sum_prod_type _).symm
    _ = _ := by
      refine (Fintype.sum_of_injective ι ι.injective _ _ (fun p hp => ?_) (fun c => ?_)).symm
      · rw [Function.extend_apply' _ _ _ hp, Pi.zero_apply, zero_mul]
      · rw [ι.injective.extend_apply, ι.injective.extend_apply]

/-- `r ≤ ⌈r / D⌉ D` for `D > 0`. -/
private theorem le_ceil_mul_rot (r D : ℕ) (hD : 0 < D) : r ≤ ⌈(r : ℚ) / (D : ℚ)⌉₊ * D := by
  have h1 := Nat.le_ceil ((r : ℚ) / D)
  rw [div_le_iff₀ (by exact_mod_cast hD)] at h1
  exact_mod_cast h1

open Filter Topology in
/-- **A limit in the span is a short combination:** if `P a → X` as `a → ∞` in the `n × n`
matrices, then `X = ∑_{j < J} λ_j P(a_j)` with `J ≤ n²`. The span of the `P a` is closed (finite
dimension), and a linearly independent subfamily with the same span has at most `n²` members. -/
private theorem exists_comb_of_tendsto_rot {n : ℕ} (P : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (hP : Tendsto P atTop (𝓝 X)) :
    ∃ (J : ℕ) (a lam : Fin J → ℝ), J ≤ n ^ 2 ∧ ∑ j, lam j • P (a j) = X := by
  -- `X` is in the span of the `P a`: a finite-dimensional subspace is closed
  have hX : X ∈ Submodule.span ℝ (Set.range P) :=
    (Submodule.span ℝ (Set.range P)).isClosed_of_finiteDimensional.mem_of_tendsto hP
      (Eventually.of_forall fun a => Submodule.subset_span ⟨a, rfl⟩)
  -- a linearly independent subfamily with the same span has at most `n²` members
  obtain ⟨κ, b, -, hspan, hli⟩ := exists_linearIndependent' ℝ P
  have : Finite κ := hli.finite
  have : Fintype κ := Fintype.ofFinite κ
  have hκ : Fintype.card κ ≤ n ^ 2 := by
    have h := hli.fintype_card_le_finrank
    rwa [Module.finrank_matrix, Module.finrank_self, Fintype.card_fin, mul_one, ← sq] at h
  rw [← hspan] at hX
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hX
  let e := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ, fun j => b (e j), fun j => c (e j), hκ, ?_⟩
  rw [← hc]
  exact e.sum_comp fun k => c k • P (b k)

/-- The weights are nonnegative. -/
private theorem attnWeights_nonneg_rot {T : Type*} [Fintype T] (sees : T → T → Prop)
    [DecidableRel sees] (Z : Matrix T T ℝ) (t s : T) : 0 ≤ attnWeights sees Z t s := by
  simp only [attnWeights, Matrix.of_apply]
  split_ifs
  · exact div_nonneg (Real.exp_pos _).le
      (Finset.sum_nonneg fun s' _ => by split_ifs <;> positivity)
  · exact le_rfl

/-- If token `t` sees itself, the weight of `s` is at most `exp (Z t s − Z t t)`. -/
private theorem attnWeights_le_rot {T : Type*} [Fintype T] (sees : T → T → Prop)
    [DecidableRel sees] (Z : Matrix T T ℝ) (t s : T) (ht : sees t t) :
    attnWeights sees Z t s ≤ Real.exp (Z t s - Z t t) := by
  simp only [attnWeights, Matrix.of_apply]
  split_ifs with hs
  · rw [Real.exp_sub]
    refine div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) ?_
    have h := Finset.single_le_sum (f := fun s' => if sees t s' then Real.exp (Z t s') else 0)
      (fun s' _ => by split_ifs <;> positivity) (Finset.mem_univ t)
    simpa only [ht, ite_true] using h
  · exact (Real.exp_pos _).le

/-- The denominator of row `t` of the weights is positive when token `t` sees some token. -/
private theorem attnWeights_den_pos_rot {T : Type*} [Fintype T] (sees : T → T → Prop)
    [DecidableRel sees] (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
    0 < ∑ s', if sees t s' then Real.exp (Z t s') else 0 := by
  obtain ⟨s, hs⟩ := ht
  refine Finset.sum_pos' (fun s' _ => ?_) ⟨s, Finset.mem_univ _, ?_⟩
  · split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  · simp only [hs, ite_true]
    exact Real.exp_pos _

/-- Row `t` of the weights sums to `1` when token `t` sees some token. -/
private theorem attnWeights_sum_rot {T : Type*} [Fintype T] (sees : T → T → Prop)
    [DecidableRel sees] (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
    ∑ s, attnWeights sees Z t s = 1 := by
  have hS := attnWeights_den_pos_rot sees Z t ht
  have h1 : ∀ s, attnWeights sees Z t s = (if sees t s then Real.exp (Z t s) else 0)
      / ∑ s', if sees t s' then Real.exp (Z t s') else 0 := by
    intro s
    simp only [attnWeights, Matrix.of_apply]
    split_ifs
    · rfl
    · rw [zero_div]
  simp only [h1, ← Finset.sum_div]
  exact div_self hS.ne'

/-- **The scores of a head by position alone:** `a cos ((t − s) ϑ_{c₀})`. -/
private noncomputable def posScores_rot {n : ℕ} {pl : Type*} (ϑ : pl → ℝ) (c₀ : pl) (a : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun t s => a * Real.cos ((((t : ℤ) - (s : ℤ) : ℤ) : ℝ) * ϑ c₀)

/-- If `k ϑ_{c₀} ∉ 2πℤ` for `0 < k < n`, then `cos ((t − s) ϑ_{c₀}) < 1` for `s ≠ t`. -/
private theorem cos_lt_one_rot {n : ℕ} {pl : Type*} (ϑ : pl → ℝ) (c₀ : pl)
    (hϑ : ∀ k : ℕ, 0 < k → k < n → ∀ z : ℤ, (k : ℝ) * ϑ c₀ ≠ 2 * Real.pi * z) (t s : Fin n)
    (hst : s ≠ t) : Real.cos ((((t : ℤ) - (s : ℤ) : ℤ) : ℝ) * ϑ c₀) < 1 := by
  refine lt_of_le_of_ne (Real.cos_le_one _) fun h1 => ?_
  obtain ⟨z, hz⟩ := (Real.cos_eq_one_iff _).1 h1
  have ht := t.isLt
  have hs := s.isLt
  rcases lt_or_gt_of_ne hst with h | h
  · -- `s < t`: the gap `k = t − s`
    have h' : (s : ℕ) < t := h
    refine hϑ ((t : ℕ) - s) (by omega) (by omega) z ?_
    rw [Nat.cast_sub h'.le]
    push_cast at hz
    linear_combination -hz
  · -- `t < s`: the gap `k = s − t`, and `cos` is even
    have h' : (t : ℕ) < s := h
    refine hϑ ((s : ℕ) - t) (by omega) (by omega) (-z) ?_
    rw [Nat.cast_sub h'.le]
    push_cast at hz ⊢
    linear_combination hz

open Filter Topology in
/-- **The weights of a head by position alone tend to the identity** as `a → ∞`: token `t` sees
itself with the score `a`, and every other token with a score `a cos(…)`, `cos(…) < 1`. -/
private theorem tendsto_attnWeights_rot {n : ℕ} {pl : Type*} (sees : Fin n → Fin n → Prop)
    [DecidableRel sees] (hsees : ∀ t, sees t t) (ϑ : pl → ℝ) (c₀ : pl)
    (hϑ : ∀ k : ℕ, 0 < k → k < n → ∀ z : ℤ, (k : ℝ) * ϑ c₀ ≠ 2 * Real.pi * z) :
    Tendsto (fun a : ℝ => attnWeights sees (posScores_rot ϑ c₀ a)) atTop (𝓝 1) := by
  -- off the diagonal, the weight is at most `exp (a (cos(…) − 1)) → 0`
  have hoff : ∀ t s : Fin n, s ≠ t →
      Tendsto (fun a : ℝ => attnWeights sees (posScores_rot ϑ c₀ a) t s) atTop (𝓝 0) := by
    intro t s hst
    have hc := cos_lt_one_rot ϑ c₀ hϑ t s hst
    have hlim : Tendsto (fun a : ℝ =>
        Real.exp (a * (Real.cos ((((t : ℤ) - (s : ℤ) : ℤ) : ℝ) * ϑ c₀) - 1))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg (by linarith))
    refine squeeze_zero (fun a => attnWeights_nonneg_rot sees _ t s) (fun a => ?_) hlim
    refine (attnWeights_le_rot sees _ t s (hsees t)).trans (le_of_eq ?_)
    simp only [posScores_rot, Matrix.of_apply, sub_self, Int.cast_zero, zero_mul, Real.cos_zero]
    ring_nf
  refine tendsto_pi_nhds.2 fun t => tendsto_pi_nhds.2 fun s => ?_
  by_cases hst : s = t
  · subst hst
    -- the weight of `t` is `1` minus the others
    have hrow : ∀ a : ℝ, attnWeights sees (posScores_rot ϑ c₀ a) s s
        = 1 - ∑ s' ∈ Finset.univ.erase s, attnWeights sees (posScores_rot ϑ c₀ a) s s' := by
      intro a
      rw [← attnWeights_sum_rot sees _ s ⟨s, hsees s⟩,
        ← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
      ring
    have h0 := tendsto_finsetSum (Finset.univ.erase s)
      fun s' hs' => hoff s s' (Finset.ne_of_mem_erase hs')
    rw [Finset.sum_const_zero] at h0
    have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
    rw [sub_zero] at h1
    rw [Matrix.one_apply_eq]
    exact h1.congr fun a => (hrow a).symm
  · rw [Matrix.one_apply_ne' hst]
    exact hoff t s hst

/-- The unit row `e` of the plane `c₀`: `(e R^k) ⬝ e = cos (k ϑ_{c₀})`. -/
private theorem rotaryPow_single_rot {pl : Type*} [DecidableEq pl] [Fintype pl] (ϑ : pl → ℝ)
    (c₀ : pl) (k : ℤ) :
    (Pi.single (c₀, (0 : Fin 2)) (1 : ℝ) ᵥ* rotaryPow ϑ k) ⬝ᵥ Pi.single (c₀, (0 : Fin 2)) 1
      = Real.cos (k * ϑ c₀) := by
  rw [Matrix.single_vecMul, dotProduct_single, one_smul, mul_one]
  simp [rotaryPow, Matrix.row]

/-- **A head by position alone** (`W_Q = W_K = 0`, `b_Q = a √d_h e`, `b_K = e`) has the scores
`a cos ((t − s) ϑ_{c₀})` at every input `h`. -/
private theorem scores_rot {n : ℕ} {d pl : Type*} [Fintype d] [Fintype pl] [DecidableEq pl]
    (ϑ : pl → ℝ) (c₀ : pl) (a : ℝ) (h : Matrix (Fin n) d ℝ) :
    (Matrix.of fun t s : Fin n => (Real.sqrt (Fintype.card (pl × Fin 2)))⁻¹ *
      (((h t ᵥ* (0 : Matrix d (pl × Fin 2) ℝ) + (a * Real.sqrt (Fintype.card (pl × Fin 2))) •
          Pi.single (c₀, (0 : Fin 2)) (1 : ℝ)) ᵥ* rotaryPow ϑ ((t : ℤ) - (s : ℤ))) ⬝ᵥ
        (h s ᵥ* (0 : Matrix d (pl × Fin 2) ℝ) + Pi.single (c₀, (0 : Fin 2)) (1 : ℝ))))
      = posScores_rot ϑ c₀ a := by
  have hD : 0 < Real.sqrt (Fintype.card (pl × Fin 2)) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨(c₀, 0)⟩))
  ext t s
  simp only [Matrix.of_apply, posScores_rot, Matrix.vecMul_zero, zero_add, Matrix.smul_vecMul,
    smul_dotProduct, rotaryPow_single_rot, smul_eq_mul]
  field_simp

/-- **The term of a new head:** with the value matrix `λ V`, the value bias `0` and the output
matrix `O`, a head by position alone adds `λ P_a h V O`. -/
private theorem newHead_rot {n : ℕ} {d pl : Type*} [Fintype d] [Fintype pl] [DecidableEq pl]
    (sees : Fin n → Fin n → Prop) [DecidableRel sees] (ϑ : pl → ℝ) (c₀ : pl) (a lam : ℝ)
    (V : Matrix d (pl × Fin 2) ℝ) (O : Matrix (pl × Fin 2) d ℝ) (h : Matrix (Fin n) d ℝ) :
    attnWeights sees (Matrix.of fun t s : Fin n => (Real.sqrt (Fintype.card (pl × Fin 2)))⁻¹ *
      (((h t ᵥ* (0 : Matrix d (pl × Fin 2) ℝ) + (a * Real.sqrt (Fintype.card (pl × Fin 2))) •
          Pi.single (c₀, (0 : Fin 2)) (1 : ℝ)) ᵥ* rotaryPow ϑ ((t : ℤ) - (s : ℤ))) ⬝ᵥ
        (h s ᵥ* (0 : Matrix d (pl × Fin 2) ℝ) + Pi.single (c₀, (0 : Fin 2)) (1 : ℝ))))
      * (h * (lam • V) + Matrix.of fun _ => (0 : pl × Fin 2 → ℝ)) * O
      = lam • (attnWeights sees (posScores_rot ϑ c₀ a) * h * (V * O)) := by
  have h0 : (Matrix.of fun _ : Fin n => (0 : pl × Fin 2 → ℝ)) = 0 := rfl
  rw [scores_rot, h0, add_zero]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

/-- **Proposition C.6 of the absorb paper (Rotary embeddings with biases):** let attention blocks
have biases and rotary embeddings, with a mask in which every token sees itself, and let one of
the rotary angles, `ϑ`, satisfy `k ϑ ∉ 2πℤ` for `0 < k < T`. Then every attention block absorbs
`h M`, for every `M`, with at most `T² ⌈rank M / d_h⌉` more heads. -/
theorem exists_attentionBlockRotaryB_add_linear {n : ℕ} {d H pl : Type*} [Fintype d]
    [DecidableEq d] [Fintype H] [Fintype pl] [DecidableEq pl] (sees : Fin n → Fin n → Prop)
    [DecidableRel sees] (hsees : ∀ t, sees t t) (ϑ : pl → ℝ) (c₀ : pl)
    (hϑ : ∀ k : ℕ, 0 < k → k < n → ∀ z : ℤ, (k : ℝ) * ϑ c₀ ≠ 2 * Real.pi * z)
    (WQ WK WV : H → Matrix d (pl × Fin 2) ℝ) (bQ bK bV : H → pl × Fin 2 → ℝ)
    (WO : H → Matrix (pl × Fin 2) d ℝ) (bO : d → ℝ) (M : Matrix d d ℝ) :
    ∃ (K : Type) (_ : Fintype K),
      Fintype.card K ≤ n ^ 2 * ⌈(M.rank : ℚ) / (Fintype.card (pl × Fin 2) : ℚ)⌉₊ ∧
      ∃ (WQ' WK' WV' : H ⊕ K → Matrix d (pl × Fin 2) ℝ) (bQ' bK' bV' : H ⊕ K → pl × Fin 2 → ℝ)
        (WO' : H ⊕ K → Matrix (pl × Fin 2) d ℝ) (bO' : d → ℝ),
        ∀ h : Matrix (Fin n) d ℝ,
          h * M + attentionBlockRotaryB sees ϑ WQ WK WV bQ bK bV WO bO h
            = attentionBlockRotaryB sees ϑ WQ' WK' WV' bQ' bK' bV' WO' bO' h := by
  -- `1 = ∑_j λ_j P_{a_j}` with `J ≤ n²` heads by position alone
  obtain ⟨J, a, lam, hJ, hcomb⟩ :=
    exists_comb_of_tendsto_rot _ _ (tendsto_attnWeights_rot sees hsees ϑ c₀ hϑ)
  -- `M = ∑_i V_i O_i` with `N = ⌈rank M / d_h⌉` chunks
  have hD : 0 < Fintype.card (pl × Fin 2) := Fintype.card_pos_iff.2 ⟨(c₀, 0)⟩
  obtain ⟨V, O, hVO⟩ := exists_chunks_rot (D := pl × Fin 2) _ M (le_ceil_mul_rot M.rank _ hD)
  -- the new head `(j, i)` attends by position with `a_j` and has the value `λ_j V_i`
  refine ⟨Fin J × Fin ⌈(M.rank : ℚ) / (Fintype.card (pl × Fin 2) : ℚ)⌉₊, inferInstance, ?_,
    Sum.elim WQ fun _ => 0, Sum.elim WK fun _ => 0, Sum.elim WV fun k => lam k.1 • V k.2,
    Sum.elim bQ fun k => (a k.1 * Real.sqrt (Fintype.card (pl × Fin 2))) •
      Pi.single (c₀, (0 : Fin 2)) (1 : ℝ),
    Sum.elim bK fun _ => Pi.single (c₀, (0 : Fin 2)) (1 : ℝ), Sum.elim bV fun _ => 0,
    Sum.elim WO fun k => O k.2, bO, fun h => ?_⟩
  · rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ hJ
  -- the new heads add `(∑_j λ_j P_{a_j}) h (∑_i V_i O_i) = 1 h M`
  have hnew : ∑ k : Fin J × Fin ⌈(M.rank : ℚ) / (Fintype.card (pl × Fin 2) : ℚ)⌉₊,
      lam k.1 • (attnWeights sees (posScores_rot ϑ c₀ (a k.1)) * h * (V k.2 * O k.2))
        = h * M := by
    rw [Fintype.sum_prod_type]
    simp only [← Matrix.mul_sum, hVO, ← Matrix.smul_mul, ← Matrix.sum_mul,
      hcomb, Matrix.one_mul]
  simp only [attentionBlockRotaryB, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    newHead_rot, hnew]
  abel

/-- **Proposition C.6 without a mask.** -/
theorem exists_attentionBlockRotaryB_add_linear_noMask {n : ℕ} {d H pl : Type*} [Fintype d]
    [DecidableEq d] [Fintype H] [Fintype pl] [DecidableEq pl] (ϑ : pl → ℝ) (c₀ : pl)
    (hϑ : ∀ k : ℕ, 0 < k → k < n → ∀ z : ℤ, (k : ℝ) * ϑ c₀ ≠ 2 * Real.pi * z)
    (WQ WK WV : H → Matrix d (pl × Fin 2) ℝ) (bQ bK bV : H → pl × Fin 2 → ℝ)
    (WO : H → Matrix (pl × Fin 2) d ℝ) (bO : d → ℝ) (M : Matrix d d ℝ) :
    ∃ (K : Type) (_ : Fintype K),
      Fintype.card K ≤ n ^ 2 * ⌈(M.rank : ℚ) / (Fintype.card (pl × Fin 2) : ℚ)⌉₊ ∧
      ∃ (WQ' WK' WV' : H ⊕ K → Matrix d (pl × Fin 2) ℝ) (bQ' bK' bV' : H ⊕ K → pl × Fin 2 → ℝ)
        (WO' : H ⊕ K → Matrix (pl × Fin 2) d ℝ) (bO' : d → ℝ),
        ∀ h : Matrix (Fin n) d ℝ,
          h * M + attentionBlockRotaryB (fun _ _ : Fin n => True) ϑ WQ WK WV bQ bK bV WO bO h
            = attentionBlockRotaryB (fun _ _ : Fin n => True) ϑ WQ' WK' WV' bQ' bK' bV' WO' bO'
              h := by
  exact exists_attentionBlockRotaryB_add_linear (fun _ _ : Fin n => True) (fun _ => trivial) ϑ
    c₀ hϑ WQ WK WV bQ bK bV WO bO M

/-- **Proposition C.6 with the causal mask:** token `t` sees the tokens `s ≤ t`. -/
theorem exists_attentionBlockRotaryB_add_linear_causal {n : ℕ} {d H pl : Type*} [Fintype d]
    [DecidableEq d] [Fintype H] [Fintype pl] [DecidableEq pl] (ϑ : pl → ℝ) (c₀ : pl)
    (hϑ : ∀ k : ℕ, 0 < k → k < n → ∀ z : ℤ, (k : ℝ) * ϑ c₀ ≠ 2 * Real.pi * z)
    (WQ WK WV : H → Matrix d (pl × Fin 2) ℝ) (bQ bK bV : H → pl × Fin 2 → ℝ)
    (WO : H → Matrix (pl × Fin 2) d ℝ) (bO : d → ℝ) (M : Matrix d d ℝ) :
    ∃ (K : Type) (_ : Fintype K),
      Fintype.card K ≤ n ^ 2 * ⌈(M.rank : ℚ) / (Fintype.card (pl × Fin 2) : ℚ)⌉₊ ∧
      ∃ (WQ' WK' WV' : H ⊕ K → Matrix d (pl × Fin 2) ℝ) (bQ' bK' bV' : H ⊕ K → pl × Fin 2 → ℝ)
        (WO' : H ⊕ K → Matrix (pl × Fin 2) d ℝ) (bO' : d → ℝ),
        ∀ h : Matrix (Fin n) d ℝ,
          h * M + attentionBlockRotaryB (fun t s : Fin n => s ≤ t) ϑ WQ WK WV bQ bK bV WO bO h
            = attentionBlockRotaryB (fun t s : Fin n => s ≤ t) ϑ WQ' WK' WV' bQ' bK' bV' WO'
              bO' h := by
  exact exists_attentionBlockRotaryB_add_linear (fun t s : Fin n => s ≤ t) (fun t => le_refl t) ϑ
    c₀ hϑ WQ WK WV bQ bK bV WO bO M

/-- **"The first angle of Su et al. (2021) is `ϑ = 1`, which satisfies the condition for every
`T`":** `k · 1 ∉ 2πℤ` for every `k > 0`. -/
theorem rotary_angle_one (k : ℕ) (hk : 0 < k) (z : ℤ) : (k : ℝ) * 1 ≠ 2 * Real.pi * z := by
  intro h
  rw [mul_one] at h
  have hz : (z : ℝ) ≠ 0 := by
    rintro hz
    rw [hz, mul_zero] at h
    exact (Nat.cast_pos.2 hk).ne' h
  -- `π = k / (2 z)` would be rational
  apply irrational_pi.ne_rational k (2 * z)
  push_cast
  rw [eq_div_iff (mul_ne_zero two_ne_zero hz), h]
  ring

end Skips
