import SkipsLean.Symmetry.BiasesGeneratedGroupSum
import SkipsLean.Symmetry.BiasesGeneratedGroupAttention

/-!
# The symmetries inside attention heads with biases act block by block

Paper (skips paper), Section 4.1 and Appendix A.6: the changes of basis inside the heads of an
attention block, between queries and keys and between values and outputs; with biases also the
shift of the key biases, and the value biases moved into the output bias.

`Symmetry/BiasesGeneratedGroupSum.lean` asks of a family of symmetries inside the blocks, to be
used in a network with two kinds of block, that it acts block by block (`InsideBlocksLocal`).
Here: the family `headsAct` of `Symmetry/BiasesGeneratedGroupAttention.lean` does, when every
token sees a token. It moves the write bias of a block by `−∑_i ν_i W_{O,i}`, a row that depends
on the writes alone.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise ENNReal

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees] {χ : Matrix T d ℝ → Matrix T d ℝ}
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-! ### Helpers: copies of the private helpers of `Symmetry/BiasesGeneratedGroupAttention.lean`

The map of every block is kept: the helpers `actGL_bga`, `headsAct_apply_bga`, `sum_mul_GL_bga`
and the chain from `f_QK_bga` to `block_act_bga`, with the suffix `_bla`. -/

/-- Helper: the map of `(K, K', κ, ν)` with `K`, `K'` given in `GL`. -/
private noncomputable def actGL_bla (K N : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (κ ν : ∀ ℓ, H ℓ → dh ℓ → ℝ)
    (q : Params (Arch.attention sees χ H dh) dIn dOut
      × Biases (Arch.attention sees χ H dh) dOut) :
    Params (Arch.attention sees χ H dh) dIn dOut × Biases (Arch.attention sees χ H dh) dOut :=
  ((q.1.headsQK K).headsVO N,
    (((q.2.headsQK K).headsVO N).keyShift κ).valueShift ((q.1.headsQK K).headsVO N) ν)

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `headsAct σ` is the map of `σ` with `glOfMatrix` of its matrices. -/
private theorem headsAct_apply_bla (σ : HeadsSpace H dh)
    (q : Params (Arch.attention sees χ H dh) dIn dOut
      × Biases (Arch.attention sees χ H dh) dOut) :
    headsAct σ q = actGL_bla (fun ℓ i => glOfMatrix (σ.1 ℓ i))
      (fun ℓ i => glOfMatrix (σ.2.1 ℓ i)) σ.2.2.1 σ.2.2.2 q := rfl


/-- Helper (the private `sum_mul_GL_ahb` of `Symmetry/AttentionHeadsBiases.lean`):
`∑_k (x G)_k (G⁻¹ y)_k = x · y` for `G ∈ GL n`. -/
private theorem sum_mul_GL_bla {n : Type*} [Fintype n] [DecidableEq n] (G : GL n ℝ)
    (x y : n → ℝ) :
    ∑ k, (∑ a, x a * (G : Matrix n n ℝ) a k) * (∑ b, ((G⁻¹ : GL n ℝ) : Matrix n n ℝ) k b * y b)
      = ∑ a, x a * y a := by
  have h : (x ᵥ* (G : Matrix n n ℝ)) ⬝ᵥ (((G⁻¹ : GL n ℝ) : Matrix n n ℝ) *ᵥ y) = x ⬝ᵥ y := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact h


omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the map `f ℓ` of an attention block is the same on `M'` and `M` if the query columns
of head `i` of `M'` are those of `M` times `G_i`, its key columns those of `M` times `G_i^{-⊤}`,
and its value columns those of `M`: the scores `∑_k (q G)_k (k G^{-⊤})_k = q · k` are kept. -/
private theorem f_QK_bla (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L)
    (M M' : Matrix T (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) ℝ)
    (hq : ∀ t i k, M' t (i, Sum.inl k)
      = ∑ a, M t (i, Sum.inl a) * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) a k)
    (hk : ∀ t i k, M' t (i, Sum.inr (Sum.inl k))
      = ∑ a, M t (i, Sum.inr (Sum.inl a))
        * (((K ℓ i)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ) k a)
    (hv : ∀ t i k, M' t (i, Sum.inr (Sum.inr k)) = M t (i, Sum.inr (Sum.inr k))) :
    (Arch.attention sees χ H dh).f ℓ M' = (Arch.attention sees χ H dh).f ℓ M := by
  -- the scores of every head are kept
  have hsc : ∀ i : H ℓ, (Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
        * ∑ k, M' t' (i, Sum.inl k) * M' s' (i, Sum.inr (Sum.inl k)) : Matrix T T ℝ)
      = Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
        * ∑ k, M t' (i, Sum.inl k) * M s' (i, Sum.inr (Sum.inl k)) := by
    intro i
    ext t' s'
    simp only [Matrix.of_apply, hq, hk]
    congr 1
    rw [← sum_mul_GL_bla (K ℓ i) (fun a => M t' (i, Sum.inl a))
      (fun a => M s' (i, Sum.inr (Sum.inl a)))]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  ext t p
  show ∑ s, attnWeights sees (Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
        * ∑ k, M' t' (p.1, Sum.inl k) * M' s' (p.1, Sum.inr (Sum.inl k))) t s
      * M' s (p.1, Sum.inr (Sum.inr p.2))
    = ∑ s, attnWeights sees (Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
        * ∑ k, M t' (p.1, Sum.inl k) * M s' (p.1, Sum.inr (Sum.inl k))) t s
      * M s (p.1, Sum.inr (Sum.inr p.2))
  rw [hsc p.1]
  simp only [hv]

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the changes of basis between queries and keys, with the biases of the queries and
keys moved along, keep the map `n ↦ f(n W_read + b_read) W_write + b_write` of every block. -/
private theorem block_headsQKB_bla
    (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (b : Biases (Arch.attention sees χ H dh) dOut) (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L)
    (n : Matrix T d ℝ) :
    (Arch.attention sees χ H dh).f ℓ (n * (θ.headsQK K).read ℓ
          + Matrix.of fun _ => (b.headsQK K).read ℓ) * (θ.headsQK K).write ℓ
        + Matrix.of (fun _ => (b.headsQK K).write ℓ)
      = (Arch.attention sees χ H dh).f ℓ (n * θ.read ℓ + Matrix.of fun _ => b.read ℓ)
          * θ.write ℓ + Matrix.of fun _ => b.write ℓ := by
  rw [f_QK_bla K ℓ (n * θ.read ℓ + Matrix.of fun _ => b.read ℓ) _ ?_ ?_ ?_]
  · rfl
  · -- the query columns: `(n W_Q + b_Q) K = n (W_Q K) + b_Q K`
    intro t i k
    show ∑ a, n t a * (∑ k', θ.read ℓ a (i, Sum.inl k') * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) k' k)
        + ∑ k', b.read ℓ (i, Sum.inl k') * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) k' k
      = ∑ a', (∑ a, n t a * θ.read ℓ a (i, Sum.inl a') + b.read ℓ (i, Sum.inl a'))
          * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) a' k
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  · -- the key columns: `(n W_K + b_K) K^{-⊤} = n (W_K K^{-⊤}) + b_K K^{-⊤}`
    intro t i k
    show ∑ a, n t a * (∑ k', θ.read ℓ a (i, Sum.inr (Sum.inl k'))
          * (((K ℓ i)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ) k k')
        + ∑ k', b.read ℓ (i, Sum.inr (Sum.inl k'))
          * (((K ℓ i)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ) k k'
      = ∑ a', (∑ a, n t a * θ.read ℓ a (i, Sum.inr (Sum.inl a'))
          + b.read ℓ (i, Sum.inr (Sum.inl a')))
          * (((K ℓ i)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ) k a'
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  · -- the value columns do not move
    intro t i k
    rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `f ℓ (M') W' = f ℓ (M) W` if the query and key columns of `M'` are those of `M`, the
value columns of head `i` of `M'` are those of `M` times `G_i`, and the rows `(i, ·)` of `W'` are
`G_i^{-1}` times those of `W`: the weights are kept, and `(a v G)(G^{-1} W_O) = a v W_O`. -/
private theorem f_VO_bla (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L)
    (M M' : Matrix T (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) ℝ) (W W' : Matrix (H ℓ × dh ℓ) d ℝ)
    (hq : ∀ t i k, M' t (i, Sum.inl k) = M t (i, Sum.inl k))
    (hk : ∀ t i k, M' t (i, Sum.inr (Sum.inl k)) = M t (i, Sum.inr (Sum.inl k)))
    (hv : ∀ t i k, M' t (i, Sum.inr (Sum.inr k))
      = ∑ a, M t (i, Sum.inr (Sum.inr a)) * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) a k)
    (hW : ∀ i k c, W' (i, k) c
      = ∑ k', (((K ℓ i)⁻¹ : GL (dh ℓ) ℝ) : Matrix (dh ℓ) (dh ℓ) ℝ) k k' * W (i, k') c) :
    (Arch.attention sees χ H dh).f ℓ M' * W' = (Arch.attention sees χ H dh).f ℓ M * W := by
  -- the scores of every head are kept
  have hsc : ∀ i : H ℓ, (Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
        * ∑ k, M' t' (i, Sum.inl k) * M' s' (i, Sum.inr (Sum.inl k)) : Matrix T T ℝ)
      = Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
        * ∑ k, M t' (i, Sum.inl k) * M s' (i, Sum.inr (Sum.inl k)) := by
    intro i
    ext t' s'
    simp only [Matrix.of_apply, hq, hk]
  -- head by head
  ext t c
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ∑ k, (∑ s, attnWeights sees (Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
          * ∑ k, M' t' (i, Sum.inl k) * M' s' (i, Sum.inr (Sum.inl k))) t s
        * M' s (i, Sum.inr (Sum.inr k))) * W' (i, k) c
    = ∑ k, (∑ s, attnWeights sees (Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
          * ∑ k, M t' (i, Sum.inl k) * M s' (i, Sum.inr (Sum.inl k))) t s
        * M s (i, Sum.inr (Sum.inr k))) * W (i, k) c
  rw [hsc i]
  generalize attnWeights sees (Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
    * ∑ k, M t' (i, Sum.inl k) * M s' (i, Sum.inr (Sum.inl k))) = P
  simp only [hv, hW]
  -- the weighted values of head `i` are multiplied by `G_i`
  have e : ∀ k, ∑ s, P t s
        * ∑ a, M s (i, Sum.inr (Sum.inr a)) * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) a k
      = ∑ a, (∑ s, P t s * M s (i, Sum.inr (Sum.inr a)))
        * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) a k := by
    intro k
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  simp only [e]
  exact sum_mul_GL_bla (K ℓ i) _ _

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the changes of basis between values and outputs, with the biases of the values moved
along, keep the map `n ↦ f(n W_read + b_read) W_write + b_write` of every block. -/
private theorem block_headsVOB_bla
    (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (b : Biases (Arch.attention sees χ H dh) dOut) (K : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ) (ℓ : Fin L)
    (n : Matrix T d ℝ) :
    (Arch.attention sees χ H dh).f ℓ (n * (θ.headsVO K).read ℓ
          + Matrix.of fun _ => (b.headsVO K).read ℓ) * (θ.headsVO K).write ℓ
        + Matrix.of (fun _ => (b.headsVO K).write ℓ)
      = (Arch.attention sees χ H dh).f ℓ (n * θ.read ℓ + Matrix.of fun _ => b.read ℓ)
          * θ.write ℓ + Matrix.of fun _ => b.write ℓ := by
  rw [f_VO_bla K ℓ (n * θ.read ℓ + Matrix.of fun _ => b.read ℓ)
    (n * (θ.headsVO K).read ℓ + Matrix.of fun _ => (b.headsVO K).read ℓ) (θ.write ℓ)
    ((θ.headsVO K).write ℓ) ?_ ?_ ?_ ?_]
  · rfl
  · intro t i k
    rfl
  · intro t i k
    rfl
  · -- the value columns: `(n W_V + b_V) K = n (W_V K) + b_V K`
    intro t i k
    show ∑ a, n t a * (∑ k', θ.read ℓ a (i, Sum.inr (Sum.inr k'))
          * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) k' k)
        + ∑ k', b.read ℓ (i, Sum.inr (Sum.inr k')) * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) k' k
      = ∑ a', (∑ a, n t a * θ.read ℓ a (i, Sum.inr (Sum.inr a'))
          + b.read ℓ (i, Sum.inr (Sum.inr a'))) * (K ℓ i : Matrix (dh ℓ) (dh ℓ) ℝ) a' k
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  · intro i k c
    rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the attention weights do not change when a function `r t` of the row alone is added
to the scores: numerator and denominator of row `t` are multiplied by `e^{r t}`. -/
private theorem attnWeights_add_row_bla (Z Z' : Matrix T T ℝ) (r : T → ℝ)
    (hZ : ∀ t s, Z' t s = Z t s + r t) :
    attnWeights sees Z' = attnWeights sees Z := by
  ext t s
  simp only [attnWeights, Matrix.of_apply, hZ, Real.exp_add]
  split_ifs with h
  · -- the denominator is multiplied by `e^{r t}` too
    have e : (∑ s', if sees t s' then Real.exp (Z t s') * Real.exp (r t) else 0)
        = (∑ s', if sees t s' then Real.exp (Z t s') else 0) * Real.exp (r t) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s' _ => ?_
      split_ifs
      · rfl
      · rw [zero_mul]
    rw [e, mul_div_mul_right _ _ (Real.exp_pos _).ne']
  · rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `attnWeights_den_pos_ba` of `Absorb/BiasesAttention.lean`): the
denominator of row `t` of the weights is positive when token `t` sees some token. -/
private theorem attnWeights_den_pos_bla (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
    0 < ∑ s', if sees t s' then Real.exp (Z t s') else 0 := by
  obtain ⟨s, hs⟩ := ht
  refine Finset.sum_pos' (fun s' _ => ?_) ⟨s, Finset.mem_univ _, ?_⟩
  · split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  · simp only [hs, ite_true]
    exact Real.exp_pos _

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `attnWeights_sum_ba` of `Absorb/BiasesAttention.lean`): row `t` of the
weights sums to `1` when token `t` sees some token. -/
private theorem attnWeights_sum_bla (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
    ∑ s, attnWeights sees Z t s = 1 := by
  have hS := attnWeights_den_pos_bla Z t ht
  have h1 : ∀ s, attnWeights sees Z t s = (if sees t s then Real.exp (Z t s) else 0)
      / ∑ s', if sees t s' then Real.exp (Z t s') else 0 := by
    intro s
    simp only [attnWeights, Matrix.of_apply]
    split_ifs
    · rfl
    · rw [zero_div]
  simp only [h1, ← Finset.sum_div]
  exact div_self hS.ne'

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] [(ℓ : Fin L) → DecidableEq (dh ℓ)] in
/-- Helper: the map `f ℓ` is the same on `M'` and `M` if the keys of head `i` of `M'` are those
of `M` shifted by `κ_i` and the queries and values are those of `M`: the score of `(t, s)` moves
by `q_t · κ_i / √d_h`, the same for every `s`. -/
private theorem f_keyShift_bla (ℓ : Fin L) (M M' : Matrix T (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) ℝ)
    (κ : H ℓ → dh ℓ → ℝ)
    (hq : ∀ t i k, M' t (i, Sum.inl k) = M t (i, Sum.inl k))
    (hk : ∀ t i k, M' t (i, Sum.inr (Sum.inl k)) = M t (i, Sum.inr (Sum.inl k)) + κ i k)
    (hv : ∀ t i k, M' t (i, Sum.inr (Sum.inr k)) = M t (i, Sum.inr (Sum.inr k))) :
    (Arch.attention sees χ H dh).f ℓ M' = (Arch.attention sees χ H dh).f ℓ M := by
  -- the weights of every head are kept
  have hsc : ∀ i : H ℓ, attnWeights sees (Matrix.of fun t' s' =>
        (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
        * ∑ k, M' t' (i, Sum.inl k) * M' s' (i, Sum.inr (Sum.inl k)) : Matrix T T ℝ)
      = attnWeights sees (Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
        * ∑ k, M t' (i, Sum.inl k) * M s' (i, Sum.inr (Sum.inl k))) := by
    intro i
    refine attnWeights_add_row_bla _ _
      (fun t' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹ * ∑ k, M t' (i, Sum.inl k) * κ i k)
      fun t' s' => ?_
    simp only [Matrix.of_apply, hq, hk, mul_add, Finset.sum_add_distrib]
  ext t p
  show ∑ s, attnWeights sees (Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
        * ∑ k, M' t' (p.1, Sum.inl k) * M' s' (p.1, Sum.inr (Sum.inl k))) t s
      * M' s (p.1, Sum.inr (Sum.inr p.2))
    = ∑ s, attnWeights sees (Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
        * ∑ k, M t' (p.1, Sum.inl k) * M s' (p.1, Sum.inr (Sum.inl k))) t s
      * M s (p.1, Sum.inr (Sum.inr p.2))
  rw [hsc p.1]
  simp only [hv]

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] [(ℓ : Fin L) → DecidableEq (dh ℓ)] in
/-- Helper: if every token sees some token, `f ℓ M' = f ℓ M + 1 ν` when the values of head `i`
of `M'` are those of `M` shifted by `ν_i` and the queries and keys are those of `M`: the weights
are kept, and they sum to `1` on every row. -/
private theorem f_valueShift_bla (hsee : ∀ t, ∃ s, sees t s) (ℓ : Fin L)
    (M M' : Matrix T (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) ℝ) (ν : H ℓ → dh ℓ → ℝ)
    (hq : ∀ t i k, M' t (i, Sum.inl k) = M t (i, Sum.inl k))
    (hk : ∀ t i k, M' t (i, Sum.inr (Sum.inl k)) = M t (i, Sum.inr (Sum.inl k)))
    (hv : ∀ t i k, M' t (i, Sum.inr (Sum.inr k)) = M t (i, Sum.inr (Sum.inr k)) + ν i k) :
    (Arch.attention sees χ H dh).f ℓ M'
      = (Arch.attention sees χ H dh).f ℓ M + Matrix.of fun _ (q : H ℓ × dh ℓ) => ν q.1 q.2 := by
  -- the scores of every head are kept
  have hsc : ∀ i : H ℓ, (Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
        * ∑ k, M' t' (i, Sum.inl k) * M' s' (i, Sum.inr (Sum.inl k)) : Matrix T T ℝ)
      = Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
        * ∑ k, M t' (i, Sum.inl k) * M s' (i, Sum.inr (Sum.inl k)) := by
    intro i
    ext t' s'
    simp only [Matrix.of_apply, hq, hk]
  ext t p
  show ∑ s, attnWeights sees (Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
        * ∑ k, M' t' (p.1, Sum.inl k) * M' s' (p.1, Sum.inr (Sum.inl k))) t s
      * M' s (p.1, Sum.inr (Sum.inr p.2))
    = ∑ s, attnWeights sees (Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
        * ∑ k, M t' (p.1, Sum.inl k) * M s' (p.1, Sum.inr (Sum.inl k))) t s
      * M s (p.1, Sum.inr (Sum.inr p.2)) + ν p.1 p.2
  rw [hsc p.1]
  -- the weights of row `t` sum to `1`
  simp only [hv, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    attnWeights_sum_bla _ t (hsee t), one_mul]

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] [(ℓ : Fin L) → DecidableEq (dh ℓ)] in
/-- Helper: the shifts `κ` of the key biases keep the map of every block. -/
private theorem block_keyShift_bla (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (b : Biases (Arch.attention sees χ H dh) dOut) (κ : ∀ ℓ, H ℓ → dh ℓ → ℝ) (ℓ : Fin L)
    (n : Matrix T d ℝ) :
    (Arch.attention sees χ H dh).f ℓ (n * θ.read ℓ
          + Matrix.of fun _ => (b.keyShift κ).read ℓ) * θ.write ℓ
        + Matrix.of (fun _ => (b.keyShift κ).write ℓ)
      = (Arch.attention sees χ H dh).f ℓ (n * θ.read ℓ + Matrix.of fun _ => b.read ℓ)
          * θ.write ℓ + Matrix.of fun _ => b.write ℓ := by
  -- the keys of head `i` move by `κ_i`, the queries and values do not move
  rw [f_keyShift_bla ℓ (n * θ.read ℓ + Matrix.of fun _ => b.read ℓ) _ (κ ℓ) ?_ ?_ ?_]
  · rfl
  · intro t i k
    rfl
  · intro t i k
    show (n * θ.read ℓ) t (i, Sum.inr (Sum.inl k)) + (b.read ℓ (i, Sum.inr (Sum.inl k)) + κ ℓ i k)
      = (n * θ.read ℓ) t (i, Sum.inr (Sum.inl k)) + b.read ℓ (i, Sum.inr (Sum.inl k)) + κ ℓ i k
    rw [add_assoc]
  · intro t i k
    rfl

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] [(ℓ : Fin L) → DecidableEq (dh ℓ)] in
/-- Helper: the value biases moved by `ν` into the output bias keep the map of every block, if
every token sees a token. -/
private theorem block_valueShift_bla (hsee : ∀ t, ∃ s, sees t s)
    (θ : Params (Arch.attention sees χ H dh) dIn dOut)
    (b : Biases (Arch.attention sees χ H dh) dOut) (ν : ∀ ℓ, H ℓ → dh ℓ → ℝ) (ℓ : Fin L)
    (n : Matrix T d ℝ) :
    (Arch.attention sees χ H dh).f ℓ (n * θ.read ℓ
          + Matrix.of fun _ => (b.valueShift θ ν).read ℓ) * θ.write ℓ
        + Matrix.of (fun _ => (b.valueShift θ ν).write ℓ)
      = (Arch.attention sees χ H dh).f ℓ (n * θ.read ℓ + Matrix.of fun _ => b.read ℓ)
          * θ.write ℓ + Matrix.of fun _ => b.write ℓ := by
  -- the values of head `i` move by `ν_i`, the queries and keys do not move
  rw [f_valueShift_bla hsee ℓ (n * θ.read ℓ + Matrix.of fun _ => b.read ℓ) _ (ν ℓ) ?_ ?_ ?_]
  · -- the output moves by `∑_i ν_i W_{O,i}`, the write bias by the opposite
    rw [Matrix.add_mul, add_assoc]
    congr 1
    ext t c
    show (∑ q : H ℓ × dh ℓ, ν ℓ q.1 q.2 * θ.write ℓ q c)
        + (b.write ℓ c - ∑ i, ∑ k, ν ℓ i k * θ.write ℓ (i, k) c) = b.write ℓ c
    rw [Fintype.sum_prod_type]
    ring
  · intro t i k
    rfl
  · intro t i k
    rfl
  · intro t i k
    show (n * θ.read ℓ) t (i, Sum.inr (Sum.inr k)) + (b.read ℓ (i, Sum.inr (Sum.inr k)) + ν ℓ i k)
      = (n * θ.read ℓ) t (i, Sum.inr (Sum.inr k)) + b.read ℓ (i, Sum.inr (Sum.inr k)) + ν ℓ i k
    rw [add_assoc]

omit [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: every map `actGL_bla K N κ ν` keeps the map of every block, if every token sees a
token: the four steps each keep it. -/
private theorem block_act_bla (hsee : ∀ t, ∃ s, sees t s) (K N : ∀ ℓ, H ℓ → GL (dh ℓ) ℝ)
    (κ ν : ∀ ℓ, H ℓ → dh ℓ → ℝ)
    (q : Params (Arch.attention sees χ H dh) dIn dOut
      × Biases (Arch.attention sees χ H dh) dOut) (ℓ : Fin L) (n : Matrix T d ℝ) :
    (Arch.attention sees χ H dh).f ℓ (n * (actGL_bla K N κ ν q).1.read ℓ
          + Matrix.of fun _ => (actGL_bla K N κ ν q).2.read ℓ) * (actGL_bla K N κ ν q).1.write ℓ
        + Matrix.of (fun _ => (actGL_bla K N κ ν q).2.write ℓ)
      = (Arch.attention sees χ H dh).f ℓ (n * q.1.read ℓ + Matrix.of fun _ => q.2.read ℓ)
          * q.1.write ℓ + Matrix.of fun _ => q.2.write ℓ :=
  (block_valueShift_bla hsee _ _ ν ℓ n).trans ((block_keyShift_bla _ _ κ ℓ n).trans
    ((block_headsVOB_bla _ _ N ℓ n).trans (block_headsQKB_bla q.1 q.2 K ℓ n)))

/-! ### Helpers: the parts of `headsAct σ q` -/

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write bias of `headsAct σ q` is that of `q` minus `∑_i ν_i W'_{O,i}`, with `W'`
the new write. -/
private theorem headsAct_biasWrite_bla (σ : HeadsSpace H dh)
    (q : Params (Arch.attention sees χ H dh) dIn dOut
      × Biases (Arch.attention sees χ H dh) dOut) (ℓ : Fin L) (c : d) :
    (headsAct σ q).2.write ℓ c
      = q.2.write ℓ c - ∑ i, ∑ k, σ.2.2.2 ℓ i k * (headsAct σ q).1.write ℓ (i, k) c := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]
  [(ℓ : Fin L) → Fintype (H ℓ)] [(ℓ : Fin L) → Fintype (dh ℓ)]
  [(ℓ : Fin L) → DecidableEq (dh ℓ)] in
/-- Helper: the rows `(i, ·)` of `W` multiplied by a matrix `P_i` lie in the span of the rows of
`W`. -/
private theorem span_heads_le_bla {I n m : Type*} [Fintype n] (P : I → Matrix n n ℝ)
    (W : Matrix (I × n) m ℝ) :
    Submodule.span ℝ (Set.range
        (Matrix.of fun (p : I × n) c => ∑ k', P p.1 p.2 k' * W (p.1, k') c).row)
      ≤ Submodule.span ℝ (Set.range W.row) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨i, k⟩, rfl⟩
  -- the new row `(i, k)` is `∑_{k'} P_{i,k k'} W_{(i, k')}`
  have h : (Matrix.of fun (p : I × n) c => ∑ k', P p.1 p.2 k' * W (p.1, k') c).row (i, k)
      = ∑ k', P i k k' • W.row (i, k') := by
    funext c
    simp only [Matrix.row_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h]
  exact Submodule.sum_mem _ fun k' _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, k'), rfl⟩)

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]
  [(ℓ : Fin L) → Fintype (H ℓ)] [(ℓ : Fin L) → Fintype (dh ℓ)]
  [(ℓ : Fin L) → DecidableEq (dh ℓ)] in
/-- Helper: the rows `(i, ·)` of `W` multiplied by an invertible matrix `G_i` span the space of
the rows of `W`: each is a combination of the other, with `G_i` and with `G_i⁻¹`. -/
private theorem span_heads_bla {I n m : Type*} [Fintype n] [DecidableEq n] (G : I → GL n ℝ)
    (W : Matrix (I × n) m ℝ) :
    Submodule.span ℝ (Set.range (Matrix.of fun (p : I × n) c =>
        ∑ k', ((G p.1 : GL n ℝ) : Matrix n n ℝ) p.2 k' * W (p.1, k') c).row)
      = Submodule.span ℝ (Set.range W.row) := by
  refine le_antisymm (span_heads_le_bla (fun i => ((G i : GL n ℝ) : Matrix n n ℝ)) W) ?_
  -- `W` is `G_i⁻¹` times the new rows, head by head
  have h : W = Matrix.of fun (p : I × n) c =>
      ∑ k', (((G p.1)⁻¹ : GL n ℝ) : Matrix n n ℝ) p.2 k'
        * (Matrix.of fun (p : I × n) c =>
          ∑ k', ((G p.1 : GL n ℝ) : Matrix n n ℝ) p.2 k' * W (p.1, k') c) (p.1, k') c := by
    ext ⟨i, k⟩ c
    have e : ((((G i)⁻¹ : GL n ℝ) : Matrix n n ℝ)
        *ᵥ (((G i : GL n ℝ) : Matrix n n ℝ) *ᵥ fun k' => W (i, k') c)) k = W (i, k) c := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact e.symm
  calc Submodule.span ℝ (Set.range W.row)
      = Submodule.span ℝ (Set.range (Matrix.of fun (p : I × n) c =>
          ∑ k', (((G p.1)⁻¹ : GL n ℝ) : Matrix n n ℝ) p.2 k'
            * (Matrix.of fun (p : I × n) c =>
              ∑ k', ((G p.1 : GL n ℝ) : Matrix n n ℝ) p.2 k' * W (p.1, k') c) (p.1, k') c).row) :=
        by rw [← h]
    _ ≤ _ := span_heads_le_bla (fun i => (((G i)⁻¹ : GL n ℝ) : Matrix n n ℝ)) _

/-- **The symmetries inside attention heads with biases act block by block,** when every token
sees a token. -/
theorem insideBlocksLocal_heads (hsee : ∀ t, ∃ s, sees t s) :
    InsideBlocksLocal (A := Arch.attention (T := T) (d := d) sees χ H dh) (dIn := dIn)
      (dOut := dOut) headsAct (headsSet H dh) := by
  refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · -- the map of a block: the four steps each keep it
    intro σ _ q ℓ n
    rw [headsAct_apply_bla]
    exact block_act_bla hsee _ _ _ _ q ℓ n
  · -- the reads through the reads, the writes through the writes, the read biases through the
    -- read biases; the write biases move by `−∑_i ν_i W'_{O,i}`, with the new writes `W'`
    intro σ _ q q' hr hw hb
    have hW : (headsAct σ q).1.write = (headsAct σ q').1.write := by
      unfold headsAct Params.headsVO Params.headsQK
      rw [hw]
    refine ⟨?_, hW, ?_, ?_⟩
    · unfold headsAct Params.headsVO Params.headsQK
      rw [hr]
    · unfold headsAct Biases.valueShift Biases.keyShift Biases.headsVO Biases.headsQK
      rw [hb]
    · funext ℓ c
      simp only [Pi.sub_apply]
      rw [headsAct_biasWrite_bla, headsAct_biasWrite_bla, hW]
      ring
  · -- the rows of head `i` of the new write are `K'_i⁻¹` times those of the old one
    intro σ _ q ℓ
    exact span_heads_bla (fun i => (glOfMatrix (σ.2.1 ℓ i))⁻¹) (q.1.write ℓ)

end Skips
