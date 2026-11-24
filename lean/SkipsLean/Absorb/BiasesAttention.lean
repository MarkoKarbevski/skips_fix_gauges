import SkipsLean.Absorb.BiasesConstructions

/-!
# Attention blocks with biases never absorb a linear term

Paper (absorb paper), Appendix C. Theorem C.1 (Exact absorption with biases): "Let blocks have
biases, and let `M ≠ 0`. […] (ii) No tanh block and no attention block as above absorbs `x M`, at
any width." For attention, "A block absorbs `x M`, for `M ≠ 0`, if a block of the same kind with
biases satisfies […], with the same mask, `h M + B_θ(h) = B_{θ′}(h)` for all
`h ∈ ℝ^{T × d_model}`", and "as above" is: "These scores do not depend on the positions of the
tokens".

Proof of Theorem C.1 (ii), "Attention": "Suppose that `h M + B_θ(h) = B_{θ′}(h)` for all `h`, and
let `C` and `C′` be the sums of the value–output products `W_{V,i} W_{O,i}` of the heads of `θ` and
of `θ′`. If all rows of `h` equal `x`, all keys of a head are equal, so each row of `P_i(h)` is
uniform on the tokens it sees, and all values equal `x W_{V,i} + b_{V,i}`. So every row of `B_θ(h)`
is `x C` plus a constant row, and the equation gives `M = C′ − C`. Now add `ϵδ` to the first row of
this `h`, for a row `δ`, and look at the second row, which sees the first token with or without a
causal mask. […] Hence `δ C = δ C′` for every `δ`, so `C = C′` and `M = 0`, a contradiction."

The proof uses the mask through one pair of tokens only (the second token sees the first). So the
statement is for any mask in which some token sees another token, and the paper's two masks on at
least two tokens are stated by name (no mask: `sees = fun _ _ => True`; the causal mask on `Fin n`:
`sees t s` is `s ≤ t`). The two blocks may have any numbers of heads and any head dimensions. If
every token sees itself only (one token, for the paper's masks), the block is affine in `h` and
absorbs `h M` with more heads; the paper's theorem does not state a number of tokens.

The block with biases is `attentionBlockB` (`Absorb/BiasesConstructions.lean`).
-/

namespace Skips

open Matrix

/-- The denominator of row `t` of the weights is positive when token `t` sees some token. -/
private theorem attnWeights_den_pos_ba {T : Type*} [Fintype T] (sees : T → T → Prop)
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
private theorem attnWeights_sum_ba {T : Type*} [Fintype T] (sees : T → T → Prop)
    [DecidableRel sees] (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
    ∑ s, attnWeights sees Z t s = 1 := by
  have hS := attnWeights_den_pos_ba sees Z t ht
  have h1 : ∀ s, attnWeights sees Z t s = (if sees t s then Real.exp (Z t s) else 0)
      / ∑ s', if sees t s' then Real.exp (Z t s') else 0 := by
    intro s
    simp only [attnWeights, Matrix.of_apply]
    split_ifs
    · rfl
    · rw [zero_div]
  simp only [h1, ← Finset.sum_div]
  exact div_self hS.ne'

/-- If all scores of row `t` are equal, every token that `t` sees has the weight `1 / n_t`, with
`n_t` the number of tokens that `t` sees. -/
private theorem attnWeights_const_row_ba {T : Type*} [Fintype T] (sees : T → T → Prop)
    [DecidableRel sees] (Z : Matrix T T ℝ) (t : T) (z : ℝ) (hZ : ∀ s, Z t s = z) (s : T)
    (hs : sees t s) :
    attnWeights sees Z t s = (∑ s', if sees t s' then (1 : ℝ) else 0)⁻¹ := by
  simp only [attnWeights, Matrix.of_apply, hs, ite_true, hZ]
  have e : (∑ s', if sees t s' then Real.exp z else 0)
      = Real.exp z * ∑ s', if sees t s' then (1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    simp only [mul_ite, mul_one, mul_zero]
  rw [e, div_mul_cancel_left₀ (Real.exp_pos z).ne']

/-- An entry of the weights of scores that are continuous in `ε` is continuous in `ε`. -/
private theorem continuous_attnWeights_ba {T : Type*} [Fintype T] (sees : T → T → Prop)
    [DecidableRel sees] (Z : ℝ → Matrix T T ℝ) (hZ : ∀ t s, Continuous fun ε => Z ε t s)
    (t s : T) :
    Continuous fun ε => attnWeights sees (Z ε) t s := by
  simp only [attnWeights, Matrix.of_apply]
  by_cases hs : sees t s
  · simp only [hs, ite_true]
    refine (hZ t s).rexp.div (continuous_finsetSum _ fun s' _ => ?_)
      fun ε => (attnWeights_den_pos_ba sees (Z ε) t ⟨s, hs⟩).ne'
    by_cases hs' : sees t s'
    · simp only [hs', ite_true]
      exact (hZ t s').rexp
    · simp only [hs', ite_false]
      exact continuous_const
  · simp only [hs, ite_false]
    exact continuous_const

/-- The scores of head `i` of an attention block with biases at the input `h`. -/
private noncomputable def scoresB_ba {T d H dh : Type*} [Fintype d] [Fintype dh]
    (WQ WK : H → Matrix d dh ℝ) (bQ bK : H → dh → ℝ) (h : Matrix T d ℝ) (i : H) :
    Matrix T T ℝ :=
  (Real.sqrt (Fintype.card dh))⁻¹ •
    ((h * WQ i + Matrix.of fun _ => bQ i) * (h * WK i + Matrix.of fun _ => bK i)ᵀ)

/-- The weights of head `i` at the input `ε H₀` are continuous in `ε`. -/
private theorem continuous_weight_ba {T d H dh : Type*} [Fintype T] [Fintype d] [Fintype dh]
    (sees : T → T → Prop) [DecidableRel sees] (WQ WK : H → Matrix d dh ℝ)
    (bQ bK : H → dh → ℝ) (H₀ : Matrix T d ℝ) (i : H) (t s : T) :
    Continuous fun ε : ℝ => attnWeights sees (scoresB_ba WQ WK bQ bK (ε • H₀) i) t s := by
  refine continuous_attnWeights_ba sees _ (fun t' s' => ?_) t s
  have hZ : Continuous fun ε : ℝ => scoresB_ba WQ WK bQ bK (ε • H₀) i := by
    unfold scoresB_ba
    fun_prop
  exact hZ.matrix_elem t' s'

/-- At the input `0`, all scores of a row are equal, so a seen token has the weight `1 / n_t`. -/
private theorem attnWeights_scoresB_zero_ba {T d H dh : Type*} [Fintype T] [Fintype d]
    [Fintype dh] (sees : T → T → Prop) [DecidableRel sees] (WQ WK : H → Matrix d dh ℝ)
    (bQ bK : H → dh → ℝ) (i : H) (t s : T) (hs : sees t s) :
    attnWeights sees (scoresB_ba WQ WK bQ bK (0 : Matrix T d ℝ) i) t s
      = (∑ s', if sees t s' then (1 : ℝ) else 0)⁻¹ := by
  refine attnWeights_const_row_ba sees _ t (scoresB_ba WQ WK bQ bK (0 : Matrix T d ℝ) i t t)
    (fun s' => ?_) s hs
  simp only [scoresB_ba, Matrix.zero_mul, zero_add, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.of_apply]

/-- A row of a sum of matrices. -/
private theorem sum_row_ba {T d H : Type*} [Fintype H] (A : H → Matrix T d ℝ) (t : T) :
    (∑ i, A i) t = ∑ i, A i t :=
  Finset.sum_apply t _ _

/-- Row `t` of a head with a value bias, when row `t` of the weights sums to `1`. -/
private theorem headB_row_ba {T d dh : Type*} [Fintype T] [Fintype d] [Fintype dh]
    (P : Matrix T T ℝ) (h : Matrix T d ℝ) (WV : Matrix d dh ℝ) (bV : dh → ℝ)
    (WO : Matrix dh d ℝ) (t : T) (hP : ∑ s, P t s = 1) :
    (P * (h * WV + Matrix.of fun _ => bV) * WO : Matrix T d ℝ) t
      = (∑ s, P t s • h s) ᵥ* (WV * WO) + bV ᵥ* WO := by
  have hV : ∀ s, (h * WV + Matrix.of fun _ => bV : Matrix T dh ℝ) s = h s ᵥ* WV + bV := fun s => by
    rw [← Matrix.mul_apply_eq_vecMul]
    rfl
  rw [Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul, Matrix.vecMul_eq_sum (P t)]
  simp only [hV, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hP, one_smul,
    Matrix.add_vecMul, ← Matrix.vecMul_vecMul, Matrix.sum_vecMul, Matrix.smul_vecMul]

/-- **Row `t` of an attention block with biases**, at a token `t` that sees some token:
`∑_i (∑_s P_i(h)_{ts} h_s) W_{V,i} W_{O,i} + κ`, with `κ = ∑_i b_{V,i} W_{O,i} + b_O`. -/
private theorem attentionBlockB_row_ba {T d H dh : Type*} [Fintype T] [Fintype d] [Fintype H]
    [Fintype dh] (sees : T → T → Prop) [DecidableRel sees] (WQ WK WV : H → Matrix d dh ℝ)
    (bQ bK bV : H → dh → ℝ) (WO : H → Matrix dh d ℝ) (bO : d → ℝ) (h : Matrix T d ℝ) (t : T)
    (ht : ∃ s, sees t s) :
    attentionBlockB sees WQ WK WV bQ bK bV WO bO h t
      = ∑ i, (∑ s, attnWeights sees (scoresB_ba WQ WK bQ bK h i) t s • h s) ᵥ* (WV i * WO i)
        + (∑ i, bV i ᵥ* WO i + bO) := by
  have e : attentionBlockB sees WQ WK WV bQ bK bV WO bO h t
      = (∑ i, attnWeights sees (scoresB_ba WQ WK bQ bK h i)
          * (h * WV i + Matrix.of fun _ => bV i) * WO i : Matrix T d ℝ) t + bO := rfl
  rw [e, sum_row_ba, Finset.sum_congr rfl fun i _ => headB_row_ba
    (attnWeights sees (scoresB_ba WQ WK bQ bK h i)) h (WV i) (bV i) (WO i) t
    (attnWeights_sum_ba sees _ t ht), Finset.sum_add_distrib, add_assoc]

/-- Matrices with the same products `u A = u B` for all `u` are equal. -/
private theorem eq_of_vecMul_eq_ba {m n : Type*} [Fintype m] [DecidableEq m]
    {A B : Matrix m n ℝ} (h : ∀ u, u ᵥ* A = u ᵥ* B) : A = B := by
  ext a b
  have hb := congrFun (h (Pi.single a 1)) b
  simpa only [single_vecMul, one_smul, Matrix.row_apply] using hb

/-- Row `t` of a sum of matrices `A + B`. -/
private theorem add_row_ba {T d : Type*} (A B : Matrix T d ℝ) (t : T) :
    (A + B) t = A t + B t := rfl

/-- **Proof of Theorem C.1 (ii), attention:** if `h M + B_θ(h) = B_θ'(h)` for every `h`, and a
token `t₂` sees another token `t₁`, then `M = 0`. -/
private theorem eq_zero_of_forall_ba {T d H dh H' dh' : Type*} [Fintype T] [Fintype d]
    [Fintype H] [Fintype dh] [Fintype H'] [Fintype dh'] (sees : T → T → Prop)
    [DecidableRel sees] {t₁ t₂ : T} (h12 : t₁ ≠ t₂) (hs : sees t₂ t₁)
    (WQ WK WV : H → Matrix d dh ℝ) (bQ bK bV : H → dh → ℝ) (WO : H → Matrix dh d ℝ)
    (bO : d → ℝ) (WQ' WK' WV' : H' → Matrix d dh' ℝ) (bQ' bK' bV' : H' → dh' → ℝ)
    (WO' : H' → Matrix dh' d ℝ) (bO' : d → ℝ) (M : Matrix d d ℝ)
    (hall : ∀ h : Matrix T d ℝ, h * M + attentionBlockB sees WQ WK WV bQ bK bV WO bO h
      = attentionBlockB sees WQ' WK' WV' bQ' bK' bV' WO' bO' h) : M = 0 := by
  classical
  have ht : ∃ s, sees t₂ s := ⟨t₁, hs⟩
  -- row `t₂` of the equation, with the rows of both blocks
  have hrow : ∀ h : Matrix T d ℝ, h t₂ ᵥ* M
      + (∑ i, (∑ s, attnWeights sees (scoresB_ba WQ WK bQ bK h i) t₂ s • h s) ᵥ* (WV i * WO i)
        + (∑ i, bV i ᵥ* WO i + bO))
      = ∑ j, (∑ s, attnWeights sees (scoresB_ba WQ' WK' bQ' bK' h j) t₂ s • h s)
          ᵥ* (WV' j * WO' j) + (∑ j, bV' j ᵥ* WO' j + bO') := by
    intro h
    have e := congrFun (hall h) t₂
    rw [add_row_ba, Matrix.mul_apply_eq_vecMul,
      attentionBlockB_row_ba sees WQ WK WV bQ bK bV WO bO h t₂ ht,
      attentionBlockB_row_ba sees WQ' WK' WV' bQ' bK' bV' WO' bO' h t₂ ht] at e
    exact e
  generalize ∑ i, bV i ᵥ* WO i + bO = κ at hrow
  generalize ∑ j, bV' j ᵥ* WO' j + bO' = κ' at hrow
  -- Step 1 (all rows equal `x`): the weights of a row sum to `1`, so `x M + x C + κ = x C' + κ'`
  have h1 : ∀ x : d → ℝ, x ᵥ* M + (x ᵥ* ∑ i, WV i * WO i + κ)
      = x ᵥ* ∑ j, WV' j * WO' j + κ' := by
    intro x
    have e := hrow (Matrix.of fun _ => x)
    have hx : ∀ s, (Matrix.of fun _ : T => x) s = x := fun s => rfl
    simp only [hx, ← Finset.sum_smul, attnWeights_sum_ba sees _ t₂ ht, one_smul,
      ← Matrix.vecMul_sum] at e
    exact e
  -- at `x = 0`: `κ = κ'`
  have hκ : κ = κ' := by simpa only [Matrix.zero_vecMul, zero_add] using h1 0
  subst hκ
  -- the number `n₂` of tokens that `t₂` sees is positive
  have hN : 0 < ∑ s', if sees t₂ s' then (1 : ℝ) else 0 := by
    refine Finset.sum_pos' (fun s' _ => ?_) ⟨t₁, Finset.mem_univ _, ?_⟩
    · split_ifs
      · exact zero_le_one
      · exact le_rfl
    · simp only [hs, ite_true]
      exact one_pos
  -- Steps 2 and 3: `δ C = δ C'` for every row `δ`
  have hC : ∀ δ : d → ℝ, δ ᵥ* ∑ i, WV i * WO i = δ ᵥ* ∑ j, WV' j * WO' j := by
    intro δ
    -- the input `H₀` whose row `t₁` is `δ` and whose other rows are `0`
    obtain ⟨H₀, hH₀⟩ : ∃ H₀ : Matrix T d ℝ, ∀ s, H₀ s = if s = t₁ then δ else 0 :=
      ⟨Matrix.of fun t => if t = t₁ then δ else 0, fun s => rfl⟩
    have hsum : ∀ (a : T → ℝ) (ε : ℝ), ∑ s, a s • (ε • H₀) s = ε • a t₁ • δ := by
      intro a ε
      have e : ∀ s, a s • (ε • H₀) s = if s = t₁ then ε • a t₁ • δ else 0 := by
        intro s
        show a s • ε • H₀ s = _
        rw [hH₀]
        split_ifs with hst
        · rw [hst, smul_comm]
        · rw [smul_zero, smul_zero]
      simp only [e, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hrow₂ : ∀ ε : ℝ, (ε • H₀) t₂ = 0 := by
      intro ε
      show ε • H₀ t₂ = 0
      simp only [hH₀, h12.symm, ite_false, smul_zero]
    -- Step 2: at the input `ε H₀`, `ε F(ε) + κ = ε F'(ε) + κ`
    have h2 : ∀ ε : ℝ, ε ≠ 0 →
        ∑ i, attnWeights sees (scoresB_ba WQ WK bQ bK (ε • H₀) i) t₂ t₁ • (δ ᵥ* (WV i * WO i))
          = ∑ j, attnWeights sees (scoresB_ba WQ' WK' bQ' bK' (ε • H₀) j) t₂ t₁
              • (δ ᵥ* (WV' j * WO' j)) := by
      intro ε hε
      have e := hrow (ε • H₀)
      simp only [hsum, hrow₂, Matrix.zero_vecMul, zero_add, Matrix.smul_vecMul,
        ← Finset.smul_sum] at e
      exact smul_right_injective (d → ℝ) hε (add_right_cancel e)
    -- Step 3: both sides are continuous in `ε`, so they agree at `ε = 0`
    have hc : Continuous fun ε : ℝ => ∑ i, attnWeights sees (scoresB_ba WQ WK bQ bK (ε • H₀) i)
        t₂ t₁ • (δ ᵥ* (WV i * WO i)) :=
      continuous_finsetSum _ fun i _ =>
        (continuous_weight_ba sees WQ WK bQ bK H₀ i t₂ t₁).smul continuous_const
    have hc' : Continuous fun ε : ℝ => ∑ j, attnWeights sees
        (scoresB_ba WQ' WK' bQ' bK' (ε • H₀) j) t₂ t₁ • (δ ᵥ* (WV' j * WO' j)) :=
      continuous_finsetSum _ fun j _ =>
        (continuous_weight_ba sees WQ' WK' bQ' bK' H₀ j t₂ t₁).smul continuous_const
    have hF := Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hc hc' fun ε hε => h2 ε hε
    have h0 := congrFun hF 0
    -- at `ε = 0` every weight of row `t₂` is `1 / n₂`
    simp only [zero_smul, attnWeights_scoresB_zero_ba sees _ _ _ _ _ t₂ t₁ hs,
      ← Finset.smul_sum, ← Matrix.vecMul_sum] at h0
    exact smul_right_injective (d → ℝ) (inv_ne_zero hN.ne') h0
  -- `C = C'` and `κ = κ'` in Step 1 give `x M = 0` for every `x`
  refine eq_of_vecMul_eq_ba fun x => ?_
  have e := h1 x
  rw [hC x] at e
  rw [Matrix.vecMul_zero]
  exact add_eq_right.mp e

/-- **Theorem C.1 (ii) of the absorb paper for attention blocks with biases:** with a mask in which
some token sees another token, no attention block with biases, with any number of heads and any
head dimension, absorbs `h M` with `M ≠ 0`. -/
theorem forall_exists_ne_attentionBlockB {T d H dh H' dh' : Type*} [Fintype T] [Fintype d]
    [Fintype H] [Fintype dh] [Fintype H'] [Fintype dh'] (sees : T → T → Prop)
    [DecidableRel sees] (hsees : ∃ t₁ t₂, t₁ ≠ t₂ ∧ sees t₂ t₁)
    (WQ WK WV : H → Matrix d dh ℝ) (bQ bK bV : H → dh → ℝ) (WO : H → Matrix dh d ℝ)
    (bO : d → ℝ) (WQ' WK' WV' : H' → Matrix d dh' ℝ) (bQ' bK' bV' : H' → dh' → ℝ)
    (WO' : H' → Matrix dh' d ℝ) (bO' : d → ℝ) (M : Matrix d d ℝ) (hM : M ≠ 0) :
    ∃ h : Matrix T d ℝ, h * M + attentionBlockB sees WQ WK WV bQ bK bV WO bO h
      ≠ attentionBlockB sees WQ' WK' WV' bQ' bK' bV' WO' bO' h := by
  obtain ⟨t₁, t₂, h12, hs⟩ := hsees
  exact not_forall.mp fun hall => hM (eq_zero_of_forall_ba sees h12 hs WQ WK WV bQ bK bV WO bO
    WQ' WK' WV' bQ' bK' bV' WO' bO' M hall)

/-- **Theorem C.1 (ii) for attention blocks with biases, without a mask:** on at least two tokens,
every token sees every token. -/
theorem forall_exists_ne_attentionBlockB_noMask {T d H dh H' dh' : Type*} [Fintype T] [Fintype d]
    [Fintype H] [Fintype dh] [Fintype H'] [Fintype dh'] (hT : 2 ≤ Fintype.card T)
    (WQ WK WV : H → Matrix d dh ℝ) (bQ bK bV : H → dh → ℝ) (WO : H → Matrix dh d ℝ)
    (bO : d → ℝ) (WQ' WK' WV' : H' → Matrix d dh' ℝ) (bQ' bK' bV' : H' → dh' → ℝ)
    (WO' : H' → Matrix dh' d ℝ) (bO' : d → ℝ) (M : Matrix d d ℝ) (hM : M ≠ 0) :
    ∃ h : Matrix T d ℝ,
      h * M + attentionBlockB (fun _ _ : T => True) WQ WK WV bQ bK bV WO bO h
        ≠ attentionBlockB (fun _ _ : T => True) WQ' WK' WV' bQ' bK' bV' WO' bO' h := by
  obtain ⟨t₁, t₂, h12⟩ := Fintype.exists_pair_of_one_lt_card hT
  exact forall_exists_ne_attentionBlockB _ ⟨t₁, t₂, h12, trivial⟩ WQ WK WV bQ bK bV WO bO
    WQ' WK' WV' bQ' bK' bV' WO' bO' M hM

/-- **Theorem C.1 (ii) for attention blocks with biases, with the causal mask:** on the tokens
`0, …, n − 1`, `n ≥ 2`, token `t` sees the tokens `s ≤ t`. -/
theorem forall_exists_ne_attentionBlockB_causal {n : ℕ} (hn : 2 ≤ n) {d H dh H' dh' : Type*}
    [Fintype d] [Fintype H] [Fintype dh] [Fintype H'] [Fintype dh']
    (WQ WK WV : H → Matrix d dh ℝ) (bQ bK bV : H → dh → ℝ) (WO : H → Matrix dh d ℝ)
    (bO : d → ℝ) (WQ' WK' WV' : H' → Matrix d dh' ℝ) (bQ' bK' bV' : H' → dh' → ℝ)
    (WO' : H' → Matrix dh' d ℝ) (bO' : d → ℝ) (M : Matrix d d ℝ) (hM : M ≠ 0) :
    ∃ h : Matrix (Fin n) d ℝ,
      h * M + attentionBlockB (fun t s : Fin n => s ≤ t) WQ WK WV bQ bK bV WO bO h
        ≠ attentionBlockB (fun t s : Fin n => s ≤ t) WQ' WK' WV' bQ' bK' bV' WO' bO' h := by
  -- token `1` sees token `0`
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := Fin.ne_of_val_ne zero_ne_one
  have hs : (⟨0, by omega⟩ : Fin n) ≤ ⟨1, by omega⟩ := Fin.mk_le_mk.2 zero_le_one
  exact forall_exists_ne_attentionBlockB _ ⟨_, _, h01, hs⟩ WQ WK WV bQ bK bV WO bO
    WQ' WK' WV' bQ' bK' bV' WO' bO' M hM

end Skips
