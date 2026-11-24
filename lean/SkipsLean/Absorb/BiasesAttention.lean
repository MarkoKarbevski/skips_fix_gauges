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
  sorry

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
  sorry

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
  sorry

end Skips
