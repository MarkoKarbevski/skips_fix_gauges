import SkipsLean.Network.Attention
import SkipsLean.Network.Analytic

/-!
# Attention blocks are real-analytic

Paper (skips paper), Section 1.1: "These five kinds of block are real-analytic, and we call them
analytic blocks" (attention, tanh, GELU, SwiGLU and GeGLU blocks). The proofs of both papers use
that the outputs of a network of such blocks are real-analytic in the weights (dimension paper,
proof of Proposition 4.6: "The outputs are analytic in `θ`"). For the attention block of
`Network/Attention.lean`:
the weights of a matrix of scores are real-analytic in the scores (in a row of a token that sees
some token the denominator is positive; the row of a token that sees no token is `0`), and the
map `f_ℓ` of `Arch.attention` is real-analytic, for every mask.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d : Type*} {L : ℕ} [Fintype T]

/-- The denominator of row `t` of the weights is positive when token `t` sees some token. -/
private theorem attnWeights_den_pos_ana (sees : T → T → Prop) [DecidableRel sees]
    (Z : Matrix T T ℝ) (t : T) (ht : ∃ s, sees t s) :
    0 < ∑ s', if sees t s' then Real.exp (Z t s') else 0 := by
  obtain ⟨s, hs⟩ := ht
  refine Finset.sum_pos' (fun s' _ => ?_) ⟨s, Finset.mem_univ _, ?_⟩
  · split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  · simp only [hs, ite_true]
    exact Real.exp_pos _

/-- An entry of the weights of analytic scores is analytic. -/
private theorem analyticOnNhd_attnWeights_entry_ana (sees : T → T → Prop) [DecidableRel sees]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Z : E → Matrix T T ℝ)
    (hZ : ∀ t s, AnalyticOnNhd ℝ (fun h => Z h t s) Set.univ) (t s : T) :
    AnalyticOnNhd ℝ (fun h => attnWeights sees (Z h) t s) Set.univ := by
  simp only [attnWeights, Matrix.of_apply]
  by_cases hs : sees t s
  · simp only [hs, ite_true]
    refine (hZ t s).rexp.div (Finset.analyticOnNhd_fun_sum _ fun s' _ => ?_)
      fun h _ => (attnWeights_den_pos_ana sees (Z h) t ⟨s, hs⟩).ne'
    by_cases hs' : sees t s'
    · simp only [hs', ite_true]
      exact (hZ t s').rexp
    · simp only [hs', ite_false]
      exact analyticOnNhd_const
  · simp only [hs, ite_false]
    exact analyticOnNhd_const

/-- The attention weights are a real-analytic function of the matrix of scores, for every
mask. -/
theorem analyticOnNhd_attnWeights (sees : T → T → Prop) [DecidableRel sees] :
    AnalyticOnNhd ℝ (attnWeights sees : Matrix T T ℝ → Matrix T T ℝ) Set.univ := by
  -- entry `(t, s)` of the weights of the scores `Z` is analytic in `Z`
  show AnalyticOnNhd ℝ (fun Z : Matrix T T ℝ => fun t => fun s => attnWeights sees Z t s)
    Set.univ
  exact AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun s =>
    analyticOnNhd_attnWeights_entry_ana sees id
      (fun t' s' => analyticOnNhd_matrix_entry t' s') t s

/-- The map of an attention block of `Arch.attention` is real-analytic. -/
theorem analyticOnNhd_f_attention (sees : T → T → Prop) [DecidableRel sees]
    (χ : Matrix T d ℝ → Matrix T d ℝ) (H dh : Fin L → Type) [∀ ℓ, Fintype (H ℓ)]
    [∀ ℓ, Fintype (dh ℓ)] (ℓ : Fin L) :
    AnalyticOnNhd ℝ ((Arch.attention sees χ H dh).f ℓ) Set.univ := by
  show AnalyticOnNhd ℝ (fun M : Matrix T (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) ℝ =>
    (Matrix.of fun t p =>
    ∑ s, attnWeights sees (Matrix.of fun t' s' => (Real.sqrt (Fintype.card (dh ℓ)))⁻¹
        * ∑ k, M t' (p.1, Sum.inl k) * M s' (p.1, Sum.inr (Sum.inl k))) t s
      * M s (p.1, Sum.inr (Sum.inr p.2)) : Matrix T (H ℓ × dh ℓ) ℝ)) Set.univ
  -- entry `(t, p)`: a sum over `s` of a weight times an entry of `M`
  refine AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun p => ?_
  simp only [Matrix.of_apply]
  refine Finset.analyticOnNhd_fun_sum _ fun s _ => ?_
  refine AnalyticOnNhd.mul ?_ (analyticOnNhd_matrix_entry s _)
  -- the weight is analytic since the scores are polynomials in the entries of `M`
  refine analyticOnNhd_attnWeights_entry_ana sees _ (fun t' s' => ?_) t s
  simp only [Matrix.of_apply]
  exact analyticOnNhd_const.mul (Finset.analyticOnNhd_fun_sum _ fun k _ =>
    (analyticOnNhd_matrix_entry t' _).mul (analyticOnNhd_matrix_entry s' _))

/-- The map of an attention block of `Arch.attention` is differentiable. -/
theorem differentiable_f_attention (sees : T → T → Prop) [DecidableRel sees]
    (χ : Matrix T d ℝ → Matrix T d ℝ) (H dh : Fin L → Type) [∀ ℓ, Fintype (H ℓ)]
    [∀ ℓ, Fintype (dh ℓ)] (ℓ : Fin L) :
    Differentiable ℝ ((Arch.attention sees χ H dh).f ℓ) :=
  fun M => ((analyticOnNhd_f_attention sees χ H dh ℓ) M (Set.mem_univ M)).differentiableAt

end Skips
