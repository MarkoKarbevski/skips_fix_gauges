import SkipsLean.Network.Attention
import SkipsLean.Network.Analytic

/-!
# Attention blocks are real-analytic

Paper (dimension paper), Section 2: the attention block is one of the "analytic blocks"; the
proofs of the dimension paper use that the output of a network of such blocks is a real-analytic
function of the weights and of the input. For the attention block of `Network/Attention.lean`:
the weights of a matrix of scores are real-analytic in the scores (in a row of a token that sees
some token the denominator is positive; the row of a token that sees no token is `0`), and the
map `f_ℓ` of `Arch.attention` is real-analytic, for every mask.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d : Type*} {L : ℕ} [Fintype T]

/-- The attention weights are a real-analytic function of the matrix of scores, for every
mask. -/
theorem analyticOnNhd_attnWeights (sees : T → T → Prop) [DecidableRel sees] :
    AnalyticOnNhd ℝ (attnWeights sees : Matrix T T ℝ → Matrix T T ℝ) Set.univ := by
  sorry

/-- The map of an attention block of `Arch.attention` is real-analytic. -/
theorem analyticOnNhd_f_attention (sees : T → T → Prop) [DecidableRel sees]
    (χ : Matrix T d ℝ → Matrix T d ℝ) (H dh : Fin L → Type) [∀ ℓ, Fintype (H ℓ)]
    [∀ ℓ, Fintype (dh ℓ)] (ℓ : Fin L) :
    AnalyticOnNhd ℝ ((Arch.attention sees χ H dh).f ℓ) Set.univ := by
  sorry

/-- The map of an attention block of `Arch.attention` is differentiable. -/
theorem differentiable_f_attention (sees : T → T → Prop) [DecidableRel sees]
    (χ : Matrix T d ℝ → Matrix T d ℝ) (H dh : Fin L → Type) [∀ ℓ, Fintype (H ℓ)]
    [∀ ℓ, Fintype (dh ℓ)] (ℓ : Fin L) :
    Differentiable ℝ ((Arch.attention sees χ H dh).f ℓ) := by
  sorry

end Skips
