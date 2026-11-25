import SkipsLean.Symmetry.BiasesFlat
import SkipsLean.Dimension.FunctionalBiasesKinks

/-!
# Changes of basis and translations with biases are flat, for any blocks

Paper (skips paper), Lemma A.8 (Translations are not tied): "In a residual network with biases
and without normalization, adding a row `g` to the hidden states `h_ℓ, …, h_L` preserves the
function once the biases are adjusted, for every `ℓ = 0, …, L`." The lemma does not restrict the
kind of block.

`Symmetry/BiasesFlat.lean` proves that the directions of the changes of basis and of the
translations are flat for differentiable blocks. Here the same four statements without a
hypothesis on the blocks, so that they also serve ReLU, ReLU² and ReGLU blocks with biases
(twins of `cobDir_mem_flat_skipless'` and `cobDir_const_mem_flat_residual'` without biases); they
use `mem_flatB_of_hasDerivAt'` (`Dimension/FunctionalBiasesKinks.lean`). The bounds on the
functional dimension that follow, together with the symmetries inside blocks, are in
`Symmetry/InsideBlocksBiases.lean`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {A : Arch T d L} (p : ParamsB A dIn dOut)

/-- **The directions of the changes of basis are flat in a skipless network with biases,** for
any blocks, without normalization. -/
theorem cobDirB_mem_flatB_skipless' (hA : A.χ = id) (X : Fin (L + 1) → Matrix d d ℝ) :
    cobDirB p X ∈ flatB A 0 p := by
  sorry

/-- **The direction of one change of basis at all hidden states is flat in a residual network
with biases,** for any blocks, without normalization. -/
theorem cobDirB_const_mem_flatB_residual' (hA : A.χ = id) (X : Matrix d d ℝ) :
    cobDirB p (fun _ => X) ∈ flatB A 1 p := by
  sorry

/-- **Lemma A.8, first sentence, as flat directions, for any blocks:** the directions of the
translations of a residual network with biases are flat. -/
theorem translateDir_mem_flatB' (hA : A.χ = id) (g : Fin (L + 1) → d → ℝ) :
    ((0, translateDir p.1 g) : ParamsB A dIn dOut) ∈ flatB A 1 p := by
  sorry

/-- **The directions of the translations of the hidden states of a skipless network with biases
are flat,** for any blocks. -/
theorem translateAtDir_mem_flatB' (hA : A.χ = id) (g : Fin (L + 1) → d → ℝ) :
    ((0, translateAtDir p.1 g) : ParamsB A dIn dOut) ∈ flatB A 0 p := by
  sorry

end Skips
