import SkipsLean.Imports
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# A level set that lies in images of a space of smaller dimension

Paper (dimension paper): Appendix B, proof of Proposition 4.6 (the equality condition and local
identifiability), the direction from local identifiability to the equality condition; the same
argument proves Proposition 4.5 of the skips paper:

"By the constant rank theorem, after shrinking `U`, the set `Z = {θ′ ∈ U : F_X(θ′) = F_X(θ)}` is
a connected manifold of dimension `P − r`, whose tangent space at each point is the kernel of the
Jacobian. For any further input `x`, the Jacobian on `X ∪ {x}` has rank `r` on `U` as well, so it
has the same kernel, and `θ′ ↦ F_{θ′}(x)` is constant on `Z`. […] Conversely, let every `θ′` in a
neighborhood of `θ` in `Z` be the image of `θ` under a symmetry. With the permutations and the
sign flips, the symmetries form a Lie group of dimension `k` with finitely many components, and
the images of `θ` under it form the image of a manifold of dimension `k` under a smooth map. By
Sard's theorem this image contains no open subset of a manifold of larger dimension, so
`P − r ≤ k`".

Stated here without manifolds and without the constant rank theorem, for maps between
finite-dimensional real spaces. `F` is the map of the outputs on a batch `X`, of class `C¹`, and
`θ₀` a point; `r` is the rank of its derivative at `θ₀`. The maps `g j` are the outputs on the
larger batches `X ∪ {x}`: the kernel of the derivative of `g j` lies in that of `F` at every
point, and its rank is at most `r` at every point (so `θ₀` is a point of the largest rank). The
images of `θ₀` under the symmetries are the union of the images of countably many maps `Φ i` of
class `C¹` on open subsets `Ω i` of a space `M` (of dimension `k`). If near `θ₀` every point with
`g j θ = g j θ₀` for all `j` is in one of these images, then the kernel of the derivative of `F` at
`θ₀` has dimension at most that of `M`: `P − r ≤ k`.

In place of Sard's theorem the proof can use the Hausdorff dimension (Mathlib:
`dimH_image_le_of_locally_lipschitzOn`, `dimH_iUnion`, `Real.dimH_of_nonempty_interior`): the
level set contains the image of a ball of the kernel under a map with a Lipschitz left inverse.
-/

namespace Skips

open Filter Topology

/-- **Proof of Proposition 4.6 (dimension paper) and of Proposition 4.5 (skips paper), from local
identifiability to the equality condition, for maps between finite-dimensional spaces:** let `F`
and the maps `g j` be of class `C¹`, with `ker Dg_j(θ) ⊆ ker DF(θ)` and
`rank Dg_j(θ) ≤ rank DF(θ₀)` at every `θ`. If every `θ` near `θ₀` with `g j θ = g j θ₀` for all
`j` lies in the image of one of countably many maps `Φ i` of class `C¹` on open subsets of `M`,
then `dim ker DF(θ₀) ≤ dim M`. -/
theorem finrank_ker_le_of_level_set_subset_iUnion_image
    {P Y Y' M : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Y'] [NormedSpace ℝ Y'] [FiniteDimensional ℝ Y']
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    {F : P → Y} (hF : ContDiff ℝ 1 F) (θ₀ : P)
    {J : Type*} (g : J → P → Y') (hg : ∀ j, ContDiff ℝ 1 (g j))
    (hker : ∀ j θ, LinearMap.ker (fderiv ℝ (g j) θ).toLinearMap
      ≤ LinearMap.ker (fderiv ℝ F θ).toLinearMap)
    (hrank : ∀ j θ, Module.finrank ℝ (LinearMap.range (fderiv ℝ (g j) θ).toLinearMap)
      ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ F θ₀).toLinearMap))
    {ι : Type*} [Countable ι] (Φ : ι → M → P) (Ω : ι → Set M) (hΩ : ∀ i, IsOpen (Ω i))
    (hΦ : ∀ i, ContDiffOn ℝ 1 (Φ i) (Ω i))
    (hloc : ∃ U ∈ 𝓝 θ₀, ∀ θ ∈ U, (∀ j, g j θ = g j θ₀) → ∃ i, ∃ m ∈ Ω i, Φ i m = θ) :
    Module.finrank ℝ (LinearMap.ker (fderiv ℝ F θ₀).toLinearMap) ≤ Module.finrank ℝ M := by
  sorry

end Skips
