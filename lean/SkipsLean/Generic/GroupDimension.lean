import SkipsLean.Generic.Cayley
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# The dimensions of the groups of changes of basis

Paper (skips paper): Theorem 3.3 (ii): "The changes of basis that preserve the function at all
parameters form a group of dimension `(L + 1) dim 𝒢` in a skipless network and `dim 𝒢` in a
residual one: `(L + 1) d_model²` and `d_model²` without normalization, and
`(L + 1) d_model (d_model − 1)/2` and `d_model (d_model − 1)/2` under pre-RMSNorm."

Here the four dimensions, for the sets of families `(m_1, …, m_n)` of `d × d` matrices: all
invertible, all orthogonal, all equal to one invertible matrix, all equal to one orthogonal
matrix. The dimension is the Hausdorff dimension of the set (Mathlib's `dimH`), for the metric of
the entrywise norm; for these sets, which are smooth submanifolds, it is the dimension of the
manifold. (Mathlib has no dimension of the orthogonal group as a Lie group; the Hausdorff
dimension is the notion that the proof of Proposition 4.5 uses in this library,
`Generic/LevelSetImages.lean`.) The invertible matrices are an open subset of the space of
matrices; the orthogonal group is covered by finitely many smooth images of the antisymmetric
matrices (`Generic/Cayley.lean`), and contains the image of the antisymmetric matrices under the
Cayley transform, which has a smooth inverse. Which changes of basis preserve the function of
which network: `Symmetry/CobGroup.lean`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise ENNReal

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The families of `n` invertible `d × d` matrices have dimension `n d²`. -/
theorem dimH_setOf_forall_isUnit_det (n : ℕ) :
    dimH {m : Fin n → Matrix d d ℝ | ∀ ℓ, IsUnit (m ℓ).det}
      = ((n * Fintype.card d ^ 2 : ℕ) : ℝ≥0∞) := by
  sorry

/-- The families of `n` orthogonal `d × d` matrices have dimension `n d (d − 1) / 2`. -/
theorem dimH_setOf_forall_mem_orthogonalGroup (n : ℕ) :
    dimH {m : Fin n → Matrix d d ℝ | ∀ ℓ, m ℓ ∈ Matrix.orthogonalGroup d ℝ}
      = ((n * (Fintype.card d * (Fintype.card d - 1) / 2) : ℕ) : ℝ≥0∞) := by
  sorry

/-- The families of `n ≥ 1` matrices that are all equal to one invertible matrix have dimension
`d²`. -/
theorem dimH_setOf_const_isUnit_det {n : ℕ} (hn : 0 < n) :
    dimH {m : Fin n → Matrix d d ℝ | ∃ g : Matrix d d ℝ, IsUnit g.det ∧ ∀ ℓ, m ℓ = g}
      = ((Fintype.card d ^ 2 : ℕ) : ℝ≥0∞) := by
  sorry

/-- The families of `n ≥ 1` matrices that are all equal to one orthogonal matrix have dimension
`d (d − 1) / 2`. -/
theorem dimH_setOf_const_mem_orthogonalGroup {n : ℕ} (hn : 0 < n) :
    dimH {m : Fin n → Matrix d d ℝ |
        ∃ Q : Matrix d d ℝ, Q ∈ Matrix.orthogonalGroup d ℝ ∧ ∀ ℓ, m ℓ = Q}
      = ((Fintype.card d * (Fintype.card d - 1) / 2 : ℕ) : ℝ≥0∞) := by
  sorry

end Skips
