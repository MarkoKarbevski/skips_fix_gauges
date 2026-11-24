import SkipsLean.Dimension.UpperBoundRMSNorm

/-!
# The orthogonal group is covered by Cayley transforms and sign changes

A step for the proof of Proposition 4.6 of the dimension paper (and of Proposition 4.5 of the
skips paper), from local identifiability to the equality condition, under pre-RMSNorm: "With the
permutations and the sign flips, the symmetries form a Lie group of dimension `k` with finitely
many components, and the images of `θ` under it form the image of a manifold of dimension `k`
under a smooth map." Under pre-RMSNorm the changes of basis are orthogonal, and the orthogonal
group is not an open subset of a vector space. Here it is covered by finitely many images of the
space of antisymmetric matrices, whose dimension is `d (d − 1) / 2` (`finrank_antisymmetric`),
under maps that are smooth: every orthogonal `Q` is `(1 − A)(1 + A)⁻¹ D` with `A` antisymmetric
and `D` a diagonal matrix of signs (the Cayley transform; `1 + A` is invertible for every
antisymmetric `A`).
-/

namespace Skips

open Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- For an antisymmetric real matrix `A`, the matrix `1 + A` is invertible. -/
theorem isUnit_det_one_add_of_mem_antisymmetric {A : Matrix d d ℝ} (hA : A ∈ antisymmetric d) :
    IsUnit (1 + A).det := by
  sorry

/-- The Cayley transform `(1 − A)(1 + A)⁻¹` of an antisymmetric matrix is orthogonal. -/
theorem cayley_mem_orthogonalGroup {A : Matrix d d ℝ} (hA : A ∈ antisymmetric d) :
    (1 - A) * (1 + A)⁻¹ ∈ Matrix.orthogonalGroup d ℝ := by
  sorry

/-- For every real square matrix `Q` there are signs `±1` on the columns such that, for the
diagonal matrix `D` of these signs, `1 + Q D` is invertible. -/
theorem exists_det_one_add_mul_diagonal_ne_zero (Q : Matrix d d ℝ) :
    ∃ s : d → Bool, (1 + Q * Matrix.diagonal fun i => if s i then (1 : ℝ) else -1).det ≠ 0 := by
  sorry

/-- **Every orthogonal matrix is a Cayley transform times a diagonal matrix of signs:**
`Q = (1 − A)(1 + A)⁻¹ D` with `A` antisymmetric and `D = diag(±1)`. -/
theorem exists_cayley_mul_diagonal_of_mem_orthogonalGroup {Q : Matrix d d ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup d ℝ) :
    ∃ (s : d → Bool) (A : Matrix d d ℝ), A ∈ antisymmetric d ∧
      Q = (1 - A) * (1 + A)⁻¹ * Matrix.diagonal fun i => if s i then (1 : ℝ) else -1 := by
  sorry

end Skips
