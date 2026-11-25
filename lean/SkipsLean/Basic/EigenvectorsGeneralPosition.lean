import SkipsLean.Imports

/-!
# A matrix with more than `d` eigenvectors in general position is a multiple of the identity

A fact of linear algebra, stated once for the two forms of Lemma A.18 of the skips paper for
ReGLU blocks with the readout (`Dimension/UpperBoundReadoutInside.lean`,
`Symmetry/LocallyFreeReadout.lean`). The proof of the lemma says: "each read, of rank `d_model`
and with generic columns, then forces `G_{ℓ−1} = I` and the remaining scales to be 1". For a
ReGLU block the change of basis `G_{ℓ−1}` multiplies every gate column and every value column of
the read by a number of its own, so every column is an eigenvector of `G_{ℓ−1}`; "generic
columns" is used in this form: more than `d` vectors, any `d` of them linearly independent.

Proof: `d` of the vectors form a basis, and one more vector has all its coordinates in this basis
nonzero (else it and `d − 1` vectors of the basis would be dependent); comparing `M v` in the
basis, all eigenvalues are equal.
-/

namespace Skips

open Matrix

/-- If more than `d` vectors of `ℝ^d`, any `d` of which are linearly independent, are all
eigenvectors of a matrix `M`, then `M` is a multiple of the identity. -/
theorem eq_smul_one_of_eigenvectors_generalPosition {d q : Type*} [Fintype d] [DecidableEq d]
    [Fintype q] (v : q → d → ℝ)
    (hgp : ∀ S : Finset q, S.card ≤ Fintype.card d → LinearIndependent ℝ fun j : S => v j)
    (hq : Fintype.card d < Fintype.card q) (M : Matrix d d ℝ)
    (hM : ∀ j, ∃ μ : ℝ, M *ᵥ v j = μ • v j) :
    ∃ μ : ℝ, M = μ • (1 : Matrix d d ℝ) := by
  sorry

end Skips
