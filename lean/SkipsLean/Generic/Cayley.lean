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
  have hAt : Aᵀ = -A := hA
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
  -- `(1 + A) v = 0` gives `v + A v = 0`.
  rw [Matrix.add_mulVec, Matrix.one_mulVec] at hv
  -- `v ⬝ᵥ A v = (Aᵀ v) ⬝ᵥ v = -(A v ⬝ᵥ v) = -(v ⬝ᵥ A v)`, so it is `0`.
  have hskew : v ⬝ᵥ (A *ᵥ v) = 0 := by
    have h1 : v ⬝ᵥ (A *ᵥ v) = -(v ⬝ᵥ (A *ᵥ v)) := by
      calc v ⬝ᵥ (A *ᵥ v) = (v ᵥ* A) ⬝ᵥ v := Matrix.dotProduct_mulVec v A v
        _ = (Aᵀ *ᵥ v) ⬝ᵥ v := by rw [Matrix.mulVec_transpose]
        _ = -(v ⬝ᵥ (A *ᵥ v)) := by
          rw [hAt, Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]
    linarith
  -- Hence `v ⬝ᵥ v = v ⬝ᵥ (v + A v) - v ⬝ᵥ A v = 0`, and `v = 0`.
  have hvv : v ⬝ᵥ v = 0 := by
    have h2 : v ⬝ᵥ (v + A *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
    rw [dotProduct_add, hskew, add_zero] at h2
    exact h2
  exact hv0 (dotProduct_self_eq_zero.1 hvv)

/-- The Cayley transform `(1 − A)(1 + A)⁻¹` of an antisymmetric matrix is orthogonal. -/
theorem cayley_mem_orthogonalGroup {A : Matrix d d ℝ} (hA : A ∈ antisymmetric d) :
    (1 - A) * (1 + A)⁻¹ ∈ Matrix.orthogonalGroup d ℝ := by
  have hAt : Aᵀ = -A := hA
  have hB := isUnit_det_one_add_of_mem_antisymmetric hA
  set X := (1 + A)⁻¹ with hX
  have hBX : (1 + A) * X = 1 := Matrix.mul_nonsing_inv _ hB
  -- `(1 − A)ᵀ = 1 + A`, `(1 + A)ᵀ = 1 − A`, and `1 + A`, `1 − A` commute.
  have hCt : (1 - A)ᵀ = 1 + A := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hAt, sub_neg_eq_add]
  have hBt : (1 + A)ᵀ = 1 - A := by
    rw [Matrix.transpose_add, Matrix.transpose_one, hAt, ← sub_eq_add_neg]
  have hcomm : (1 + A) * (1 - A) = (1 - A) * (1 + A) := by
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one]
    abel
  -- `Qᵀ Q = Xᵀ (1 + A)(1 − A) X = Xᵀ (1 − A)(1 + A) X = Xᵀ (1 + A)ᵀ`
  -- `= ((1 + A) X)ᵀ = 1`.
  rw [Matrix.mem_orthogonalGroup_iff']
  calc ((1 - A) * X)ᵀ * ((1 - A) * X) = Xᵀ * ((1 + A) * (1 - A)) * X := by
        rw [Matrix.transpose_mul, hCt]; simp only [Matrix.mul_assoc]
    _ = Xᵀ * (1 + A)ᵀ * ((1 + A) * X) := by rw [hcomm, hBt]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [← Matrix.transpose_mul, hBX, Matrix.transpose_one, Matrix.one_mul]

/-- The matrix whose column `j` is `e_j ± q_j` (sign from `s j`) for `j ∈ S`, and `e_j` else. -/
private def colMat_cay (Q : Matrix d d ℝ) (S : Finset d) (s : d → Bool) : Matrix d d ℝ :=
  Matrix.of fun i j =>
    if j ∈ S then (1 : Matrix d d ℝ) i j + (if s j then 1 else -1) * Q i j
    else (1 : Matrix d d ℝ) i j

omit [Fintype d] in
/-- Adding a column `a ∉ S` to `S` changes only column `a`. -/
private theorem colMat_insert_cay (Q : Matrix d d ℝ) {S : Finset d} {a : d} (ha : a ∉ S)
    (s : d → Bool) (b : Bool) :
    colMat_cay Q (insert a S) (Function.update s a b) =
      updateCol (colMat_cay Q S s) a
        (fun i => (1 : Matrix d d ℝ) i a + (if b then 1 else -1) * Q i a) := by
  ext i j
  rw [updateCol_apply]
  by_cases hj : j = a
  · subst hj
    simp [colMat_cay]
  · have hs : Function.update s a b j = s j := Function.update_of_ne hj _ _
    simp [colMat_cay, hj, Finset.mem_insert]

/-- Induction on `S`: some choice of signs gives a nonzero determinant. -/
private theorem exists_det_colMat_ne_zero_cay (Q : Matrix d d ℝ) (S : Finset d) :
    ∃ s : d → Bool, (colMat_cay Q S s).det ≠ 0 := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => true, ?_⟩
    have h1 : colMat_cay Q ∅ (fun _ => true) = 1 := by
      ext i j; simp [colMat_cay]
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  | insert a S ha ih =>
    obtain ⟨s, hs⟩ := ih
    set M := colMat_cay Q S s with hM
    -- Column `a` of `M` is `e_a`.
    have hcol : (fun i => M i a) = fun i => (1 : Matrix d d ℝ) i a := by
      funext i; simp [hM, colMat_cay, ha]
    set u : d → ℝ := fun i => (1 : Matrix d d ℝ) i a with hu
    set w : d → ℝ := fun i => Q i a with hw
    -- `det(col a := u + w) + det(col a := u − w) = 2 det(col a := u) = 2 det M ≠ 0`.
    have hsum : (updateCol M a (u + w)).det + (updateCol M a (u + (-1 : ℝ) • w)).det
        = 2 * M.det := by
      rw [det_updateCol_add, det_updateCol_add, det_updateCol_smul]
      have : updateCol M a u = M := by rw [← hcol, updateCol_eq_self]
      rw [this]
      ring
    by_cases hp : (updateCol M a (u + w)).det = 0
    · refine ⟨Function.update s a false, ?_⟩
      rw [colMat_insert_cay Q ha]
      have he : (fun i => (1 : Matrix d d ℝ) i a + (if false = true then 1 else -1) * Q i a)
          = u + (-1 : ℝ) • w := by
        funext i; simp [hu, hw]
      rw [he]
      intro h0
      rw [hp, h0] at hsum
      exact hs (by linarith)
    · refine ⟨Function.update s a true, ?_⟩
      rw [colMat_insert_cay Q ha]
      have he : (fun i => (1 : Matrix d d ℝ) i a + (if true = true then 1 else -1) * Q i a)
          = u + w := by
        funext i; simp [hu, hw]
      rw [he]
      exact hp

/-- For every real square matrix `Q` there are signs `±1` on the columns such that, for the
diagonal matrix `D` of these signs, `1 + Q D` is invertible. -/
theorem exists_det_one_add_mul_diagonal_ne_zero (Q : Matrix d d ℝ) :
    ∃ s : d → Bool, (1 + Q * Matrix.diagonal fun i => if s i then (1 : ℝ) else -1).det ≠ 0 := by
  obtain ⟨s, hs⟩ := exists_det_colMat_ne_zero_cay Q Finset.univ
  refine ⟨s, ?_⟩
  have h : colMat_cay Q Finset.univ s =
      1 + Q * Matrix.diagonal fun i => if s i then (1 : ℝ) else -1 := by
    ext i j
    simp only [colMat_cay, Matrix.of_apply, Finset.mem_univ, ite_true, Matrix.add_apply,
      Matrix.mul_diagonal]
    ring
  rw [← h]
  exact hs

/-- **Every orthogonal matrix is a Cayley transform times a diagonal matrix of signs:**
`Q = (1 − A)(1 + A)⁻¹ D` with `A` antisymmetric and `D = diag(±1)`. -/
theorem exists_cayley_mul_diagonal_of_mem_orthogonalGroup {Q : Matrix d d ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup d ℝ) :
    ∃ (s : d → Bool) (A : Matrix d d ℝ), A ∈ antisymmetric d ∧
      Q = (1 - A) * (1 + A)⁻¹ * Matrix.diagonal fun i => if s i then (1 : ℝ) else -1 := by
  sorry

end Skips
