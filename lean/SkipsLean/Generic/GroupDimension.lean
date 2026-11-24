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

omit [DecidableEq d] in
/-- The map `g ↦ (g, …, g)` preserves the Hausdorff dimension (it is an isometry). -/
private theorem dimH_image_const_gdim {n : ℕ} (hn : 0 < n) (U : Set (Matrix d d ℝ)) :
    dimH ((fun g => fun _ : Fin n => g) '' U) = dimH U := by
  refine Isometry.dimH_image (fun a b => le_antisymm (edist_pi_le_iff.2 fun _ => le_rfl) ?_) U
  exact edist_le_pi_edist (fun _ : Fin n => a) (fun _ => b) ⟨0, hn⟩

/-- The families of `n` antisymmetric matrices have dimension `n d (d − 1) / 2`. -/
private theorem dimH_antisymmetric_gdim (n : ℕ) :
    dimH {a : Fin n → Matrix d d ℝ | ∀ ℓ, a ℓ ∈ antisymmetric d}
      = ((n * (Fintype.card d * (Fintype.card d - 1) / 2) : ℕ) : ℝ≥0∞) := by
  -- the families of antisymmetric matrices, inside all the families of matrices
  let ι : (Fin n → antisymmetric d) →ₗ[ℝ] (Fin n → Matrix d d ℝ) :=
    LinearMap.pi fun ℓ => (antisymmetric d).subtype.comp (LinearMap.proj ℓ)
  have hι : Function.Injective ι := fun m₁ m₂ h => funext fun ℓ => Subtype.ext (congrFun h ℓ)
  have hdim : Module.finrank ℝ (Fin n → antisymmetric d)
      = n * (Fintype.card d * (Fintype.card d - 1) / 2) := by
    rw [Module.finrank_pi_fintype, finrank_antisymmetric, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  -- the set is the range of `ι`, a subspace, seen through the isometric inclusion
  have hset : {a : Fin n → Matrix d d ℝ | ∀ ℓ, a ℓ ∈ antisymmetric d}
      = Subtype.val '' (Set.univ : Set (LinearMap.range ι)) := by
    ext a
    rw [Set.image_univ, Subtype.range_coe_subtype, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
      LinearMap.mem_range]
    constructor
    · intro h
      exact ⟨fun ℓ => ⟨a ℓ, h ℓ⟩, rfl⟩
    · rintro ⟨v, rfl⟩ ℓ
      exact (v ℓ).2
  rw [hset, isometry_subtype_coe.dimH_image, Real.dimH_univ_eq_finrank,
    LinearMap.finrank_range_of_inj hι, hdim]

/-- In a complete normed algebra, `y ↦ (1 − y) (1 + y)⁻¹ c` is differentiable where `1 + y` is a
unit. -/
private theorem differentiableAt_cayley_ring_gdim {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [CompleteSpace R] (c x : R) (hx : IsUnit (1 + x)) :
    DifferentiableAt ℝ (fun y : R => (1 - y) * Ring.inverse (1 + y) * c) x := by
  have h1 : DifferentiableAt ℝ (fun y : R => 1 + y) x :=
    (differentiableAt_const _).add differentiableAt_id
  have h2 : DifferentiableAt ℝ (fun y : R => 1 - y) x :=
    (differentiableAt_const _).sub differentiableAt_id
  exact (h2.mul (h1.inverse hx)).mul (differentiableAt_const c)

/-- The Cayley transform times a fixed matrix is differentiable where `1 + Y` is invertible
(through the operator norm, for which the matrices form a normed algebra with the same
topology). -/
private theorem differentiableAt_cayley_gdim (N X : Matrix d d ℝ) (hX : IsUnit (1 + X).det) :
    DifferentiableAt ℝ (fun Y : Matrix d d ℝ => (1 - Y) * (1 + Y)⁻¹ * N) X := by
  have hinv : ∀ Y : Matrix d d ℝ, (1 + Y)⁻¹ = Ring.inverse (1 + Y) :=
    fun Y => Matrix.nonsing_inv_eq_ringInverse _
  simp only [hinv]
  have hu : IsUnit (1 + X) := (Matrix.isUnit_iff_isUnit_det _).2 hX
  let iR : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let iA : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  have iC : @CompleteSpace (Matrix d d ℝ) iR.toUniformSpace :=
    (inferInstance : CompleteSpace (d → d → ℝ))
  exact @differentiableAt_cayley_ring_gdim (Matrix d d ℝ) iR iA iC N X hu

/-- The family version: `a ↦ ((1 − a ℓ)(1 + a ℓ)⁻¹ M ℓ)_ℓ` is differentiable where every
`1 + a ℓ` is invertible. -/
private theorem differentiableOn_cayley_gdim {n : ℕ} (M : Fin n → Matrix d d ℝ) :
    DifferentiableOn ℝ (fun a : Fin n → Matrix d d ℝ => fun ℓ => (1 - a ℓ) * (1 + a ℓ)⁻¹ * M ℓ)
      {a | ∀ ℓ, IsUnit (1 + a ℓ).det} := by
  intro a ha
  refine DifferentiableAt.differentiableWithinAt (differentiableAt_pi.2 fun ℓ => ?_)
  have hp : DifferentiableAt ℝ (fun a : Fin n → Matrix d d ℝ => a ℓ) a :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Matrix d d ℝ) ℓ).differentiableAt
  have hc := (differentiableAt_cayley_gdim (M ℓ) (a ℓ) (ha ℓ)).comp a hp
  exact hc

/-- The Cayley transform is an involution on the antisymmetric matrices: for antisymmetric `A`
and `Q = (1 − A)(1 + A)⁻¹`, `1 + Q` is invertible and `(1 − Q)(1 + Q)⁻¹ = A`. -/
private theorem cayley_cayley_gdim {A : Matrix d d ℝ} (hA : A ∈ antisymmetric d) :
    IsUnit (1 + (1 - A) * (1 + A)⁻¹).det ∧
      (1 - (1 - A) * (1 + A)⁻¹) * (1 + (1 - A) * (1 + A)⁻¹)⁻¹ = A := by
  have hB := isUnit_det_one_add_of_mem_antisymmetric hA
  set X := (1 + A)⁻¹ with hX
  have hBX : (1 + A) * X = 1 := Matrix.mul_nonsing_inv _ hB
  have hXB : X * (1 + A) = 1 := Matrix.nonsing_inv_mul _ hB
  -- `1 + Q = ((1 + A) + (1 − A)) X = 2 X`, with inverse `(1 + A) / 2`
  have h1Q : 1 + (1 - A) * X = (2 : ℝ) • X := by
    calc 1 + (1 - A) * X = ((1 + A) + (1 - A)) * X := by rw [Matrix.add_mul (1 + A), hBX]
      _ = (2 : ℝ) • X := by
        rw [show ((1 + A) + (1 - A) : Matrix d d ℝ) = (2 : ℝ) • 1 by rw [two_smul]; abel,
          Matrix.smul_mul, Matrix.one_mul]
  have hR : (1 + (1 - A) * X) * ((1 / 2 : ℝ) • (1 + A)) = 1 := by
    rw [h1Q, Matrix.smul_mul, Matrix.mul_smul, hXB, smul_smul]
    norm_num
  -- `1 − Q = ((1 + A) − (1 − A)) X = 2 A X`
  have h1mQ : 1 - (1 - A) * X = (2 : ℝ) • (A * X) := by
    calc 1 - (1 - A) * X = ((1 + A) - (1 - A)) * X := by rw [Matrix.sub_mul (1 + A), hBX]
      _ = (2 : ℝ) • (A * X) := by
        rw [show ((1 + A) - (1 - A) : Matrix d d ℝ) = (2 : ℝ) • A by rw [two_smul]; abel,
          Matrix.smul_mul]
  refine ⟨Matrix.isUnit_det_of_right_inverse hR, ?_⟩
  rw [Matrix.inv_eq_right_inv hR, h1mQ, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_assoc, hXB, Matrix.mul_one]
  norm_num

/-- The families of `n` orthogonal matrices have dimension `n d (d − 1) / 2`. -/
private theorem dimH_orthogonal_gdim (n : ℕ) :
    dimH {m : Fin n → Matrix d d ℝ | ∀ ℓ, m ℓ ∈ Matrix.orthogonalGroup d ℝ}
      = ((n * (Fintype.card d * (Fintype.card d - 1) / 2) : ℕ) : ℝ≥0∞) := by
  set S := {a : Fin n → Matrix d d ℝ | ∀ ℓ, a ℓ ∈ antisymmetric d} with hS
  set O := {m : Fin n → Matrix d d ℝ | ∀ ℓ, m ℓ ∈ Matrix.orthogonalGroup d ℝ} with hO
  -- the diagonal matrix of the signs `s`
  let D : (d → Bool) → Matrix d d ℝ := fun s => Matrix.diagonal fun i => if s i then 1 else -1
  -- the Cayley maps, with the signs `s ℓ` (or none: `M ℓ = 1`)
  let Φ : (Fin n → Matrix d d ℝ) → (Fin n → Matrix d d ℝ) → (Fin n → Matrix d d ℝ) :=
    fun M a ℓ => (1 - a ℓ) * (1 + a ℓ)⁻¹ * M ℓ
  have hdiff : ∀ M, DifferentiableOn ℝ (Φ M) S := fun M =>
    (differentiableOn_cayley_gdim M).mono fun a ha ℓ =>
      isUnit_det_one_add_of_mem_antisymmetric (ha ℓ)
  rw [← dimH_antisymmetric_gdim n]
  refine le_antisymm ?_ ?_
  · -- `≤`: every orthogonal family is `Φ (D ∘ s) a` for some signs `s` and antisymmetric `a`
    have hcover : O ⊆ ⋃ s : Fin n → d → Bool, Φ (fun ℓ => D (s ℓ)) '' S := by
      intro m hm
      choose s A hA hmA using fun ℓ => exists_cayley_mul_diagonal_of_mem_orthogonalGroup (hm ℓ)
      exact Set.mem_iUnion.2 ⟨s, A, hA, funext fun ℓ => (hmA ℓ).symm⟩
    refine (dimH_mono hcover).trans ?_
    rw [dimH_iUnion]
    exact iSup_le fun s => (hdiff _).dimH_image_le
  · -- `≥`: the Cayley map `Ψ = Φ 1` sends `S` into `O`, and `Ψ (Ψ a) = a` on `S`
    set Ψ := Φ fun _ => 1 with hΨ
    have hΨa : ∀ a ∈ S, Ψ a ∈ O ∧ (∀ ℓ, IsUnit (1 + Ψ a ℓ).det) ∧ Ψ (Ψ a) = a := by
      intro a ha
      have hc := fun ℓ => cayley_cayley_gdim (ha ℓ)
      simp only [hΨ, Φ, Matrix.mul_one] at hc ⊢
      exact ⟨fun ℓ => cayley_mem_orthogonalGroup (ha ℓ), fun ℓ => (hc ℓ).1,
        funext fun ℓ => (hc ℓ).2⟩
    have hsub : S ⊆ Ψ '' (Ψ '' S) := fun a ha => ⟨Ψ a, ⟨a, ha, rfl⟩, (hΨa a ha).2.2⟩
    have hdiff' : DifferentiableOn ℝ Ψ (Ψ '' S) :=
      (differentiableOn_cayley_gdim _).mono (by
        rintro _ ⟨a, ha, rfl⟩
        exact (hΨa a ha).2.1)
    calc dimH S ≤ dimH (Ψ '' (Ψ '' S)) := dimH_mono hsub
      _ ≤ dimH (Ψ '' S) := hdiff'.dimH_image_le
      _ ≤ dimH O := dimH_mono (by
        rintro _ ⟨a, ha, rfl⟩
        exact (hΨa a ha).1)

/-- The families of `n` invertible `d × d` matrices have dimension `n d²`. -/
theorem dimH_setOf_forall_isUnit_det (n : ℕ) :
    dimH {m : Fin n → Matrix d d ℝ | ∀ ℓ, IsUnit (m ℓ).det}
      = ((n * Fintype.card d ^ 2 : ℕ) : ℝ≥0∞) := by
  -- the set is open (the determinant is continuous) and contains the family `(1, …, 1)`
  have hopen : IsOpen {m : Fin n → Matrix d d ℝ | ∀ ℓ, IsUnit (m ℓ).det} := by
    simp only [isUnit_iff_ne_zero, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun ℓ =>
      isOpen_ne_fun (continuous_apply ℓ).matrix_det continuous_const
  have h1 : (fun _ => 1 : Fin n → Matrix d d ℝ) ∈
      {m : Fin n → Matrix d d ℝ | ∀ ℓ, IsUnit (m ℓ).det} := fun ℓ => by simp
  have hfin : Module.finrank ℝ (Fin n → Matrix d d ℝ) = n * Fintype.card d ^ 2 := by
    rw [Module.finrank_pi_fintype, Module.finrank_matrix]
    simp [sq]
  rw [Real.dimH_of_mem_nhds (hopen.mem_nhds h1)]
  exact congrArg Nat.cast hfin

/-- The families of `n` orthogonal `d × d` matrices have dimension `n d (d − 1) / 2`. -/
theorem dimH_setOf_forall_mem_orthogonalGroup (n : ℕ) :
    dimH {m : Fin n → Matrix d d ℝ | ∀ ℓ, m ℓ ∈ Matrix.orthogonalGroup d ℝ}
      = ((n * (Fintype.card d * (Fintype.card d - 1) / 2) : ℕ) : ℝ≥0∞) := by
  exact dimH_orthogonal_gdim n

/-- The families of `n ≥ 1` matrices that are all equal to one invertible matrix have dimension
`d²`. -/
theorem dimH_setOf_const_isUnit_det {n : ℕ} (hn : 0 < n) :
    dimH {m : Fin n → Matrix d d ℝ | ∃ g : Matrix d d ℝ, IsUnit g.det ∧ ∀ ℓ, m ℓ = g}
      = ((Fintype.card d ^ 2 : ℕ) : ℝ≥0∞) := by
  -- the set is the image of the invertible matrices under `g ↦ (g, …, g)`
  have hset : {m : Fin n → Matrix d d ℝ | ∃ g : Matrix d d ℝ, IsUnit g.det ∧ ∀ ℓ, m ℓ = g}
      = (fun g => fun _ : Fin n => g) '' {g : Matrix d d ℝ | IsUnit g.det} := by
    ext m
    constructor
    · rintro ⟨g, hg, hm⟩
      exact ⟨g, hg, funext fun ℓ => (hm ℓ).symm⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, fun _ => rfl⟩
  -- the invertible matrices are open and contain `1`
  have hopen : IsOpen {g : Matrix d d ℝ | IsUnit g.det} := by
    simp only [isUnit_iff_ne_zero]
    exact isOpen_ne_fun continuous_id.matrix_det continuous_const
  have h1 : (1 : Matrix d d ℝ) ∈ {g : Matrix d d ℝ | IsUnit g.det} := by simp
  have hfin : Module.finrank ℝ (Matrix d d ℝ) = Fintype.card d ^ 2 := by
    rw [Module.finrank_matrix]
    simp [sq]
  rw [hset, dimH_image_const_gdim hn, Real.dimH_of_mem_nhds (hopen.mem_nhds h1)]
  exact congrArg Nat.cast hfin

/-- The families of `n ≥ 1` matrices that are all equal to one orthogonal matrix have dimension
`d (d − 1) / 2`. -/
theorem dimH_setOf_const_mem_orthogonalGroup {n : ℕ} (hn : 0 < n) :
    dimH {m : Fin n → Matrix d d ℝ |
        ∃ Q : Matrix d d ℝ, Q ∈ Matrix.orthogonalGroup d ℝ ∧ ∀ ℓ, m ℓ = Q}
      = ((Fintype.card d * (Fintype.card d - 1) / 2 : ℕ) : ℝ≥0∞) := by
  -- the set is the image of the orthogonal group under `Q ↦ (Q, …, Q)`, for `n` and for `1`
  have hset : ∀ k : ℕ, {m : Fin k → Matrix d d ℝ |
        ∃ Q : Matrix d d ℝ, Q ∈ Matrix.orthogonalGroup d ℝ ∧ ∀ ℓ, m ℓ = Q}
      = (fun g => fun _ : Fin k => g) '' (Matrix.orthogonalGroup d ℝ : Set (Matrix d d ℝ)) := by
    intro k
    ext m
    constructor
    · rintro ⟨Q, hQ, hm⟩
      exact ⟨Q, hQ, funext fun ℓ => (hm ℓ).symm⟩
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q, hQ, fun _ => rfl⟩
  have h1 : {m : Fin 1 → Matrix d d ℝ | ∀ ℓ, m ℓ ∈ Matrix.orthogonalGroup d ℝ}
      = {m : Fin 1 → Matrix d d ℝ |
        ∃ Q : Matrix d d ℝ, Q ∈ Matrix.orthogonalGroup d ℝ ∧ ∀ ℓ, m ℓ = Q} := by
    ext m
    constructor
    · intro hm
      exact ⟨m 0, hm 0, fun ℓ => by rw [Subsingleton.elim ℓ 0]⟩
    · rintro ⟨Q, hQ, hm⟩ ℓ
      rw [hm ℓ]
      exact hQ
  have h := dimH_orthogonal_gdim (d := d) 1
  rw [h1, hset, dimH_image_const_gdim Nat.one_pos, one_mul] at h
  rw [hset, dimH_image_const_gdim hn, h]

end Skips
