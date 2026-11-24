import SkipsLean.Imports
import SkipsLean.Dimension.UpperBoundRMSNorm

/-!
# The changes of basis `exp m_ℓ` near the identity, as a map of `m`

Paper (dimension paper): Appendix B, proof of Proposition 4.6: "The changes of basis of
Proposition 3.2 […] form a Lie group of dimension `k`, which acts smoothly. It acts locally freely
at `θ`, so the map that sends an element of the group to the image of `θ` under it is an immersion
near the identity".

The map that sends an element of the group to the image of `θ` is written here in the chart
`m ↦ exp m` of the group at the identity: `cobExp θ m = θ.cob (exp m) (exp m)` for a family
`m_0, …, m_L` of matrices. It passes through `θ` at `m = 0`, and it is strictly differentiable at
`0` with the derivative `m ↦ cobDir θ m` (the direction of the changes of basis,
`Dimension/UpperBound.lean`). For antisymmetric `m_ℓ` the matrices `exp m_ℓ` are orthogonal. With
the constant family `m_ℓ = m` it is the change of basis of a residual network.

Used by the statements on local identifiability, with and without skip connections
(`Dimension/LocalIdentifiability*.lean`, `Residual/LocalIdentifiability*.lean`). The proofs were
first written inside `Dimension/LocalIdentifiability.lean`, which has its own private copies.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- The invertible matrix `exp Y`, with inverse `exp (-Y)`. -/
noncomputable def expGL (Y : Matrix d d ℝ) : GL d ℝ where
  val := NormedSpace.exp Y
  inv := NormedSpace.exp (-Y)
  val_inv := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_right, add_neg_cancel,
      NormedSpace.exp_zero]
  inv_val := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]

/-- The matrix of `expGL Y` is `exp Y`. -/
theorem coe_expGL (Y : Matrix d d ℝ) : (expGL Y : Matrix d d ℝ) = NormedSpace.exp Y := rfl

/-- The matrix of the inverse of `expGL Y` is `exp (-Y)`. -/
theorem coe_expGL_inv (Y : Matrix d d ℝ) :
    (↑(expGL Y)⁻¹ : Matrix d d ℝ) = NormedSpace.exp (-Y) := rfl

/-- For antisymmetric `Y`, `exp Y` is orthogonal: `(exp Y)ᵀ = exp Yᵀ = exp (-Y)`. -/
theorem exp_mem_orthogonalGroup_of_transpose_eq_neg {Y : Matrix d d ℝ} (hY : Yᵀ = -Y) :
    NormedSpace.exp Y ∈ Matrix.orthogonalGroup d ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff', ← Matrix.exp_transpose, hY]
  exact (expGL Y).inv_val

-- As in Mathlib's `MatrixExponential.lean`: without this option the instances of the operator
-- norm (e.g. `CompleteSpace`) are not found.
set_option backward.isDefEq.respectTransparency false in
/-- The matrix exponential is strictly differentiable at `0` with derivative the identity. The
strict derivative only sees the topology, so it may be computed with the operator norm, under which
matrices form a Banach algebra. -/
theorem hasStrictFDerivAt_matrix_exp_zero :
    HasStrictFDerivAt (fun Y : Matrix d d ℝ => NormedSpace.exp Y)
      (ContinuousLinearMap.id ℝ (Matrix d d ℝ)) 0 := by
  let _ : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  exact hasStrictFDerivAt_exp_zero (𝕂 := ℝ)

/-- The parameters `θ.cob (exp m) (exp m)`: the change of basis `exp m_ℓ` at the hidden state
`h_ℓ`. -/
noncomputable def cobExp {A : Arch T d L} (θ : Params A dIn dOut)
    (m : Fin (L + 1) → Matrix d d ℝ) : Params A dIn dOut :=
  θ.cob (fun ℓ => expGL (m ℓ)) (fun ℓ => expGL (m ℓ))

/-- `θ.cob G G` is linear in the pair `(G, G⁻¹)` of families of matrices: the map
`(P, R) ↦ (E P_0, R_{ℓ-1} W_read^ℓ, W_write^ℓ P_ℓ, R_L D)`. -/
private noncomputable def cobLin {A : Arch T d L} (θ : Params A dIn dOut) :
    (Fin (L + 1) → Matrix d d ℝ) × (Fin (L + 1) → Matrix d d ℝ) →ₗ[ℝ] Params A dIn dOut where
  toFun p := ⟨θ.E * p.1 0, fun ℓ => p.2 ℓ.castSucc * θ.read ℓ, fun ℓ => θ.write ℓ * p.1 ℓ.succ,
    p.2 (Fin.last L) * θ.D⟩
  map_add' p q := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Params.add_E, Params.add_read,
        Params.add_write, Params.add_D, Matrix.mul_add, Matrix.add_mul]
  map_smul' c p := by
    refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Params.smul_E, Params.smul_read,
        Params.smul_write, Params.smul_D, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

omit [Fintype T] in
/-- The orbit map `m ↦ θ.cob (exp m) (exp m)` is strictly differentiable at `0`, with derivative
`m ↦ cobDir θ m`. -/
theorem hasStrictFDerivAt_cobExp {A : Arch T d L} (θ : Params A dIn dOut) :
    ∃ Φ' : (Fin (L + 1) → Matrix d d ℝ) →L[ℝ] Params A dIn dOut,
      HasStrictFDerivAt (cobExp θ) Φ' 0 ∧ ∀ m, Φ' m = cobDir θ m := by
  -- the components `m ↦ exp (m_ℓ)` and `m ↦ exp (-m_ℓ)`
  have h1 : ∀ ℓ : Fin (L + 1), HasStrictFDerivAt
      (fun m : Fin (L + 1) → Matrix d d ℝ => NormedSpace.exp (m ℓ))
      ((ContinuousLinearMap.id ℝ (Matrix d d ℝ)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (L + 1) => Matrix d d ℝ) ℓ)) 0 :=
    fun ℓ => hasStrictFDerivAt_matrix_exp_zero.comp (0 : Fin (L + 1) → Matrix d d ℝ)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (L + 1) => Matrix d d ℝ)
        ℓ).hasStrictFDerivAt
  have h2 : ∀ ℓ : Fin (L + 1), HasStrictFDerivAt
      (fun m : Fin (L + 1) → Matrix d d ℝ => NormedSpace.exp (-m ℓ))
      ((ContinuousLinearMap.id ℝ (Matrix d d ℝ)).comp
        (-ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (L + 1) => Matrix d d ℝ) ℓ)) 0 := by
    intro ℓ
    have hg : HasStrictFDerivAt (fun Y : Matrix d d ℝ => NormedSpace.exp Y)
        (ContinuousLinearMap.id ℝ (Matrix d d ℝ))
        ((-ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (L + 1) => Matrix d d ℝ) ℓ) 0) := by
      rw [map_zero]
      exact hasStrictFDerivAt_matrix_exp_zero
    exact hg.comp (0 : Fin (L + 1) → Matrix d d ℝ)
      (-ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (L + 1) => Matrix d d ℝ)
        ℓ).hasStrictFDerivAt
  have hΨ := (hasStrictFDerivAt_pi.2 h1).prodMk (hasStrictFDerivAt_pi.2 h2)
  -- then the linear map `(P, R) ↦ (E P_0, R_{ℓ-1} W_read^ℓ, W_write^ℓ P_ℓ, R_L D)`
  let B := LinearMap.toContinuousLinearMap (cobLin θ)
  refine ⟨B.comp _, B.hasStrictFDerivAt.comp (0 : Fin (L + 1) → Matrix d d ℝ) hΨ, fun m => ?_⟩
  -- the derivative: `(E m_0, -m_{ℓ-1} W_read^ℓ, W_write^ℓ m_ℓ, -m_L D)`
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · rfl
  · show -m ℓ.castSucc * θ.read ℓ = -(m ℓ.castSucc * θ.read ℓ)
    exact Matrix.neg_mul _ _
  · rfl
  · show -m (Fin.last L) * θ.D = -(m (Fin.last L) * θ.D)
    exact Matrix.neg_mul _ _

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- At `m = 0` the orbit map gives `θ`. -/
theorem cobExp_zero {A : Arch T d L} (θ : Params A dIn dOut) : cobExp θ 0 = θ := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [cobExp, Params.cob, coe_expGL, coe_expGL_inv, Pi.zero_apply, neg_zero,
      NormedSpace.exp_zero, Matrix.mul_one, Matrix.one_mul]

end Skips
