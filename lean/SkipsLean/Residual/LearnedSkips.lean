import SkipsLean.Symmetry.Reduction

/-!
# Learned skips, identity skips, and the one change of basis of a residual network

Paper: "Skip Connections Unlock at Least d_model² Parameters per Layer", Section 3:
equations (6) and (7), Theorem 3.2 (learned skips reduce to identity skips) and the parts of
Theorem 3.3 (one change of basis for the whole network) that say which changes of basis preserve
the function.

In `hidden A S θ x` and `eval A S θ x` the stream matrices `S ℓ` are the skips `A_ℓ` of the paper:
`S = 0` is a skipless network, `S = 1` a residual network, and a general `S` a network with learned
skips. Equation (6), that the changes of basis together with `A_ℓ ↦ G_{ℓ-1}⁻¹ A_ℓ G_ℓ` preserve the
function, is `Skips.eval_cob`.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn]
variable {A : Arch T d L}

/-- Equation (7): the products `Λ_ℓ = A_{ℓ+1} ⋯ A_L` of the skips, with `Λ_L = I`. -/
def skipProd (S : Fin L → GL d ℝ) : Fin (L + 1) → GL d ℝ :=
  Fin.reverseInduction (motive := fun _ => GL d ℝ) 1 (fun ℓ Λ => S ℓ * Λ)

@[simp] theorem skipProd_last (S : Fin L → GL d ℝ) : skipProd S (Fin.last L) = 1 := by
  simp [skipProd]

/-- Equation (7): `A_ℓ Λ_ℓ = Λ_{ℓ-1}`. -/
@[simp] theorem skipProd_castSucc (S : Fin L → GL d ℝ) (ℓ : Fin L) :
    skipProd S ℓ.castSucc = S ℓ * skipProd S ℓ.succ := by
  simp [skipProd]

/-- The skips after the change of basis by `Λ` are the identity: `Λ_{ℓ-1}⁻¹ A_ℓ Λ_ℓ = I`, since
`Λ_{ℓ-1} = A_ℓ Λ_ℓ` (equation (7)). -/
private theorem cobSkip_skipProd (S : Fin L → GL d ℝ) :
    cobSkip (fun ℓ => (S ℓ : Matrix d d ℝ)) (skipProd S) = 1 := by
  funext ℓ
  simp only [cobSkip, Pi.one_apply]
  rw [mul_assoc, ← Units.val_mul, ← skipProd_castSucc, Units.inv_mul]

/-- A product of orthogonal matrices is orthogonal: if every learned skip `A_ℓ` is orthogonal, so
is every `Λ_ℓ = A_{ℓ+1} ⋯ A_L`. -/
private theorem skipProd_mem_orthogonalGroup (S : Fin L → GL d ℝ)
    (hS : ∀ ℓ, (S ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) (ℓ : Fin (L + 1)) :
    (skipProd S ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  induction ℓ using Fin.reverseInduction with
  | last =>
    -- `Λ_L = I`.
    rw [skipProd_last, Units.val_one]
    exact one_mem _
  | cast i ih =>
    -- `Λ_{i-1} = A_i Λ_i`.
    rw [skipProd_castSucc, Units.val_mul]
    exact mul_mem (hS i) ih

/-- The identity skips are unchanged by the same change of basis `G` at every hidden state:
`G⁻¹ I G = I`. -/
private theorem cobSkip_one_const (G : GL d ℝ) :
    cobSkip (1 : Fin L → Matrix d d ℝ) (fun _ => G) = 1 := by
  funext ℓ
  simp only [cobSkip, Pi.one_apply, Matrix.mul_one, Units.inv_mul]

omit [DecidableEq d] in
/-- The chosen columns `c` of a product `M N` are `M` times the chosen columns of `N`. -/
private theorem submatrix_id_mul {r : Type*} (M : Matrix d d ℝ) (N : Matrix d r ℝ) (c : d → r) :
    (M * N).submatrix id c = M * N.submatrix id c := by
  rw [Matrix.submatrix_mul M N id id c Function.bijective_id, Matrix.submatrix_id_id]

variable (θ : Params A dIn dOut) (x : Matrix T dIn ℝ)

/-- **Theorem 3.2 (i).** Without normalization, a network with invertible learned skips `A_ℓ`
computes the same function as the residual network with the embedding `E Λ_0`, the reads
`Λ_{ℓ-1}⁻¹ W_read^ℓ`, the writes `W_write^ℓ Λ_ℓ` and the readout `D`. -/
theorem eval_learned_eq_residual (hA : A.χ = id) (S : Fin L → GL d ℝ) :
    eval A (fun ℓ => (S ℓ : Matrix d d ℝ)) θ x
      = eval A 1 (θ.cob (skipProd S) (skipProd S)) x := by
  -- Without normalization `χ (h Λ_ℓ) = χ (h) Λ_ℓ` holds trivially.
  have hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (skipProd S ℓ : Matrix d d ℝ))
      = A.χ h * (skipProd S ℓ : Matrix d d ℝ) := by
    intro ℓ h
    simp only [hA, id_eq]
  -- Proposition 3.2 with `G = K = Λ` turns the skips `A_ℓ` into `Λ_{ℓ-1}⁻¹ A_ℓ Λ_ℓ = I`.
  rw [← eval_cob (M := fun ℓ => (S ℓ : Matrix d d ℝ)) (θ := θ) (G := skipProd S)
    (K := skipProd S) (x := x) hχ, cobSkip_skipProd]

/-- In Theorem 3.2 (i) the readout is unchanged, since `Λ_L = I`. -/
theorem cob_skipProd_D (S : Fin L → GL d ℝ) :
    (θ.cob (skipProd S) (skipProd S)).D = θ.D := by
  -- The readout becomes `Λ_L⁻¹ D` and `Λ_L = I`.
  change (↑(skipProd S (Fin.last L))⁻¹ : Matrix d d ℝ) * θ.D = θ.D
  rw [skipProd_last, inv_one, Units.val_one, Matrix.one_mul]

/-- **Theorem 3.2 (ii), first sentence.** Under pre-RMSNorm the same holds when every learned
skip is orthogonal. -/
theorem eval_learned_eq_residual_rmsNorm (ε : ℝ) (hA : A.χ = rmsNorm ε) (S : Fin L → GL d ℝ)
    (hS : ∀ ℓ, (S ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) :
    eval A (fun ℓ => (S ℓ : Matrix d d ℝ)) θ x
      = eval A 1 (θ.cob (skipProd S) (skipProd S)) x := by
  -- Every `Λ_ℓ` is orthogonal, so pre-RMSNorm commutes with it (Lemma A.1).
  have hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (skipProd S ℓ : Matrix d d ℝ))
      = A.χ h * (skipProd S ℓ : Matrix d d ℝ) := by
    intro ℓ h
    rw [hA]
    exact rmsNorm_mul_orthogonal ε (skipProd_mem_orthogonalGroup S hS ℓ) h
  -- Proposition 3.2 with `G = K = Λ` turns the skips `A_ℓ` into `Λ_{ℓ-1}⁻¹ A_ℓ Λ_ℓ = I`.
  rw [← eval_cob (M := fun ℓ => (S ℓ : Matrix d d ℝ)) (θ := θ) (G := skipProd S)
    (K := skipProd S) (x := x) hχ, cobSkip_skipProd]

/-- **Theorem 3.3 (i), "if", under pre-RMSNorm:** the same orthogonal change of basis at every
hidden state preserves the function of a residual network. (Without normalization this is
`Skips.eval_cob_residual`.) -/
theorem eval_cob_residual_rmsNorm (ε : ℝ) (hA : A.χ = rmsNorm ε) (Q : GL d ℝ)
    (hQ : (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) :
    eval A 1 (θ.cob (fun _ => Q) (fun _ => Q)) x = eval A 1 θ x := by
  -- Pre-RMSNorm commutes with the orthogonal `Q` (Lemma A.1).
  have hχ : ∀ (_ : Fin (L + 1)) (h : Matrix T d ℝ),
      A.χ (h * (Q : Matrix d d ℝ)) = A.χ h * (Q : Matrix d d ℝ) := by
    intro _ h
    rw [hA]
    exact rmsNorm_mul_orthogonal ε hQ h
  -- Proposition 3.2 with `G = K = Q` at every hidden state; the identity skips stay `Q⁻¹ I Q = I`.
  have h := eval_cob (M := 1) (θ := θ) (G := fun _ => Q) (K := fun _ => Q) (x := x) hχ
  rwa [cobSkip_one_const] at h

/-- **Theorem 3.3 (iii), without normalization, for the read of a block.** In a residual network,
if `d` columns of the read of block `ℓ` form an invertible matrix, the same change of basis at all
hidden states preserves the function and turns these columns into the identity. -/
theorem exists_cob_residual_read_eq_one (hA : A.χ = id) (ℓ : Fin L) (c : d → A.r ℓ)
    (hc : IsUnit ((θ.read ℓ).submatrix id c).det) :
    ∃ G : GL d ℝ,
      (∀ x : Matrix T dIn ℝ, eval A 1 (θ.cob (fun _ => G) (fun _ => G)) x = eval A 1 θ x) ∧
      ((θ.cob (fun _ => G) (fun _ => G)).read ℓ).submatrix id c = 1 := by
  -- `G` is the matrix `W₁` of the chosen columns, invertible by hypothesis.
  obtain ⟨G, hG⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr hc
  -- One change of basis at all hidden states preserves the function of a residual network.
  refine ⟨G, fun x => eval_cob_residual (θ := θ) (x := x) hA G, ?_⟩
  -- The chosen columns of the new read are `G⁻¹ W₁ = I`.
  change ((↑G⁻¹ : Matrix d d ℝ) * θ.read ℓ).submatrix id c = 1
  rw [submatrix_id_mul, ← hG, Units.inv_mul]

/-- **Theorem 3.3 (iii), without normalization, for the readout.** -/
theorem exists_cob_residual_D_eq_one (hA : A.χ = id) (cD : d → dOut)
    (hcD : IsUnit (θ.D.submatrix id cD).det) :
    ∃ G : GL d ℝ,
      (∀ x : Matrix T dIn ℝ, eval A 1 (θ.cob (fun _ => G) (fun _ => G)) x = eval A 1 θ x) ∧
      (θ.cob (fun _ => G) (fun _ => G)).D.submatrix id cD = 1 := by
  -- `G` is the matrix `D₁` of the chosen columns, invertible by hypothesis.
  obtain ⟨G, hG⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr hcD
  -- One change of basis at all hidden states preserves the function of a residual network.
  refine ⟨G, fun x => eval_cob_residual (θ := θ) (x := x) hA G, ?_⟩
  -- The chosen columns of the new readout are `G⁻¹ D₁ = I`.
  change ((↑G⁻¹ : Matrix d d ℝ) * θ.D).submatrix id cD = 1
  rw [submatrix_id_mul, ← hG, Units.inv_mul]

/-- **Theorem 3.3 (iii), under pre-RMSNorm, for the read of a block.** One orthogonal change of
basis at all hidden states preserves the function and turns the chosen columns of the read of
block `ℓ` into an upper triangular matrix. -/
theorem exists_cob_residual_read_upperTriangular [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (ℓ : Fin L) (c : d → A.r ℓ) :
    ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
      (∀ x : Matrix T dIn ℝ, eval A 1 (θ.cob (fun _ => Q) (fun _ => Q)) x = eval A 1 θ x) ∧
      (((θ.cob (fun _ => Q) (fun _ => Q)).read ℓ).submatrix id c).BlockTriangular id := by
  -- QR factorization of the chosen columns `W₁`: an orthogonal `Q` with `Qᵀ W₁` upper triangular.
  obtain ⟨Q, hQ, htri⟩ :=
    exists_orthogonal_transpose_mul_upperTriangular ((θ.read ℓ).submatrix id c)
  -- `Q` is invertible, with inverse `Qᵀ`.
  let Q' : GL d ℝ :=
    ⟨Q, Qᵀ, (Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ, (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hQ⟩
  have hQ' : (Q' : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := hQ
  -- The same orthogonal change of basis at all hidden states preserves the function.
  refine ⟨Q', hQ', fun x => eval_cob_residual_rmsNorm θ x ε hA Q' hQ', ?_⟩
  -- The chosen columns of the new read are `Q⁻¹ W₁ = Qᵀ W₁`, upper triangular.
  change (((↑Q'⁻¹ : Matrix d d ℝ) * θ.read ℓ).submatrix id c).BlockTriangular id
  rw [submatrix_id_mul, coe_inv_of_mem_orthogonalGroup Q' hQ']
  exact htri

/-- **Theorem 3.3 (iii), under pre-RMSNorm, for the readout.** One orthogonal change of basis at
all hidden states preserves the function and turns the chosen columns of the readout `D` into an
upper triangular matrix. -/
theorem exists_cob_residual_D_upperTriangular [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (cD : d → dOut) :
    ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
      (∀ x : Matrix T dIn ℝ, eval A 1 (θ.cob (fun _ => Q) (fun _ => Q)) x = eval A 1 θ x) ∧
      ((θ.cob (fun _ => Q) (fun _ => Q)).D.submatrix id cD).BlockTriangular id := by
  -- QR factorization of the chosen columns `W₁`: an orthogonal `Q` with `Qᵀ W₁` upper triangular.
  obtain ⟨Q, hQ, htri⟩ :=
    exists_orthogonal_transpose_mul_upperTriangular (θ.D.submatrix id cD)
  -- `Q` is invertible, with inverse `Qᵀ`.
  let Q' : GL d ℝ :=
    ⟨Q, Qᵀ, (Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ, (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hQ⟩
  have hQ' : (Q' : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := hQ
  -- The same orthogonal change of basis at all hidden states preserves the function.
  refine ⟨Q', hQ', fun x => eval_cob_residual_rmsNorm θ x ε hA Q' hQ', ?_⟩
  -- The chosen columns of the new readout are `Q⁻¹ W₁ = Qᵀ W₁`, upper triangular.
  change (((↑Q'⁻¹ : Matrix d d ℝ) * θ.D).submatrix id cD).BlockTriangular id
  rw [submatrix_id_mul, coe_inv_of_mem_orthogonalGroup Q' hQ']
  exact htri

end Skips
