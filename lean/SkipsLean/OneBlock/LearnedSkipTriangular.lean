import SkipsLean.OneBlock.LearnedSkipKinds
import SkipsLean.Symmetry.Reduction

/-!
# One block with an upper triangular learned skip under pre-RMSNorm

Paper (skips paper): Appendix B: "A learned skip `A ∈ ℝ^{d_model × d_model}` is full or upper
triangular." Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a learned skip
`A`, full or upper triangular. For generic parameters and `ε > 0`, its functional dimension exceeds
that of the residual network of part (ii) by exactly `d_model (d_model + 1)/2`, and it satisfies
the equality condition." Its proof, for the triangular skip: "For an upper triangular `A`, view
the network as the network with a full `A` restricted to triangular skips: its flat directions are
those of the full network whose entry `η_A` is upper triangular. […] For an upper triangular `A`,
`A Y − X_a A` must be upper triangular, which determines `Y` from `X_a` […]. They then have
dimension `d_model (d_model − 1)/2`."

Here: the upper triangular matrices as a subspace, the family whose skips are upper triangular
(`funDimLearnedTri`, the family `funDimSkips` of `OneBlock/LearnedSkip.lean` with the inclusion),
and for one tanh, GELU, SwiGLU or GeGLU block of width at least `d`, `d_in, d_out ≥ d ≥ 2`,
`ε > 0`: at almost every `(θ, A)` with `A` upper triangular the functional dimension is
`P + d (d + 1)/2 − d (d − 1)/2 − s`, where `P` counts the weights without the skip (the equality
condition: the network has `P + d (d + 1)/2` parameters and its symmetries have dimension
`d (d − 1)/2 + s`), and it exceeds that of the residual network by `d (d + 1)/2`.

The route of the proofs, from the full skip (`OneBlock/LearnedSkipKinds.lean`):
- at a triangular skip `R` that is invertible, the triangular family and the full family have the
  same functional dimension (`funDimLearnedTri_eq_funDimLearned`): every direction `a` of the skip
  is a triangular one plus `−X_0 R` for an antisymmetric `X_0`, because an antisymmetric `X` with
  `X R` upper triangular is `0`, and the direction of the rotation of `h_0` by `X_0` is flat;
- the functional dimension of the full family is the same at `(θ, A)` and at its image under
  orthogonal changes of basis, with `A ↦ G_0⁻¹ A G_1` (`funDimLearned_cob`);
- a QR factorization (`exists_orthogonal_transpose_mul_upperTriangular`) carries a generic `(θ, A)`
  to a point with a triangular skip; the generic functional dimension of the triangular family is
  the largest (`ae_funDimSkips_ge`); the restricted family has at most the functional dimension of
  the full one (`funDimSkips_comp_le`, `funDimLearned_add_le_rmsNorm`).
Not stated here: ReLU, ReLU², ReGLU and attention blocks; blocks narrower than `d`; `ε = 0`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [LinearOrder d]
  [Fintype dIn] [Fintype dOut]

/-- The upper triangular `d × d` matrices (for a linear order on `d`): `M i j = 0` for `j < i`. -/
def upperTriangular (d : Type*) [Fintype d] [LinearOrder d] : Submodule ℝ (Matrix d d ℝ) where
  carrier := {M | M.BlockTriangular id}
  add_mem' := fun {a b} ha hb i j hij => by
    rw [Matrix.add_apply, ha hij, hb hij, add_zero]
  zero_mem' := fun i j _ => rfl
  smul_mem' := fun c {a} ha i j hij => by
    rw [Matrix.smul_apply, ha hij, smul_zero]

/-- The inclusion of the families of upper triangular skips into the families of all skips. -/
noncomputable def triSkips (d : Type*) [Fintype d] [LinearOrder d] (L : ℕ) :
    (Fin L → upperTriangular d) →L[ℝ] (Fin L → Matrix d d ℝ) :=
  ContinuousLinearMap.pi fun ℓ => (upperTriangular d).subtypeL.comp (ContinuousLinearMap.proj ℓ)

/-- **The functional dimension of the network with upper triangular learned skips,** at the
weights and skips `p = (θ, (A_ℓ))`, `A_ℓ` upper triangular. -/
noncomputable abbrev funDimLearnedTri (A : Arch T d L)
    (p : Params A dIn dOut × (Fin L → upperTriangular d)) : ℕ :=
  funDimSkips A (triSkips d L) p

omit [DecidableEq d] in
/-- Helper: the pairs `(i, j)` with `i < j` and those with `j < i` are as many (swap them). -/
private theorem card_gt_eq_card_lt_lst :
    Fintype.card {p : d × d // p.2 < p.1} = Fintype.card {p : d × d // p.1 < p.2} :=
  Fintype.card_congr ((Equiv.prodComm d d).subtypeEquiv fun _ => Iff.rfl)

omit [DecidableEq d] in
/-- Helper: the pairs `(i, j)` with `i ≤ j` are those with `i < j` and the `n` pairs `(i, i)`,
and with the pairs `j < i` they make all `n²` pairs. -/
private theorem card_le_lt_lst :
    Fintype.card {p : d × d // p.1 ≤ p.2} = Fintype.card {p : d × d // p.1 < p.2} + Fintype.card d
    ∧ Fintype.card {p : d × d // p.1 ≤ p.2} + Fintype.card {p : d × d // p.1 < p.2}
      = Fintype.card d * Fintype.card d := by
  classical
  -- `i ≤ j` is `i < j` or `i = j`, never both
  have h1 : Fintype.card {p : d × d // p.1 ≤ p.2}
      = Fintype.card {p : d × d // p.1 < p.2} + Fintype.card {p : d × d // p.1 = p.2} := by
    rw [← Fintype.card_subtype_or_disjoint _ _ (fun r hr hq x hx => (hr x hx).ne (hq x hx))]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun p => le_iff_lt_or_eq)
  -- the pairs `(i, i)` are numbered by `i`
  have h2 : Fintype.card {p : d × d // p.1 = p.2} = Fintype.card d :=
    Fintype.card_congr
      { toFun := fun p => p.1.1
        invFun := fun i => ⟨(i, i), rfl⟩
        left_inv := fun p => by
          obtain ⟨⟨a, b⟩, h⟩ := p
          change a = b at h
          subst h
          rfl
        right_inv := fun _ => rfl }
  -- the complement of `i ≤ j` is `j < i`
  have h3 : Fintype.card {p : d × d // ¬ p.1 ≤ p.2} = Fintype.card {p : d × d // p.2 < p.1} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun _ => not_le)
  have h4 := Fintype.card_subtype_compl (fun p : d × d => p.1 ≤ p.2)
  have h5 := Fintype.card_subtype_le (fun p : d × d => p.1 ≤ p.2)
  rw [Fintype.card_prod] at h4 h5
  rw [h3, card_gt_eq_card_lt_lst] at h4
  refine ⟨h1.trans (by rw [h2]), ?_⟩
  omega

omit [DecidableEq d] in
/-- Helper: there are `n (n - 1)/2` pairs `(i, j)` with `i < j`. -/
private theorem card_lt_lst :
    Fintype.card {p : d × d // p.1 < p.2} = Fintype.card d * (Fintype.card d - 1) / 2 := by
  obtain ⟨h1, h2⟩ := card_le_lt_lst (d := d)
  have h3 : Fintype.card d * (Fintype.card d - 1) + Fintype.card d
      = Fintype.card d * Fintype.card d := by
    cases h : Fintype.card d with
    | zero => rfl
    | succ m => rw [Nat.add_sub_cancel]; ring
  generalize Fintype.card d * (Fintype.card d - 1) = x at h3 ⊢
  generalize Fintype.card d * Fintype.card d = q at h2 h3
  omega

omit [DecidableEq d] in
/-- Helper: an upper triangular matrix is a free choice of its entries `(i, j)`, `i ≤ j`. -/
private def upperTriangularEquiv_lst :
    upperTriangular d ≃ₗ[ℝ] ({p : d × d // p.1 ≤ p.2} → ℝ) where
  toFun M p := (M : Matrix d d ℝ) p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨Matrix.of fun i j => if h : i ≤ j then f ⟨(i, j), h⟩ else 0, fun i j hij => by
    -- the entries below the diagonal are `0`
    simp only [of_apply]
    exact dite_eq_right (not_le.2 hij)⟩
  left_inv M := by
    apply Subtype.ext
    ext i j
    simp only [of_apply]
    by_cases h : i ≤ j
    · rw [dite_eq_left h]
    · rw [dite_eq_right h]
      exact (M.2 (not_le.1 h)).symm
  right_inv f := by
    funext p
    simp only [of_apply]
    rw [dite_eq_left p.2]

omit [DecidableEq d] in
/-- The upper triangular `d × d` matrices have dimension `d (d + 1)/2`. -/
theorem finrank_upperTriangular :
    Module.finrank ℝ (upperTriangular d) = Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the dimension is the number of pairs `i ≤ j`, that is `n (n - 1)/2 + n`
  rw [upperTriangularEquiv_lst.finrank_eq, Module.finrank_fintype_fun_eq_card,
    (card_le_lt_lst (d := d)).1, card_lt_lst]
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  have h3 : Fintype.card d * (Fintype.card d + 1)
      = Fintype.card d * (Fintype.card d - 1) + 2 * Fintype.card d := by
    cases h : Fintype.card d with
    | zero => rfl
    | succ m => rw [Nat.add_sub_cancel]; ring
  rw [h3]
  generalize Fintype.card d * (Fintype.card d - 1) = x at h2 ⊢
  omega

/-- **One block under pre-RMSNorm (`ε > 0`), at an invertible upper triangular skip `R`:** the
family of upper triangular skips has the functional dimension of the family of all skips. -/
theorem funDimLearnedTri_eq_funDimLearned {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (θ : Params A dIn dOut)
    (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det) :
    funDimLearnedTri A (θ, R) = funDimLearned A (θ, fun ℓ => (R ℓ : Matrix d d ℝ)) := by
  sorry

/-- **The functional dimension with full learned skips is invariant under orthogonal changes of
basis** (pre-RMSNorm, `ε > 0`): at `(θ.cob Q Q, (Q_{ℓ-1}⁻¹ A_ℓ Q_ℓ))` it is the same as at
`(θ, (A_ℓ))`. -/
theorem funDimLearned_cob {A : Arch T d L} {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (θ : Params A dIn dOut) (S : Fin L → Matrix d d ℝ)
    (Q : Fin (L + 1) → GL d ℝ) (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) :
    funDimLearned A (θ.cob Q Q, cobSkip S Q) = funDimLearned A (θ, S) := by
  sorry

variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)] {ε : ℝ}

/-- **Theorem B.1 (iii) of the skips paper for one tanh block with an upper triangular learned
skip, `ε > 0`:** at almost every `(θ, A)`, `A` upper triangular, the functional dimension is
`P + d (d + 1)/2 − d (d − 1)/2`. -/
theorem ae_funDimLearnedTri_tanh_rmsNorm [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.mlp Real.tanh (rmsNorm ε) hid) p
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper, "exceeds that of the residual network of part (ii) by
exactly `d (d + 1)/2`", for one tanh block with an upper triangular learned skip, `ε > 0`:** at
almost every `(θ, A)`, `A` upper triangular, and almost every `θ'`. -/
theorem ae_funDimLearnedTri_tanh_rmsNorm_eq_residual_add [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearnedTri (Arch.mlp Real.tanh (rmsNorm ε) hid) p
      = funDim (Arch.mlp Real.tanh (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one GELU block with an upper triangular learned
skip, `ε > 0`:** at almost every `(θ, A)`, `A` upper triangular, the functional dimension is
`P + d (d + 1)/2 − d (d − 1)/2`. -/
theorem ae_funDimLearnedTri_gelu_rmsNorm [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.mlp gelu (rmsNorm ε) hid) p
        + Fintype.card d * (Fintype.card d - 1) / 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper, "exceeds that of the residual network of part (ii) by
exactly `d (d + 1)/2`", for one GELU block with an upper triangular learned skip, `ε > 0`:** at
almost every `(θ, A)`, `A` upper triangular, and almost every `θ'`. -/
theorem ae_funDimLearnedTri_gelu_rmsNorm_eq_residual_add [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearnedTri (Arch.mlp gelu (rmsNorm ε) hid) p
      = funDim (Arch.mlp gelu (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one SwiGLU block with an upper triangular learned
skip, `ε > 0`:** at almost every `(θ, A)`, `A` upper triangular, the functional dimension is
`P + d (d + 1)/2 − d (d − 1)/2 − d_hidden`. -/
theorem ae_funDimLearnedTri_swiglu_rmsNorm [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.gated silu (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper, "exceeds that of the residual network of part (ii) by
exactly `d (d + 1)/2`", for one SwiGLU block with an upper triangular learned skip, `ε > 0`:** at
almost every `(θ, A)`, `A` upper triangular, and almost every `θ'`. -/
theorem ae_funDimLearnedTri_swiglu_rmsNorm_eq_residual_add [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearnedTri (Arch.gated silu (rmsNorm ε) hid) p
      = funDim (Arch.gated silu (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for one GeGLU block with an upper triangular learned
skip, `ε > 0`:** at almost every `(θ, A)`, `A` upper triangular, the functional dimension is
`P + d (d + 1)/2 − d (d − 1)/2 − d_hidden`. -/
theorem ae_funDimLearnedTri_geglu_rmsNorm [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.gated gelu (rmsNorm ε) hid) p
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper, "exceeds that of the residual network of part (ii) by
exactly `d (d + 1)/2`", for one GeGLU block with an upper triangular learned skip, `ε > 0`:** at
almost every `(θ, A)`, `A` upper triangular, and almost every `θ'`. -/
theorem ae_funDimLearnedTri_geglu_rmsNorm_eq_residual_add [Nonempty T] (hε : 0 < ε)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearnedTri (Arch.gated gelu (rmsNorm ε) hid) p
      = funDim (Arch.gated gelu (rmsNorm ε) hid) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

end Skips
