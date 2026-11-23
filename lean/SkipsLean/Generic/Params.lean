import SkipsLean.Generic.AnalyticZeroSet
import SkipsLean.Dimension.UpperBoundRMSNorm
import SkipsLean.Symmetry.Reduction

/-!
# Statements at generic parameters

Papers: "A statement holds at generic parameters if it holds outside a set of Lebesgue measure
zero" (Section 2 of both papers).

The parameter space is a finite-dimensional real vector space. Its Lebesgue measures are its
additive Haar measures, which differ from each other by a positive constant, so "measure zero"
does not depend on which one is taken. A statement at generic parameters is written
`∀ᵐ θ ∂μ, …` for an arbitrary additive Haar measure `μ` on the parameters.

Stated here: at generic parameters every choice of `d` columns of a read or of the readout, and
every choice of `d` rows of the embedding or of a write, forms an invertible matrix (the last
sentence of Proposition 3.3 of the dimension paper and of its proof); in particular `E` and the
writes have rank `d`; and the upper bounds of Theorem 4.3 hold at generic parameters.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {A : Arch T d L}

/-- The parameters carry their Borel σ-algebra. -/
noncomputable instance : MeasurableSpace (Params A dIn dOut) := borel _

instance : BorelSpace (Params A dIn dOut) := ⟨rfl⟩

variable (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]

/-- **Proposition 3.3, "at generic parameters every hidden state has such columns".** At generic
parameters, any `d` distinct columns of a read or of the readout, and any `d` distinct rows of the
embedding or of a write, form an invertible matrix. -/
theorem ae_isUnit_det_submatrix :
    ∀ᵐ θ ∂μ,
      (∀ (ℓ : Fin L) (c : d ↪ A.r ℓ), IsUnit ((θ.read ℓ).submatrix id c).det) ∧
      (∀ c : d ↪ dOut, IsUnit (θ.D.submatrix id c).det) ∧
      (∀ ρ : d ↪ dIn, IsUnit (θ.E.submatrix ρ id).det) ∧
      (∀ (ℓ : Fin L) (ρ : d ↪ A.w ℓ), IsUnit ((θ.write ℓ).submatrix ρ id).det) := by
  sorry

/-- At generic parameters `E` and every write have rank `d`, when `d_in ≥ d` and every block has
at least `d` rows in its write (for an MLP block, at least `d` hidden units). -/
theorem ae_rank_E_write (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d ∧ ∀ ℓ, (θ.write ℓ).rank = Fintype.card d := by
  sorry

/-- **Theorem 4.3 at generic parameters, without normalization, for the changes of basis:**
the functional dimension is at most `P - (L + 1) d²`. -/
theorem ae_funDim_add_le_skipless (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) :
    ∀ᵐ θ ∂μ, funDim A 0 θ + (L + 1) * Fintype.card d ^ 2
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **Theorem 4.3 at generic parameters, under pre-RMSNorm, for the changes of basis:** the
functional dimension is at most `P - (L + 1) d (d - 1) / 2`. -/
theorem ae_funDim_add_le_skipless_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) :
    ∀ᵐ θ ∂μ, funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **Skips paper: the upper bound for residual networks at generic parameters,** without
normalization and under pre-RMSNorm, for the one change of basis. -/
theorem ae_funDim_add_le_residual (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim A 1 θ + Fintype.card d ^ 2 ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

theorem ae_funDim_add_le_residual_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim A 1 θ + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end Skips
