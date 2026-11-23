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

omit [Fintype T] [DecidableEq d] in
/-- Helper: an entry of a matrix that depends linearly on the parameters is an analytic function
of the parameters (a linear functional on a finite-dimensional space is continuous linear). -/
private theorem analyticOnNhd_entry {m n : Type*} (Φ : Params A dIn dOut →ₗ[ℝ] Matrix m n ℝ)
    (i : m) (j : n) : AnalyticOnNhd ℝ (fun θ => Φ θ i j) Set.univ := by
  let l : Params A dIn dOut →ₗ[ℝ] ℝ := Matrix.entryLinearMap ℝ ℝ i j ∘ₗ Φ
  rw [show (fun θ => Φ θ i j) = ⇑l from rfl, ← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).analyticOnNhd _

omit [Fintype T] [DecidableEq d] in
/-- Helper: the determinant of a square matrix that depends linearly on the parameters is an
analytic function of the parameters: a finite sum of signed finite products of entries. -/
private theorem analyticOnNhd_det {n : Type*} [Fintype n] [DecidableEq n]
    (Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ) :
    AnalyticOnNhd ℝ (fun θ => (Φ θ).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ => analyticOnNhd_entry Φ (σ i) i)

omit [Fintype T] [DecidableEq d] in
/-- Helper: if a square matrix that depends linearly on the parameters is the identity at one
parameter, it is invertible at almost every parameter. Its determinant is analytic and not
identically zero, so its zero set is null. -/
private theorem ae_isUnit_det_of_linear {n : Type*} [Fintype n] [DecidableEq n]
    (Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ) (θ₀ : Params A dIn dOut) (h₀ : Φ θ₀ = 1) :
    ∀ᵐ θ ∂μ, IsUnit (Φ θ).det := by
  have hne : ∃ θ, (Φ θ).det ≠ 0 := ⟨θ₀, by rw [h₀, Matrix.det_one]; exact one_ne_zero⟩
  have hnull := measure_zeroSet_of_analytic μ (analyticOnNhd_det Φ) hne
  -- in `ℝ`, a unit is a nonzero number
  rw [ae_iff]
  simpa only [isUnit_iff_ne_zero, not_not] using hnull

omit [Fintype d] in
/-- Helper: a `d × m` matrix whose columns `c` form the identity matrix. -/
private theorem exists_submatrix_cols_eq_one {m : Type*} (c : d ↪ m) :
    ∃ M : Matrix d m ℝ, M.submatrix id c = 1 := by
  classical
  refine ⟨Matrix.of fun i j => if c i = j then 1 else 0, ?_⟩
  ext i k
  simp [Matrix.one_apply]

omit [Fintype d] in
/-- Helper: an `m × d` matrix whose rows `ρ` form the identity matrix. -/
private theorem exists_submatrix_rows_eq_one {m : Type*} (ρ : d ↪ m) :
    ∃ M : Matrix m d ℝ, M.submatrix ρ id = 1 := by
  classical
  refine ⟨Matrix.of fun j i => if j = ρ i then 1 else 0, ?_⟩
  ext k i
  simp [Matrix.one_apply]

/-- **Proposition 3.3, "at generic parameters every hidden state has such columns".** At generic
parameters, any `d` distinct columns of a read or of the readout, and any `d` distinct rows of the
embedding or of a write, form an invertible matrix. -/
theorem ae_isUnit_det_submatrix :
    ∀ᵐ θ ∂μ,
      (∀ (ℓ : Fin L) (c : d ↪ A.r ℓ), IsUnit ((θ.read ℓ).submatrix id c).det) ∧
      (∀ c : d ↪ dOut, IsUnit (θ.D.submatrix id c).det) ∧
      (∀ ρ : d ↪ dIn, IsUnit (θ.E.submatrix ρ id).det) ∧
      (∀ (ℓ : Fin L) (ρ : d ↪ A.w ℓ), IsUnit ((θ.write ℓ).submatrix ρ id).det) := by
  -- countably many conditions (finitely many `ℓ` and choices); each one fails on a null set
  -- reads: the parameter with read `ℓ` equal to `1` on the columns `c` and `0` elsewhere
  have hread : ∀ᵐ θ ∂μ, ∀ (ℓ : Fin L) (c : d ↪ A.r ℓ),
      IsUnit ((θ.read ℓ).submatrix id c).det := by
    refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun c => ?_
    obtain ⟨M, hM⟩ := exists_submatrix_cols_eq_one c
    let Φ : Params A dIn dOut →ₗ[ℝ] Matrix d d ℝ :=
      { toFun := fun θ => (θ.read ℓ).submatrix id c
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine ae_isUnit_det_of_linear μ Φ ⟨0, Pi.single ℓ M, 0, 0⟩ ?_
    show (Pi.single (M := fun ℓ => Matrix d (A.r ℓ) ℝ) ℓ M ℓ).submatrix id c = 1
    rw [Pi.single_eq_same]
    exact hM
  -- the readout
  have hD : ∀ᵐ θ ∂μ, ∀ c : d ↪ dOut, IsUnit (θ.D.submatrix id c).det := by
    refine ae_all_iff.2 fun c => ?_
    obtain ⟨M, hM⟩ := exists_submatrix_cols_eq_one c
    let Φ : Params A dIn dOut →ₗ[ℝ] Matrix d d ℝ :=
      { toFun := fun θ => θ.D.submatrix id c
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact ae_isUnit_det_of_linear μ Φ ⟨0, 0, 0, M⟩ hM
  -- the embedding
  have hE : ∀ᵐ θ ∂μ, ∀ ρ : d ↪ dIn, IsUnit (θ.E.submatrix ρ id).det := by
    refine ae_all_iff.2 fun ρ => ?_
    obtain ⟨M, hM⟩ := exists_submatrix_rows_eq_one ρ
    let Φ : Params A dIn dOut →ₗ[ℝ] Matrix d d ℝ :=
      { toFun := fun θ => θ.E.submatrix ρ id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact ae_isUnit_det_of_linear μ Φ ⟨M, 0, 0, 0⟩ hM
  -- writes
  have hwrite : ∀ᵐ θ ∂μ, ∀ (ℓ : Fin L) (ρ : d ↪ A.w ℓ),
      IsUnit ((θ.write ℓ).submatrix ρ id).det := by
    refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun ρ => ?_
    obtain ⟨M, hM⟩ := exists_submatrix_rows_eq_one ρ
    let Φ : Params A dIn dOut →ₗ[ℝ] Matrix d d ℝ :=
      { toFun := fun θ => (θ.write ℓ).submatrix ρ id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine ae_isUnit_det_of_linear μ Φ ⟨0, 0, Pi.single ℓ M, 0⟩ ?_
    show (Pi.single (M := fun ℓ => Matrix (A.w ℓ) d ℝ) ℓ M ℓ).submatrix ρ id = 1
    rw [Pi.single_eq_same]
    exact hM
  exact hread.and (hD.and (hE.and hwrite))

omit [Fintype T] in
/-- Helper: a matrix with `d` columns has rank `d` if some `d` of its rows form an invertible
matrix (rank at most the width, and at least the rank of a submatrix). -/
private theorem rank_eq_of_isUnit_det_submatrix {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- Helper: at generic parameters `E` has rank `d`, when `d_in ≥ d`. -/
private theorem ae_rank_E (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d := by
  -- `d` rows of `E`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  exact rank_eq_of_isUnit_det_submatrix θ.E ρ (hθ.2.2.1 ρ)

/-- At generic parameters `E` and every write have rank `d`, when `d_in ≥ d` and every block has
at least `d` rows in its write (for an MLP block, at least `d` hidden units). -/
theorem ae_rank_E_write (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d ∧ ∀ ℓ, (θ.write ℓ).rank = Fintype.card d := by
  filter_upwards [ae_rank_E μ hdIn, ae_isUnit_det_submatrix μ] with θ hE hθ
  refine ⟨hE, fun ℓ => ?_⟩
  -- `d` rows of the write of block `ℓ`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le (hw ℓ)
  exact rank_eq_of_isUnit_det_submatrix (θ.write ℓ) ρ (hθ.2.2.2 ℓ ρ)

/-- **Theorem 4.3 at generic parameters, without normalization, for the changes of basis:**
the functional dimension is at most `P - (L + 1) d²`. -/
theorem ae_funDim_add_le_skipless (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) :
    ∀ᵐ θ ∂μ, funDim A 0 θ + (L + 1) * Fintype.card d ^ 2
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the pointwise bound holds wherever `E` and the writes have rank `d`
  filter_upwards [ae_rank_E_write μ hdIn hw] with θ hθ
  exact funDim_add_le_skipless θ hA hf hθ.1 hθ.2

/-- **Theorem 4.3 at generic parameters, under pre-RMSNorm, for the changes of basis:** the
functional dimension is at most `P - (L + 1) d (d - 1) / 2`. -/
theorem ae_funDim_add_le_skipless_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hw : ∀ ℓ, Fintype.card d ≤ Fintype.card (A.w ℓ)) :
    ∀ᵐ θ ∂μ, funDim A 0 θ + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the pointwise bound holds wherever `E` and the writes have rank `d`
  filter_upwards [ae_rank_E_write μ hdIn hw] with θ hθ
  exact funDim_add_le_skipless_rmsNorm θ hε hA hf hθ.1 hθ.2

/-- **Skips paper: the upper bound for residual networks at generic parameters,** without
normalization and under pre-RMSNorm, for the one change of basis. -/
theorem ae_funDim_add_le_residual (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim A 1 θ + Fintype.card d ^ 2 ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the pointwise bound holds wherever `E` has rank `d`
  filter_upwards [ae_rank_E μ hdIn] with θ hE
  exact funDim_add_le_residual θ hA hf hE

theorem ae_funDim_add_le_residual_rmsNorm {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim A 1 θ + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- the pointwise bound holds wherever `E` has rank `d`
  filter_upwards [ae_rank_E μ hdIn] with θ hE
  exact funDim_add_le_residual_rmsNorm θ hε hA hf hE

end Skips
