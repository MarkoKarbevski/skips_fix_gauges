import SkipsLean.Network.Blocks
import SkipsLean.Generic.Params

/-!
# Helpers shared by the one-block theorems

The proofs of Theorem 5.1 of the dimension paper for the different kinds of block use the same
pieces: the linear map `X ↦ cobDir θ X`, the weights as linear maps of the parameters, the
analyticity of the entries of `C = E W_read` and `A = W_write D`, "an analytic function that is
not identically zero is nonzero at generic parameters", the derivative of `θ ↦ F_θ(x)` along a
line `τ ↦ θ + τ η`, and two facts of linear algebra. They are collected here, for every
architecture, so that the files of the kinds of block do not repeat them.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {A : Arch T d L}

/-! ### The directions of the changes of basis, as a linear map -/

/-- `X ↦ cobDir θ X`, as a linear map. -/
noncomputable def cobDirLin (θ : Params A dIn dOut) :
    (Fin (L + 1) → Matrix d d ℝ) →ₗ[ℝ] Params A dIn dOut where
  toFun := cobDir θ
  map_add' X Y := by
    apply Params.ext' <;> intros <;>
      simp only [cobDir, Params.add_E, Params.add_read, Params.add_write, Params.add_D,
        Pi.add_apply, Matrix.mul_add, Matrix.add_mul, neg_add]
  map_smul' c X := by
    apply Params.ext' <;> intros <;>
      simp only [cobDir, Params.smul_E, Params.smul_read, Params.smul_write, Params.smul_D,
        Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_neg, RingHom.id_apply]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
@[simp]
theorem cobDirLin_apply (θ : Params A dIn dOut) (X : Fin (L + 1) → Matrix d d ℝ) :
    cobDirLin θ X = cobDir θ X := rfl

omit [DecidableEq d] in
/-- The families `X` of `d × d` matrices on the `L + 1` hidden states form a space of dimension
`(L + 1) d²`. -/
theorem finrank_cobDomain :
    Module.finrank ℝ (Fin (L + 1) → Matrix d d ℝ) = (L + 1) * Fintype.card d ^ 2 := by
  rw [Module.finrank_pi_fintype, Module.finrank_matrix]
  simp [sq]

/-! ### The weights as linear maps of the parameters -/

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The embedding, as a linear map of the parameters. -/
def Params.linE : Params A dIn dOut →ₗ[ℝ] Matrix dIn d ℝ where
  toFun θ := θ.E
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The read of block `ℓ`, as a linear map of the parameters. -/
def Params.linRead (ℓ : Fin L) : Params A dIn dOut →ₗ[ℝ] Matrix d (A.r ℓ) ℝ where
  toFun θ := θ.read ℓ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The write of block `ℓ`, as a linear map of the parameters. -/
def Params.linWrite (ℓ : Fin L) : Params A dIn dOut →ₗ[ℝ] Matrix (A.w ℓ) d ℝ where
  toFun θ := θ.write ℓ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The readout, as a linear map of the parameters. -/
def Params.linD : Params A dIn dOut →ₗ[ℝ] Matrix d dOut ℝ where
  toFun θ := θ.D
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
@[simp] theorem Params.linE_apply (θ : Params A dIn dOut) : Params.linE θ = θ.E := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
@[simp] theorem Params.linRead_apply (ℓ : Fin L) (θ : Params A dIn dOut) :
    Params.linRead ℓ θ = θ.read ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
@[simp] theorem Params.linWrite_apply (ℓ : Fin L) (θ : Params A dIn dOut) :
    Params.linWrite ℓ θ = θ.write ℓ := rfl

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
@[simp] theorem Params.linD_apply (θ : Params A dIn dOut) : Params.linD θ = θ.D := rfl

/-! ### Analytic functions of the parameters -/

/-- A linear functional on a finite-dimensional space is analytic. -/
theorem analyticOnNhd_linear {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (l : P →ₗ[ℝ] ℝ) : AnalyticOnNhd ℝ l Set.univ := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).analyticOnNhd _

/-- An entry of the product of two linear matrix-valued maps is analytic (it is a polynomial of
degree two). -/
theorem analyticOnNhd_mul_apply {P m n p : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] [Fintype n] (F : P →ₗ[ℝ] Matrix m n ℝ)
    (G : P →ₗ[ℝ] Matrix n p ℝ) (i : m) (j : p) :
    AnalyticOnNhd ℝ (fun y => (F y * G y) i j) Set.univ := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticOnNhd_fun_sum _ fun k _ =>
    (analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ i k).comp F)).mul
      (analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ k j).comp G))

/-- An analytic function that is not identically zero is nonzero almost everywhere. -/
theorem ae_ne_zero_of_analytic {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasurableSpace P] [BorelSpace P] (μ : Measure P)
    [μ.IsAddHaarMeasure] {g : P → ℝ} (hg : AnalyticOnNhd ℝ g Set.univ) (hne : ∃ y, g y ≠ 0) :
    ∀ᵐ y ∂μ, g y ≠ 0 := by
  rw [ae_iff]
  simpa only [ne_eq, not_not] using measure_zeroSet_of_analytic μ hg hne

omit [Fintype T] [DecidableEq d] in
/-- An entry of `E W_read^ℓ` is an analytic function of the parameters. -/
theorem analyticOnNhd_E_mul_read (ℓ : Fin L) (a : dIn) (j : A.r ℓ) :
    AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => (θ.E * θ.read ℓ) a j) Set.univ :=
  analyticOnNhd_mul_apply (Params.linE (A := A) (dIn := dIn) (dOut := dOut)) (Params.linRead ℓ) a j

omit [Fintype T] [DecidableEq d] in
/-- An entry of `W_write^ℓ D` is an analytic function of the parameters. -/
theorem analyticOnNhd_write_mul_D (ℓ : Fin L) (i : A.w ℓ) (o : dOut) :
    AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => (θ.write ℓ * θ.D) i o) Set.univ :=
  analyticOnNhd_mul_apply (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) ℓ) Params.linD i o

/-! ### Linear algebra -/

/-- A matrix with `d` rows and an invertible `d × d` submatrix has rank `d`. -/
theorem rank_eq_card_of_isUnit_det {n : Type*} [Fintype n] (M : Matrix d n ℝ) (c : d ↪ n)
    (h : IsUnit (M.submatrix id c).det) : M.rank = Fintype.card d := by
  have h1 := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)
  have h2 := M.rank_submatrix_le id c
  have h3 := M.rank_le_card_height
  omega

omit [DecidableEq d] in
/-- A sum of `card d` ones is not zero, for `d ≥ 2` (the entries of a product of two matrices of
ones). -/
theorem sum_one_mul_one_ne_zero (hd : 2 ≤ Fintype.card d) : ∑ _k : d, (1 : ℝ) * 1 ≠ 0 := by
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (0 : ℝ) < Fintype.card d := by exact_mod_cast (show 0 < Fintype.card d by omega)
  linarith

/-- Two columns of a product `E W` are not collinear for some `E` and `W`: with `E` whose row `a`
is `e_{k₁}` for `a = a₁` and `e_{k₂}` otherwise, and `W` whose row `k` is `e_i` for `k = k₁` and
`e_j` otherwise, the minor `C_{a₁ i} C_{a₂ j} - C_{a₁ j} C_{a₂ i}` of `C = E W` is `1`. -/
theorem exists_minor_ne_zero {m n q : Type*} [Fintype n] [DecidableEq m] [DecidableEq n]
    [DecidableEq q] {a₁ a₂ : m} {k₁ k₂ : n} {i j : q} (ha : a₁ ≠ a₂) (hk : k₁ ≠ k₂)
    (hij : i ≠ j) :
    ∃ (E : Matrix m n ℝ) (W : Matrix n q ℝ),
      (E * W) a₁ i * (E * W) a₂ j - (E * W) a₁ j * (E * W) a₂ i ≠ 0 := by
  let W : Matrix n q ℝ := Matrix.of fun k l => if l = (if k = k₁ then i else j) then 1 else 0
  let E : Matrix m n ℝ := Matrix.of fun a k => if k = (if a = a₁ then k₁ else k₂) then 1 else 0
  -- row `a` of `C = E W` is row `k₁` or `k₂` of `W`
  have hEW : ∀ a l, (E * W) a l = W (if a = a₁ then k₁ else k₂) l := by
    intro a l
    simp only [E, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  refine ⟨E, W, ?_⟩
  rw [hEW, hEW, hEW, hEW]
  simp only [W, Matrix.of_apply, ↓reduceIte, ha.symm, hk.symm, hij, hij.symm, mul_one, mul_zero,
    sub_zero, ne_eq, one_ne_zero, not_false_eq_true]

/-! ### Derivatives along a line of parameters -/

/-- A polynomial `a + τ b + τ² c` has derivative `b` at `τ = 0`. -/
theorem hasDerivAt_quad (a b c : ℝ) :
    HasDerivAt (fun τ : ℝ => a + τ * b + τ * τ * c) b 0 := by
  have h := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const b).const_add a |>.add
    (((hasDerivAt_id' (x := (0 : ℝ))).mul (hasDerivAt_id' (x := (0 : ℝ)))).mul_const c)
  convert h using 1
  ring

omit [DecidableEq d] in
/-- The chain rule along the line `τ ↦ θ + τ η`: the derivative of `τ ↦ F_{θ + τ η}(x)` at `0` is
the derivative of `θ ↦ F_θ(x)` along `η`. -/
theorem hasDerivAt_eval_line (S : Fin L → Matrix d d ℝ) (θ η : Params A dIn dOut)
    (x : Matrix T dIn ℝ)
    (hdiff : DifferentiableAt ℝ (fun θ' : Params A dIn dOut => eval A S θ' x) θ) :
    HasDerivAt (fun τ : ℝ => eval A S (θ + τ • η) x)
      (fderiv ℝ (fun θ' : Params A dIn dOut => eval A S θ' x) θ η) 0 := by
  -- the line has velocity `η` and passes through `θ` at `τ = 0`
  have hline : HasDerivAt (fun τ : ℝ => θ + τ • η) η 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const η).const_add θ
    rw [one_smul] at h
    exact h
  have h0 : θ = θ + (0 : ℝ) • η := by rw [zero_smul, add_zero]
  exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline h0

/-! ### The maps of the blocks are differentiable -/

variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The map of an MLP block is differentiable if its activation is. -/
theorem differentiable_f_mlp (hσ : Differentiable ℝ σ) (ℓ : Fin L) :
    Differentiable ℝ ((Arch.mlp (T := T) (d := d) σ χ hid).f ℓ) :=
  differentiable_pi.2 fun t => differentiable_pi.2 fun i =>
    hσ.comp (differentiable_pi.1 (differentiable_pi.1 differentiable_id t) i)

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The map of a gated block is differentiable if its gate activation is. -/
theorem differentiable_f_gated (hσ : Differentiable ℝ σ) (ℓ : Fin L) :
    Differentiable ℝ ((Arch.gated (T := T) (d := d) σ χ hid).f ℓ) := by
  -- every entry of a matrix is a differentiable (linear) function of the matrix
  have he : ∀ t j, Differentiable ℝ fun M : Matrix T (hid ℓ ⊕ hid ℓ) ℝ => M t j :=
    fun t j => differentiable_pi.1 (differentiable_pi.1 differentiable_id t) j
  -- the entry `(t, i)` of the output is `σ(M t (inl i)) * M t (inr i)`
  exact differentiable_pi.2 fun t => differentiable_pi.2 fun i =>
    (hσ.comp (he t (Sum.inl i))).mul (he t (Sum.inr i))

end Skips
