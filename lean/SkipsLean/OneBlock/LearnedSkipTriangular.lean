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

section Copies

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the product of two differentiable matrix-valued maps is differentiable (a copy of the
private `differentiable_matMul` of `Dimension/Functional.lean`). -/
private theorem differentiable_matMul_lst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : E → Matrix m n ℝ} {g : E → Matrix n p ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun y => f y * g y) := by
  -- matrix multiplication as a bilinear map
  let B : Matrix m n ℝ →ₗ[ℝ] Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  -- the same map with continuous linear maps (all spaces are finite-dimensional)
  let B' : Matrix m n ℝ →L[ℝ] Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n p ℝ →ₗ[ℝ] Matrix m p ℝ) ≃ₗ[ℝ] (Matrix n p ℝ →L[ℝ] Matrix m p ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.differentiable.comp hf).clm_apply hg

omit [Fintype T] [DecidableEq d] [LinearOrder d] in
/-- Helper: a linear function of the weights `θ`, as a continuous linear map of `(θ, v)` (the
space of weights is finite-dimensional). -/
private noncomputable def fstLin_lst {A : Arch T d L} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (l : Params A dIn dOut →ₗ[ℝ] F) : Params A dIn dOut × V →L[ℝ] F :=
  (LinearMap.toContinuousLinearMap l).comp (ContinuousLinearMap.fst ℝ (Params A dIn dOut) V)

omit [LinearOrder d] in
/-- Helper: the skip of block `ℓ`, `(θ, v) ↦ (ι v)_ℓ`, as a continuous linear map. -/
private noncomputable def skipLin_lst (A : Arch T d L) (ι : V →L[ℝ] (Fin L → Matrix d d ℝ))
    (ℓ : Fin L) : Params A dIn dOut × V →L[ℝ] Matrix d d ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => Matrix d d ℝ) ℓ).comp
    (ι.comp (ContinuousLinearMap.snd ℝ (Params A dIn dOut) V))

omit [DecidableEq d] [LinearOrder d] in
/-- **The output is differentiable in the weights and the skips jointly:** for differentiable
maps `f_ℓ` and `χ`, the map `(θ, v) ↦ F_{θ, ι v}(x)` is differentiable. -/
private theorem differentiable_evalSkips_lst (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hχ : Differentiable ℝ A.χ) (x : Matrix T dIn ℝ) :
    Differentiable ℝ (fun p : Params A dIn dOut × V => evalSkips A ι p x) := by
  -- the weights and the skips are continuous linear functions of `(θ, v)`
  have hE : Differentiable ℝ (fun p : Params A dIn dOut × V => p.1.E) :=
    (fstLin_lst (V := V) (F := Matrix dIn d ℝ)
      { toFun := fun θ : Params A dIn dOut => θ.E, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }).differentiable
  have hr : ∀ ℓ, Differentiable ℝ (fun p : Params A dIn dOut × V => p.1.read ℓ) := fun ℓ =>
    (fstLin_lst (V := V) (F := Matrix d (A.r ℓ) ℝ)
      { toFun := fun θ : Params A dIn dOut => θ.read ℓ, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }).differentiable
  have hw : ∀ ℓ, Differentiable ℝ (fun p : Params A dIn dOut × V => p.1.write ℓ) := fun ℓ =>
    (fstLin_lst (V := V) (F := Matrix (A.w ℓ) d ℝ)
      { toFun := fun θ : Params A dIn dOut => θ.write ℓ, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }).differentiable
  have hD : Differentiable ℝ (fun p : Params A dIn dOut × V => p.1.D) :=
    (fstLin_lst (V := V) (F := Matrix d dOut ℝ)
      { toFun := fun θ : Params A dIn dOut => θ.D, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }).differentiable
  have hS : ∀ ℓ, Differentiable ℝ (fun p : Params A dIn dOut × V => ι p.2 ℓ) := fun ℓ =>
    (skipLin_lst (dIn := dIn) (dOut := dOut) A ι ℓ).differentiable
  -- every hidden state is differentiable in `(θ, v)`, by induction on `ℓ`
  have hh : ∀ ℓ : Fin (L + 1), Differentiable ℝ
      (fun p : Params A dIn dOut × V => hidden A (ι p.2) p.1 x ℓ) := by
    intro ℓ
    induction ℓ using Fin.induction with
    | zero =>
      -- `h_0 = x E`
      simp only [hidden_zero]
      exact differentiable_matMul_lst (differentiable_const x) hE
    | succ ℓ ih =>
      -- `h_{ℓ+1} = h_ℓ (ι v)_ℓ + f_ℓ (χ(h_ℓ) W_read) W_write`
      simp only [hidden_succ]
      exact (differentiable_matMul_lst ih (hS ℓ)).add
        (differentiable_matMul_lst ((hf ℓ).comp (differentiable_matMul_lst (hχ.comp ih)
          (hr ℓ))) (hw ℓ))
  -- the output `χ(h_L) D`
  simp only [evalSkips, eval]
  exact differentiable_matMul_lst (hχ.comp (hh (Fin.last L))) hD

end Copies

section Rotations

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [DecidableEq d] [LinearOrder d] in
/-- Helper (the twin of `mem_flat_of_hasDerivAt'`): if a curve `γ` through `p` with velocity `v`
keeps the function near `τ = 0`, then `v` is flat. -/
private theorem mem_flatSkips_of_hasDerivAt_lst {A : Arch T d L}
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (p : Params A dIn dOut × V)
    (γ : ℝ → Params A dIn dOut × V) (v : Params A dIn dOut × V) (hγ : HasDerivAt γ v 0)
    (hγ0 : γ 0 = p)
    (hconst : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ x : Matrix T dIn ℝ,
      evalSkips A ι (γ τ) x = evalSkips A ι p x) :
    v ∈ flatSkips A ι p := by
  rw [flatSkips, Submodule.mem_iInf]
  intro x
  rw [LinearMap.mem_ker]
  show fderiv ℝ (fun p' => evalSkips A ι p' x) p v = 0
  by_cases hx : DifferentiableAt ℝ (fun p' : Params A dIn dOut × V => evalSkips A ι p' x) p
  · -- the chain rule: `τ ↦ F_{γ(τ)}(x)` has derivative `D_p F(x) v` at `0`
    have hl : HasFDerivAt (fun p' => evalSkips A ι p' x)
        (fderiv ℝ (fun p' => evalSkips A ι p' x) p) (γ 0) := by
      rw [hγ0]
      exact hx.hasFDerivAt
    have h1 := hl.comp_hasDerivAt (0 : ℝ) hγ
    -- the same map is constant near `0`, so its derivative there is `0`
    have h2 : HasDerivAt ((fun p' => evalSkips A ι p' x) ∘ γ) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (evalSkips A ι p x)).congr_of_eventuallyEq
        (hconst.mono fun τ hτ => hτ x)
    exact h1.unique h2
  · -- not differentiable at `p`: Mathlib's derivative is `0`
    rw [fderiv_zero_of_not_differentiableAt hx, _root_.zero_apply]

/-! ### The rotations `exp (τ X_ℓ)` (copies of the private helpers of
`Dimension/UpperBoundRMSNorm.lean`) -/

-- As in Mathlib's `MatrixExponential.lean`: without this option the instances of the operator
-- norm (e.g. `CompleteSpace`) are not found.
omit [LinearOrder d] in
set_option backward.isDefEq.respectTransparency false in
/-- The derivative at `τ = 0` of an entry of `exp (τ Y)` is the entry of `Y` (computed with the
operator norm, under which matrices form a normed ring). -/
private theorem hasDerivAt_exp_smul_apply_lst (Y : Matrix d d ℝ) (i j : d) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) i j) (Y i j) 0 := by
  let _ : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℝ ℝ i j)).hasFDerivAt.comp_hasDerivAt 0 h

omit [LinearOrder d] in
/-- With the elementwise norm, the derivative of a matrix-valued function is taken entry by
entry. -/
private theorem hasDerivAt_matrix_lst {m n : Type*} [Fintype m] [Fintype n] {f : ℝ → Matrix m n ℝ}
    {f' : Matrix m n ℝ} {x : ℝ} (h : ∀ i j, HasDerivAt (fun τ => f τ i j) (f' i j) x) :
    HasDerivAt f f' x :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 (h i)

omit [LinearOrder d] in
/-- The derivative of `τ ↦ M exp (τ Y)` at `0` is `M Y`. -/
private theorem hasDerivAt_mul_exp_lst {m : Type*} [Fintype m] (M : Matrix m d ℝ)
    (Y : Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => M * NormedSpace.exp (τ • Y)) (M * Y) 0 :=
  hasDerivAt_matrix_lst fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_apply_lst Y k j).const_mul (M i k)

omit [LinearOrder d] in
/-- The derivative of `τ ↦ exp (τ Y) M` at `0` is `Y M`. -/
private theorem hasDerivAt_exp_mul_lst {n : Type*} [Fintype n] (Y : Matrix d d ℝ)
    (M : Matrix d n ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • Y) * M) (Y * M) 0 :=
  hasDerivAt_matrix_lst fun i j => by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_smul_apply_lst Y i k).mul_const (M k j)

-- See `hasDerivAt_exp_smul_apply_lst` for this option.
omit [LinearOrder d] in
set_option backward.isDefEq.respectTransparency false in
/-- The derivative of `τ ↦ exp (-τ Y) S exp (τ Z)` at `0` is `−Y S + S Z` (the product rule,
with the operator norm). -/
private theorem hasDerivAt_exp_mul_exp_lst (Y Z S : Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • -Y) * S * NormedSpace.exp (τ • Z))
      (-(Y * S) + S * Z) 0 := by
  let _ : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-Y) (0 : ℝ)
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)
  have h := (h1.mul_const S).fun_mul h2
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at h
  rw [neg_mul] at h
  exact h

omit [LinearOrder d] in
/-- `exp (τ Y) exp (-τ Y) = 1`. -/
private theorem exp_smul_mul_exp_smul_neg_lst (Y : Matrix d d ℝ) (τ : ℝ) :
    NormedSpace.exp (τ • Y) * NormedSpace.exp (τ • -Y) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).neg_right.smul_left τ).smul_right τ),
    smul_neg, add_neg_cancel, NormedSpace.exp_zero]

omit [LinearOrder d] in
/-- The invertible matrix `exp (τ Y)`, with inverse `exp (-τ Y)`. -/
private noncomputable def expGL_lst (Y : Matrix d d ℝ) (τ : ℝ) : GL d ℝ :=
  ⟨NormedSpace.exp (τ • Y), NormedSpace.exp (τ • -Y), exp_smul_mul_exp_smul_neg_lst Y τ,
    by simpa only [neg_neg] using exp_smul_mul_exp_smul_neg_lst (-Y) τ⟩

omit [LinearOrder d] in
/-- `exp (0 Y) = 1`. -/
private theorem expGL_zero_lst (Y : Matrix d d ℝ) : expGL_lst Y 0 = 1 := by
  apply Units.ext
  change NormedSpace.exp ((0 : ℝ) • Y) = 1
  rw [zero_smul, NormedSpace.exp_zero]

omit [LinearOrder d] in
/-- For antisymmetric `Y`, `exp (τ Y)` is orthogonal: `exp (τ Y)ᵀ = exp (τ Yᵀ) = exp (-τ Y)`. -/
private theorem expGL_mem_orthogonalGroup_lst {Y : Matrix d d ℝ} (hY : Yᵀ = -Y) (τ : ℝ) :
    (expGL_lst Y τ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  change (NormedSpace.exp (τ • Y))ᵀ * NormedSpace.exp (τ • Y) = 1
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, hY]
  simpa only [neg_neg] using exp_smul_mul_exp_smul_neg_lst (-Y) τ

omit [Fintype T] [Fintype dIn] [Fintype dOut] [LinearOrder d] in
/-- The curve `τ ↦ θ.cob (exp (τ X_ℓ)) (exp (τ X_ℓ))` passes through `θ` at `τ = 0`. -/
private theorem cob_expGL_zero_lst {A : Arch T d L} (θ : Params A dIn dOut)
    (X : Fin (L + 1) → Matrix d d ℝ) :
    θ.cob (fun ℓ => expGL_lst (X ℓ) 0) (fun ℓ => expGL_lst (X ℓ) 0) = θ := by
  simp only [expGL_zero_lst]
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [Params.cob, inv_one, Units.val_one, Matrix.mul_one, Matrix.one_mul]

omit [Fintype T] [LinearOrder d] in
/-- The curve `τ ↦ θ.cob (exp (τ X_ℓ)) (exp (τ X_ℓ))` has velocity `cobDir θ X` at `τ = 0`. -/
private theorem hasDerivAt_cob_expGL_lst {A : Arch T d L} (θ : Params A dIn dOut)
    (X : Fin (L + 1) → Matrix d d ℝ) :
    HasDerivAt (fun τ : ℝ => θ.cob (fun ℓ => expGL_lst (X ℓ) τ) (fun ℓ => expGL_lst (X ℓ) τ))
      (cobDir θ X) 0 := by
  -- The norm of the parameters is that of the tuple of their components.
  let e : Params A dIn dOut ≃L[ℝ] Params.Prod A dIn dOut :=
    Params.linearEquivProd.toContinuousLinearEquiv
  -- Componentwise: `E exp (τ X_0)`, `exp (-τ X_{ℓ-1}) W_read^ℓ`, `W_write^ℓ exp (τ X_ℓ)`,
  -- `exp (-τ X_L) D`.
  have key : HasDerivAt
      (fun τ : ℝ => e (θ.cob (fun ℓ => expGL_lst (X ℓ) τ) (fun ℓ => expGL_lst (X ℓ) τ)))
      (e (cobDir θ X)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · exact hasDerivAt_mul_exp_lst θ.E (X 0)
    · exact hasDerivAt_pi.2 fun ℓ =>
        (hasDerivAt_exp_mul_lst (-X ℓ.castSucc) (θ.read ℓ)).congr_deriv (Matrix.neg_mul _ _)
    · exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_mul_exp_lst (θ.write ℓ) (X ℓ.succ)
    · exact (hasDerivAt_exp_mul_lst (-X (Fin.last L)) θ.D).congr_deriv (Matrix.neg_mul _ _)
  -- Back to the parameters through `e⁻¹`.
  exact e.symm.hasFDerivAt.comp_hasDerivAt (0 : ℝ) key

omit [LinearOrder d] in
/-- **The rotations are flat** (Proposition 3.2 under pre-RMSNorm with the skips as parameters):
for antisymmetric `X_ℓ`, the orthogonal changes of basis `G_ℓ = exp (τ X_ℓ)` together with
`S_ℓ ↦ G_{ℓ-1}⁻¹ S_ℓ G_ℓ` keep the function, so their direction
`(cobDir θ X, −X_{ℓ-1} S_ℓ + S_ℓ X_ℓ)` is flat. -/
private theorem rot_mem_flatSkips_lst {A : Arch T d L} {ε : ℝ} (hA : A.χ = rmsNorm ε)
    (θ : Params A dIn dOut) (S : Fin L → Matrix d d ℝ) (X : Fin (L + 1) → Matrix d d ℝ)
    (hX : ∀ ℓ, (X ℓ)ᵀ = -X ℓ) :
    (cobDir θ X, fun ℓ => -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ)
      ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (θ, S) := by
  -- the curve `τ ↦ (θ.cob G_τ G_τ, cobSkip S G_τ)` with `G_τ ℓ = exp (τ X_ℓ)` and its velocity
  have hγ : HasDerivAt (fun τ : ℝ => (θ.cob (fun ℓ => expGL_lst (X ℓ) τ)
      (fun ℓ => expGL_lst (X ℓ) τ), cobSkip S (fun ℓ => expGL_lst (X ℓ) τ)))
      (cobDir θ X, fun ℓ => -(X ℓ.castSucc * S ℓ) + S ℓ * X ℓ.succ) 0 :=
    (hasDerivAt_cob_expGL_lst θ X).prodMk
      (hasDerivAt_pi.2 fun ℓ => hasDerivAt_exp_mul_exp_lst (X ℓ.castSucc) (X ℓ.succ) (S ℓ))
  refine mem_flatSkips_of_hasDerivAt_lst _ _ _ _ hγ ?_ ?_
  · -- at `τ = 0` the curve is at `(θ, S)`
    refine Prod.ext (cob_expGL_zero_lst θ X) ?_
    show cobSkip S (fun ℓ => expGL_lst (X ℓ) 0) = S
    funext ℓ
    simp only [cobSkip, expGL_zero_lst, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  · -- along the curve the function is kept: pre-RMSNorm commutes with the orthogonal `G_τ ℓ`
    refine Filter.Eventually.of_forall fun τ x => ?_
    have hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (expGL_lst (X ℓ) τ : Matrix d d ℝ))
        = A.χ h * (expGL_lst (X ℓ) τ : Matrix d d ℝ) := by
      intro ℓ h
      rw [hA]
      exact rmsNorm_mul_orthogonal ε (expGL_mem_orthogonalGroup_lst (hX ℓ) τ) h
    exact eval_cob (M := S) (θ := θ) (G := fun ℓ => expGL_lst (X ℓ) τ)
      (K := fun ℓ => expGL_lst (X ℓ) τ) (x := x) hχ

end Rotations

/-! ### An antisymmetric `X` with `X R` upper triangular is `0` -/

omit [DecidableEq d] in
/-- Helper: the entries `(i, j)`, `j < i`, of `X R`, linear in the antisymmetric `X`. -/
private noncomputable def lowerLin_lst (R : Matrix d d ℝ) :
    antisymmetric d →ₗ[ℝ] ({p : d × d // p.2 < p.1} → ℝ) where
  toFun X p := ((X : Matrix d d ℝ) * R) p.1.1 p.1.2
  map_add' X Y := by
    funext p
    simp only [Submodule.coe_add, Matrix.add_mul, Matrix.add_apply, Pi.add_apply]
  map_smul' c X := by
    funext p
    simp only [Submodule.coe_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
      Pi.smul_apply, RingHom.id_apply]

/-- Helper: for `R` invertible and upper triangular, an antisymmetric `X` with `X R` upper
triangular is `0`: `X = (X R) R⁻¹` is upper triangular, and an antisymmetric upper triangular
matrix vanishes. -/
private theorem lowerLin_injective_lst {R : Matrix d d ℝ} (hRt : R.BlockTriangular id)
    (hR : IsUnit R.det) : Function.Injective (lowerLin_lst R) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro X hX
  rw [LinearMap.mem_ker] at hX
  -- `X R` is upper triangular
  have h1 : ((X : Matrix d d ℝ) * R).BlockTriangular id := fun i j hij =>
    congrFun hX ⟨(i, j), hij⟩
  -- so is `X = (X R) R⁻¹`: the inverse of an upper triangular matrix is upper triangular
  have : Invertible R := R.invertibleOfIsUnitDet hR
  have h2 : (X : Matrix d d ℝ).BlockTriangular id := by
    have h := h1.mul (Matrix.blockTriangular_inv_of_blockTriangular hRt)
    rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hR, Matrix.mul_one] at h
  -- an antisymmetric upper triangular matrix is `0`
  have hX' : ∀ i j, (X : Matrix d d ℝ) j i = -(X : Matrix d d ℝ) i j := fun i j => by
    have h := congrFun (congrFun (show (X : Matrix d d ℝ)ᵀ = -(X : Matrix d d ℝ) from X.2) i) j
    rwa [transpose_apply, Matrix.neg_apply] at h
  apply Subtype.ext
  ext i j
  show (X : Matrix d d ℝ) i j = 0
  rcases lt_trichotomy i j with h | rfl | h
  · rw [hX' j i, h2 h, neg_zero]
  · have := hX' i i
    linarith
  · exact h2 h

/-- Helper: the map `X ↦ (X R)_{j < i}` is onto (injective between spaces of dimension
`d (d − 1)/2`). -/
private theorem lowerLin_surjective_lst {R : Matrix d d ℝ} (hRt : R.BlockTriangular id)
    (hR : IsUnit R.det) : Function.Surjective (lowerLin_lst R) := by
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1
    (lowerLin_injective_lst hRt hR)
  rw [finrank_antisymmetric, Module.finrank_fintype_fun_eq_card, card_gt_eq_card_lt_lst,
    card_lt_lst]

/-- Helper: for `R` invertible and upper triangular, every `a` is upper triangular after adding
`X R` for some antisymmetric `X`. -/
private theorem exists_add_mul_mem_upperTriangular_lst {R : Matrix d d ℝ}
    (hRt : R.BlockTriangular id) (hR : IsUnit R.det) (a : Matrix d d ℝ) :
    ∃ X : antisymmetric d, a + (X : Matrix d d ℝ) * R ∈ upperTriangular d := by
  -- `X` with `(X R)_{ij} = −a_{ij}` for `j < i`
  obtain ⟨X, hX⟩ := lowerLin_surjective_lst hRt hR (fun p => -a p.1.1 p.1.2)
  refine ⟨X, fun i j hij => ?_⟩
  have h := congrFun hX ⟨(i, j), hij⟩
  change ((X : Matrix d d ℝ) * R) i j = -a i j at h
  rw [Matrix.add_apply, h, add_neg_cancel]

/-! ### Triangular directions and flat directions -/

/-- Helper: at an invertible upper triangular skip `R`, every direction `w` of the family of all
skips is a direction `(η', a')` with an upper triangular `a'` plus a flat direction: the rotation
of `h_0` by an antisymmetric `X_0` moves the skip by `−X_0 R`. -/
private theorem exists_sub_mem_flatSkips_lst {A : Arch T d 1} {ε : ℝ} (hA : A.χ = rmsNorm ε)
    (θ : Params A dIn dOut) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) (w : Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) :
    ∃ u : Params A dIn dOut × (Fin 1 → upperTriangular d),
      w - (u.1, triSkips d 1 u.2) ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ))
        (θ, fun ℓ => (R ℓ : Matrix d d ℝ)) := by
  -- `X_0` antisymmetric with `a_0 + X_0 R_0` upper triangular
  obtain ⟨X₀, hX₀⟩ := exists_add_mul_mem_upperTriangular_lst (R 0).2 hR (w.2 0)
  -- the rotation of `h_0` by `X_0`, and none of `h_1`: a flat direction
  let X : Fin (1 + 1) → Matrix d d ℝ := Fin.cons (X₀ : Matrix d d ℝ) fun _ => 0
  have hX : ∀ ℓ, (X ℓ)ᵀ = -X ℓ := by
    intro ℓ
    refine Fin.cases ?_ (fun i => ?_) ℓ
    · exact X₀.2
    · simp only [X, Fin.cons_succ, transpose_zero, neg_zero]
  have hrot := rot_mem_flatSkips_lst hA θ (fun ℓ => (R ℓ : Matrix d d ℝ)) X hX
  let u : Params A dIn dOut × (Fin 1 → upperTriangular d) :=
    (w.1 - cobDir θ X, fun _ => ⟨w.2 0 + (X₀ : Matrix d d ℝ) * R 0, hX₀⟩)
  refine ⟨u, ?_⟩
  -- `w` minus the triangular direction `u` is that flat direction
  have heq : w - (u.1, triSkips d 1 u.2)
      = (cobDir θ X, fun ℓ => -(X ℓ.castSucc * (R ℓ : Matrix d d ℝ))
          + (R ℓ : Matrix d d ℝ) * X ℓ.succ) := by
    refine Prod.ext ?_ (funext fun ℓ => ?_)
    · exact sub_sub_cancel _ _
    · obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
      show w.2 0 - (w.2 0 + (X₀ : Matrix d d ℝ) * R 0)
        = -(X (Fin.castSucc 0) * (R 0 : Matrix d d ℝ)) + (R 0 : Matrix d d ℝ) * X (Fin.succ 0)
      simp only [X, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Matrix.mul_zero, add_zero,
        sub_add_cancel_left]
  rw [heq]
  exact hrot

omit [DecidableEq d] [LinearOrder d] in
/-- Helper: a flat direction is in the kernel of the Jacobian on every batch. -/
private theorem fderiv_batch_flat_lst {A : Arch T d L} (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hχ : Differentiable ℝ A.χ) (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) {w : Params A dIn dOut × (Fin L → Matrix d d ℝ)}
    (hw : w ∈ flatSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p) :
    fderiv ℝ (fun p' : Params A dIn dOut × (Fin L → Matrix d d ℝ) => fun i : Fin n =>
      evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p' (X i)) p w = 0 := by
  -- the derivative of the outputs on the batch is the tuple of the derivatives of the outputs
  have h : fderiv ℝ (fun p' : Params A dIn dOut × (Fin L → Matrix d d ℝ) => fun i : Fin n =>
        evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p' (X i)) p =
      ContinuousLinearMap.pi fun i => fderiv ℝ (fun p' =>
        evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p' (X i)) p :=
    fderiv_pi fun i => differentiable_evalSkips_lst A _ hf hχ (X i) p
  rw [h]
  funext i
  unfold flatSkips at hw
  exact LinearMap.mem_ker.1 (Submodule.mem_iInf _ |>.1 hw (X i))

/-- **One block under pre-RMSNorm (`ε > 0`), at an invertible upper triangular skip `R`:** the
family of upper triangular skips has the functional dimension of the family of all skips. -/
theorem funDimLearnedTri_eq_funDimLearned {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (θ : Params A dIn dOut)
    (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det) :
    funDimLearnedTri A (θ, R) = funDimLearned A (θ, fun ℓ => (R ℓ : Matrix d d ℝ)) := by
  have hχ : Differentiable ℝ A.χ := by
    rw [hA]
    exact differentiable_rmsNorm hε
  -- the inclusion `m : (θ, v) ↦ (θ, v)` of the triangular family into the full one
  let m : Params A dIn dOut × (Fin 1 → upperTriangular d)
      →L[ℝ] Params A dIn dOut × (Fin 1 → Matrix d d ℝ) :=
    (ContinuousLinearMap.id ℝ (Params A dIn dOut)).prodMap (triSkips d 1)
  apply le_antisymm
  · -- the restricted family has at most the functional dimension of the full one
    exact funDimSkips_comp_le A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (triSkips d 1)
      hf hχ θ R
  · -- on every batch the rank of the full family is at most that of the triangular one
    have hbdd : BddAbove {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
        r = jacobianRankSkips A (triSkips d 1) X (θ, R)} :=
      ⟨Module.finrank ℝ (Params A dIn dOut × (Fin 1 → upperTriangular d)), by
        rintro _ ⟨n, X, rfl⟩
        exact LinearMap.finrank_range_le _⟩
    unfold funDimLearnedTri funDimLearned funDimSkips
    refine csSup_le ⟨_, 0, fun i => i.elim0, rfl⟩ ?_
    rintro _ ⟨n, X, rfl⟩
    refine le_trans ?_ (le_csSup hbdd ⟨n, X, rfl⟩)
    -- the outputs on the batch: `G` for all skips, `G ∘ m` for the triangular ones
    let G : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) → Fin n → Matrix T dOut ℝ :=
      fun p' i => evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p' (X i)
    have hG : Differentiable ℝ G :=
      differentiable_pi.2 fun i => differentiable_evalSkips_lst A _ hf hχ (X i)
    have hd : fderiv ℝ (G ∘ m) (θ, R) = (fderiv ℝ G (m (θ, R))).comp m :=
      ((hG (m (θ, R))).hasFDerivAt.comp (θ, R) m.hasFDerivAt).fderiv
    show Module.finrank ℝ (LinearMap.range (fderiv ℝ G (m (θ, R))).toLinearMap)
      ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ (G ∘ m) (θ, R)).toLinearMap)
    rw [hd]
    refine Submodule.finrank_mono ?_
    -- every value `DG w` is `DG (m u)`, with `w − m u` flat
    rintro _ ⟨w, rfl⟩
    obtain ⟨u, hu⟩ := exists_sub_mem_flatSkips_lst hA θ R hR w
    refine ⟨u, ?_⟩
    have h0 := fderiv_batch_flat_lst hf hχ _ X hu
    rw [map_sub] at h0
    exact (sub_eq_zero.1 h0).symm

omit [Fintype T] [Fintype dOut] [LinearOrder d] in
/-- Helper: the orthogonal change of basis of the weights and the skips,
`(θ, S) ↦ (θ.cob Q Q, cobSkip S Q)`, is linear. -/
private noncomputable def cobLin_lst {A : Arch T d L} (Q : Fin (L + 1) → GL d ℝ) :
    (Params A dIn dOut × (Fin L → Matrix d d ℝ))
      →ₗ[ℝ] (Params A dIn dOut × (Fin L → Matrix d d ℝ)) where
  toFun p := (p.1.cob Q Q, cobSkip p.2 Q)
  map_add' p q := by
    refine Prod.ext (Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_) (funext fun ℓ => ?_) <;>
      simp only [Prod.fst_add, Prod.snd_add, Params.cob, cobSkip, Params.add_E, Params.add_read,
        Params.add_write, Params.add_D, Pi.add_apply, Matrix.add_mul, Matrix.mul_add]
  map_smul' c p := by
    refine Prod.ext (Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_) (funext fun ℓ => ?_) <;>
      simp only [Prod.smul_fst, Prod.smul_snd, Params.cob, cobSkip, Params.smul_E,
        Params.smul_read, Params.smul_write, Params.smul_D, Pi.smul_apply, Matrix.smul_mul,
        Matrix.mul_smul, RingHom.id_apply]

omit [Fintype T] [Fintype dIn] [Fintype dOut] [LinearOrder d] in
private theorem cobLin_lst_apply {A : Arch T d L} (Q : Fin (L + 1) → GL d ℝ)
    (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) :
    cobLin_lst Q p = (p.1.cob Q Q, cobSkip p.2 Q) := rfl

omit [Fintype T] [Fintype dOut] [LinearOrder d] in
/-- Helper: under pre-RMSNorm the orthogonal change of basis keeps the function. -/
private theorem evalSkips_cobLin_lst {A : Arch T d L} {ε : ℝ} (hA : A.χ = rmsNorm ε)
    (Q : Fin (L + 1) → GL d ℝ) (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) (x : Matrix T dIn ℝ) :
    evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) (cobLin_lst Q p) x
      = evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p x := by
  -- pre-RMSNorm commutes with every orthogonal `Q_ℓ`
  have hχ : ∀ ℓ (h : Matrix T d ℝ),
      A.χ (h * (Q ℓ : Matrix d d ℝ)) = A.χ h * (Q ℓ : Matrix d d ℝ) := by
    intro ℓ h
    rw [hA]
    exact rmsNorm_mul_orthogonal ε (hQ ℓ) h
  exact eval_cob (M := p.2) (θ := p.1) (G := Q) (K := Q) (x := x) hχ

omit [LinearOrder d] in
/-- Helper: the functional dimension does not drop under an orthogonal change of basis: on every
batch the Jacobian at `p` is that at `g p` composed with `g` (the chain rule for `F ∘ g = F`). -/
private theorem funDimLearned_le_cobLin_lst {A : Arch T d L} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (Q : Fin (L + 1) → GL d ℝ)
    (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ)
    (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) :
    funDimLearned A p ≤ funDimLearned A (cobLin_lst Q p) := by
  have hχ : Differentiable ℝ A.χ := by
    rw [hA]
    exact differentiable_rmsNorm hε
  -- `g`, as a continuous linear map
  let g := LinearMap.toContinuousLinearMap (cobLin_lst (A := A) (dIn := dIn) (dOut := dOut) Q)
  -- the ranks at `g p` are bounded by the number of parameters
  have hbdd : BddAbove {r : ℕ | ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      r = jacobianRankSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) X (g p)} :=
    ⟨Module.finrank ℝ (Params A dIn dOut × (Fin L → Matrix d d ℝ)), by
      rintro _ ⟨n, X, rfl⟩
      exact LinearMap.finrank_range_le _⟩
  unfold funDimLearned funDimSkips
  refine csSup_le ⟨_, 0, fun i => i.elim0, rfl⟩ ?_
  rintro _ ⟨n, X, rfl⟩
  refine le_trans ?_ (le_csSup hbdd ⟨n, X, rfl⟩)
  -- the outputs on the batch: `G ∘ g = G`
  let G : Params A dIn dOut × (Fin L → Matrix d d ℝ) → Fin n → Matrix T dOut ℝ :=
    fun p' i => evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ)) p' (X i)
  have hG : Differentiable ℝ G :=
    differentiable_pi.2 fun i => differentiable_evalSkips_lst A _ hf hχ (X i)
  have hcomp : G ∘ g = G := funext fun p' => funext fun i => evalSkips_cobLin_lst hA Q hQ p' (X i)
  have hd : fderiv ℝ (G ∘ g) p = (fderiv ℝ G (g p)).comp g :=
    ((hG (g p)).hasFDerivAt.comp p g.hasFDerivAt).fderiv
  rw [hcomp] at hd
  -- the range of a composition lies in the range of the outer map
  show Module.finrank ℝ (LinearMap.range (fderiv ℝ G p).toLinearMap)
    ≤ Module.finrank ℝ (LinearMap.range (fderiv ℝ G (g p)).toLinearMap)
  rw [hd]
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

omit [Fintype T] [Fintype dOut] [LinearOrder d] in
/-- Helper: `a (a⁻¹ B) = B` for `a : GL d ℝ` and a rectangular `B`. -/
private theorem gl_mul_inv_mul_lst {n : Type*} (a : GL d ℝ) (B : Matrix d n ℝ) :
    (a : Matrix d d ℝ) * ((↑a⁻¹ : Matrix d d ℝ) * B) = B := by
  rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

omit [Fintype T] [Fintype dIn] [Fintype dOut] [LinearOrder d] in
/-- Helper: the change of basis by `Q⁻¹` undoes that by `Q`. -/
private theorem cobLin_inv_cobLin_lst {A : Arch T d L} (Q : Fin (L + 1) → GL d ℝ)
    (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) :
    cobLin_lst (fun ℓ => (Q ℓ)⁻¹) (cobLin_lst Q p) = p := by
  refine Prod.ext (Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_) (funext fun ℓ => ?_) <;>
    simp only [cobLin_lst_apply, Params.cob, cobSkip, inv_inv, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one, gl_mul_inv_mul_lst]

/-- **The functional dimension with full learned skips is invariant under orthogonal changes of
basis** (pre-RMSNorm, `ε > 0`): at `(θ.cob Q Q, (Q_{ℓ-1}⁻¹ A_ℓ Q_ℓ))` it is the same as at
`(θ, (A_ℓ))`. -/
theorem funDimLearned_cob {A : Arch T d L} {ε : ℝ} (hε : 0 < ε) (hA : A.χ = rmsNorm ε)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (θ : Params A dIn dOut) (S : Fin L → Matrix d d ℝ)
    (Q : Fin (L + 1) → GL d ℝ) (hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) :
    funDimLearned A (θ.cob Q Q, cobSkip S Q) = funDimLearned A (θ, S) := by
  -- the inverses `Q_ℓ⁻¹ = Q_ℓᵀ` are orthogonal too
  have hQ' : ∀ ℓ, ((Q ℓ)⁻¹ : GL d ℝ).val ∈ Matrix.orthogonalGroup d ℝ := by
    intro ℓ
    rw [coe_inv_of_mem_orthogonalGroup (Q ℓ) (hQ ℓ)]
    refine (Matrix.mem_orthogonalGroup_iff d ℝ).2 ?_
    rw [Matrix.transpose_transpose]
    exact (Matrix.mem_orthogonalGroup_iff' d ℝ).1 (hQ ℓ)
  apply le_antisymm
  · -- the change of basis by `Q⁻¹` brings `(θ.cob Q Q, cobSkip S Q)` back to `(θ, S)`
    have h := funDimLearned_le_cobLin_lst hε hA hf (fun ℓ => (Q ℓ)⁻¹) hQ' (cobLin_lst Q (θ, S))
    rw [cobLin_inv_cobLin_lst] at h
    exact h
  · exact funDimLearned_le_cobLin_lst hε hA hf Q hQ (θ, S)

variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)] {ε : ℝ}

/-! ### The named forms: the common part -/

omit [DecidableEq d] [LinearOrder d] in
/-- Helper: the full skips `Fin 1 → Matrix d d ℝ` carry the Borel σ-algebra of their norm
topology (the instance of Mathlib is stated for the entrywise topology of `Matrix`, the same
topology; a copy of the private `borelSpace_skips_lsk` of `OneBlock/LearnedSkipKinds.lean`). -/
private theorem borelSpace_skips_lst : BorelSpace (Fin 1 → Matrix d d ℝ) :=
  inferInstanceAs (BorelSpace (Fin 1 → d → d → ℝ))

omit [Fintype T] [Fintype d] [DecidableEq d] [LinearOrder d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `d (d + 1)/2 + d (d − 1)/2 = d²` (both products are even; a copy of the private
`half_add_half_lsk` of `OneBlock/LearnedSkipKinds.lean`). -/
private theorem half_add_half_lst (n : ℕ) : n * (n + 1) / 2 + n * (n - 1) / 2 = n ^ 2 := by
  have h1 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
  have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  have h3 : n * (n + 1) + n * (n - 1) = 2 * n ^ 2 := by
    cases n with
    | zero => rfl
    | succ m => rw [Nat.add_sub_cancel]; ring
  generalize n * (n + 1) = y at h1 h3 ⊢
  generalize n * (n - 1) = x at h2 h3 ⊢
  generalize n ^ 2 = q at h3 ⊢
  omega

omit [DecidableEq d] [LinearOrder d] in
/-- Helper: `ae_funDimSkips_ge` with the Borel structure of `V` and the Haar property of `μ` as
explicit arguments (Mathlib states the Borel instance of `Matrix` for its entrywise topology, the
same topology as that of the norm, but not syntactically). -/
private theorem ae_funDimSkips_ge_lst {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] (hB : BorelSpace V) (A : Arch T d L)
    (ι : V →L[ℝ] (Fin L → Matrix d d ℝ)) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (hχ : AnalyticOnNhd ℝ A.χ Set.univ) (μ : Measure (Params A dIn dOut × V))
    (hμ : μ.IsAddHaarMeasure) (p₀ : Params A dIn dOut × V) :
    ∀ᵐ p ∂μ, funDimSkips A ι p₀ ≤ funDimSkips A ι p :=
  ae_funDimSkips_ge A ι hf hχ μ p₀

omit [LinearOrder d] in
/-- Helper: if a square matrix that depends linearly on a point of `E` is the identity at one
point, it is invertible at almost every point: its determinant is analytic and not identically
zero (the private `ae_isUnit_det_of_linear` of `Generic/Params.lean`, for any `E`). -/
private theorem ae_isUnit_det_lst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] (hB : BorelSpace E) (μ : Measure E)
    (hμ : μ.IsAddHaarMeasure) (Φ : E →ₗ[ℝ] Matrix d d ℝ) (x₀ : E) (h₀ : Φ x₀ = 1) :
    ∀ᵐ x ∂μ, IsUnit (Φ x).det := by
  -- the entries are linear, so the determinant is analytic
  have hentry : ∀ i j, AnalyticOnNhd ℝ (fun x => Φ x i j) Set.univ := fun i j =>
    (LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℝ ℝ i j) ∘ₗ Φ)).analyticOnNhd _
  have hφ : AnalyticOnNhd ℝ (fun x => (Φ x).det) Set.univ := by
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => hentry (σ i) i)
  -- it is `1` at `x₀`, so its zero set is null
  have hnull := measure_zeroSet_of_analytic μ hφ ⟨x₀, by rw [h₀, Matrix.det_one]; exact one_ne_zero⟩
  rw [ae_iff]
  simpa only [isUnit_iff_ne_zero, not_not] using hnull

/-- Helper (the common part of the four kinds): for one real-analytic block under pre-RMSNorm
(`ε > 0`), if the family of all skips has `fd + (d (d − 1) + s) = P + d²` at almost every
`(θ, A)`, then the family of upper triangular skips has
`fd + (d (d − 1)/2 + s) = P + d (d + 1)/2` at almost every `(θ, A)`, `A` upper triangular. -/
private theorem ae_funDimLearnedTri_of_full_lst {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (μ : Measure (Params A dIn dOut × (Fin 1 → upperTriangular d))) [hμ : μ.IsAddHaarMeasure]
    {s : ℕ}
    (hval : ∀ (ν : Measure (Params A dIn dOut × (Fin 1 → Matrix d d ℝ))) [ν.IsAddHaarMeasure],
      ∀ᵐ p ∂ν, funDimLearned A p + (Fintype.card d * (Fintype.card d - 1) + s)
        = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2) :
    ∀ᵐ p ∂μ, funDimLearnedTri A p + (Fintype.card d * (Fintype.card d - 1) / 2 + s)
      = Module.finrank ℝ (Params A dIn dOut) + Fintype.card d * (Fintype.card d + 1) / 2 := by
  have hf' : ∀ ℓ, Differentiable ℝ (A.f ℓ) :=
    fun ℓ => differentiableOn_univ.1 (hf ℓ).differentiableOn
  have hχ : AnalyticOnNhd ℝ A.χ Set.univ := by
    rw [hA]
    exact analyticOnNhd_rmsNorm hε
  have hχ' : Differentiable ℝ A.χ := by
    rw [hA]
    exact differentiable_rmsNorm hε
  -- a Haar measure `ν` on the weights and the full skips, with the value of the full family
  have hBs : BorelSpace (Fin 1 → Matrix d d ℝ) := borelSpace_skips_lst
  have : LocallyCompactSpace (Fin 1 → Matrix d d ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 1 → d → d → ℝ))
  have hBp : BorelSpace (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) := Prod.borelSpace
  let ν : Measure (Params A dIn dOut × (Fin 1 → Matrix d d ℝ)) := Measure.addHaar
  have hνH : ν.IsAddHaarMeasure := inferInstance
  have hν := hval ν
  -- the upper bound: at every point the triangular family has at most the generic value of the
  -- full family (it is a restriction, and the generic value of the full family is the largest)
  have hup : ∀ p : Params A dIn dOut × (Fin 1 → upperTriangular d),
      funDimLearnedTri A p + (Fintype.card d * (Fintype.card d - 1) + s)
        ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
    intro p
    have h1 : funDimLearnedTri A p ≤ funDimLearned A (p.1, triSkips d 1 p.2) :=
      funDimSkips_comp_le A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (triSkips d 1)
        hf' hχ' p.1 p.2
    obtain ⟨q, hq1, hq2⟩ := ((ae_funDimSkips_ge_lst hBs A (ContinuousLinearMap.id ℝ _) hf hχ ν
      hνH (p.1, triSkips d 1 p.2)).and hν).exists
    change funDimLearned A _ ≤ funDimLearned A q at hq1
    omega
  -- at almost every full point the skip `S_0` is invertible
  have hdet : ∀ᵐ p ∂ν, IsUnit (p.2 0).det :=
    ae_isUnit_det_lst hBp ν hνH ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Matrix d d ℝ) 0)
      ∘ₗ (LinearMap.snd ℝ (Params A dIn dOut) (Fin 1 → Matrix d d ℝ))) (0, fun _ => 1) rfl
  -- the lower bound: a generic full point `p₁` with `S_0` invertible
  obtain ⟨p₁, hp₁, hdet₁⟩ := (hν.and hdet).exists
  -- QR: an orthogonal `Q₀` with `Q₀ᵀ S_0` upper triangular
  obtain ⟨Q₀, hQ₀, htri⟩ := exists_orthogonal_transpose_mul_upperTriangular (p₁.2 0)
  let G₀ : GL d ℝ := ⟨Q₀, Q₀ᵀ, (Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ₀,
    (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hQ₀⟩
  -- the changes of basis `Q₀` at `h_0` and `1` at `h_1`
  let Q : Fin (1 + 1) → GL d ℝ := Fin.cons G₀ fun _ => 1
  have hQ : ∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := by
    intro ℓ
    refine Fin.cases hQ₀ (fun i => ?_) ℓ
    simp only [Q, Fin.cons_succ, Units.val_one]
    exact one_mem _
  -- they carry `S` to the triangular skip `R = Q₀ᵀ S_0`, invertible
  let R : Fin 1 → upperTriangular d := fun _ => ⟨Q₀ᵀ * p₁.2 0, htri⟩
  have hR : IsUnit (R 0 : Matrix d d ℝ).det := by
    show IsUnit (Q₀ᵀ * p₁.2 0).det
    rw [Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse ((Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ₀)).mul
      hdet₁
  have hcob : cobSkip p₁.2 Q = fun ℓ => (R ℓ : Matrix d d ℝ) := by
    funext ℓ
    obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
    show (↑(Q (Fin.castSucc 0))⁻¹ : Matrix d d ℝ) * p₁.2 0 * (Q (Fin.succ 0) : Matrix d d ℝ)
      = Q₀ᵀ * p₁.2 0
    simp only [Q, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Units.val_one, Matrix.mul_one]
    rfl
  -- so the triangular family has at `(θ₁.cob Q Q, R)` the generic value of the full family
  have hval₁ : funDimLearnedTri A (p₁.1.cob Q Q, R) = funDimLearned A p₁ := by
    rw [funDimLearnedTri_eq_funDimLearned hε hA hf' _ R hR, ← hcob]
    exact funDimLearned_cob hε hA hf' p₁.1 p₁.2 Q hQ
  -- and almost every triangular point has at least that
  have hBt : BorelSpace (Fin 1 → upperTriangular d) := inferInstance
  have hge := ae_funDimSkips_ge_lst hBt A (triSkips d 1) hf hχ μ hμ (p₁.1.cob Q Q, R)
  have h1 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  have h2 := half_add_half_lst (Fintype.card d)
  filter_upwards [hge] with p hp
  have hp' := hup p
  change funDimLearnedTri A _ ≤ funDimLearnedTri A p at hp
  rw [hval₁] at hp
  generalize Fintype.card d * (Fintype.card d - 1) = x at h1 h2 hp' hp₁ ⊢
  generalize Fintype.card d * (Fintype.card d + 1) = y at h2 ⊢
  generalize Fintype.card d ^ 2 = q at h2 hp' hp₁
  omega

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
  have hf : ∀ ℓ, AnalyticOnNhd ℝ
      ((Arch.mlp (T := T) (d := d) Real.tanh (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_tanh ℓ
  -- the value of the family of all skips at generic `(θ, A)` (with `s = 0`)
  have h := ae_funDimLearnedTri_of_full_lst (s := 0) hε rfl hf μ fun ν =>
    (ae_funDimLearned_tanh_rmsNorm hε ν hd hdIn hdOut hhid).mono fun p hp => by
      rw [add_zero]
      exact hp
  simpa only [add_zero] using h

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
  -- `fd + d (d − 1)/2 + s = P + d (d + 1)/2` and `fd₁ + d (d − 1)/2 + s = P`
  filter_upwards [ae_funDimLearnedTri_tanh_rmsNorm hε μ hd hdIn hdOut hhid] with p hp
  filter_upwards [ae_funDim_tanh_residual_rmsNorm hε ν hd hdIn hdOut] with θ' hθ'
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at hp hθ'
  generalize Fintype.card d * (Fintype.card d + 1) / 2 = b at hp ⊢
  omega

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
  have hf : ∀ ℓ, AnalyticOnNhd ℝ
      ((Arch.mlp (T := T) (d := d) gelu (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_mlp analyticOnNhd_gelu ℓ
  -- the value of the family of all skips at generic `(θ, A)` (with `s = 0`)
  have h := ae_funDimLearnedTri_of_full_lst (s := 0) hε rfl hf μ fun ν =>
    (ae_funDimLearned_gelu_rmsNorm hε ν hd hdIn hdOut hhid).mono fun p hp => by
      rw [add_zero]
      exact hp
  simpa only [add_zero] using h

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
  -- `fd + d (d − 1)/2 + s = P + d (d + 1)/2` and `fd₁ + d (d − 1)/2 + s = P`
  filter_upwards [ae_funDimLearnedTri_gelu_rmsNorm hε μ hd hdIn hdOut hhid] with p hp
  filter_upwards [ae_funDim_gelu_residual_rmsNorm hε ν hd hdIn hdOut] with θ' hθ'
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at hp hθ'
  generalize Fintype.card d * (Fintype.card d + 1) / 2 = b at hp ⊢
  omega

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
  have hf : ∀ ℓ, AnalyticOnNhd ℝ
      ((Arch.gated (T := T) (d := d) silu (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_gated analyticOnNhd_silu ℓ
  -- the value of the family of all skips at generic `(θ, A)`
  exact ae_funDimLearnedTri_of_full_lst (s := ∑ ℓ, Fintype.card (hid ℓ)) hε rfl hf μ fun ν =>
    ae_funDimLearned_swiglu_rmsNorm hε ν hd hdIn hdOut hhid

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
  -- `fd + d (d − 1)/2 + s = P + d (d + 1)/2` and `fd₁ + d (d − 1)/2 + s = P`
  filter_upwards [ae_funDimLearnedTri_swiglu_rmsNorm hε μ hd hdIn hdOut hhid] with p hp
  filter_upwards [ae_funDim_swiglu_residual_rmsNorm hε ν hd hdIn hdOut] with θ' hθ'
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at hp hθ'
  generalize Fintype.card d * (Fintype.card d + 1) / 2 = b at hp ⊢
  omega

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
  have hf : ∀ ℓ, AnalyticOnNhd ℝ
      ((Arch.gated (T := T) (d := d) gelu (rmsNorm ε) hid).f ℓ) Set.univ :=
    fun ℓ => analyticOnNhd_f_gated analyticOnNhd_gelu ℓ
  -- the value of the family of all skips at generic `(θ, A)`
  exact ae_funDimLearnedTri_of_full_lst (s := ∑ ℓ, Fintype.card (hid ℓ)) hε rfl hf μ fun ν =>
    ae_funDimLearned_geglu_rmsNorm hε ν hd hdIn hdOut hhid

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
  -- `fd + d (d − 1)/2 + s = P + d (d + 1)/2` and `fd₁ + d (d − 1)/2 + s = P`
  filter_upwards [ae_funDimLearnedTri_geglu_rmsNorm hε μ hd hdIn hdOut hhid] with p hp
  filter_upwards [ae_funDim_geglu_residual_rmsNorm hε ν hd hdIn hdOut] with θ' hθ'
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = a at hp hθ'
  generalize Fintype.card d * (Fintype.card d + 1) / 2 = b at hp ⊢
  omega

end Skips
