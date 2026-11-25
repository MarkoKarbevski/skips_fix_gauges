import SkipsLean.Network.LayerNorm
import SkipsLean.Dimension.FunDimFamily

/-!
# LayerNorm: the difference in redundancy between skipless and residual networks

Paper (skips paper), Proposition A.15 (iii): "If the gains `γ` have nonzero entries, the
difference in redundancy between the skipless and the residual version of the LayerNorm network
equals the difference for the reduced networks of (ii)." Its proof: "The reduced parameters are
`√(d_model/(d_model − 1)) Ū^⊤ diag(γ) W` and `b + β W` for each read, `W Ū` and `b Ū` for each
write, `E Ū` for the embedding, and the analogous expressions for the readout. For `γ` with
nonzero entries each is linear and onto in `W`, `b` or `E`, so the derivative of the map from the
parameters of the LayerNorm network to those of the reduced network is onto. The LayerNorm
network computes the reduced network's function composed with this map, so by the chain rule
every batch Jacobian of the LayerNorm network is that of the reduced network times this
derivative, and at corresponding parameters both have the same functional dimension, and the
redundancy of the LayerNorm network is that of the reduced network plus the difference of the
parameter counts. That difference is the same for the skipless and the residual versions, which
have the same shapes."

Here, for the pre-LayerNorm networks of `Network/LayerNorm.lean` (any blocks, with biases):

* `ParamsLN A d_in d_out`: the parameters of a pre-LayerNorm network, the weights and biases
  with the gains `γ_ℓ` and the biases `β_ℓ` of its `L + 1` LayerNorms; `evalLNParams`: its
  function as a family in these parameters; `reduceLNParams ε U q`: "the map from the parameters
  of the LayerNorm network to those of the reduced network".
* `exists_hasFDerivAt_reduceLNParams_surjective`: for gains with nonzero entries its derivative
  is onto.
* `funDimOf_evalLNParams_eq_funDimB_reduceLN`: "at corresponding parameters both have the same
  functional dimension", for stream matrices that commute with `Z`; no differentiability of the
  blocks is asked (`Dimension/FunDimFamily.lean`).
* `funDimOf_evalLNParams_skipless`, `funDimOf_evalLNParams_residual`: the same by name;
  `funDimOf_evalLNParams_residual_add_skipless`: part (iii). The redundancy is the number of
  parameters minus the functional dimension, and the skipless and the residual version have the
  same parameters, so the statement on the differences of the redundancies is the statement
  that the functional dimension rises by the same amount from the skipless to the residual
  version in the LayerNorm network and in the reduced network; it is written without
  subtraction.

Numeric check: `layernorm_reduction_check_2026-11-25.py`, part (iii) (six cases; the rank is
read at the largest gap of the singular values).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d m dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype m]
  [DecidableEq m] [Fintype dIn] [Fintype dOut]
variable {A : Arch T d L}

/-- **The parameters of a pre-LayerNorm network:** the weights and the biases, and the gains
`γ_0, …, γ_L` and the biases `β_0, …, β_L` of its LayerNorms. -/
abbrev ParamsLN (A : Arch T d L) (dIn dOut : Type*) : Type _ :=
  ParamsB A dIn dOut × ((Fin (L + 1) → d → ℝ) × (Fin (L + 1) → d → ℝ))

/-- The function of the pre-LayerNorm network at the parameters `q = ((θ, b), (γ, β))`. -/
noncomputable def evalLNParams (A : Arch T d L) (ε : ℝ) (S : Fin L → Matrix d d ℝ)
    (q : ParamsLN A dIn dOut) (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  evalLN A ε S q.1.1 q.1.2 q.2.1 q.2.2 x

/-- **"The map from the parameters of the LayerNorm network to those of the reduced network"**
of Proposition A.15 (ii), for a matrix `U` whose columns are an orthonormal basis of `V`. -/
noncomputable def reduceLNParams (ε : ℝ) (U : Matrix d m ℝ) (q : ParamsLN A dIn dOut) :
    ParamsB (A.withNorm (rmsNorm (T := T) (d := m)
      (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ)))) dIn dOut :=
  (q.1.1.reduceLN ε U q.2.1, q.1.2.reduceLN ε U q.1.1 q.2.2)

/-- The architecture of the reduced network, as a shorthand. -/
private noncomputable abbrev redArch_lnr (A : Arch T d L) (ε : ℝ) (m : Type*) [Fintype m] :
    Arch T m L :=
  A.withNorm (rmsNorm (T := T) (d := m) (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ)))

/-- The weights of a preimage under `reduceLNParams` at the gains `γ`: `E U^⊤`,
`c⁻¹ diag(γ)⁻¹ U R`, `W U^⊤`, `c⁻¹ diag(γ_L)⁻¹ U D`, with `c = √(d/m)`. -/
private noncomputable def invW_lnr (U : Matrix d m ℝ) (γ : Fin (L + 1) → d → ℝ) {ε : ℝ}
    (y : Params (redArch_lnr A ε m) dIn dOut) : Params A dIn dOut where
  E := y.E * Uᵀ
  read ℓ := (Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ)))⁻¹
    • (Matrix.diagonal (fun i => (γ ℓ.castSucc i)⁻¹) * U * y.read ℓ)
  write ℓ := y.write ℓ * Uᵀ
  D := (Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ)))⁻¹
    • (Matrix.diagonal (fun i => (γ (Fin.last L) i)⁻¹) * U * y.D)

/-- The biases of a preimage under `reduceLNParams` at the LayerNorm biases `β`: `b_E U^⊤`,
`b_read − β W_read`, `b_write U^⊤`, `b_D − β D`. -/
private noncomputable def invB_lnr (U : Matrix d m ℝ) (γ β : Fin (L + 1) → d → ℝ) {ε : ℝ}
    (y : ParamsB (redArch_lnr A ε m) dIn dOut) : Biases A dOut where
  E := y.2.E ᵥ* Uᵀ
  read ℓ := y.2.read ℓ - β ℓ.castSucc ᵥ* (invW_lnr U γ y.1).read ℓ
  write ℓ := y.2.write ℓ ᵥ* Uᵀ
  D := y.2.D - β (Fin.last L) ᵥ* (invW_lnr U γ y.1).D

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- `c c⁻¹ M = M` for `c = √(d/m)` and any matrix `M` with rows indexed by `m`: either `m` is
empty, or `U^⊤ U = I` forces `d` to be nonempty and then `c > 0`. -/
private theorem sqrt_mul_inv_smul_lnr (U : Matrix d m ℝ) (hU : Uᵀ * U = 1) {n : Type*}
    (M : Matrix m n ℝ) :
    (Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ))
      * (Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ)))⁻¹) • M = M := by
  rcases isEmpty_or_nonempty m with hm | ⟨⟨i⟩⟩
  · ext a b
    exact isEmptyElim a
  · -- `(U^⊤ U)_{ii} = 1`, so some `U_{ki} ≠ 0` and `d` is nonempty
    have h := congrFun (congrFun hU i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    have hne : ∑ k, Uᵀ i k * U k i ≠ 0 := by
      rw [h]
      exact one_ne_zero
    obtain ⟨k, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hc : 0 < Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ)) :=
      Real.sqrt_pos.2 (div_pos (Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨k⟩))
        (Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨i⟩)))
    rw [mul_inv_cancel₀ hc.ne', one_smul]

omit [Fintype T] [Fintype m] [DecidableEq m] [Fintype dIn] [Fintype dOut] in
/-- `diag(v) diag(v)⁻¹ = I` for a vector with nonzero entries. -/
private theorem diagonal_mul_inv_lnr {v : d → ℝ} (hv : ∀ i, v i ≠ 0) :
    Matrix.diagonal v * Matrix.diagonal (fun i => (v i)⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have h : (fun i => v i * (v i)⁻¹) = fun _ => (1 : ℝ) := funext fun i => mul_inv_cancel₀ (hv i)
  rw [h, Matrix.diagonal_one]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- `U^⊤ diag(v) diag(v)⁻¹ U M = M` for `v` with nonzero entries and `U^⊤ U = I`. -/
private theorem transpose_diagonal_inv_lnr (U : Matrix d m ℝ) (hU : Uᵀ * U = 1) {v : d → ℝ}
    (hv : ∀ i, v i ≠ 0) {n : Type*} (M : Matrix m n ℝ) :
    Uᵀ * Matrix.diagonal v * (Matrix.diagonal (fun i => (v i)⁻¹) * U * M) = M := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.diagonal v), diagonal_mul_inv_lnr hv, Matrix.one_mul,
    ← Matrix.mul_assoc, hU, Matrix.one_mul]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **The preimage:** at gains with nonzero entries, `reduceLNParams` sends `(R y, (γ, β))` to
`y`. -/
private theorem reduceLNParams_inv_lnr (ε : ℝ) (U : Matrix d m ℝ) (hU : Uᵀ * U = 1)
    (γ β : Fin (L + 1) → d → ℝ) (hγ : ∀ ℓ i, γ ℓ i ≠ 0)
    (y : ParamsB (redArch_lnr A ε m) dIn dOut) :
    reduceLNParams ε U ((invW_lnr U γ y.1, invB_lnr U γ β y), (γ, β)) = y := by
  obtain ⟨θ', b'⟩ := y
  refine Prod.ext (Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
    (Biases.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
  · -- `E U^⊤ U = E`
    simp only [reduceLNParams, Params.reduceLN, invW_lnr]
    rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  · -- `c U^⊤ diag(γ) c⁻¹ diag(γ)⁻¹ U R = R`
    simp only [reduceLNParams, Params.reduceLN, invW_lnr]
    rw [Matrix.mul_smul, smul_smul, transpose_diagonal_inv_lnr U hU (hγ _),
      sqrt_mul_inv_smul_lnr U hU]
  · simp only [reduceLNParams, Params.reduceLN, invW_lnr]
    rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  · simp only [reduceLNParams, Params.reduceLN, invW_lnr]
    rw [Matrix.mul_smul, smul_smul, transpose_diagonal_inv_lnr U hU (hγ _),
      sqrt_mul_inv_smul_lnr U hU]
  · -- `b_E U^⊤ U = b_E`
    simp only [reduceLNParams, Biases.reduceLN, invB_lnr, Matrix.vecMul_vecMul, hU,
      Matrix.vecMul_one]
  · -- `(b − β W) + β W = b`
    simp only [reduceLNParams, Biases.reduceLN, invB_lnr, sub_add_cancel]
  · simp only [reduceLNParams, Biases.reduceLN, invB_lnr, Matrix.vecMul_vecMul, hU,
      Matrix.vecMul_one]
  · simp only [reduceLNParams, Biases.reduceLN, invB_lnr, sub_add_cancel]

omit [Fintype T] [DecidableEq m] [Fintype dIn] [Fintype dOut] in
/-- `reduceLNParams` is additive in the weights and the biases, for fixed gains and LayerNorm
biases. -/
private theorem reduceLNParams_add_lnr (ε : ℝ) (U : Matrix d m ℝ) (v w : ParamsB A dIn dOut)
    (g : (Fin (L + 1) → d → ℝ) × (Fin (L + 1) → d → ℝ)) :
    reduceLNParams ε U (v + w, g) = reduceLNParams ε U (v, g) + reduceLNParams ε U (w, g) := by
  refine Prod.ext (Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
    (Biases.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
  · simp only [reduceLNParams, Params.reduceLN, Prod.fst_add, Params.add_E, Matrix.add_mul]
  · simp only [reduceLNParams, Params.reduceLN, Prod.fst_add, Params.add_read, Matrix.mul_add,
      smul_add]
  · simp only [reduceLNParams, Params.reduceLN, Prod.fst_add, Params.add_write, Matrix.add_mul]
  · simp only [reduceLNParams, Params.reduceLN, Prod.fst_add, Params.add_D, Matrix.mul_add,
      smul_add]
  · simp only [reduceLNParams, Biases.reduceLN, Prod.snd_add, Biases.add_E, Matrix.add_vecMul]
  · simp only [reduceLNParams, Biases.reduceLN, Prod.fst_add, Prod.snd_add, Biases.add_read,
      Params.add_read, Matrix.vecMul_add]
    abel
  · simp only [reduceLNParams, Biases.reduceLN, Prod.snd_add, Biases.add_write,
      Matrix.add_vecMul]
  · simp only [reduceLNParams, Biases.reduceLN, Prod.fst_add, Prod.snd_add, Biases.add_D,
      Params.add_D, Matrix.vecMul_add]
    abel

omit [Fintype T] [DecidableEq m] [Fintype dIn] [Fintype dOut] in
/-- The preimage of `0` is `0`. -/
private theorem inv_zero_lnr (U : Matrix d m ℝ) (γ β : Fin (L + 1) → d → ℝ) {ε : ℝ} :
    ((invW_lnr U γ (0 : ParamsB (redArch_lnr A ε m) dIn dOut).1,
      invB_lnr U γ β (0 : ParamsB (redArch_lnr A ε m) dIn dOut)) : ParamsB A dIn dOut) = 0 := by
  refine Prod.ext (Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
    (Biases.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_) <;>
    simp [invW_lnr, invB_lnr]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype m] [DecidableEq m] in
/-- A map into the weights (of a network of any model dimension `d'`) is differentiable if its
four components are. -/
private theorem differentiableAt_params_lnr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d' : Type*} [Fintype d'] {B : Arch T d' L} {f : E → Params B dIn dOut} {x : E}
    (hE : DifferentiableAt ℝ (fun y => (f y).E) x)
    (hr : ∀ ℓ, DifferentiableAt ℝ (fun y => (f y).read ℓ) x)
    (hw : ∀ ℓ, DifferentiableAt ℝ (fun y => (f y).write ℓ) x)
    (hD : DifferentiableAt ℝ (fun y => (f y).D) x) : DifferentiableAt ℝ f x := by
  let e := (Params.linearEquivProd (A := B) (dIn := dIn) (dOut := dOut)).toContinuousLinearEquiv
  have hp : DifferentiableAt ℝ (fun y => ((f y).E, (f y).read, (f y).write, (f y).D)) x :=
    hE.prodMk ((differentiableAt_pi.2 hr).prodMk ((differentiableAt_pi.2 hw).prodMk hD))
  have hc := e.symm.differentiableAt.comp x hp
  exact hc

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype m] [DecidableEq m] [Fintype dIn] in
/-- A map into the biases (of a network of any model dimension `d'`) is differentiable if its
four components are. -/
private theorem differentiableAt_biases_lnr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d' : Type*} [Fintype d'] {B : Arch T d' L} {f : E → Biases B dOut} {x : E}
    (hE : DifferentiableAt ℝ (fun y => (f y).E) x)
    (hr : ∀ ℓ, DifferentiableAt ℝ (fun y => (f y).read ℓ) x)
    (hw : ∀ ℓ, DifferentiableAt ℝ (fun y => (f y).write ℓ) x)
    (hD : DifferentiableAt ℝ (fun y => (f y).D) x) : DifferentiableAt ℝ f x := by
  let e := (Biases.linearEquivProd (A := B) (dOut := dOut)).toContinuousLinearEquiv
  have hp : DifferentiableAt ℝ (fun y => ((f y).E, (f y).read, (f y).write, (f y).D)) x :=
    hE.prodMk ((differentiableAt_pi.2 hr).prodMk ((differentiableAt_pi.2 hw).prodMk hD))
  have hc := e.symm.differentiableAt.comp x hp
  exact hc

/-- A linear map on a finite-dimensional space is differentiable. -/
private theorem differentiable_linear_lnr {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F] (l : P →ₗ[ℝ] F) :
    Differentiable ℝ l := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).differentiable

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype m] [DecidableEq m] in
/-- The four components of the weights are differentiable (linear) functions of them. -/
private theorem differentiable_comps_lnr {d' : Type*} [Fintype d'] {B : Arch T d' L} :
    Differentiable ℝ (fun θ : Params B dIn dOut => θ.E) ∧
      (∀ ℓ, Differentiable ℝ (fun θ : Params B dIn dOut => θ.read ℓ)) ∧
      (∀ ℓ, Differentiable ℝ (fun θ : Params B dIn dOut => θ.write ℓ)) ∧
      Differentiable ℝ (fun θ : Params B dIn dOut => θ.D) :=
  ⟨differentiable_linear_lnr
      { toFun := fun θ : Params B dIn dOut => θ.E,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    fun ℓ => differentiable_linear_lnr
      { toFun := fun θ : Params B dIn dOut => θ.read ℓ,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    fun ℓ => differentiable_linear_lnr
      { toFun := fun θ : Params B dIn dOut => θ.write ℓ,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    differentiable_linear_lnr
      { toFun := fun θ : Params B dIn dOut => θ.D,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }⟩

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype m] [DecidableEq m] [Fintype dIn] in
/-- The four components of the biases are differentiable (linear) functions of them. -/
private theorem differentiable_compsB_lnr {d' : Type*} [Fintype d'] {B : Arch T d' L} :
    Differentiable ℝ (fun c : Biases B dOut => c.E) ∧
      (∀ ℓ, Differentiable ℝ (fun c : Biases B dOut => c.read ℓ)) ∧
      (∀ ℓ, Differentiable ℝ (fun c : Biases B dOut => c.write ℓ)) ∧
      Differentiable ℝ (fun c : Biases B dOut => c.D) :=
  ⟨differentiable_linear_lnr
      { toFun := fun c : Biases B dOut => c.E,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    fun ℓ => differentiable_linear_lnr
      { toFun := fun c : Biases B dOut => c.read ℓ,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    fun ℓ => differentiable_linear_lnr
      { toFun := fun c : Biases B dOut => c.write ℓ,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    differentiable_linear_lnr
      { toFun := fun c : Biases B dOut => c.D,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }⟩

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype m] [DecidableEq m] [Fintype dIn]
  [Fintype dOut] in
/-- The product of two differentiable matrix-valued maps is differentiable. -/
private theorem differentiableAt_matMul_lnr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n₁ n₂ n₃ : Type*} [Fintype n₁] [Fintype n₂] [Fintype n₃]
    {f : E → Matrix n₁ n₂ ℝ} {g : E → Matrix n₂ n₃ ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y => f y * g y) x := by
  -- matrix multiplication as a bilinear map
  let B : Matrix n₁ n₂ ℝ →ₗ[ℝ] Matrix n₂ n₃ ℝ →ₗ[ℝ] Matrix n₁ n₃ ℝ :=
    LinearMap.mk₂ ℝ (fun a b => a * b) Matrix.add_mul (fun c a b => Matrix.smul_mul c a b)
      Matrix.mul_add (fun c a b => Matrix.mul_smul a c b)
  -- the same map with continuous linear maps (all spaces are finite-dimensional)
  let B' : Matrix n₁ n₂ ℝ →L[ℝ] Matrix n₂ n₃ ℝ →L[ℝ] Matrix n₁ n₃ ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (Matrix n₂ n₃ ℝ →ₗ[ℝ] Matrix n₁ n₃ ℝ) ≃ₗ[ℝ]
        (Matrix n₂ n₃ ℝ →L[ℝ] Matrix n₁ n₃ ℝ)).toLinearMap ∘ₗ B)
  have hB : (fun y => f y * g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.differentiableAt.comp x hf).clm_apply hg

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype m] [DecidableEq m] [Fintype dIn]
  [Fintype dOut] in
/-- A row times a matrix, both differentiable, is differentiable. -/
private theorem differentiableAt_vecMul_lnr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n₁ n₂ : Type*} [Fintype n₁] [Fintype n₂] {f : E → n₁ → ℝ} {g : E → Matrix n₁ n₂ ℝ}
    {x : E} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y => f y ᵥ* g y) x := by
  -- `(v, M) ↦ v M` as a bilinear map
  let B : (n₁ → ℝ) →ₗ[ℝ] Matrix n₁ n₂ ℝ →ₗ[ℝ] (n₂ → ℝ) :=
    LinearMap.mk₂ ℝ (fun v M => v ᵥ* M) (fun v w M => Matrix.add_vecMul M v w)
      (fun c v M => Matrix.smul_vecMul c v M) (fun v M N => Matrix.vecMul_add M N v)
      (fun c v M => Matrix.vecMul_smul v c M)
  let B' : (n₁ → ℝ) →L[ℝ] Matrix n₁ n₂ ℝ →L[ℝ] (n₂ → ℝ) :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix n₁ n₂ ℝ →ₗ[ℝ] (n₂ → ℝ)) ≃ₗ[ℝ] (Matrix n₁ n₂ ℝ →L[ℝ] (n₂ → ℝ))).toLinearMap ∘ₗ B)
  have hB : (fun y => f y ᵥ* g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.differentiableAt.comp x hf).clm_apply hg

omit [Fintype T] [Fintype m] [DecidableEq m] [Fintype dIn] [Fintype dOut] in
/-- `v ↦ diag(v)` is differentiable (linear). -/
private theorem differentiable_diagonal_lnr :
    Differentiable ℝ (fun v : d → ℝ => Matrix.diagonal v) := by
  have h := differentiable_linear_lnr (Matrix.diagonalLinearMap d ℝ ℝ)
  exact h

omit [Fintype T] [DecidableEq m] in
/-- `reduceLNParams` is differentiable (its components are polynomials). -/
private theorem differentiable_reduceLNParams_lnr (ε : ℝ) (U : Matrix d m ℝ) :
    Differentiable ℝ (reduceLNParams (A := A) (dIn := dIn) (dOut := dOut) (T := T) ε U) := by
  obtain ⟨pE, pr, pw, pD⟩ := differentiable_comps_lnr (B := A) (dIn := dIn) (dOut := dOut)
  obtain ⟨bE, br, bw, bD⟩ := differentiable_compsB_lnr (B := A) (dOut := dOut)
  intro q
  -- the components of `q = ((θ, b), (γ, β))`
  have hθ : DifferentiableAt ℝ (fun q : ParamsLN A dIn dOut => q.1.1) q :=
    differentiableAt_fst.fst
  have hb : DifferentiableAt ℝ (fun q : ParamsLN A dIn dOut => q.1.2) q :=
    differentiableAt_fst.snd
  have hγ : ∀ k, DifferentiableAt ℝ
      (fun q : ParamsLN A dIn dOut => Matrix.diagonal (q.2.1 k)) q := by
    intro k
    have h1 : DifferentiableAt ℝ (fun q : ParamsLN A dIn dOut => q.2.1 k) q :=
      differentiableAt_pi.1 differentiableAt_snd.fst k
    have h2 := (differentiable_diagonal_lnr (d := d) _).comp q h1
    exact h2
  have hβ : ∀ k, DifferentiableAt ℝ (fun q : ParamsLN A dIn dOut => q.2.2 k) q :=
    fun k => differentiableAt_pi.1 differentiableAt_snd.snd k
  have tE : DifferentiableAt ℝ (fun q : ParamsLN A dIn dOut => q.1.1.E) q := (pE _).comp q hθ
  have tr : ∀ ℓ, DifferentiableAt ℝ (fun q : ParamsLN A dIn dOut => q.1.1.read ℓ) q :=
    fun ℓ => (pr ℓ _).comp q hθ
  have tw : ∀ ℓ, DifferentiableAt ℝ (fun q : ParamsLN A dIn dOut => q.1.1.write ℓ) q :=
    fun ℓ => (pw ℓ _).comp q hθ
  have tD : DifferentiableAt ℝ (fun q : ParamsLN A dIn dOut => q.1.1.D) q := (pD _).comp q hθ
  have uE : DifferentiableAt ℝ (fun q : ParamsLN A dIn dOut => q.1.2.E) q := (bE _).comp q hb
  have ur : ∀ ℓ, DifferentiableAt ℝ (fun q : ParamsLN A dIn dOut => q.1.2.read ℓ) q :=
    fun ℓ => (br ℓ _).comp q hb
  have uw : ∀ ℓ, DifferentiableAt ℝ (fun q : ParamsLN A dIn dOut => q.1.2.write ℓ) q :=
    fun ℓ => (bw ℓ _).comp q hb
  have uD : DifferentiableAt ℝ (fun q : ParamsLN A dIn dOut => q.1.2.D) q := (bD _).comp q hb
  refine (differentiableAt_params_lnr ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_).prodMk
    (differentiableAt_biases_lnr ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
  · -- `E U`
    exact differentiableAt_matMul_lnr tE (differentiableAt_const U)
  · -- `c U^⊤ diag(γ) W_read`
    exact (differentiableAt_matMul_lnr (differentiableAt_matMul_lnr (differentiableAt_const Uᵀ)
      (hγ _)) (tr ℓ)).fun_const_smul (Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ)))
  · -- `W_write U`
    exact differentiableAt_matMul_lnr (tw ℓ) (differentiableAt_const U)
  · -- `c U^⊤ diag(γ_L) D`
    exact (differentiableAt_matMul_lnr (differentiableAt_matMul_lnr (differentiableAt_const Uᵀ)
      (hγ _)) tD).fun_const_smul (Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ)))
  · -- `b_E U`
    exact differentiableAt_vecMul_lnr uE (differentiableAt_const U)
  · -- `b_read + β W_read`
    exact (ur ℓ).add (differentiableAt_vecMul_lnr (hβ _) (tr ℓ))
  · -- `b_write U`
    exact differentiableAt_vecMul_lnr (uw ℓ) (differentiableAt_const U)
  · -- `b_D + β_L D`
    exact uD.add (differentiableAt_vecMul_lnr (hβ _) tD)

omit [Fintype T] [DecidableEq m] in
/-- The preimage map `y ↦ R y` is differentiable (linear). -/
private theorem differentiable_inv_lnr (U : Matrix d m ℝ) (γ β : Fin (L + 1) → d → ℝ) {ε : ℝ} :
    Differentiable ℝ (fun y : ParamsB (redArch_lnr A ε m) dIn dOut =>
      ((invW_lnr U γ y.1, invB_lnr U γ β y) : ParamsB A dIn dOut)) := by
  obtain ⟨pE, pr, pw, pD⟩ :=
    differentiable_comps_lnr (B := redArch_lnr A ε m) (dIn := dIn) (dOut := dOut)
  obtain ⟨bE, br, bw, bD⟩ := differentiable_compsB_lnr (B := redArch_lnr A ε m) (dOut := dOut)
  intro y
  -- the components of `y = (θ', b')`
  have tE : DifferentiableAt ℝ (fun y : ParamsB (redArch_lnr A ε m) dIn dOut => y.1.E) y :=
    (pE _).comp y differentiableAt_fst
  have tr : ∀ ℓ, DifferentiableAt ℝ
      (fun y : ParamsB (redArch_lnr A ε m) dIn dOut => y.1.read ℓ) y :=
    fun ℓ => (pr ℓ _).comp y differentiableAt_fst
  have tw : ∀ ℓ, DifferentiableAt ℝ
      (fun y : ParamsB (redArch_lnr A ε m) dIn dOut => y.1.write ℓ) y :=
    fun ℓ => (pw ℓ _).comp y differentiableAt_fst
  have tD : DifferentiableAt ℝ (fun y : ParamsB (redArch_lnr A ε m) dIn dOut => y.1.D) y :=
    (pD _).comp y differentiableAt_fst
  have uE : DifferentiableAt ℝ (fun y : ParamsB (redArch_lnr A ε m) dIn dOut => y.2.E) y :=
    (bE _).comp y differentiableAt_snd
  have ur : ∀ ℓ, DifferentiableAt ℝ
      (fun y : ParamsB (redArch_lnr A ε m) dIn dOut => y.2.read ℓ) y :=
    fun ℓ => (br ℓ _).comp y differentiableAt_snd
  have uw : ∀ ℓ, DifferentiableAt ℝ
      (fun y : ParamsB (redArch_lnr A ε m) dIn dOut => y.2.write ℓ) y :=
    fun ℓ => (bw ℓ _).comp y differentiableAt_snd
  have uD : DifferentiableAt ℝ (fun y : ParamsB (redArch_lnr A ε m) dIn dOut => y.2.D) y :=
    (bD _).comp y differentiableAt_snd
  -- the reads and the readout of the preimage, `c⁻¹ diag(γ)⁻¹ U R`
  have hr : ∀ ℓ, DifferentiableAt ℝ
      (fun y : ParamsB (redArch_lnr A ε m) dIn dOut => (invW_lnr U γ y.1).read ℓ) y :=
    fun ℓ => (differentiableAt_matMul_lnr (differentiableAt_const _) (tr ℓ)).fun_const_smul
      (Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ)))⁻¹
  have hD : DifferentiableAt ℝ
      (fun y : ParamsB (redArch_lnr A ε m) dIn dOut => (invW_lnr U γ y.1).D) y :=
    (differentiableAt_matMul_lnr (differentiableAt_const _) tD).fun_const_smul
      (Real.sqrt ((Fintype.card d : ℝ) / (Fintype.card m : ℝ)))⁻¹
  refine (differentiableAt_params_lnr ?_ hr (fun ℓ => ?_) hD).prodMk
    (differentiableAt_biases_lnr ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_)
  · exact differentiableAt_matMul_lnr tE (differentiableAt_const _)
  · exact differentiableAt_matMul_lnr (tw ℓ) (differentiableAt_const _)
  · exact differentiableAt_vecMul_lnr uE (differentiableAt_const _)
  · exact (ur ℓ).sub (differentiableAt_vecMul_lnr (differentiableAt_const _) (hr ℓ))
  · exact differentiableAt_vecMul_lnr (uw ℓ) (differentiableAt_const _)
  · exact uD.sub (differentiableAt_vecMul_lnr (differentiableAt_const _) hD)

omit [Fintype T] in
/-- **A differentiable right inverse of `reduceLNParams` through `q`:**
`s y = (q.1 + R (y − Φ q), q.2)`, with the gains and the LayerNorm biases of `q`. -/
private theorem exists_section_lnr (ε : ℝ) (U : Matrix d m ℝ) (hU : Uᵀ * U = 1)
    (q : ParamsLN A dIn dOut) (hγ : ∀ ℓ i, q.2.1 ℓ i ≠ 0) :
    ∃ s : ParamsB (redArch_lnr A ε m) dIn dOut → ParamsLN A dIn dOut, Differentiable ℝ s ∧
      s (reduceLNParams ε U q) = q ∧ ∀ y, reduceLNParams ε U (s y) = y := by
  refine ⟨fun y => (q.1 + ((invW_lnr U q.2.1 (y - reduceLNParams ε U q).1,
      invB_lnr U q.2.1 q.2.2 (y - reduceLNParams ε U q)) : ParamsB A dIn dOut), q.2),
    ?_, ?_, ?_⟩
  · -- an affine map
    intro y
    have h1 : DifferentiableAt ℝ
        (fun y : ParamsB (redArch_lnr A ε m) dIn dOut => y - reduceLNParams ε U q) y :=
      differentiableAt_id.sub (differentiableAt_const _)
    have h2 := (differentiable_inv_lnr (A := A) (dIn := dIn) (dOut := dOut) U q.2.1 q.2.2
      _).comp y h1
    exact ((differentiableAt_const q.1).add h2).prodMk (differentiableAt_const _)
  · -- `s(Φ q) = (q.1 + R 0, q.2) = q`
    dsimp only
    rw [sub_self, inv_zero_lnr, add_zero]
  · -- `Φ(s y) = Φ q + Φ(R (y − Φ q), q.2) = Φ q + (y − Φ q) = y`
    intro y
    dsimp only
    rw [reduceLNParams_add_lnr, reduceLNParams_inv_lnr ε U hU _ _ hγ]
    exact add_sub_cancel _ _

/-- A map with a differentiable right inverse through `p` has a derivative at `p` that is onto
(the chain rule for `Φ ∘ s = id` at `Φ p`). -/
private theorem exists_surjective_of_section_lnr {P₁ P₂ : Type*} [NormedAddCommGroup P₁]
    [NormedSpace ℝ P₁] [NormedAddCommGroup P₂] [NormedSpace ℝ P₂] {Φ : P₁ → P₂} {s : P₂ → P₁}
    {p : P₁} (hΦ : DifferentiableAt ℝ Φ p) (hs : DifferentiableAt ℝ s (Φ p))
    (hsp : s (Φ p) = p) (hΦs : ∀ y, Φ (s y) = y) :
    ∃ Φ' : P₁ →L[ℝ] P₂, HasFDerivAt Φ Φ' p ∧ Function.Surjective Φ' := by
  refine ⟨fderiv ℝ Φ p, hΦ.hasFDerivAt, fun η => ⟨fderiv ℝ s (Φ p) η, ?_⟩⟩
  have hΦ' : HasFDerivAt Φ (fderiv ℝ Φ p) (s (Φ p)) := by
    rw [hsp]
    exact hΦ.hasFDerivAt
  have h1 := hΦ'.comp (Φ p) hs.hasFDerivAt
  have hid : Φ ∘ s = id := funext hΦs
  rw [hid] at h1
  have h2 := h1.unique (hasFDerivAt_id (Φ p))
  exact DFunLike.congr_fun h2 η

omit [Fintype T] in
/-- **Proof of Proposition A.15 (iii), "the derivative of the map from the parameters of the
LayerNorm network to those of the reduced network is onto"**, at gains with nonzero entries, for
`U` with orthonormal columns. -/
theorem exists_hasFDerivAt_reduceLNParams_surjective (ε : ℝ) (U : Matrix d m ℝ)
    (hU : Uᵀ * U = 1) (q : ParamsLN A dIn dOut) (hγ : ∀ ℓ i, q.2.1 ℓ i ≠ 0) :
    ∃ Φ' : ParamsLN A dIn dOut →L[ℝ] ParamsB (A.withNorm (rmsNorm (T := T) (d := m)
        (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ)))) dIn dOut,
      HasFDerivAt (reduceLNParams (A := A) (dIn := dIn) (dOut := dOut) (T := T) ε U) Φ' q
        ∧ Function.Surjective Φ' := by
  -- the chain rule for `Φ ∘ s = id` with the right inverse `s` through `q`
  obtain ⟨s, hs, hsp, hΦs⟩ := exists_section_lnr ε U hU q hγ
  exact exists_surjective_of_section_lnr (differentiable_reduceLNParams_lnr ε U q) (hs _) hsp hΦs

/-- **Proof of Proposition A.15 (iii), "at corresponding parameters both have the same
functional dimension":** let the columns of `U` be an orthonormal basis of `V`, with at least one
column, and let the stream matrices commute with `Z`. At gains with nonzero entries, the
functional dimension of the pre-LayerNorm network, in all its parameters, is that of the reduced
pre-RMSNorm network of dimension `m` with biases at the reduced parameters. -/
theorem funDimOf_evalLNParams_eq_funDimB_reduceLN (ε : ℝ) (U : Matrix d m ℝ)
    (hU : Uᵀ * U = 1) (hUZ : U * Uᵀ = centering d) (hm : 0 < Fintype.card m)
    (S : Fin L → Matrix d d ℝ) (hS : ∀ ℓ, centering d * S ℓ = S ℓ * centering d)
    (q : ParamsLN A dIn dOut) (hγ : ∀ ℓ i, q.2.1 ℓ i ≠ 0) :
    funDimOf (evalLNParams A ε S) q
      = funDimB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
          (fun ℓ => Uᵀ * S ℓ * U) (reduceLNParams ε U q) := by
  rw [funDimB_eq_funDimOf]
  obtain ⟨Φ', hΦ', -⟩ := exists_hasFDerivAt_reduceLNParams_surjective ε U hU q hγ
  obtain ⟨s, hs, hsp, hΦs⟩ := exists_section_lnr ε U hU q hγ
  refine funDimOf_eq_of_comp_of_section hΦ'.differentiableAt (hs _) hsp ?_ ?_
  · -- everywhere the LayerNorm network computes the reduced network at `Φ`
    refine Filter.Eventually.of_forall fun q' => funext fun x => ?_
    exact evalLN_eq_evalB_reduceLN ε U hU hUZ hm S hS q'.1.1 q'.1.2 q'.2.1 q'.2.2 x
  · -- everywhere the reduced network at `y` is the LayerNorm network at `s y`
    refine Filter.Eventually.of_forall fun y => funext fun x => ?_
    have h := evalLN_eq_evalB_reduceLN ε U hU hUZ hm S hS (s y).1.1 (s y).1.2 (s y).2.1
      (s y).2.2 x
    calc _ = evalB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
          (fun ℓ => Uᵀ * S ℓ * U) (reduceLNParams ε U (s y)).1 (reduceLNParams ε U (s y)).2 x :=
          by rw [hΦs y]
      _ = _ := h.symm

/-- The same for a skipless pre-LayerNorm network and the skipless reduced network. -/
theorem funDimOf_evalLNParams_skipless (ε : ℝ) (U : Matrix d m ℝ)
    (hU : Uᵀ * U = 1) (hUZ : U * Uᵀ = centering d) (hm : 0 < Fintype.card m)
    (q : ParamsLN A dIn dOut) (hγ : ∀ ℓ i, q.2.1 ℓ i ≠ 0) :
    funDimOf (evalLNParams A ε 0) q
      = funDimB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
          0 (reduceLNParams ε U q) := by
  have h := funDimOf_evalLNParams_eq_funDimB_reduceLN ε U hU hUZ hm (0 : Fin L → Matrix d d ℝ)
    (fun ℓ => by simp) q hγ
  have h0 : (fun ℓ => Uᵀ * (0 : Fin L → Matrix d d ℝ) ℓ * U) = (0 : Fin L → Matrix m m ℝ) := by
    funext ℓ
    simp
  rwa [h0] at h

/-- The same for a residual pre-LayerNorm network and the residual reduced network. -/
theorem funDimOf_evalLNParams_residual (ε : ℝ) (U : Matrix d m ℝ)
    (hU : Uᵀ * U = 1) (hUZ : U * Uᵀ = centering d) (hm : 0 < Fintype.card m)
    (q : ParamsLN A dIn dOut) (hγ : ∀ ℓ i, q.2.1 ℓ i ≠ 0) :
    funDimOf (evalLNParams A ε 1) q
      = funDimB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
          1 (reduceLNParams ε U q) := by
  have h := funDimOf_evalLNParams_eq_funDimB_reduceLN ε U hU hUZ hm (1 : Fin L → Matrix d d ℝ)
    (fun ℓ => by simp) q hγ
  have h1 : (fun ℓ => Uᵀ * (1 : Fin L → Matrix d d ℝ) ℓ * U) = (1 : Fin L → Matrix m m ℝ) := by
    funext ℓ
    simp [hU]
  rwa [h1] at h

/-- **Proposition A.15 (iii):** if the gains have nonzero entries, the functional dimension
rises by the same amount from the skipless to the residual version in the pre-LayerNorm network
and in the reduced networks of (ii); as both versions have the same parameters, this is "the
difference in redundancy between the skipless and the residual version of the LayerNorm network
equals the difference for the reduced networks". -/
theorem funDimOf_evalLNParams_residual_add_skipless (ε : ℝ) (U : Matrix d m ℝ)
    (hU : Uᵀ * U = 1) (hUZ : U * Uᵀ = centering d) (hm : 0 < Fintype.card m)
    (q : ParamsLN A dIn dOut) (hγ : ∀ ℓ i, q.2.1 ℓ i ≠ 0) :
    funDimOf (evalLNParams A ε 1) q
        + funDimB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
          0 (reduceLNParams ε U q)
      = funDimOf (evalLNParams A ε 0) q
        + funDimB (A.withNorm (rmsNorm (ε * (Fintype.card d : ℝ) / (Fintype.card m : ℝ))))
          1 (reduceLNParams ε U q) := by
  rw [funDimOf_evalLNParams_skipless ε U hU hUZ hm q hγ,
    funDimOf_evalLNParams_residual ε U hU hUZ hm q hγ, add_comm]

end Skips
