import SkipsLean.Residual.GaugeFixMixed
import SkipsLean.OneBlock.LearnedSkip
import SkipsLean.Dimension.FunDimFamily
import SkipsLean.Symmetry.FiniteSymmetriesCompose

/-!
# The gauge fix for networks with learned skips: what it identifies

Paper (skips paper), Appendix A.2: "On a network with learned skips, `T_G` acts by
`A_ℓ ↦ G_{ℓ−1}^{-1} A_ℓ G_ℓ` in place of the second line. When every skip `A_ℓ = U_ℓ V_ℓ` is
invertible, let `Λ_ℓ = A_{ℓ+1} ⋯ A_L`, with `Λ_L = I`, and let
`Φ(θ) = (E Λ_0, (Λ_{ℓ−1}^{-1} W_read^ℓ, W_write^ℓ Λ_ℓ)_{ℓ=1}^L, D)`, a parameter of the residual
network, with the same formula for learned skips." Theorem A.5 (ii): "Every parameter of the
residual network is `Φ(θ)` for some `θ`, and `Φ(θ̃) = Φ(θ)` exactly when `θ̃ = T_{G,K}(θ)` for some
`G` and `K` with `G_L = I`. The derivative of `Φ` is onto at every `θ`. So the networks of mixed
blocks with invertible skips and the residual networks compute the same set of functions, with
the same functional dimension at `θ` and at `Φ(θ)`. The same holds for learned skips, without the
`K_ℓ`, and for networks with biases."

Here "the same holds for learned skips, without the `K_ℓ`", as the twin of
`Residual/GaugeFixMixed.lean`. The parameters of a network with learned skips are the pairs
`p = (θ, (A_ℓ))` of `OneBlock/LearnedSkip.lean` (`funDimLearned`), its function is
`eval A p.2 p.1`, and `T_G` is `(θ, A) ↦ (θ.cob G G, cobSkip A G)`
(`Symmetry/ChangeOfBasis.lean`):

* `learnedToResidual p`: the map `Φ` for learned skips, with the matrix inverse of `Λ_{ℓ−1}`;
  for invertible skips it is `θ.cob Λ Λ` (`learnedToResidual_coe`), the parameter of
  S Theorem 3.2 (i) (`eval_learned_eq_residual`, `Residual/LearnedSkips.lean`).
* `learnedToResidual_one`: every residual parameter is `Φ(θ, I)`.
* `learnedToResidual_eq_iff`: `Φ(θ̃, Ã) = Φ(θ, A)` exactly when `(θ̃, Ã) = T_G(θ, A)` with
  `G_L = I`, for invertible skips.
* `exists_hasFDerivAt_learnedToResidual_surjective`: the derivative of `Φ` is onto.
* `eval_eq_eval_learnedToResidual`, `image_eval_learned_eq_range_residual`: without
  normalization, the same function and the same set of functions.
* `funDimLearned_eq_funDim_residual`: without normalization, for any blocks, the functional
  dimension of the network with full learned skips at `(θ, A)`, `A_ℓ` invertible, is that of the
  residual network at `Φ(θ, A)`.

The model dimension is `d : Type` here, as in `Residual/GaugeFixMixed.lean`, whose `skipProdMat`
this file uses. Not stated: the same for networks with biases.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T : Type*} {d : Type} {dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d]
  [DecidableEq d] [Fintype dIn] [Fintype dOut]
variable {A : Arch T d L}

/-- **The map `Φ` of equation (12) for learned skips:** from the weights `θ` and the skips
`A_1, …, A_L` to the parameter `E Λ_0`, `Λ_{ℓ−1}^{-1} W_read^ℓ`, `W_write^ℓ Λ_ℓ`, `D` of the
residual network, for `Λ_ℓ = A_{ℓ+1} ⋯ A_L`. -/
noncomputable def learnedToResidual (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) :
    Params A dIn dOut where
  E := p.1.E * skipProdMat p.2 0
  read ℓ := (skipProdMat p.2 ℓ.castSucc)⁻¹ * p.1.read ℓ
  write ℓ := p.1.write ℓ * skipProdMat p.2 ℓ.succ
  D := p.1.D

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- `Λ_L = I`. -/
private theorem skipProdMat_last_gfl (S : Fin L → Matrix d d ℝ) :
    skipProdMat S (Fin.last L) = 1 := by
  simp [skipProdMat]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- `Λ_{ℓ-1} = S_ℓ Λ_ℓ`. -/
private theorem skipProdMat_castSucc_gfl (S : Fin L → Matrix d d ℝ) (ℓ : Fin L) :
    skipProdMat S ℓ.castSucc = S ℓ * skipProdMat S ℓ.succ := by
  simp [skipProdMat]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Equation (12) for invertible learned skips:** `Φ(θ, A) = θ.cob Λ Λ`. -/
theorem learnedToResidual_coe (θ : Params A dIn dOut) (S : Fin L → GL d ℝ) :
    learnedToResidual (θ, fun ℓ => (S ℓ : Matrix d d ℝ)) = θ.cob (skipProd S) (skipProd S) := by
  -- the products of invertible skips are those of `skipProd`, and `Λ_L = I`
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · simp only [learnedToResidual, Params.cob, skipProdMat_coe]
  · simp only [learnedToResidual, Params.cob, skipProdMat_coe, Matrix.coe_units_inv]
  · simp only [learnedToResidual, Params.cob, skipProdMat_coe]
  · simp only [learnedToResidual, Params.cob, skipProd_last, inv_one, Units.val_one,
      Matrix.one_mul]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Theorem A.5 (ii) for learned skips, "Every parameter of the residual network is `Φ(θ)` for
some `θ`":** the same weights with the skips `A_ℓ = I`. -/
theorem learnedToResidual_one (θ : Params A dIn dOut) :
    learnedToResidual (θ, (1 : Fin L → Matrix d d ℝ)) = θ := by
  -- every `Λ_ℓ` is `I`
  have hΛ : ∀ ℓ, skipProdMat (1 : Fin L → Matrix d d ℝ) ℓ = 1 := by
    intro ℓ
    induction ℓ using Fin.reverseInduction with
    | last => rw [skipProdMat_last_gfl]
    | cast i ih => rw [skipProdMat_castSucc_gfl, ih, Pi.one_apply, Matrix.mul_one]
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · simp only [learnedToResidual, hΛ, Matrix.mul_one]
  · simp only [learnedToResidual, hΛ, inv_one, Matrix.one_mul]
  · simp only [learnedToResidual, hΛ, Matrix.mul_one]
  · rfl

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Invertible skips are the matrices of elements of `GL d ℝ`. -/
private theorem exists_coe_gfl {M : Fin L → Matrix d d ℝ} (h : ∀ ℓ, IsUnit (M ℓ)) :
    ∃ S : Fin L → GL d ℝ, M = fun ℓ => (S ℓ : Matrix d d ℝ) :=
  ⟨fun ℓ => (h ℓ).unit, funext fun ℓ => ((h ℓ).unit_spec).symm⟩

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The change of basis by `G = K = 1` is the identity. -/
private theorem cob_one_gfl (φ : Params A dIn dOut) : φ.cob (fun _ => 1) (fun _ => 1) = φ := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp [Params.cob]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- After `T_G` with `G_L = I`, the products of the skips are `G_ℓ⁻¹ Λ_ℓ` (any skips). -/
private theorem skipProdMat_cobSkip_gfl (S : Fin L → Matrix d d ℝ) (G : Fin (L + 1) → GL d ℝ)
    (hG : G (Fin.last L) = 1) (ℓ : Fin (L + 1)) :
    skipProdMat (cobSkip S G) ℓ = (↑(G ℓ)⁻¹ : Matrix d d ℝ) * skipProdMat S ℓ := by
  induction ℓ using Fin.reverseInduction with
  | last =>
    rw [skipProdMat_last_gfl, skipProdMat_last_gfl, hG, inv_one, Units.val_one, Matrix.one_mul]
  | cast i ih =>
    -- `(G_{i-1}⁻¹ S_i G_i)(G_i⁻¹ Λ_i) = G_{i-1}⁻¹ S_i Λ_i`
    rw [skipProdMat_castSucc_gfl, skipProdMat_castSucc_gfl, ih]
    simp only [cobSkip, Matrix.mul_assoc, Units.mul_inv_cancel_left]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- `a (a⁻¹ B) = B` also for a rectangular `B`. -/
private theorem gl_mul_inv_mul_gfl {n : Type*} (a : GL d ℝ) (B : Matrix d n ℝ) :
    (a : Matrix d d ℝ) * ((↑a⁻¹ : Matrix d d ℝ) * B) = B := by
  rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **The "if" direction of Theorem A.5 (ii) for learned skips:** `Φ(T_G(θ, A)) = Φ(θ, A)` when
`G_L = I`, for any skips. -/
private theorem learnedToResidual_cobSkip_gfl (θ : Params A dIn dOut) (S : Fin L → Matrix d d ℝ)
    (G : Fin (L + 1) → GL d ℝ) (hG : G (Fin.last L) = 1) :
    learnedToResidual (θ.cob G G, cobSkip S G) = learnedToResidual (θ, S) := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · -- `E G_0 G_0⁻¹ Λ_0 = E Λ_0`
    simp only [learnedToResidual, Params.cob, skipProdMat_cobSkip_gfl S G hG, Matrix.mul_assoc,
      Units.mul_inv_cancel_left]
  · -- `(G_{ℓ-1}⁻¹ Λ_{ℓ-1})⁻¹ G_{ℓ-1}⁻¹ W_read = Λ_{ℓ-1}⁻¹ W_read`
    simp only [learnedToResidual, Params.cob, skipProdMat_cobSkip_gfl S G hG, Matrix.mul_inv_rev,
      ← Matrix.coe_units_inv, inv_inv, Matrix.mul_assoc, gl_mul_inv_mul_gfl]
  · simp only [learnedToResidual, Params.cob, skipProdMat_cobSkip_gfl S G hG, Matrix.mul_assoc,
      Units.mul_inv_cancel_left]
  · simp only [learnedToResidual, Params.cob, hG, inv_one, Units.val_one, Matrix.one_mul]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Theorem A.5 (ii) for learned skips, "`Φ(θ̃) = Φ(θ)` exactly when `θ̃ = T_G(θ)` for some `G`
with `G_L = I`"** ("without the `K_ℓ`"), for invertible skips: `T_G` multiplies the weights as
the changes of basis `G_ℓ` do and sends `A_ℓ` to `G_{ℓ−1}^{-1} A_ℓ G_ℓ`. -/
theorem learnedToResidual_eq_iff (p p' : Params A dIn dOut × (Fin L → Matrix d d ℝ))
    (hp : ∀ ℓ, IsUnit (p.2 ℓ)) (hp' : ∀ ℓ, IsUnit (p'.2 ℓ)) :
    learnedToResidual p' = learnedToResidual p
      ↔ ∃ G : Fin (L + 1) → GL d ℝ,
          G (Fin.last L) = 1 ∧ p' = (p.1.cob G G, cobSkip p.2 G) := by
  -- write the skips as elements of `GL d ℝ`
  obtain ⟨θ, M⟩ := p
  obtain ⟨θ', M'⟩ := p'
  obtain ⟨S, rfl⟩ := exists_coe_gfl hp
  obtain ⟨S', rfl⟩ := exists_coe_gfl hp'
  constructor
  · intro h
    rw [learnedToResidual_coe, learnedToResidual_coe] at h
    -- the products `Λ_ℓ` and `Λ'_ℓ`, with `Λ_{ℓ-1} = S_ℓ Λ_ℓ` and `Λ_L = I`
    obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = skipProd S := ⟨_, rfl⟩
    obtain ⟨Λ', hΛ'⟩ : ∃ Λ', Λ' = skipProd S' := ⟨_, rfl⟩
    have hc : ∀ ℓ : Fin L, Λ ℓ.castSucc = S ℓ * Λ ℓ.succ := fun ℓ => by
      rw [hΛ, skipProd_castSucc]
    have hc' : ∀ ℓ : Fin L, Λ' ℓ.castSucc = S' ℓ * Λ' ℓ.succ := fun ℓ => by
      rw [hΛ', skipProd_castSucc]
    have hl : Λ (Fin.last L) = 1 := by rw [hΛ, skipProd_last]
    have hl' : Λ' (Fin.last L) = 1 := by rw [hΛ', skipProd_last]
    rw [← hΛ, ← hΛ'] at h
    -- `G_ℓ = Λ_ℓ Λ'_ℓ⁻¹`
    refine ⟨fun ℓ => Λ ℓ * (Λ' ℓ)⁻¹, by simp only [hl, hl', inv_one, mul_one], ?_⟩
    -- the weights: `θ' = (θ'.cob Λ' Λ').cob Λ'⁻¹ Λ'⁻¹ = (θ.cob Λ Λ).cob Λ'⁻¹ Λ'⁻¹`
    have hθ : θ' = θ.cob (fun ℓ => Λ ℓ * (Λ' ℓ)⁻¹) (fun ℓ => Λ ℓ * (Λ' ℓ)⁻¹) := by
      calc θ' = (θ'.cob Λ' Λ').cob (fun ℓ => (Λ' ℓ)⁻¹) (fun ℓ => (Λ' ℓ)⁻¹) := by
            rw [cob_cob]
            simp only [mul_inv_cancel]
            exact (cob_one_gfl θ').symm
        _ = _ := by rw [h, cob_cob]
    refine Prod.ext hθ ?_
    -- the skips: `G_{ℓ-1}⁻¹ S_ℓ G_ℓ = Λ'_{ℓ-1} Λ_{ℓ-1}⁻¹ S_ℓ Λ_ℓ Λ'_ℓ⁻¹ = S'_ℓ`
    funext ℓ
    simp only [cobSkip]
    rw [← Units.val_mul, ← Units.val_mul, hc ℓ, hc' ℓ]
    congr 1
    group
  · rintro ⟨G, hG, h⟩
    rw [h]
    exact learnedToResidual_cobSkip_gfl θ _ G hG

omit [Fintype T] [DecidableEq d] in
/-- A map into the weights is differentiable if its four components are. -/
private theorem differentiableAt_params_gfl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Params A dIn dOut} {x : E}
    (hE : DifferentiableAt ℝ (fun y => (f y).E) x)
    (hr : ∀ ℓ, DifferentiableAt ℝ (fun y => (f y).read ℓ) x)
    (hw : ∀ ℓ, DifferentiableAt ℝ (fun y => (f y).write ℓ) x)
    (hD : DifferentiableAt ℝ (fun y => (f y).D) x) : DifferentiableAt ℝ f x := by
  let e := (Params.linearEquivProd (A := A) (dIn := dIn) (dOut := dOut)).toContinuousLinearEquiv
  have hp : DifferentiableAt ℝ (fun y => ((f y).E, (f y).read, (f y).write, (f y).D)) x :=
    hE.prodMk ((differentiableAt_pi.2 hr).prodMk ((differentiableAt_pi.2 hw).prodMk hD))
  have hc := e.symm.differentiableAt.comp x hp
  exact hc

/-- A linear map on a finite-dimensional space is differentiable. -/
private theorem differentiable_linear_gfl {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F] (l : P →ₗ[ℝ] F) :
    Differentiable ℝ l := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).differentiable

omit [Fintype T] [DecidableEq d] in
private theorem differentiable_E_gfl :
    Differentiable ℝ (fun θ : Params A dIn dOut => θ.E) :=
  differentiable_linear_gfl
    { toFun := fun θ : Params A dIn dOut => θ.E,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] in
private theorem differentiable_read_gfl (ℓ : Fin L) :
    Differentiable ℝ (fun θ : Params A dIn dOut => θ.read ℓ) :=
  differentiable_linear_gfl
    { toFun := fun θ : Params A dIn dOut => θ.read ℓ,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] in
private theorem differentiable_write_gfl (ℓ : Fin L) :
    Differentiable ℝ (fun θ : Params A dIn dOut => θ.write ℓ) :=
  differentiable_linear_gfl
    { toFun := fun θ : Params A dIn dOut => θ.write ℓ,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] in
private theorem differentiable_D_gfl :
    Differentiable ℝ (fun θ : Params A dIn dOut => θ.D) :=
  differentiable_linear_gfl
    { toFun := fun θ : Params A dIn dOut => θ.D,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] in
/-- The weights of a pair `(θ, A)` are a differentiable (linear) function of it. -/
private theorem differentiable_fst_gfl :
    Differentiable ℝ (fun p : Params A dIn dOut × (Fin L → Matrix d d ℝ) => p.1) :=
  differentiable_fst

omit [Fintype T] [DecidableEq d] in
/-- The skip `A_ℓ` of a pair `(θ, A)` is a differentiable (linear) function of it. -/
private theorem differentiable_skip_gfl (ℓ : Fin L) :
    Differentiable ℝ (fun p : Params A dIn dOut × (Fin L → Matrix d d ℝ) => p.2 ℓ) :=
  differentiable_linear_gfl
    { toFun := fun p : Params A dIn dOut × (Fin L → Matrix d d ℝ) => p.2 ℓ,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The product of two differentiable matrix-valued maps is differentiable. -/
private theorem differentiableAt_matMul_gfl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {f : E → Matrix m n ℝ} {g : E → Matrix n p ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y => f y * g y) x := by
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
  exact (B'.differentiableAt.comp x hf).clm_apply hg

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The products `Λ_ℓ` of differentiable skips are differentiable. -/
private theorem differentiableAt_skipProdMat_gfl {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {S : E → Fin L → Matrix d d ℝ} {x : E}
    (hS : ∀ ℓ, DifferentiableAt ℝ (fun y => S y ℓ) x) (ℓ : Fin (L + 1)) :
    DifferentiableAt ℝ (fun y => skipProdMat (S y) ℓ) x := by
  induction ℓ using Fin.reverseInduction with
  | last =>
    simp only [skipProdMat_last_gfl]
    exact differentiableAt_const _
  | cast i ih =>
    -- `Λ_{i-1} = S_i Λ_i`
    simp only [skipProdMat_castSucc_gfl]
    exact differentiableAt_matMul_gfl (hS i) ih

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- A product of invertible matrices is invertible. -/
private theorem isUnit_skipProdMat_gfl {S : Fin L → Matrix d d ℝ} (hS : ∀ ℓ, IsUnit (S ℓ))
    (ℓ : Fin (L + 1)) : IsUnit (skipProdMat S ℓ) := by
  induction ℓ using Fin.reverseInduction with
  | last =>
    rw [skipProdMat_last_gfl]
    exact isUnit_one
  | cast i ih =>
    rw [skipProdMat_castSucc_gfl]
    exact (hS i).mul ih

/-- In a complete normed algebra, the inverse is differentiable at a unit. -/
private theorem differentiableAt_ringInverse_gfl {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [CompleteSpace R] {x : R} (hx : IsUnit x) :
    DifferentiableAt ℝ (fun y : R => Ring.inverse y) x :=
  differentiableAt_inverse hx

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The matrix inverse is differentiable at an invertible matrix (through the operator norm, for
which the matrices form a complete normed algebra with the same topology). -/
private theorem differentiableAt_inv_gfl {X : Matrix d d ℝ} (hX : IsUnit X) :
    DifferentiableAt ℝ (fun Y : Matrix d d ℝ => Y⁻¹) X := by
  have hinv : (fun Y : Matrix d d ℝ => Y⁻¹) = fun Y => Ring.inverse Y :=
    funext fun Y => Matrix.nonsing_inv_eq_ringInverse Y
  rw [hinv]
  let iR : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let iA : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  have iC : @CompleteSpace (Matrix d d ℝ) iR.toUniformSpace :=
    (inferInstance : CompleteSpace (d → d → ℝ))
  exact @differentiableAt_ringInverse_gfl (Matrix d d ℝ) iR iA iC X hX

omit [Fintype T] in
/-- `Φ` is differentiable at weights and invertible skips. -/
private theorem differentiableAt_learnedToResidual_gfl
    (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) (hp : ∀ ℓ, IsUnit (p.2 ℓ)) :
    DifferentiableAt ℝ (learnedToResidual (A := A) (dIn := dIn) (dOut := dOut)) p := by
  have hS : ∀ ℓ, DifferentiableAt ℝ
      (fun q : Params A dIn dOut × (Fin L → Matrix d d ℝ) => q.2 ℓ) p :=
    fun ℓ => differentiable_skip_gfl ℓ p
  have h1 : DifferentiableAt ℝ (fun q : Params A dIn dOut × (Fin L → Matrix d d ℝ) => q.1) p :=
    differentiable_fst_gfl p
  refine differentiableAt_params_gfl ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · -- `E Λ_0`
    have hE := (differentiable_E_gfl (A := A) (dIn := dIn) (dOut := dOut) p.1).comp p h1
    exact differentiableAt_matMul_gfl hE (differentiableAt_skipProdMat_gfl hS 0)
  · -- `Λ_{ℓ-1}⁻¹ W_read^ℓ`, with `Λ_{ℓ-1}` invertible at `p`
    have hu := isUnit_skipProdMat_gfl hp ℓ.castSucc
    have hi := (differentiableAt_inv_gfl hu).comp p
      (differentiableAt_skipProdMat_gfl hS ℓ.castSucc)
    have hR := (differentiable_read_gfl (A := A) (dIn := dIn) (dOut := dOut) ℓ p.1).comp p h1
    exact differentiableAt_matMul_gfl hi hR
  · -- `W_write^ℓ Λ_ℓ`
    have hW := (differentiable_write_gfl (A := A) (dIn := dIn) (dOut := dOut) ℓ p.1).comp p h1
    exact differentiableAt_matMul_gfl hW (differentiableAt_skipProdMat_gfl hS ℓ.succ)
  · exact (differentiable_D_gfl (A := A) (dIn := dIn) (dOut := dOut) p.1).comp p h1

omit [Fintype T] in
/-- A change of basis is a differentiable (linear) map of the weights. -/
private theorem differentiable_cob_gfl (G K : Fin (L + 1) → GL d ℝ) :
    Differentiable ℝ (fun φ : Params A dIn dOut => φ.cob G K) := by
  intro φ
  refine differentiableAt_params_gfl ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · exact differentiableAt_matMul_gfl (differentiable_E_gfl φ) (differentiableAt_const _)
  · exact differentiableAt_matMul_gfl (differentiableAt_const _) (differentiable_read_gfl ℓ φ)
  · exact differentiableAt_matMul_gfl (differentiable_write_gfl ℓ φ) (differentiableAt_const _)
  · exact differentiableAt_matMul_gfl (differentiableAt_const _) (differentiable_D_gfl φ)

omit [Fintype T] in
/-- **A differentiable right inverse of `Φ` through `p = (θ, A)`:** `s(θ') = (θ'.cob Λ⁻¹ Λ⁻¹, A)`
with the skips `A` of `p`; `Φ ∘ s = id`, `s(Φ p) = p`, and its skips are invertible. -/
private theorem exists_section_gfl (p : Params A dIn dOut × (Fin L → Matrix d d ℝ))
    (hp : ∀ ℓ, IsUnit (p.2 ℓ)) :
    ∃ s : Params A dIn dOut → Params A dIn dOut × (Fin L → Matrix d d ℝ), Differentiable ℝ s ∧
      s (learnedToResidual p) = p ∧ (∀ θ', learnedToResidual (s θ') = θ') ∧
      ∀ θ' ℓ, IsUnit ((s θ').2 ℓ) := by
  obtain ⟨θ, M⟩ := p
  obtain ⟨S, rfl⟩ := exists_coe_gfl hp
  refine ⟨fun θ' => (θ'.cob (fun ℓ => (skipProd S ℓ)⁻¹) (fun ℓ => (skipProd S ℓ)⁻¹),
    fun ℓ => (S ℓ : Matrix d d ℝ)), ?_, ?_, ?_, fun θ' ℓ => Units.isUnit (S ℓ)⟩
  · -- an affine map
    intro θ'
    have h1 := differentiable_cob_gfl (A := A) (dIn := dIn) (dOut := dOut)
      (fun ℓ => (skipProd S ℓ)⁻¹) (fun ℓ => (skipProd S ℓ)⁻¹) θ'
    exact h1.prodMk (differentiableAt_const _)
  · -- `s(Φ p) = ((θ.cob Λ Λ).cob Λ⁻¹ Λ⁻¹, A) = p`
    dsimp only
    rw [learnedToResidual_coe, cob_cob]
    simp only [mul_inv_cancel]
    rw [cob_one_gfl]
  · -- `Φ(s θ') = (θ'.cob Λ⁻¹ Λ⁻¹).cob Λ Λ = θ'`
    intro θ'
    dsimp only
    rw [learnedToResidual_coe, cob_cob]
    simp only [inv_mul_cancel]
    exact cob_one_gfl θ'

/-- A map with a differentiable right inverse through `p` has a derivative at `p` that is onto
(the chain rule for `Φ ∘ s = id` at `Φ p`). -/
private theorem exists_surjective_of_section_gfl {P₁ P₂ : Type*} [NormedAddCommGroup P₁]
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
/-- **Theorem A.5 (ii) for learned skips, "The derivative of `Φ` is onto at every `θ`"** (with
invertible skips). -/
theorem exists_hasFDerivAt_learnedToResidual_surjective
    (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) (hp : ∀ ℓ, IsUnit (p.2 ℓ)) :
    ∃ Φ' : (Params A dIn dOut × (Fin L → Matrix d d ℝ)) →L[ℝ] Params A dIn dOut,
      HasFDerivAt (learnedToResidual (A := A) (dIn := dIn) (dOut := dOut)) Φ' p
        ∧ Function.Surjective Φ' := by
  -- the chain rule for `Φ ∘ s = id` with the right inverse `s` through `p`
  obtain ⟨s, hs, hsp, hΦs, -⟩ := exists_section_gfl p hp
  exact exists_surjective_of_section_gfl (differentiableAt_learnedToResidual_gfl p hp) (hs _)
    hsp hΦs

omit [Fintype T] [Fintype dOut] in
/-- **Theorem A.5 (i) and (ii) for learned skips, `F_θ = F^res_{Φ(θ)}`:** without normalization,
a network with invertible learned skips computes the function of the residual network at
`Φ(θ, A)`. -/
theorem eval_eq_eval_learnedToResidual (hA : A.χ = id)
    (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) (hp : ∀ ℓ, IsUnit (p.2 ℓ))
    (x : Matrix T dIn ℝ) :
    eval A p.2 p.1 x = eval A 1 (learnedToResidual p) x := by
  -- write the skips as elements of `GL d ℝ`; then this is Theorem 3.2 (i)
  obtain ⟨θ, M⟩ := p
  obtain ⟨S, rfl⟩ := exists_coe_gfl hp
  rw [learnedToResidual_coe]
  exact eval_learned_eq_residual (θ := θ) (x := x) hA S

omit [Fintype T] [Fintype dOut] in
/-- **Theorem A.5 (ii) for learned skips, the same set of functions:** without normalization,
the networks with invertible learned skips and the residual networks compute the same set of
functions. -/
theorem image_eval_learned_eq_range_residual (hA : A.χ = id) :
    (fun p : Params A dIn dOut × (Fin L → Matrix d d ℝ) => eval A p.2 p.1)
        '' {p | ∀ ℓ, IsUnit (p.2 ℓ)}
      = Set.range fun θ : Params A dIn dOut => eval A 1 θ := by
  ext F
  constructor
  · -- `F_{θ,A} = F^res_{Φ(θ,A)}`
    rintro ⟨p, hp, rfl⟩
    exact ⟨learnedToResidual p, funext fun x => (eval_eq_eval_learnedToResidual hA p hp x).symm⟩
  · -- `F^res_θ` is the network with the skips `A_ℓ = I`
    rintro ⟨θ, rfl⟩
    exact ⟨(θ, 1), fun ℓ => isUnit_one, rfl⟩

omit [Fintype T] in
/-- Near weights and invertible skips, the skips stay invertible. -/
private theorem eventually_isUnit_gfl (p : Params A dIn dOut × (Fin L → Matrix d d ℝ))
    (hp : ∀ ℓ, IsUnit (p.2 ℓ)) : ∀ᶠ q in nhds p, ∀ ℓ, IsUnit (q.2 ℓ) := by
  rw [Filter.eventually_all]
  intro ℓ
  -- the determinant of `A_ℓ` is continuous and nonzero at `p`
  have hc : Continuous fun q : Params A dIn dOut × (Fin L → Matrix d d ℝ) => (q.2 ℓ).det :=
    (differentiable_skip_gfl ℓ).continuous.matrix_det
  have hne : (p.2 ℓ).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (hp ℓ)).ne_zero
  filter_upwards [hc.continuousAt.eventually_ne hne] with q h
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit h)

/-- **Theorem A.5 (ii) for learned skips, "with the same functional dimension at `θ` and at
`Φ(θ)`":** without normalization, for any blocks, the functional dimension of the network with
full learned skips at `(θ, A)` with invertible `A_ℓ` (in the weights and the skips) is that of
the residual network at `Φ(θ, A)`. -/
theorem funDimLearned_eq_funDim_residual (hA : A.χ = id)
    (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) (hp : ∀ ℓ, IsUnit (p.2 ℓ)) :
    funDimLearned A p = funDim A 1 (learnedToResidual p) := by
  -- both are `funDimOf` of their families
  have e1 : funDimLearned A p
      = funDimOf (evalSkips A (ContinuousLinearMap.id ℝ (Fin L → Matrix d d ℝ))) p :=
    funDimSkips_eq_funDimOf A _ p
  rw [e1, funDim_eq_funDimOf]
  obtain ⟨Φ', hΦ', -⟩ := exists_hasFDerivAt_learnedToResidual_surjective p hp
  obtain ⟨s, hs, hsp, hΦs, hsu⟩ := exists_section_gfl p hp
  refine funDimOf_eq_of_comp_of_section hΦ'.differentiableAt (hs _) hsp ?_ ?_
  · -- near `p` the skips are invertible, and `F_{θ,A} = F^res_{Φ(θ,A)}`
    filter_upwards [eventually_isUnit_gfl p hp] with q hq
    funext x
    exact eval_eq_eval_learnedToResidual hA q hq x
  · -- everywhere `F^res_{θ'} = F_{s(θ')}`
    refine Filter.Eventually.of_forall fun y => funext fun x => ?_
    show eval A 1 y x = eval A (s y).2 (s y).1 x
    rw [eval_eq_eval_learnedToResidual hA (s y) (hsu y) x, hΦs y]

end Skips
