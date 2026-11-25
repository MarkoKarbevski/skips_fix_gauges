import SkipsLean.Residual.GaugeFixLearned
import SkipsLean.Dimension.FunDimFamily
import SkipsLean.Symmetry.BiasesSymmetries

/-!
# The gauge fix with biases, for networks of mixed blocks and for learned skips

Paper (skips paper), Appendix A.2, after equation (12): "With biases, `Φ` also sends the
embedding bias `b_E` to `b_E Λ_0` and each write bias `b_write^ℓ` to `b_write^ℓ Λ_ℓ`, and keeps
each read bias." Theorem A.5 (ii): "The same holds for learned skips, without the `K_ℓ`, and for
networks with biases." Its proof: "Part (i), with biases and a skip bias. Merge the identity
units, `A_ℓ = U_ℓ V_ℓ`, and write the network as
`h_ℓ = h_{ℓ−1} A_ℓ + k_ℓ + f_ℓ(h_{ℓ−1} W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ` with
`h_0 = x E + b_E`, where `k_ℓ ∈ ℝ^{1 × d_model}` is a skip bias (`k_ℓ = 0` is allowed). […]
`b'_write^ℓ = (b_write^ℓ + k_ℓ) Λ_ℓ`"; "Part (ii). The identity units carry no biases of their
own, since these would only add to the write bias."

Here, in the frame of `Network/Biases.lean` (`evalB A S θ b`: the stream matrices `S` are the
skips, the block adds `f_ℓ(χ(h) W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ` to the stream). A
skip bias `k_ℓ` is added to the stream as `b_write^ℓ` is, so the network with a skip bias is the
network with the write bias `b_write^ℓ + k_ℓ`, and the statements below are those of the proof
with `k_ℓ` merged into the write bias.

* `Biases.mulSkipProd b Λ`: the biases `b_E Λ_0`, `b_read^ℓ`, `b_write^ℓ Λ_ℓ`, `b_D`.
* Networks of mixed blocks with biases: the parameters are the pairs `p = (θ, b)` of a parameter
  `θ` of `A.mixed` and the biases `b` of the embedding, of the hidden units and of the readout
  ("The identity units carry no biases of their own"); `evalMixedB A p x`; `mixedToResidualB p`,
  the map `Φ` with biases. `T_{G,K}` acts by `(θ.cobMixed G G K, b.cob G)`.
* Networks with learned skips and biases: the parameters are `p = ((θ, b), (A_ℓ))`, the function
  is `evalB A p.2 p.1.1 p.1.2`, and `learnedToResidualB p` is `Φ` with biases. `T_G` acts by
  `((θ.cob G G, b.cob G), cobSkip A G)`; that it preserves the function is `evalB_cob`
  (`Symmetry/BiasesSymmetries.lean`).
* For both: (i) the same function as the residual network with biases at `Φ(p)`; (ii) every
  parameter of the residual network with biases is a `Φ(p)`; `Φ(p̃) = Φ(p)` exactly when
  `p̃ = T(p)` with `G_L = I`; the derivative of `Φ` is onto; the same set of functions; and the
  same functional dimension at `p` and at `Φ(p)` (`funDimOf` of `Dimension/FunDimFamily.lean`
  for the family at hand, `funDimB` for the residual network with biases).

The model dimension is `d : Type`, as in `Residual/GaugeFixMixed.lean`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T : Type*} {d : Type} {dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d]
  [DecidableEq d] [Fintype dIn] [Fintype dOut]
variable {A : Arch T d L}

/-- **The biases under the map `Φ`:** "`Φ` also sends the embedding bias `b_E` to `b_E Λ_0` and
each write bias `b_write^ℓ` to `b_write^ℓ Λ_ℓ`, and keeps each read bias"; the readout bias is
kept. -/
def Biases.mulSkipProd (b : Biases A dOut) (Λ : Fin (L + 1) → Matrix d d ℝ) : Biases A dOut where
  E := b.E ᵥ* Λ 0
  read := b.read
  write ℓ := b.write ℓ ᵥ* Λ ℓ.succ
  D := b.D

/-! ### Networks of mixed blocks with biases -/

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- `Λ_L = I`. -/
private theorem skipProdMat_last_gfb (S : Fin L → Matrix d d ℝ) :
    skipProdMat S (Fin.last L) = 1 := by
  simp [skipProdMat]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- `Λ_{ℓ-1} = S_ℓ Λ_ℓ`. -/
private theorem skipProdMat_castSucc_gfb (S : Fin L → Matrix d d ℝ) (ℓ : Fin L) :
    skipProdMat S ℓ.castSucc = S ℓ * skipProdMat S ℓ.succ := by
  simp [skipProdMat]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- For invertible skips the products are those of `skipProd`, as functions. -/
private theorem skipProdMat_coe_gfb (S : Fin L → GL d ℝ) :
    skipProdMat (fun ℓ => (S ℓ : Matrix d d ℝ)) = fun ℓ => (skipProd S ℓ : Matrix d d ℝ) :=
  funext (skipProdMat_coe S)

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- With the skips `A_ℓ = I`, every `Λ_ℓ` is `I`. -/
private theorem skipProdMat_one_gfb :
    skipProdMat (1 : Fin L → Matrix d d ℝ) = fun _ => 1 := by
  funext ℓ
  induction ℓ using Fin.reverseInduction with
  | last => rw [skipProdMat_last_gfb]
  | cast i ih => rw [skipProdMat_castSucc_gfb, ih, Pi.one_apply, Matrix.mul_one]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- After `T_G` with `G_L = I`, the products of the skips are `G_ℓ⁻¹ Λ_ℓ` (any skips). -/
private theorem skipProdMat_cobSkip_gfb (S : Fin L → Matrix d d ℝ) (G : Fin (L + 1) → GL d ℝ)
    (hG : G (Fin.last L) = 1) :
    skipProdMat (cobSkip S G) = fun ℓ => (↑(G ℓ)⁻¹ : Matrix d d ℝ) * skipProdMat S ℓ := by
  funext ℓ
  induction ℓ using Fin.reverseInduction with
  | last =>
    rw [skipProdMat_last_gfb, skipProdMat_last_gfb, hG, inv_one, Units.val_one, Matrix.one_mul]
  | cast i ih =>
    -- `(G_{i-1}⁻¹ S_i G_i)(G_i⁻¹ Λ_i) = G_{i-1}⁻¹ S_i Λ_i`
    rw [skipProdMat_castSucc_gfb, skipProdMat_castSucc_gfb, ih]
    simp only [cobSkip, Matrix.mul_assoc, Units.mul_inv_cancel_left]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- A product of invertible matrices is invertible. -/
private theorem isUnit_skipProdMat_gfb {S : Fin L → Matrix d d ℝ} (hS : ∀ ℓ, IsUnit (S ℓ))
    (ℓ : Fin (L + 1)) : IsUnit (skipProdMat S ℓ) := by
  induction ℓ using Fin.reverseInduction with
  | last =>
    rw [skipProdMat_last_gfb]
    exact isUnit_one
  | cast i ih =>
    rw [skipProdMat_castSucc_gfb]
    exact (hS i).mul ih

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Invertible skips are the matrices of elements of `GL d ℝ`. -/
private theorem exists_coe_gfb {M : Fin L → Matrix d d ℝ} (h : ∀ ℓ, IsUnit (M ℓ)) :
    ∃ S : Fin L → GL d ℝ, M = fun ℓ => (S ℓ : Matrix d d ℝ) :=
  ⟨fun ℓ => (h ℓ).unit, funext fun ℓ => ((h ℓ).unit_spec).symm⟩

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The change of basis of the biases is `mulSkipProd` by the matrices of `G`. -/
private theorem mulSkipProd_coe_gfb (b : Biases A dOut) (G : Fin (L + 1) → GL d ℝ) :
    b.mulSkipProd (fun ℓ => (G ℓ : Matrix d d ℝ)) = b.cob G :=
  rfl

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Two `mulSkipProd` are one, by the products. -/
private theorem mulSkipProd_mulSkipProd_gfb (b : Biases A dOut)
    (Λ Λ' : Fin (L + 1) → Matrix d d ℝ) :
    (b.mulSkipProd Λ).mulSkipProd Λ' = b.mulSkipProd (fun ℓ => Λ ℓ * Λ' ℓ) := by
  refine Biases.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [Biases.mulSkipProd, Matrix.vecMul_vecMul]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- `mulSkipProd` by `I` is the identity. -/
private theorem mulSkipProd_one_gfb (b : Biases A dOut) : b.mulSkipProd (fun _ => 1) = b := by
  refine Biases.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp only [Biases.mulSkipProd, Matrix.vecMul_one]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- `(b G) (G⁻¹ Λ) = b Λ`, for the biases. -/
private theorem mulSkipProd_cob_gfb (b : Biases A dOut) (G : Fin (L + 1) → GL d ℝ)
    (Λ : Fin (L + 1) → Matrix d d ℝ) :
    (b.cob G).mulSkipProd (fun ℓ => (↑(G ℓ)⁻¹ : Matrix d d ℝ) * Λ ℓ) = b.mulSkipProd Λ := by
  rw [← mulSkipProd_coe_gfb, mulSkipProd_mulSkipProd_gfb]
  simp only [Units.mul_inv_cancel_left]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- `mulSkipProd` by invertible matrices is injective. -/
private theorem mulSkipProd_injective_gfb {Λ : Fin (L + 1) → Matrix d d ℝ}
    (hΛ : ∀ ℓ, IsUnit (Λ ℓ)) {b b' : Biases A dOut} (h : b.mulSkipProd Λ = b'.mulSkipProd Λ) :
    b = b' := by
  -- `mulSkipProd` by `Λ⁻¹` undoes `mulSkipProd` by `Λ`
  have e : ∀ c : Biases A dOut, c = (c.mulSkipProd Λ).mulSkipProd (fun ℓ => (Λ ℓ)⁻¹) := by
    intro c
    rw [mulSkipProd_mulSkipProd_gfb]
    have hinv : (fun ℓ => Λ ℓ * (Λ ℓ)⁻¹) = fun _ => (1 : Matrix d d ℝ) :=
      funext fun ℓ => Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (hΛ ℓ))
    rw [hinv, mulSkipProd_one_gfb]
  calc b = _ := e b
    _ = _ := by rw [h]
    _ = b' := (e b').symm

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The skips after the change of basis by `Λ` are the identity: `Λ_{ℓ-1}⁻¹ A_ℓ Λ_ℓ = I`. -/
private theorem cobSkip_skipProd_gfb (S : Fin L → GL d ℝ) :
    cobSkip (fun ℓ => (S ℓ : Matrix d d ℝ)) (skipProd S) = 1 := by
  funext ℓ
  simp only [cobSkip, Pi.one_apply]
  rw [mul_assoc, ← Units.val_mul, ← skipProd_castSucc, Units.inv_mul]

omit [Fintype T] [Fintype dOut] in
/-- **Theorem 3.2 (i) with biases:** without normalization, the network with invertible learned
skips and biases computes the function of the residual network at `(θ.cob Λ Λ, b.cob Λ)`. -/
private theorem evalB_learned_gfb (hA : A.χ = id) (θ : Params A dIn dOut) (b : Biases A dOut)
    (S : Fin L → GL d ℝ) (x : Matrix T dIn ℝ) :
    evalB A (fun ℓ => (S ℓ : Matrix d d ℝ)) θ b x
      = evalB A 1 (θ.cob (skipProd S) (skipProd S)) (b.cob (skipProd S)) x := by
  have hχ : ∀ ℓ (h : Matrix T d ℝ), A.χ (h * (skipProd S ℓ : Matrix d d ℝ))
      = A.χ h * (skipProd S ℓ : Matrix d d ℝ) := fun ℓ h => by simp only [hA, id_eq]
  -- the changes of basis `G = K = Λ` turn the skips into `Λ_{ℓ-1}⁻¹ A_ℓ Λ_ℓ = I`
  rw [← evalB_cob (M := fun ℓ => (S ℓ : Matrix d d ℝ)) (θ := θ) (b := b) (G := skipProd S)
    (K := skipProd S) (x := x) hχ, cobSkip_skipProd_gfb]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The skips of `T_{G,K}(θ)` are `G_{ℓ-1}⁻¹ (U_ℓ V_ℓ) G_ℓ`. -/
private theorem skips_cobMixed_gfb (θ : Params A.mixed dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (K : Fin L → GL d ℝ) :
    (fun ℓ => (θ.cobMixed G Q K).mixU ℓ * (θ.cobMixed G Q K).mixV ℓ)
      = cobSkip (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) G := by
  unfold Params.cobMixed
  rw [Params.mixU_mix, Params.mixV_mix]
  funext ℓ
  simp only [cobSkip, Matrix.mul_assoc, Units.mul_inv_cancel_left]

omit [Fintype T] [Fintype dIn] [Fintype dOut] [DecidableEq d] in
/-- The skips of `Params.mix φ U V` are `U_ℓ V_ℓ`. -/
private theorem skips_mix_gfb (φ : Params A dIn dOut) (U V : Fin L → Matrix d d ℝ) :
    (fun ℓ => (Params.mix φ U V).mixU ℓ * (Params.mix φ U V).mixV ℓ) = fun ℓ => U ℓ * V ℓ := by
  rw [Params.mixU_mix, Params.mixV_mix]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The hidden units of `T_{G,K}(θ)` are `θ.unmix.cob G Q`. -/
private theorem unmix_cobMixed_gfb (θ : Params A.mixed dIn dOut) (G Q : Fin (L + 1) → GL d ℝ)
    (K : Fin L → GL d ℝ) : (θ.cobMixed G Q K).unmix = θ.unmix.cob G Q := by
  unfold Params.cobMixed
  exact Params.unmix_mix _ _ _

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- `Φ` of a network of mixed blocks is `Φ` for learned skips of its hidden units and its skips
`U_ℓ V_ℓ`. -/
private theorem mixedToResidual_eq_gfb (θ : Params A.mixed dIn dOut) :
    mixedToResidual θ = learnedToResidual (θ.unmix, fun ℓ => θ.mixU ℓ * θ.mixV ℓ) :=
  rfl

omit [Fintype T] [DecidableEq d] in
/-- A map into the weights is differentiable if its four components are. -/
private theorem differentiableAt_params_gfb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Arch T d L} {f : E → Params B dIn dOut} {x : E}
    (hE : DifferentiableAt ℝ (fun y => (f y).E) x)
    (hr : ∀ ℓ, DifferentiableAt ℝ (fun y => (f y).read ℓ) x)
    (hw : ∀ ℓ, DifferentiableAt ℝ (fun y => (f y).write ℓ) x)
    (hD : DifferentiableAt ℝ (fun y => (f y).D) x) : DifferentiableAt ℝ f x := by
  let e := (Params.linearEquivProd (A := B) (dIn := dIn) (dOut := dOut)).toContinuousLinearEquiv
  have hp : DifferentiableAt ℝ (fun y => ((f y).E, (f y).read, (f y).write, (f y).D)) x :=
    hE.prodMk ((differentiableAt_pi.2 hr).prodMk ((differentiableAt_pi.2 hw).prodMk hD))
  have hc := e.symm.differentiableAt.comp x hp
  exact hc

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- A map into the biases is differentiable if its four components are. -/
private theorem differentiableAt_biases_gfb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Biases A dOut} {x : E}
    (hE : DifferentiableAt ℝ (fun y => (f y).E) x)
    (hr : ∀ ℓ, DifferentiableAt ℝ (fun y => (f y).read ℓ) x)
    (hw : ∀ ℓ, DifferentiableAt ℝ (fun y => (f y).write ℓ) x)
    (hD : DifferentiableAt ℝ (fun y => (f y).D) x) : DifferentiableAt ℝ f x := by
  let e := (Biases.linearEquivProd (A := A) (dOut := dOut)).toContinuousLinearEquiv
  have hp : DifferentiableAt ℝ (fun y => ((f y).E, (f y).read, (f y).write, (f y).D)) x :=
    hE.prodMk ((differentiableAt_pi.2 hr).prodMk ((differentiableAt_pi.2 hw).prodMk hD))
  have hc := e.symm.differentiableAt.comp x hp
  exact hc

/-- A linear map on a finite-dimensional space is differentiable. -/
private theorem differentiable_linear_gfb {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F] (l : P →ₗ[ℝ] F) :
    Differentiable ℝ l := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).differentiable

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The product of two differentiable matrix-valued maps is differentiable. -/
private theorem differentiableAt_matMul_gfb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- A row times a matrix, both differentiable, is differentiable. -/
private theorem differentiableAt_vecMul_gfb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : Type*} [Fintype m] [Fintype n] {f : E → m → ℝ} {g : E → Matrix m n ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y => f y ᵥ* g y) x := by
  -- `(v, M) ↦ v M` as a bilinear map
  let B : (m → ℝ) →ₗ[ℝ] Matrix m n ℝ →ₗ[ℝ] (n → ℝ) :=
    LinearMap.mk₂ ℝ (fun v M => v ᵥ* M) (fun v w M => Matrix.add_vecMul M v w)
      (fun c v M => Matrix.smul_vecMul c v M) (fun v M N => Matrix.vecMul_add M N v)
      (fun c v M => Matrix.vecMul_smul v c M)
  let B' : (m → ℝ) →L[ℝ] Matrix m n ℝ →L[ℝ] (n → ℝ) :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
        (Matrix m n ℝ →ₗ[ℝ] (n → ℝ)) ≃ₗ[ℝ] (Matrix m n ℝ →L[ℝ] (n → ℝ))).toLinearMap ∘ₗ B)
  have hB : (fun y => f y ᵥ* g y) = fun y => B' (f y) (g y) := rfl
  rw [hB]
  exact (B'.differentiableAt.comp x hf).clm_apply hg

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The products `Λ_ℓ` of differentiable skips are differentiable. -/
private theorem differentiableAt_skipProdMat_gfb {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {S : E → Fin L → Matrix d d ℝ} {x : E}
    (hS : ∀ ℓ, DifferentiableAt ℝ (fun y => S y ℓ) x) (ℓ : Fin (L + 1)) :
    DifferentiableAt ℝ (fun y => skipProdMat (S y) ℓ) x := by
  induction ℓ using Fin.reverseInduction with
  | last =>
    simp only [skipProdMat_last_gfb]
    exact differentiableAt_const _
  | cast i ih =>
    -- `Λ_{i-1} = S_i Λ_i`
    simp only [skipProdMat_castSucc_gfb]
    exact differentiableAt_matMul_gfb (hS i) ih

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- `(b, Λ) ↦ b.mulSkipProd Λ` is differentiable. -/
private theorem differentiableAt_mulSkipProd_gfb {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {b : E → Biases A dOut} {Λ : E → Fin (L + 1) → Matrix d d ℝ} {x : E}
    (hb : DifferentiableAt ℝ b x) (hΛ : ∀ ℓ, DifferentiableAt ℝ (fun y => Λ y ℓ) x) :
    DifferentiableAt ℝ (fun y => (b y).mulSkipProd (Λ y)) x := by
  -- the four components of the biases, as linear maps
  have pE : Differentiable ℝ (fun c : Biases A dOut => c.E) :=
    differentiable_linear_gfb
      { toFun := fun c : Biases A dOut => c.E,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have pr : ∀ ℓ, Differentiable ℝ (fun c : Biases A dOut => c.read ℓ) := fun ℓ =>
    differentiable_linear_gfb
      { toFun := fun c : Biases A dOut => c.read ℓ,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have pw : ∀ ℓ, Differentiable ℝ (fun c : Biases A dOut => c.write ℓ) := fun ℓ =>
    differentiable_linear_gfb
      { toFun := fun c : Biases A dOut => c.write ℓ,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have pD : Differentiable ℝ (fun c : Biases A dOut => c.D) :=
    differentiable_linear_gfb
      { toFun := fun c : Biases A dOut => c.D,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  refine differentiableAt_biases_gfb ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · have h := (pE (b x)).comp x hb
    exact differentiableAt_vecMul_gfb h (hΛ 0)
  · have h := ((pr ℓ) (b x)).comp x hb
    exact h
  · have h := ((pw ℓ) (b x)).comp x hb
    exact differentiableAt_vecMul_gfb h (hΛ ℓ.succ)
  · have h := (pD (b x)).comp x hb
    exact h

omit [Fintype T] [DecidableEq d] in
/-- The four components of the weights are differentiable (linear) functions of them. -/
private theorem differentiable_comps_gfb {B : Arch T d L} :
    Differentiable ℝ (fun θ : Params B dIn dOut => θ.E) ∧
      (∀ ℓ, Differentiable ℝ (fun θ : Params B dIn dOut => θ.read ℓ)) ∧
      (∀ ℓ, Differentiable ℝ (fun θ : Params B dIn dOut => θ.write ℓ)) ∧
      Differentiable ℝ (fun θ : Params B dIn dOut => θ.D) :=
  ⟨differentiable_linear_gfb
      { toFun := fun θ : Params B dIn dOut => θ.E,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    fun ℓ => differentiable_linear_gfb
      { toFun := fun θ : Params B dIn dOut => θ.read ℓ,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    fun ℓ => differentiable_linear_gfb
      { toFun := fun θ : Params B dIn dOut => θ.write ℓ,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    differentiable_linear_gfb
      { toFun := fun θ : Params B dIn dOut => θ.D,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }⟩

omit [Fintype T] in
/-- A change of basis is a differentiable (linear) map of the weights. -/
private theorem differentiable_cob_gfb (G K : Fin (L + 1) → GL d ℝ) :
    Differentiable ℝ (fun φ : Params A dIn dOut => φ.cob G K) := by
  obtain ⟨hE, hr, hw, hD⟩ := differentiable_comps_gfb (B := A) (dIn := dIn) (dOut := dOut)
  intro φ
  refine differentiableAt_params_gfb ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · exact differentiableAt_matMul_gfb (hE φ) (differentiableAt_const _)
  · exact differentiableAt_matMul_gfb (differentiableAt_const _) (hr ℓ φ)
  · exact differentiableAt_matMul_gfb (hw ℓ φ) (differentiableAt_const _)
  · exact differentiableAt_matMul_gfb (differentiableAt_const _) (hD φ)

omit [Fintype T] [DecidableEq d] in
/-- `φ ↦ Params.mix φ U V` is a differentiable (affine) map. -/
private theorem differentiable_mix_gfb (U V : Fin L → Matrix d d ℝ) :
    Differentiable ℝ (fun φ : Params A dIn dOut => Params.mix φ U V) := by
  obtain ⟨hE, hr, hw, hD⟩ := differentiable_comps_gfb (B := A) (dIn := dIn) (dOut := dOut)
  intro φ
  refine differentiableAt_params_gfb ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · exact hE φ
  · -- entry by entry: the columns `Sum.inl` are constant, the others are those of `W_read^ℓ`
    refine differentiableAt_pi.2 fun a => differentiableAt_pi.2 fun s => ?_
    cases s with
    | inl c =>
      show DifferentiableAt ℝ (fun _ : Params A dIn dOut => U ℓ a c) φ
      exact differentiableAt_const _
    | inr j =>
      show DifferentiableAt ℝ (fun φ : Params A dIn dOut => φ.read ℓ a j) φ
      exact differentiableAt_pi.1 (differentiableAt_pi.1 (hr ℓ φ) a) j
  · -- row by row: the rows `Sum.inl` are constant, the others are those of `W_write^ℓ`
    refine differentiableAt_pi.2 fun s => ?_
    cases s with
    | inl a =>
      show DifferentiableAt ℝ (fun _ : Params A dIn dOut => V ℓ a) φ
      exact differentiableAt_const _
    | inr c =>
      show DifferentiableAt ℝ (fun φ : Params A dIn dOut => φ.write ℓ c) φ
      exact differentiableAt_pi.1 (hw ℓ φ) c
  · exact hD φ

/-- A map with a differentiable right inverse through `p` has a derivative at `p` that is onto
(the chain rule for `Φ ∘ s = id` at `Φ p`). -/
private theorem exists_surjective_of_section_gfb {P₁ P₂ : Type*} [NormedAddCommGroup P₁]
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

/-- **The function of the network of mixed blocks with biases:** the network of `A` with the
learned skips `U_ℓ V_ℓ`, the hidden units of `θ` and the biases `b`; the identity units carry no
biases. -/
def evalMixedB (A : Arch T d L) (p : Params A.mixed dIn dOut × Biases A dOut)
    (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  evalB A (fun ℓ => p.1.mixU ℓ * p.1.mixV ℓ) p.1.unmix p.2 x

/-- **The map `Φ` of equation (12) with biases, for networks of mixed blocks.** -/
noncomputable def mixedToResidualB (p : Params A.mixed dIn dOut × Biases A dOut) :
    ParamsB A dIn dOut :=
  (mixedToResidual p.1, p.2.mulSkipProd (skipProdMat fun ℓ => p.1.mixU ℓ * p.1.mixV ℓ))

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The change of basis by `G = K = 1` is the identity. -/
private theorem cob_one_gfb (φ : Params A dIn dOut) : φ.cob (fun _ => 1) (fun _ => 1) = φ := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp [Params.cob]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Two changes of basis of the biases are one, by the products. -/
private theorem cob_cob_biases_gfb (b : Biases A dOut) (G G' : Fin (L + 1) → GL d ℝ) :
    (b.cob G).cob G' = b.cob (fun ℓ => G ℓ * G' ℓ) := by
  rw [← mulSkipProd_coe_gfb, ← mulSkipProd_coe_gfb, ← mulSkipProd_coe_gfb,
    mulSkipProd_mulSkipProd_gfb]
  simp only [Units.val_mul]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The change of basis of the biases by `G = 1` is the identity. -/
private theorem cob_one_biases_gfb (b : Biases A dOut) : b.cob (fun _ => 1) = b := by
  rw [← mulSkipProd_coe_gfb]
  simp only [Units.val_one]
  exact mulSkipProd_one_gfb b

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **`Φ` with biases of a network of mixed blocks with invertible skips:**
`(θ.unmix.cob Λ Λ, b.cob Λ)`. -/
private theorem mixedToResidualB_coe_gfb (θ : Params A.mixed dIn dOut) (b : Biases A dOut)
    (S : Fin L → GL d ℝ) (hS : (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) = fun ℓ => (S ℓ : Matrix d d ℝ)) :
    mixedToResidualB (θ, b)
      = (θ.unmix.cob (skipProd S) (skipProd S), b.cob (skipProd S)) := by
  show (mixedToResidual θ, b.mulSkipProd (skipProdMat fun ℓ => θ.mixU ℓ * θ.mixV ℓ)) = _
  rw [mixedToResidual_eq_gfb, hS, learnedToResidual_coe, skipProdMat_coe_gfb, mulSkipProd_coe_gfb]

omit [Fintype T] [DecidableEq d] in
/-- The skips `U_ℓ V_ℓ` are differentiable functions of the parameters. -/
private theorem differentiable_mixSkip_gfb (ℓ : Fin L) :
    Differentiable ℝ
      (fun p : Params A.mixed dIn dOut × Biases A dOut => p.1.mixU ℓ * p.1.mixV ℓ) := by
  have hU : Differentiable ℝ (fun p : Params A.mixed dIn dOut × Biases A dOut => p.1.mixU ℓ) :=
    differentiable_linear_gfb
      { toFun := fun p : Params A.mixed dIn dOut × Biases A dOut => p.1.mixU ℓ,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hV : Differentiable ℝ (fun p : Params A.mixed dIn dOut × Biases A dOut => p.1.mixV ℓ) :=
    differentiable_linear_gfb
      { toFun := fun p : Params A.mixed dIn dOut × Biases A dOut => p.1.mixV ℓ,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  intro p
  exact differentiableAt_matMul_gfb (hU p) (hV p)

omit [Fintype T] in
/-- Near a parameter with invertible skips, the skips stay invertible. -/
private theorem eventually_isUnit_mixed_gfb (p : Params A.mixed dIn dOut × Biases A dOut)
    (hp : ∀ ℓ, IsUnit (p.1.mixU ℓ * p.1.mixV ℓ)) :
    ∀ᶠ q in nhds p, ∀ ℓ, IsUnit (q.1.mixU ℓ * q.1.mixV ℓ) := by
  rw [Filter.eventually_all]
  intro ℓ
  -- the determinant of `U_ℓ V_ℓ` is continuous and nonzero at `p`
  have hc : Continuous fun q : Params A.mixed dIn dOut × Biases A dOut =>
      (q.1.mixU ℓ * q.1.mixV ℓ).det :=
    (differentiable_mixSkip_gfb ℓ).continuous.matrix_det
  have hne : (p.1.mixU ℓ * p.1.mixV ℓ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (hp ℓ)).ne_zero
  filter_upwards [hc.continuousAt.eventually_ne hne] with q h
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit h)

omit [Fintype T] in
/-- `Φ` with biases is differentiable at a parameter with invertible skips. -/
private theorem differentiableAt_mixedToResidualB_gfb
    (p : Params A.mixed dIn dOut × Biases A dOut) (hp : ∀ ℓ, IsUnit (p.1.mixU ℓ * p.1.mixV ℓ)) :
    DifferentiableAt ℝ (mixedToResidualB (A := A) (dIn := dIn) (dOut := dOut)) p := by
  -- the weights: `Φ` of `Residual/GaugeFixMixed.lean`
  obtain ⟨Φ', hΦ', -⟩ := exists_hasFDerivAt_mixedToResidual_surjective p.1 hp
  have h1 : DifferentiableAt ℝ
      (fun q : Params A.mixed dIn dOut × Biases A dOut => mixedToResidual q.1) p :=
    hΦ'.differentiableAt.comp p differentiableAt_fst
  -- the biases: `b_E Λ_0`, `b_read`, `b_write Λ_ℓ`, `b_D`
  have h2 : DifferentiableAt ℝ (fun q : Params A.mixed dIn dOut × Biases A dOut =>
      q.2.mulSkipProd (skipProdMat fun ℓ => q.1.mixU ℓ * q.1.mixV ℓ)) p :=
    differentiableAt_mulSkipProd_gfb differentiableAt_snd
      (fun ℓ => differentiableAt_skipProdMat_gfb (fun k => differentiable_mixSkip_gfb k p) ℓ)
  exact h1.prodMk h2

omit [Fintype T] in
/-- **A differentiable right inverse of `Φ` with biases through `p = (θ, b)`:**
`s(θ', b') = (Params.mix (θ'.cob Λ⁻¹ Λ⁻¹) U V, b'.cob Λ⁻¹)` with the identity units `U`, `V` of
`θ`. -/
private theorem exists_section_mixed_gfb (p : Params A.mixed dIn dOut × Biases A dOut)
    (hp : ∀ ℓ, IsUnit (p.1.mixU ℓ * p.1.mixV ℓ)) :
    ∃ s : ParamsB A dIn dOut → Params A.mixed dIn dOut × Biases A dOut, Differentiable ℝ s ∧
      s (mixedToResidualB p) = p ∧ (∀ y, mixedToResidualB (s y) = y) ∧
      ∀ y ℓ, IsUnit ((s y).1.mixU ℓ * (s y).1.mixV ℓ) := by
  obtain ⟨θ, b⟩ := p
  change ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ) at hp
  obtain ⟨S, hS⟩ := exists_coe_gfb hp
  refine ⟨fun y => (Params.mix (y.1.cob (fun ℓ => (skipProd S ℓ)⁻¹) (fun ℓ => (skipProd S ℓ)⁻¹))
      θ.mixU θ.mixV, y.2.cob (fun ℓ => (skipProd S ℓ)⁻¹)), ?_, ?_, ?_, ?_⟩
  · -- an affine map
    intro y
    have hc := (differentiable_cob_gfb (A := A) (dIn := dIn) (dOut := dOut)
      (fun ℓ => (skipProd S ℓ)⁻¹) (fun ℓ => (skipProd S ℓ)⁻¹) y.1).comp y differentiableAt_fst
    have h1 := (differentiable_mix_gfb (A := A) (dIn := dIn) (dOut := dOut) θ.mixU θ.mixV
      _).comp y hc
    have h2 : DifferentiableAt ℝ (fun y : ParamsB A dIn dOut =>
        y.2.mulSkipProd (fun ℓ => (((skipProd S ℓ)⁻¹ : GL d ℝ) : Matrix d d ℝ))) y :=
      differentiableAt_mulSkipProd_gfb differentiableAt_snd (fun ℓ => differentiableAt_const _)
    exact h1.prodMk h2
  · -- `s(Φ p) = (Params.mix ((θ.unmix.cob Λ Λ).cob Λ⁻¹ Λ⁻¹) U V, (b.cob Λ).cob Λ⁻¹) = p`
    rw [mixedToResidualB_coe_gfb θ b S hS]
    dsimp only
    rw [cob_cob, cob_cob_biases_gfb]
    simp only [mul_inv_cancel]
    rw [cob_one_gfb, cob_one_biases_gfb, Params.mix_unmix]
  · -- `Φ(s y) = ((y.1.cob Λ⁻¹ Λ⁻¹).cob Λ Λ, (y.2.cob Λ⁻¹).cob Λ) = y`
    rintro ⟨φ, c⟩
    dsimp only
    rw [mixedToResidualB_coe_gfb _ _ S ((skips_mix_gfb _ θ.mixU θ.mixV).trans hS),
      Params.unmix_mix, cob_cob, cob_cob_biases_gfb]
    simp only [inv_mul_cancel]
    rw [cob_one_gfb, cob_one_biases_gfb]
  · -- the identity units of `s y` are those of `θ`
    intro y ℓ
    dsimp only
    rw [Params.mixU_mix, Params.mixV_mix]
    exact hp ℓ

omit [Fintype T] [Fintype dOut] in
/-- **Theorem A.5 (i) with biases, "The maps `T_{G,K}` preserve the function":** without
normalization, with the embedding bias and the write biases multiplied as the embedding and the
writes are. -/
theorem evalMixedB_cobMixed (hA : A.χ = id) (p : Params A.mixed dIn dOut × Biases A dOut)
    (G : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ) (x : Matrix T dIn ℝ) :
    evalMixedB A (p.1.cobMixed G G K, p.2.cob G) x = evalMixedB A p x := by
  obtain ⟨θ, b⟩ := p
  -- the skips of `T_{G,K}(θ)` are `G_{ℓ-1}⁻¹ (U_ℓ V_ℓ) G_ℓ` and its hidden units `θ.unmix.cob G G`
  show evalB A (fun ℓ => (θ.cobMixed G G K).mixU ℓ * (θ.cobMixed G G K).mixV ℓ)
    (θ.cobMixed G G K).unmix (b.cob G) x = evalB A (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) θ.unmix b x
  rw [skips_cobMixed_gfb, unmix_cobMixed_gfb]
  -- the changes of basis of the network with biases, `χ = id`
  exact evalB_cob (M := fun ℓ => θ.mixU ℓ * θ.mixV ℓ) (θ := θ.unmix) (b := b) (G := G) (K := G)
    (x := x) (fun ℓ h => by simp only [hA, id_eq])

omit [Fintype T] [Fintype dOut] in
/-- **Theorem A.5 (i) with biases, `F_θ = F^res_{Φ(θ)}`:** without normalization, a network of
mixed blocks with biases and invertible skips computes the function of the residual network with
biases at `Φ(p)`. -/
theorem evalMixedB_eq_evalB_mixedToResidualB (hA : A.χ = id)
    (p : Params A.mixed dIn dOut × Biases A dOut) (hp : ∀ ℓ, IsUnit (p.1.mixU ℓ * p.1.mixV ℓ))
    (x : Matrix T dIn ℝ) :
    evalMixedB A p x = evalB A 1 (mixedToResidualB p).1 (mixedToResidualB p).2 x := by
  -- the skips `U_ℓ V_ℓ` are invertible, `Φ(p) = (θ.unmix.cob Λ Λ, b.cob Λ)`: Theorem 3.2 (i)
  obtain ⟨θ, b⟩ := p
  obtain ⟨S, hS⟩ := exists_coe_gfb hp
  rw [mixedToResidualB_coe_gfb θ b S hS]
  show evalB A (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) θ.unmix b x = _
  rw [hS]
  exact evalB_learned_gfb hA θ.unmix b S x

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Theorem A.5 (ii) with biases, "Every parameter of the residual network is `Φ(θ)` for some
`θ`".** -/
theorem mixedToResidualB_mix_one (q : ParamsB A dIn dOut) :
    mixedToResidualB (Params.mix q.1 1 1, q.2) = q := by
  obtain ⟨θ, b⟩ := q
  refine Prod.ext (mixedToResidual_mix_one θ) ?_
  -- the skips are `I`, so every `Λ_ℓ` is `I`
  show b.mulSkipProd (skipProdMat fun ℓ => (Params.mix θ 1 1).mixU ℓ * (Params.mix θ 1 1).mixV ℓ)
    = b
  rw [Params.mixU_mix, Params.mixV_mix]
  have h1 : (fun ℓ => (1 : Fin L → Matrix d d ℝ) ℓ * (1 : Fin L → Matrix d d ℝ) ℓ) = 1 :=
    funext fun ℓ => by simp
  rw [h1, skipProdMat_one_gfb, mulSkipProd_one_gfb]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Theorem A.5 (ii) with biases, "`Φ(θ̃) = Φ(θ)` exactly when `θ̃ = T_{G,K}(θ)` for some `G`
and `K` with `G_L = I`"**, for invertible skips. -/
theorem mixedToResidualB_eq_iff (p p' : Params A.mixed dIn dOut × Biases A dOut)
    (hp : ∀ ℓ, IsUnit (p.1.mixU ℓ * p.1.mixV ℓ))
    (hp' : ∀ ℓ, IsUnit (p'.1.mixU ℓ * p'.1.mixV ℓ)) :
    mixedToResidualB p' = mixedToResidualB p
      ↔ ∃ (G : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ),
          G (Fin.last L) = 1 ∧ p' = (p.1.cobMixed G G K, p.2.cob G) := by
  obtain ⟨θ, b⟩ := p
  obtain ⟨θ', b'⟩ := p'
  -- after `T_{G,K}` with `G_L = I` the products of the skips are `G_ℓ⁻¹ Λ_ℓ`
  have key : ∀ (G : Fin (L + 1) → GL d ℝ), G (Fin.last L) = 1 → ∀ K : Fin L → GL d ℝ,
      (skipProdMat fun ℓ => (θ.cobMixed G G K).mixU ℓ * (θ.cobMixed G G K).mixV ℓ)
        = fun ℓ => (↑(G ℓ)⁻¹ : Matrix d d ℝ) * skipProdMat (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) ℓ := by
    intro G hG K
    rw [skips_cobMixed_gfb, skipProdMat_cobSkip_gfb _ G hG]
  constructor
  · intro h
    have h1 : mixedToResidual θ' = mixedToResidual θ := congrArg Prod.fst h
    have h2 : b'.mulSkipProd (skipProdMat fun ℓ => θ'.mixU ℓ * θ'.mixV ℓ)
        = b.mulSkipProd (skipProdMat fun ℓ => θ.mixU ℓ * θ.mixV ℓ) := congrArg Prod.snd h
    -- the weights: Theorem A.5 (ii) without biases
    obtain ⟨G, K, hG, rfl⟩ := (mixedToResidual_eq_iff θ θ' hp hp').1 h1
    refine ⟨G, K, hG, ?_⟩
    -- the biases: `b' (G⁻¹ Λ) = b Λ = (b G) (G⁻¹ Λ)`, and `G⁻¹ Λ` is invertible
    rw [key G hG K, ← mulSkipProd_cob_gfb b G] at h2
    have hu : ∀ ℓ, IsUnit ((↑(G ℓ)⁻¹ : Matrix d d ℝ)
        * skipProdMat (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) ℓ) :=
      fun ℓ => (Units.isUnit _).mul (isUnit_skipProdMat_gfb hp ℓ)
    rw [mulSkipProd_injective_gfb hu h2]
  · rintro ⟨G, K, hG, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine Prod.ext ((mixedToResidual_eq_iff θ _ hp hp').2 ⟨G, K, hG, rfl⟩) ?_
    show (b.cob G).mulSkipProd
        (skipProdMat fun ℓ => (θ.cobMixed G G K).mixU ℓ * (θ.cobMixed G G K).mixV ℓ)
      = b.mulSkipProd (skipProdMat fun ℓ => θ.mixU ℓ * θ.mixV ℓ)
    rw [key G hG K, mulSkipProd_cob_gfb]

omit [Fintype T] in
/-- **Theorem A.5 (ii) with biases, "The derivative of `Φ` is onto at every `θ`"** (with
invertible skips). -/
theorem exists_hasFDerivAt_mixedToResidualB_surjective
    (p : Params A.mixed dIn dOut × Biases A dOut) (hp : ∀ ℓ, IsUnit (p.1.mixU ℓ * p.1.mixV ℓ)) :
    ∃ Φ' : (Params A.mixed dIn dOut × Biases A dOut) →L[ℝ] ParamsB A dIn dOut,
      HasFDerivAt (mixedToResidualB (A := A) (dIn := dIn) (dOut := dOut)) Φ' p
        ∧ Function.Surjective Φ' := by
  -- the chain rule for `Φ ∘ s = id` with the right inverse `s` through `p`
  obtain ⟨s, hs, hsp, hΦs, -⟩ := exists_section_mixed_gfb p hp
  exact exists_surjective_of_section_gfb (differentiableAt_mixedToResidualB_gfb p hp) (hs _)
    hsp hΦs

omit [Fintype T] [Fintype dOut] in
/-- **Theorem A.5 (ii) with biases, the same set of functions:** without normalization, the
networks of mixed blocks with biases and invertible skips and the residual networks with biases
compute the same set of functions. -/
theorem image_evalMixedB_eq_range_residual (hA : A.χ = id) :
    (fun p : Params A.mixed dIn dOut × Biases A dOut => evalMixedB A p)
        '' {p | ∀ ℓ, IsUnit (p.1.mixU ℓ * p.1.mixV ℓ)}
      = Set.range fun q : ParamsB A dIn dOut => evalB A 1 q.1 q.2 := by
  ext F
  constructor
  · -- `F_p = F^res_{Φ(p)}`
    rintro ⟨p, hp, rfl⟩
    exact ⟨mixedToResidualB p,
      funext fun x => (evalMixedB_eq_evalB_mixedToResidualB hA p hp x).symm⟩
  · -- `F^res_q` is the network of mixed blocks with `U_ℓ = V_ℓ = I`
    rintro ⟨⟨θ, b⟩, rfl⟩
    refine ⟨(Params.mix θ 1 1, b), fun ℓ => ?_, funext fun x => ?_⟩
    · show IsUnit ((Params.mix θ 1 1).mixU ℓ * (Params.mix θ 1 1).mixV ℓ)
      rw [Params.mixU_mix, Params.mixV_mix]
      exact isUnit_one.mul isUnit_one
    · show evalB A (fun ℓ => (Params.mix θ 1 1).mixU ℓ * (Params.mix θ 1 1).mixV ℓ)
        (Params.mix θ 1 1).unmix b x = evalB A 1 θ b x
      rw [Params.mixU_mix, Params.mixV_mix, Params.unmix_mix]
      congr 1
      funext ℓ
      simp

/-- **Theorem A.5 (ii) with biases, "with the same functional dimension at `θ` and at
`Φ(θ)`":** without normalization, for any blocks, at a parameter with invertible skips the
functional dimension of the network of mixed blocks with biases is that of the residual network
with biases at `Φ(p)`. -/
theorem funDimOf_evalMixedB_eq_funDimB_residual (hA : A.χ = id)
    (p : Params A.mixed dIn dOut × Biases A dOut) (hp : ∀ ℓ, IsUnit (p.1.mixU ℓ * p.1.mixV ℓ)) :
    funDimOf (evalMixedB A) p = funDimB A 1 (mixedToResidualB p) := by
  rw [funDimB_eq_funDimOf]
  obtain ⟨Φ', hΦ', -⟩ := exists_hasFDerivAt_mixedToResidualB_surjective p hp
  obtain ⟨s, hs, hsp, hΦs, hsu⟩ := exists_section_mixed_gfb p hp
  refine funDimOf_eq_of_comp_of_section hΦ'.differentiableAt (hs _) hsp ?_ ?_
  · -- near `p` the skips are invertible, and `F_q = F^res_{Φ(q)}`
    filter_upwards [eventually_isUnit_mixed_gfb p hp] with q hq
    funext x
    exact evalMixedB_eq_evalB_mixedToResidualB hA q hq x
  · -- everywhere `F^res_y = F_{s(y)}`
    refine Filter.Eventually.of_forall fun y => funext fun x => ?_
    show evalB A 1 y.1 y.2 x = evalMixedB A (s y) x
    rw [evalMixedB_eq_evalB_mixedToResidualB hA (s y) (hsu y) x, hΦs y]

/-! ### Networks with learned skips and biases -/

/-- **The map `Φ` of equation (12) with biases, for learned skips:** at `p = ((θ, b), (A_ℓ))`. -/
noncomputable def learnedToResidualB (p : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ)) :
    ParamsB A dIn dOut :=
  (learnedToResidual (p.1.1, p.2), p.1.2.mulSkipProd (skipProdMat p.2))

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **`Φ` with biases for invertible learned skips:** `(θ.cob Λ Λ, b.cob Λ)`. -/
private theorem learnedToResidualB_coe_gfb (θ : Params A dIn dOut) (b : Biases A dOut)
    (S : Fin L → GL d ℝ) :
    learnedToResidualB ((θ, b), fun ℓ => (S ℓ : Matrix d d ℝ))
      = (θ.cob (skipProd S) (skipProd S), b.cob (skipProd S)) := by
  show (learnedToResidual (θ, fun ℓ => (S ℓ : Matrix d d ℝ)),
    b.mulSkipProd (skipProdMat fun ℓ => (S ℓ : Matrix d d ℝ))) = _
  rw [learnedToResidual_coe, skipProdMat_coe_gfb, mulSkipProd_coe_gfb]

omit [Fintype T] [DecidableEq d] in
/-- The skip `A_ℓ` of `((θ, b), A)` is a differentiable (linear) function of it. -/
private theorem differentiable_skip_gfb (ℓ : Fin L) :
    Differentiable ℝ (fun p : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ) => p.2 ℓ) :=
  differentiable_linear_gfb
    { toFun := fun p : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ) => p.2 ℓ,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Fintype T] in
/-- Near weights, biases and invertible skips, the skips stay invertible. -/
private theorem eventually_isUnit_learned_gfb (p : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ))
    (hp : ∀ ℓ, IsUnit (p.2 ℓ)) : ∀ᶠ q in nhds p, ∀ ℓ, IsUnit (q.2 ℓ) := by
  rw [Filter.eventually_all]
  intro ℓ
  -- the determinant of `A_ℓ` is continuous and nonzero at `p`
  have hc : Continuous fun q : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ) => (q.2 ℓ).det :=
    (differentiable_skip_gfb ℓ).continuous.matrix_det
  have hne : (p.2 ℓ).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (hp ℓ)).ne_zero
  filter_upwards [hc.continuousAt.eventually_ne hne] with q h
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit h)

omit [Fintype T] in
/-- `Φ` with biases for learned skips is differentiable at invertible skips. -/
private theorem differentiableAt_learnedToResidualB_gfb
    (p : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ)) (hp : ∀ ℓ, IsUnit (p.2 ℓ)) :
    DifferentiableAt ℝ (learnedToResidualB (A := A) (dIn := dIn) (dOut := dOut)) p := by
  -- the weights: `Φ` of `Residual/GaugeFixLearned.lean` at `(θ, A)`
  obtain ⟨Φ', hΦ', -⟩ := exists_hasFDerivAt_learnedToResidual_surjective (p.1.1, p.2) hp
  have hm : DifferentiableAt ℝ
      (fun q : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ) => (q.1.1, q.2)) p :=
    differentiableAt_fst.fst.prodMk differentiableAt_snd
  have h1 : DifferentiableAt ℝ
      (fun q : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ) =>
        learnedToResidual (q.1.1, q.2)) p := by
    have hc := hΦ'.differentiableAt.comp p hm
    exact hc
  -- the biases: `b_E Λ_0`, `b_read`, `b_write Λ_ℓ`, `b_D`
  have h2 : DifferentiableAt ℝ (fun q : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ) =>
      q.1.2.mulSkipProd (skipProdMat q.2)) p :=
    differentiableAt_mulSkipProd_gfb differentiableAt_fst.snd
      (fun ℓ => differentiableAt_skipProdMat_gfb (fun k => differentiable_skip_gfb k p) ℓ)
  exact h1.prodMk h2

omit [Fintype T] in
/-- **A differentiable right inverse of `Φ` with biases through `p = ((θ, b), A)`:**
`s(θ', b') = ((θ'.cob Λ⁻¹ Λ⁻¹, b'.cob Λ⁻¹), A)` with the skips `A` of `p`. -/
private theorem exists_section_learned_gfb (p : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ))
    (hp : ∀ ℓ, IsUnit (p.2 ℓ)) :
    ∃ s : ParamsB A dIn dOut → ParamsB A dIn dOut × (Fin L → Matrix d d ℝ),
      Differentiable ℝ s ∧ s (learnedToResidualB p) = p ∧ (∀ y, learnedToResidualB (s y) = y) ∧
      ∀ y ℓ, IsUnit ((s y).2 ℓ) := by
  obtain ⟨⟨θ, b⟩, M⟩ := p
  obtain ⟨S, rfl⟩ := exists_coe_gfb hp
  refine ⟨fun y => ((y.1.cob (fun ℓ => (skipProd S ℓ)⁻¹) (fun ℓ => (skipProd S ℓ)⁻¹),
      y.2.cob (fun ℓ => (skipProd S ℓ)⁻¹)), fun ℓ => (S ℓ : Matrix d d ℝ)), ?_, ?_, ?_,
      fun y ℓ => Units.isUnit (S ℓ)⟩
  · -- an affine map
    intro y
    have h1 := (differentiable_cob_gfb (A := A) (dIn := dIn) (dOut := dOut)
      (fun ℓ => (skipProd S ℓ)⁻¹) (fun ℓ => (skipProd S ℓ)⁻¹) y.1).comp y differentiableAt_fst
    have h2 : DifferentiableAt ℝ (fun y : ParamsB A dIn dOut =>
        y.2.mulSkipProd (fun ℓ => (((skipProd S ℓ)⁻¹ : GL d ℝ) : Matrix d d ℝ))) y :=
      differentiableAt_mulSkipProd_gfb differentiableAt_snd (fun ℓ => differentiableAt_const _)
    exact (h1.prodMk h2).prodMk (differentiableAt_const _)
  · -- `s(Φ p) = (((θ.cob Λ Λ).cob Λ⁻¹ Λ⁻¹, (b.cob Λ).cob Λ⁻¹), A) = p`
    rw [learnedToResidualB_coe_gfb]
    dsimp only
    rw [cob_cob, cob_cob_biases_gfb]
    simp only [mul_inv_cancel]
    rw [cob_one_gfb, cob_one_biases_gfb]
  · -- `Φ(s y) = ((y.1.cob Λ⁻¹ Λ⁻¹).cob Λ Λ, (y.2.cob Λ⁻¹).cob Λ) = y`
    rintro ⟨φ, c⟩
    dsimp only
    rw [learnedToResidualB_coe_gfb, cob_cob, cob_cob_biases_gfb]
    simp only [inv_mul_cancel]
    rw [cob_one_gfb, cob_one_biases_gfb]

omit [Fintype T] [Fintype dOut] in
/-- **Theorem A.5 (i) with biases for learned skips, `F_θ = F^res_{Φ(θ)}`:** without
normalization, a network with biases and invertible learned skips computes the function of the
residual network with biases at `Φ(p)`. -/
theorem evalB_eq_evalB_learnedToResidualB (hA : A.χ = id)
    (p : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ)) (hp : ∀ ℓ, IsUnit (p.2 ℓ))
    (x : Matrix T dIn ℝ) :
    evalB A p.2 p.1.1 p.1.2 x
      = evalB A 1 (learnedToResidualB p).1 (learnedToResidualB p).2 x := by
  -- write the skips as elements of `GL d ℝ`; then this is Theorem 3.2 (i) with biases
  obtain ⟨⟨θ, b⟩, M⟩ := p
  obtain ⟨S, rfl⟩ := exists_coe_gfb hp
  rw [learnedToResidualB_coe_gfb]
  exact evalB_learned_gfb hA θ b S x

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Theorem A.5 (ii) with biases for learned skips:** every parameter of the residual network
with biases is `Φ` of the same weights and biases with the skips `A_ℓ = I`. -/
theorem learnedToResidualB_one (q : ParamsB A dIn dOut) :
    learnedToResidualB (q, (1 : Fin L → Matrix d d ℝ)) = q := by
  obtain ⟨θ, b⟩ := q
  refine Prod.ext (learnedToResidual_one θ) ?_
  -- every `Λ_ℓ` is `I`
  show b.mulSkipProd (skipProdMat (1 : Fin L → Matrix d d ℝ)) = b
  rw [skipProdMat_one_gfb, mulSkipProd_one_gfb]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Theorem A.5 (ii) with biases for learned skips, "`Φ(θ̃) = Φ(θ)` exactly when
`θ̃ = T_G(θ)` for some `G` with `G_L = I`"**, for invertible skips. -/
theorem learnedToResidualB_eq_iff (p p' : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ))
    (hp : ∀ ℓ, IsUnit (p.2 ℓ)) (hp' : ∀ ℓ, IsUnit (p'.2 ℓ)) :
    learnedToResidualB p' = learnedToResidualB p
      ↔ ∃ G : Fin (L + 1) → GL d ℝ,
          G (Fin.last L) = 1 ∧ p' = ((p.1.1.cob G G, p.1.2.cob G), cobSkip p.2 G) := by
  obtain ⟨⟨θ, b⟩, M⟩ := p
  obtain ⟨⟨θ', b'⟩, M'⟩ := p'
  constructor
  · intro h
    have h1 : learnedToResidual (θ', M') = learnedToResidual (θ, M) := congrArg Prod.fst h
    have h2 : b'.mulSkipProd (skipProdMat M') = b.mulSkipProd (skipProdMat M) :=
      congrArg Prod.snd h
    -- the weights and the skips: Theorem A.5 (ii) for learned skips without biases
    obtain ⟨G, hG, h3⟩ := (learnedToResidual_eq_iff (θ, M) (θ', M') hp hp').1 h1
    simp only [Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    refine ⟨G, hG, ?_⟩
    -- the biases: `b' (G⁻¹ Λ) = b Λ = (b G) (G⁻¹ Λ)`, and `G⁻¹ Λ` is invertible
    rw [skipProdMat_cobSkip_gfb M G hG, ← mulSkipProd_cob_gfb b G] at h2
    have hu : ∀ ℓ, IsUnit ((↑(G ℓ)⁻¹ : Matrix d d ℝ) * skipProdMat M ℓ) :=
      fun ℓ => (Units.isUnit _).mul (isUnit_skipProdMat_gfb hp ℓ)
    rw [mulSkipProd_injective_gfb hu h2]
  · rintro ⟨G, hG, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine Prod.ext ((learnedToResidual_eq_iff (θ, M) (θ.cob G G, cobSkip M G) hp hp').2
      ⟨G, hG, rfl⟩) ?_
    show (b.cob G).mulSkipProd (skipProdMat (cobSkip M G)) = b.mulSkipProd (skipProdMat M)
    rw [skipProdMat_cobSkip_gfb M G hG, mulSkipProd_cob_gfb]

omit [Fintype T] in
/-- **Theorem A.5 (ii) with biases for learned skips, the derivative of `Φ` is onto** (with
invertible skips). -/
theorem exists_hasFDerivAt_learnedToResidualB_surjective
    (p : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ)) (hp : ∀ ℓ, IsUnit (p.2 ℓ)) :
    ∃ Φ' : (ParamsB A dIn dOut × (Fin L → Matrix d d ℝ)) →L[ℝ] ParamsB A dIn dOut,
      HasFDerivAt (learnedToResidualB (A := A) (dIn := dIn) (dOut := dOut)) Φ' p
        ∧ Function.Surjective Φ' := by
  -- the chain rule for `Φ ∘ s = id` with the right inverse `s` through `p`
  obtain ⟨s, hs, hsp, hΦs, -⟩ := exists_section_learned_gfb p hp
  exact exists_surjective_of_section_gfb (differentiableAt_learnedToResidualB_gfb p hp) (hs _)
    hsp hΦs

omit [Fintype T] [Fintype dOut] in
/-- **Theorem A.5 (ii) with biases for learned skips, the same set of functions**, without
normalization. -/
theorem image_evalB_learned_eq_range_residual (hA : A.χ = id) :
    (fun p : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ) => evalB A p.2 p.1.1 p.1.2)
        '' {p | ∀ ℓ, IsUnit (p.2 ℓ)}
      = Set.range fun q : ParamsB A dIn dOut => evalB A 1 q.1 q.2 := by
  ext F
  constructor
  · -- `F_p = F^res_{Φ(p)}`
    rintro ⟨p, hp, rfl⟩
    exact ⟨learnedToResidualB p,
      funext fun x => (evalB_eq_evalB_learnedToResidualB hA p hp x).symm⟩
  · -- `F^res_q` is the network with the skips `A_ℓ = I`
    rintro ⟨q, rfl⟩
    exact ⟨(q, 1), fun ℓ => isUnit_one, rfl⟩

/-- **Theorem A.5 (ii) with biases for learned skips, the same functional dimension:** without
normalization, for any blocks, at weights, biases and invertible skips `p`, the functional
dimension of the network with learned skips and biases (in the weights, the biases and the
skips) is that of the residual network with biases at `Φ(p)`. -/
theorem funDimOf_evalB_learned_eq_funDimB_residual (hA : A.χ = id)
    (p : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ)) (hp : ∀ ℓ, IsUnit (p.2 ℓ)) :
    funDimOf (fun q : ParamsB A dIn dOut × (Fin L → Matrix d d ℝ) => evalB A q.2 q.1.1 q.1.2) p
      = funDimB A 1 (learnedToResidualB p) := by
  rw [funDimB_eq_funDimOf]
  obtain ⟨Φ', hΦ', -⟩ := exists_hasFDerivAt_learnedToResidualB_surjective p hp
  obtain ⟨s, hs, hsp, hΦs, hsu⟩ := exists_section_learned_gfb p hp
  refine funDimOf_eq_of_comp_of_section hΦ'.differentiableAt (hs _) hsp ?_ ?_
  · -- near `p` the skips are invertible, and `F_q = F^res_{Φ(q)}`
    filter_upwards [eventually_isUnit_learned_gfb p hp] with q hq
    funext x
    exact evalB_eq_evalB_learnedToResidualB hA q hq x
  · -- everywhere `F^res_y = F_{s(y)}`
    refine Filter.Eventually.of_forall fun y => funext fun x => ?_
    show evalB A 1 y.1 y.2 x = evalB A (s y).2 (s y).1.1 (s y).1.2 x
    rw [evalB_eq_evalB_learnedToResidualB hA (s y) (hsu y) x, hΦs y]

end Skips
