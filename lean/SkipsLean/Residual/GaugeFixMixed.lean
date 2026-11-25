import SkipsLean.Symmetry.MixedJunctions
import SkipsLean.Dimension.Functional

/-!
# The gauge fix for networks of mixed blocks: what it identifies

Paper (skips paper), Appendix A.2, equation (12): "When every skip `A_ℓ = U_ℓ V_ℓ` is invertible,
let `Λ_ℓ = A_{ℓ+1} ⋯ A_L`, with `Λ_L = I`, and let
`Φ(θ) = (E Λ_0, (Λ_{ℓ−1}^{-1} W_read^ℓ, W_write^ℓ Λ_ℓ)_{ℓ=1}^L, D)`, a parameter of the residual
network". Theorem A.5: "Consider networks without normalization in (i) and (ii), and parameters
`θ` whose skips `A_ℓ` are invertible. […] (ii) What the gauge fix identifies. Every parameter of
the residual network is `Φ(θ)` for some `θ`, and `Φ(θ̃) = Φ(θ)` exactly when `θ̃ = T_{G,K}(θ)`
for some `G` and `K` with `G_L = I`. The derivative of `Φ` is onto at every `θ`. So the networks
of mixed blocks with invertible skips and the residual networks compute the same set of
functions, with the same functional dimension at `θ` and at `Φ(θ)`. The same holds for learned
skips, without the `K_ℓ`, and for networks with biases."

Here, for the networks of mixed blocks of `Network/Mixed.lean`, any blocks:

* `skipProdMat S`: the products `Λ_ℓ` of any matrices `S_ℓ` (for invertible ones it is
  `skipProd` of `Residual/LearnedSkips.lean`); `mixedToResidual θ`: the map `Φ` of (12) on all
  parameters of the network of mixed blocks, with the matrix inverse of `Λ_{ℓ−1}` (which is the
  inverse when the skips are invertible, the only case in which the statements use it).
* `mixedToResidual_mix`: for invertible `U_ℓ`, `V_ℓ` it is `θ.cob Λ Λ`, the `Φ(θ)` of
  `Symmetry/MixedJunctions.lean`; `mixedToResidual_mix_one`: "Every parameter of the residual
  network is `Φ(θ)` for some `θ`" (the `θ` with the same entries and `U_ℓ = V_ℓ = I`).
* `mixedToResidual_eq_iff`: `Φ(θ̃) = Φ(θ)` exactly when `θ̃ = T_{G,K}(θ)` with `G_L = I`, for
  parameters with invertible skips.
* `exists_hasFDerivAt_mixedToResidual_surjective`: "The derivative of `Φ` is onto at every `θ`".
* `evalMixed_eq_eval_mixedToResidual`, `image_evalMixed_eq_range_residual`: without
  normalization, `F_θ = F^res_{Φ(θ)}`, and the two families "compute the same set of functions".
* `funDim_mixed_eq_funDim_residual`: "with the same functional dimension at `θ` and at `Φ(θ)`",
  the functional dimension of the network of mixed blocks being that of the skipless network of
  the architecture `A.mixed` in the parameters `E`, `[U | W_read]`, `[V ; W_write]`, `D`. No
  differentiability of the blocks is asked: `F^res = F ∘ s` for the affine map
  `s(θ') = T_{G,K}^{-1}(θ', I, I)` through `θ`, so the two batches of outputs are differentiable
  at `θ` and at `Φ(θ)` together.

Not stated here: the same for learned skips "without the `K_ℓ`", and for networks with biases.
Numeric check: `mixed_blocks_check_2026-11-25.py`, parts (3) and (4).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T : Type*} {d : Type} {dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d]
  [DecidableEq d] [Fintype dIn] [Fintype dOut]
variable {A : Arch T d L}

/-- The products `Λ_ℓ = S_{ℓ+1} ⋯ S_L` of matrices `S_1, …, S_L`, with `Λ_L = I` (equation (7)
for matrices that need not be invertible). -/
def skipProdMat (S : Fin L → Matrix d d ℝ) : Fin (L + 1) → Matrix d d ℝ :=
  Fin.reverseInduction (motive := fun _ => Matrix d d ℝ) 1 (fun ℓ Λ => S ℓ * Λ)

/-- **The map `Φ` of equation (12)** on the parameters of a network of mixed blocks: the
embedding `E Λ_0`, the reads `Λ_{ℓ−1}^{-1} W_read^ℓ`, the writes `W_write^ℓ Λ_ℓ` and the readout
`D`, for `Λ_ℓ = A_{ℓ+1} ⋯ A_L` and `A_ℓ = U_ℓ V_ℓ`. -/
noncomputable def mixedToResidual (θ : Params A.mixed dIn dOut) : Params A dIn dOut where
  E := θ.E * skipProdMat (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) 0
  read ℓ := (skipProdMat (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) ℓ.castSucc)⁻¹ * θ.unmix.read ℓ
  write ℓ := θ.unmix.write ℓ * skipProdMat (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) ℓ.succ
  D := θ.D

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- `Λ_L = I`. -/
private theorem skipProdMat_last_gfm (S : Fin L → Matrix d d ℝ) :
    skipProdMat S (Fin.last L) = 1 := by
  simp [skipProdMat]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- `Λ_{ℓ-1} = S_ℓ Λ_ℓ`. -/
private theorem skipProdMat_castSucc_gfm (S : Fin L → Matrix d d ℝ) (ℓ : Fin L) :
    skipProdMat S ℓ.castSucc = S ℓ * skipProdMat S ℓ.succ := by
  simp [skipProdMat]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- For invertible matrices, `skipProdMat` is `skipProd`. -/
theorem skipProdMat_coe (S : Fin L → GL d ℝ) (ℓ : Fin (L + 1)) :
    skipProdMat (fun ℓ => (S ℓ : Matrix d d ℝ)) ℓ = (skipProd S ℓ : Matrix d d ℝ) := by
  induction ℓ using Fin.reverseInduction with
  | last => rw [skipProdMat_last_gfm, skipProd_last, Units.val_one]
  | cast i ih => rw [skipProdMat_castSucc_gfm, skipProd_castSucc, Units.val_mul, ih]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The change of basis by `G = K = 1` is the identity. -/
private theorem cob_one_gfm (φ : Params A dIn dOut) : φ.cob (fun _ => 1) (fun _ => 1) = φ := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_ <;>
    simp [Params.cob]

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- Two changes of basis are one change of basis (the products, hidden state by hidden state). -/
private theorem cob_cob_gfm (φ : Params A dIn dOut) (G K G' K' : Fin (L + 1) → GL d ℝ) :
    (φ.cob G K).cob G' K' = φ.cob (fun ℓ => G ℓ * G' ℓ) (fun ℓ => K ℓ * K' ℓ) := by
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · simp [Params.cob, Matrix.mul_assoc]
  · simp [Params.cob, Matrix.mul_assoc, _root_.mul_inv_rev]
  · simp [Params.cob, Matrix.mul_assoc]
  · simp [Params.cob, Matrix.mul_assoc, _root_.mul_inv_rev]

omit [Fintype T] [Fintype dOut] [Fintype dIn] in
/-- `mixedToResidual_mix` without the instances that its statement does not use. -/
private theorem mixedToResidual_mix_gfm (θ : Params A dIn dOut) (U V : Fin L → GL d ℝ) :
    mixedToResidual
        (Params.mix θ (fun ℓ => (U ℓ : Matrix d d ℝ)) (fun ℓ => (V ℓ : Matrix d d ℝ)))
      = θ.cob (skipProd fun ℓ => U ℓ * V ℓ) (skipProd fun ℓ => U ℓ * V ℓ) := by
  -- the products of the skips `U_ℓ V_ℓ` are the `Λ_ℓ` of `skipProd`
  have hΛ : ∀ ℓ, skipProdMat (fun ℓ =>
      (Params.mix θ (fun ℓ => (U ℓ : Matrix d d ℝ)) (fun ℓ => (V ℓ : Matrix d d ℝ))).mixU ℓ *
      (Params.mix θ (fun ℓ => (U ℓ : Matrix d d ℝ)) (fun ℓ => (V ℓ : Matrix d d ℝ))).mixV ℓ) ℓ
      = (skipProd (fun ℓ => U ℓ * V ℓ) ℓ : Matrix d d ℝ) := by
    intro ℓ
    rw [Params.mixU_mix, Params.mixV_mix, ← skipProdMat_coe]
    simp only [Units.val_mul]
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · simp only [mixedToResidual, Params.cob, hΛ]
    rfl
  · simp only [mixedToResidual, Params.cob, hΛ, Matrix.coe_units_inv, Params.unmix_mix]
  · simp only [mixedToResidual, Params.cob, hΛ, Params.unmix_mix]
  · -- the readout: `Λ_L = I`
    simp only [mixedToResidual, Params.cob, skipProd_last, inv_one, Units.val_one,
      Matrix.one_mul]
    rfl

omit [Fintype T] [Fintype dOut] [Fintype dIn] in
/-- **Equation (12):** for invertible `U_ℓ` and `V_ℓ`, `Φ` of the network of mixed blocks with
the hidden units of `θ` is `θ.cob Λ Λ`. -/
theorem mixedToResidual_mix (θ : Params A dIn dOut) (U V : Fin L → GL d ℝ) :
    mixedToResidual
        (Params.mix θ (fun ℓ => (U ℓ : Matrix d d ℝ)) (fun ℓ => (V ℓ : Matrix d d ℝ)))
      = θ.cob (skipProd fun ℓ => U ℓ * V ℓ) (skipProd fun ℓ => U ℓ * V ℓ) := by
  -- the same statement without the instances that it does not use
  exact mixedToResidual_mix_gfm θ U V

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- **Theorem A.5 (ii), "Every parameter of the residual network is `Φ(θ)` for some `θ`":** the
`θ` with the same entries and `U_ℓ = V_ℓ = I`. -/
theorem mixedToResidual_mix_one (θ : Params A dIn dOut) :
    mixedToResidual (Params.mix θ 1 1) = θ := by
  -- every `Λ_ℓ` is `I`
  have hΛ : ∀ ℓ, skipProdMat (fun ℓ => (Params.mix θ 1 1).mixU ℓ * (Params.mix θ 1 1).mixV ℓ) ℓ
      = 1 := by
    intro ℓ
    rw [Params.mixU_mix, Params.mixV_mix]
    induction ℓ using Fin.reverseInduction with
    | last => rw [skipProdMat_last_gfm]
    | cast i ih => rw [skipProdMat_castSucc_gfm, ih, Pi.one_apply, Matrix.mul_one, Matrix.mul_one]
  refine Params.ext' ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · simp only [mixedToResidual, hΛ, Matrix.mul_one]
    rfl
  · simp only [mixedToResidual, hΛ, inv_one, Matrix.one_mul, Params.unmix_mix]
  · simp only [mixedToResidual, hΛ, Matrix.mul_one, Params.unmix_mix]
  · rfl

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- A product `M N` of square matrices is a unit exactly when both are: here, one direction. -/
private theorem isUnit_of_isUnit_mul_gfm {M N : Matrix d d ℝ} (h : IsUnit (M * N)) :
    IsUnit M ∧ IsUnit N := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at h
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left h),
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right h)⟩

omit [Fintype T] [Fintype dOut] [Fintype dIn] in
/-- A parameter with invertible skips `U_ℓ V_ℓ` is `Params.mix` of its hidden units and of
invertible `U_ℓ`, `V_ℓ`. -/
private theorem exists_mix_gfm (θ : Params A.mixed dIn dOut)
    (hθ : ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)) :
    ∃ (φ : Params A dIn dOut) (U V : Fin L → GL d ℝ),
      θ = Params.mix φ (fun ℓ => (U ℓ : Matrix d d ℝ)) (fun ℓ => (V ℓ : Matrix d d ℝ)) := by
  have hU : ∀ ℓ, IsUnit (θ.mixU ℓ) := fun ℓ => (isUnit_of_isUnit_mul_gfm (hθ ℓ)).1
  have hV : ∀ ℓ, IsUnit (θ.mixV ℓ) := fun ℓ => (isUnit_of_isUnit_mul_gfm (hθ ℓ)).2
  refine ⟨θ.unmix, fun ℓ => (hU ℓ).unit, fun ℓ => (hV ℓ).unit, ?_⟩
  simp only [IsUnit.unit_spec]
  exact (Params.mix_unmix θ).symm

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- After `T_{G,K}` with `G_L = I`, the products of the skips are `G_ℓ⁻¹ Λ_ℓ`. -/
private theorem skipProd_cob_gfm (U V : Fin L → GL d ℝ) (G : Fin (L + 1) → GL d ℝ)
    (hG : G (Fin.last L) = 1) (K : Fin L → GL d ℝ) (ℓ : Fin (L + 1)) :
    skipProd (fun ℓ => (G ℓ.castSucc)⁻¹ * U ℓ * K ℓ * ((K ℓ)⁻¹ * V ℓ * G ℓ.succ)) ℓ
      = (G ℓ)⁻¹ * skipProd (fun ℓ => U ℓ * V ℓ) ℓ := by
  induction ℓ using Fin.reverseInduction with
  | last => simp [hG]
  | cast i ih =>
    -- `Λ'_{i-1} = (G_{i-1}⁻¹ U K)(K⁻¹ V G_i) G_i⁻¹ Λ_i = G_{i-1}⁻¹ U V Λ_i = G_{i-1}⁻¹ Λ_{i-1}`
    rw [skipProd_castSucc, skipProd_castSucc, ih]
    group

omit [Fintype T] [Fintype dOut] [Fintype dIn] in
/-- **The "if" direction of Theorem A.5 (ii):** `Φ(T_{G,K}(θ)) = Φ(θ)` when `G_L = I`. -/
private theorem mixedToResidual_cobMixed_gfm (φ : Params A dIn dOut) (U V : Fin L → GL d ℝ)
    (G : Fin (L + 1) → GL d ℝ) (hG : G (Fin.last L) = 1) (K : Fin L → GL d ℝ) :
    mixedToResidual ((Params.mix φ (fun ℓ => (U ℓ : Matrix d d ℝ))
        (fun ℓ => (V ℓ : Matrix d d ℝ))).cobMixed G G K)
      = mixedToResidual (Params.mix φ (fun ℓ => (U ℓ : Matrix d d ℝ))
        (fun ℓ => (V ℓ : Matrix d d ℝ))) := by
  -- `T_{G,K}(θ)` has the hidden units `φ.cob G G` and the invertible identity units
  -- `G_{ℓ-1}⁻¹ U_ℓ K_ℓ`, `K_ℓ⁻¹ V_ℓ G_ℓ`
  have h1 : (Params.mix φ (fun ℓ => (U ℓ : Matrix d d ℝ))
      (fun ℓ => (V ℓ : Matrix d d ℝ))).cobMixed G G K
      = Params.mix (φ.cob G G) (fun ℓ => (((G ℓ.castSucc)⁻¹ * U ℓ * K ℓ : GL d ℝ) : Matrix d d ℝ))
        (fun ℓ => (((K ℓ)⁻¹ * V ℓ * G ℓ.succ : GL d ℝ) : Matrix d d ℝ)) := by
    unfold Params.cobMixed
    rw [Params.unmix_mix, Params.mixU_mix, Params.mixV_mix]
    simp only [Units.val_mul]
  -- its `Λ'_ℓ` are `G_ℓ⁻¹ Λ_ℓ`, so `Φ = (φ.cob G G).cob Λ' Λ' = φ.cob (G Λ') (G Λ') = φ.cob Λ Λ`
  rw [h1, mixedToResidual_mix_gfm, mixedToResidual_mix_gfm, cob_cob_gfm]
  have h2 : (fun ℓ => G ℓ * skipProd (fun ℓ => (G ℓ.castSucc)⁻¹ * U ℓ * K ℓ
      * ((K ℓ)⁻¹ * V ℓ * G ℓ.succ)) ℓ) = skipProd (fun ℓ => U ℓ * V ℓ) := by
    funext ℓ
    rw [skipProd_cob_gfm U V G hG K ℓ, mul_inv_cancel_left]
  rw [h2]

omit [Fintype T] [Fintype dOut] [Fintype dIn] in
/-- **Theorem A.5 (ii), "`Φ(θ̃) = Φ(θ)` exactly when `θ̃ = T_{G,K}(θ)` for some `G` and `K` with
`G_L = I`"**, for parameters of the network of mixed blocks whose skips `A_ℓ = U_ℓ V_ℓ` are
invertible. -/
theorem mixedToResidual_eq_iff (θ θ' : Params A.mixed dIn dOut)
    (hθ : ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)) (hθ' : ∀ ℓ, IsUnit (θ'.mixU ℓ * θ'.mixV ℓ)) :
    mixedToResidual θ' = mixedToResidual θ
      ↔ ∃ (G : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ),
          G (Fin.last L) = 1 ∧ θ' = θ.cobMixed G G K := by
  -- write `θ` and `θ'` with invertible `U_ℓ`, `V_ℓ`
  obtain ⟨φ, U, V, rfl⟩ := exists_mix_gfm θ hθ
  obtain ⟨φ', U', V', rfl⟩ := exists_mix_gfm θ' hθ'
  constructor
  · intro h
    rw [mixedToResidual_mix_gfm, mixedToResidual_mix_gfm] at h
    -- the products `Λ_ℓ` and `Λ'_ℓ`, with `Λ_{ℓ-1} = U_ℓ V_ℓ Λ_ℓ` and `Λ_L = I`
    obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = skipProd fun ℓ => U ℓ * V ℓ := ⟨_, rfl⟩
    obtain ⟨Λ', hΛ'⟩ : ∃ Λ', Λ' = skipProd fun ℓ => U' ℓ * V' ℓ := ⟨_, rfl⟩
    have hc : ∀ ℓ : Fin L, Λ ℓ.castSucc = U ℓ * V ℓ * Λ ℓ.succ := fun ℓ => by
      rw [hΛ, skipProd_castSucc]
    have hc' : ∀ ℓ : Fin L, Λ' ℓ.castSucc = U' ℓ * V' ℓ * Λ' ℓ.succ := fun ℓ => by
      rw [hΛ', skipProd_castSucc]
    have hl : Λ (Fin.last L) = 1 := by rw [hΛ, skipProd_last]
    have hl' : Λ' (Fin.last L) = 1 := by rw [hΛ', skipProd_last]
    rw [← hΛ, ← hΛ'] at h
    -- `G_ℓ = Λ_ℓ Λ'_ℓ⁻¹` and `K_ℓ = U_ℓ⁻¹ G_{ℓ-1} U'_ℓ`
    refine ⟨fun ℓ => Λ ℓ * (Λ' ℓ)⁻¹, fun ℓ => (U ℓ)⁻¹ * (Λ ℓ.castSucc * (Λ' ℓ.castSucc)⁻¹) * U' ℓ,
      by simp only [hl, hl', inv_one, mul_one], ?_⟩
    -- the hidden units: `φ' = (φ'.cob Λ' Λ').cob Λ'⁻¹ Λ'⁻¹ = (φ.cob Λ Λ).cob Λ'⁻¹ Λ'⁻¹`
    have hφ : φ' = φ.cob (fun ℓ => Λ ℓ * (Λ' ℓ)⁻¹) (fun ℓ => Λ ℓ * (Λ' ℓ)⁻¹) := by
      calc φ' = (φ'.cob Λ' Λ').cob (fun ℓ => (Λ' ℓ)⁻¹) (fun ℓ => (Λ' ℓ)⁻¹) := by
            rw [cob_cob_gfm]
            simp only [mul_inv_cancel]
            exact (cob_one_gfm φ').symm
        _ = _ := by rw [h, cob_cob_gfm]
    unfold Params.cobMixed
    rw [Params.unmix_mix, Params.mixU_mix, Params.mixV_mix, ← hφ]
    congr 1
    · -- `G_{ℓ-1}⁻¹ U_ℓ K_ℓ = U'_ℓ`
      funext ℓ
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    · -- `K_ℓ⁻¹ V_ℓ G_ℓ = U'_ℓ⁻¹ Λ'_{ℓ-1} Λ_{ℓ-1}⁻¹ U_ℓ V_ℓ Λ_ℓ Λ'_ℓ⁻¹ = V'_ℓ`
      funext ℓ
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      dsimp only
      rw [hc ℓ, hc' ℓ]
      group
  · rintro ⟨G, K, hG, h⟩
    rw [h]
    exact mixedToResidual_cobMixed_gfm φ U V G hG K

omit [Fintype T] [DecidableEq d] in
/-- A map into the parameters is differentiable if its four components are. -/
private theorem differentiableAt_params_gfm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

omit [Fintype T] [DecidableEq d] in
/-- A linear map on the parameters is differentiable. -/
private theorem differentiable_linear_gfm {B : Arch T d L} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (l : Params B dIn dOut →ₗ[ℝ] F) : Differentiable ℝ l := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).differentiable

omit [Fintype T] [DecidableEq d] in
private theorem differentiable_E_gfm {B : Arch T d L} :
    Differentiable ℝ (fun θ : Params B dIn dOut => θ.E) :=
  differentiable_linear_gfm
    { toFun := fun θ => θ.E, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] in
private theorem differentiable_read_gfm {B : Arch T d L} (ℓ : Fin L) :
    Differentiable ℝ (fun θ : Params B dIn dOut => θ.read ℓ) :=
  differentiable_linear_gfm
    { toFun := fun θ => θ.read ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] in
private theorem differentiable_write_gfm {B : Arch T d L} (ℓ : Fin L) :
    Differentiable ℝ (fun θ : Params B dIn dOut => θ.write ℓ) :=
  differentiable_linear_gfm
    { toFun := fun θ => θ.write ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] in
private theorem differentiable_D_gfm {B : Arch T d L} :
    Differentiable ℝ (fun θ : Params B dIn dOut => θ.D) :=
  differentiable_linear_gfm
    { toFun := fun θ => θ.D, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] in
private theorem differentiable_mixU_gfm (ℓ : Fin L) :
    Differentiable ℝ (fun θ : Params A.mixed dIn dOut => θ.mixU ℓ) :=
  differentiable_linear_gfm
    { toFun := fun θ => θ.mixU ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] in
private theorem differentiable_mixV_gfm (ℓ : Fin L) :
    Differentiable ℝ (fun θ : Params A.mixed dIn dOut => θ.mixV ℓ) :=
  differentiable_linear_gfm
    { toFun := fun θ => θ.mixV ℓ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] in
private theorem differentiable_unmixRead_gfm (ℓ : Fin L) :
    Differentiable ℝ (fun θ : Params A.mixed dIn dOut => θ.unmix.read ℓ) :=
  differentiable_linear_gfm
    { toFun := fun θ => θ.unmix.read ℓ, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] in
private theorem differentiable_unmixWrite_gfm (ℓ : Fin L) :
    Differentiable ℝ (fun θ : Params A.mixed dIn dOut => θ.unmix.write ℓ) :=
  differentiable_linear_gfm
    { toFun := fun θ => θ.unmix.write ℓ, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The product of two differentiable matrix-valued maps is differentiable. -/
private theorem differentiableAt_matMul_gfm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

omit [Fintype T] in
/-- Every `Λ_ℓ` is a differentiable (polynomial) function of the parameters. -/
private theorem differentiable_skipProdMat_gfm (ℓ : Fin (L + 1)) :
    Differentiable ℝ (fun θ : Params A.mixed dIn dOut =>
      skipProdMat (fun ℓ => θ.mixU ℓ * θ.mixV ℓ) ℓ) := by
  induction ℓ using Fin.reverseInduction with
  | last =>
    simp only [skipProdMat_last_gfm]
    exact differentiable_const _
  | cast i ih =>
    -- `Λ_{i-1} = U_i V_i Λ_i`
    simp only [skipProdMat_castSucc_gfm]
    intro θ
    exact differentiableAt_matMul_gfm
      (differentiableAt_matMul_gfm (differentiable_mixU_gfm i θ) (differentiable_mixV_gfm i θ))
      (ih θ)

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- A product of invertible matrices is invertible. -/
private theorem isUnit_skipProdMat_gfm {S : Fin L → Matrix d d ℝ} (hS : ∀ ℓ, IsUnit (S ℓ))
    (ℓ : Fin (L + 1)) : IsUnit (skipProdMat S ℓ) := by
  induction ℓ using Fin.reverseInduction with
  | last =>
    rw [skipProdMat_last_gfm]
    exact isUnit_one
  | cast i ih =>
    rw [skipProdMat_castSucc_gfm]
    exact (hS i).mul ih

/-- In a complete normed algebra, the inverse is differentiable at a unit. -/
private theorem differentiableAt_ringInverse_gfm {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [CompleteSpace R] {x : R} (hx : IsUnit x) :
    DifferentiableAt ℝ (fun y : R => Ring.inverse y) x :=
  differentiableAt_inverse hx

omit [Fintype T] [Fintype dIn] [Fintype dOut] in
/-- The matrix inverse is differentiable at an invertible matrix (through the operator norm, for
which the matrices form a complete normed algebra with the same topology). -/
private theorem differentiableAt_inv_gfm {X : Matrix d d ℝ} (hX : IsUnit X) :
    DifferentiableAt ℝ (fun Y : Matrix d d ℝ => Y⁻¹) X := by
  have hinv : (fun Y : Matrix d d ℝ => Y⁻¹) = fun Y => Ring.inverse Y :=
    funext fun Y => Matrix.nonsing_inv_eq_ringInverse Y
  rw [hinv]
  let iR : NormedRing (Matrix d d ℝ) := Matrix.linftyOpNormedRing
  let iA : NormedAlgebra ℝ (Matrix d d ℝ) := Matrix.linftyOpNormedAlgebra
  have iC : @CompleteSpace (Matrix d d ℝ) iR.toUniformSpace :=
    (inferInstance : CompleteSpace (d → d → ℝ))
  exact @differentiableAt_ringInverse_gfm (Matrix d d ℝ) iR iA iC X hX

omit [Fintype T] in
/-- `Φ` is differentiable at a parameter with invertible skips. -/
private theorem differentiableAt_mixedToResidual_gfm (θ : Params A.mixed dIn dOut)
    (hθ : ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)) :
    DifferentiableAt ℝ (mixedToResidual (A := A) (dIn := dIn) (dOut := dOut)) θ := by
  refine differentiableAt_params_gfm ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · -- `E Λ_0`
    exact differentiableAt_matMul_gfm (differentiable_E_gfm θ) (differentiable_skipProdMat_gfm 0 θ)
  · -- `Λ_{ℓ-1}⁻¹ W_read^ℓ`, with `Λ_{ℓ-1}` invertible at `θ`
    have hu := isUnit_skipProdMat_gfm hθ ℓ.castSucc
    have hi := (differentiableAt_inv_gfm hu).comp θ (differentiable_skipProdMat_gfm ℓ.castSucc θ)
    exact differentiableAt_matMul_gfm hi (differentiable_unmixRead_gfm ℓ θ)
  · -- `W_write^ℓ Λ_ℓ`
    exact differentiableAt_matMul_gfm (differentiable_unmixWrite_gfm ℓ θ)
      (differentiable_skipProdMat_gfm ℓ.succ θ)
  · exact differentiable_D_gfm θ

omit [Fintype T] in
/-- A change of basis is a differentiable (linear) map of the parameters. -/
private theorem differentiable_cob_gfm (G K : Fin (L + 1) → GL d ℝ) :
    Differentiable ℝ (fun φ : Params A dIn dOut => φ.cob G K) := by
  intro φ
  refine differentiableAt_params_gfm ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · exact differentiableAt_matMul_gfm (differentiable_E_gfm φ) (differentiableAt_const _)
  · exact differentiableAt_matMul_gfm (differentiableAt_const _) (differentiable_read_gfm ℓ φ)
  · exact differentiableAt_matMul_gfm (differentiable_write_gfm ℓ φ) (differentiableAt_const _)
  · exact differentiableAt_matMul_gfm (differentiableAt_const _) (differentiable_D_gfm φ)

omit [Fintype T] [DecidableEq d] in
/-- `φ ↦ Params.mix φ U V` is a differentiable (affine) map. -/
private theorem differentiable_mix_gfm (U V : Fin L → Matrix d d ℝ) :
    Differentiable ℝ (fun φ : Params A dIn dOut => Params.mix φ U V) := by
  intro φ
  refine differentiableAt_params_gfm ?_ (fun ℓ => ?_) (fun ℓ => ?_) ?_
  · exact differentiable_E_gfm φ
  · -- entry by entry: the columns `Sum.inl` are constant, the others are those of `W_read^ℓ`
    refine differentiableAt_pi.2 fun a => differentiableAt_pi.2 fun s => ?_
    cases s with
    | inl b =>
      show DifferentiableAt ℝ (fun _ : Params A dIn dOut => U ℓ a b) φ
      exact differentiableAt_const _
    | inr j =>
      show DifferentiableAt ℝ (fun φ : Params A dIn dOut => φ.read ℓ a j) φ
      exact differentiableAt_pi.1 (differentiableAt_pi.1 (differentiable_read_gfm ℓ φ) a) j
  · -- row by row: the rows `Sum.inl` are constant, the others are those of `W_write^ℓ`
    refine differentiableAt_pi.2 fun s => ?_
    cases s with
    | inl a =>
      show DifferentiableAt ℝ (fun _ : Params A dIn dOut => V ℓ a) φ
      exact differentiableAt_const _
    | inr b =>
      show DifferentiableAt ℝ (fun φ : Params A dIn dOut => φ.write ℓ b) φ
      exact differentiableAt_pi.1 (differentiable_write_gfm ℓ φ) b
  · exact differentiable_D_gfm φ

omit [Fintype T] in
/-- **A differentiable right inverse of `Φ` through `θ`:** `r(θ') = Params.mix
(θ'.cob Λ⁻¹ Λ⁻¹) U V` with the identity units `U`, `V` of `θ`; `Φ ∘ r = id` and `r(Φ θ) = θ`. -/
private theorem exists_rightInverse_gfm (θ : Params A.mixed dIn dOut)
    (hθ : ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)) :
    ∃ r : Params A dIn dOut → Params A.mixed dIn dOut, Differentiable ℝ r ∧
      r (mixedToResidual θ) = θ ∧ (∀ θ', mixedToResidual (r θ') = θ') ∧
      ∀ θ' ℓ, IsUnit ((r θ').mixU ℓ * (r θ').mixV ℓ) := by
  obtain ⟨φ, U, V, rfl⟩ := exists_mix_gfm θ hθ
  refine ⟨fun θ' => Params.mix (θ'.cob (fun ℓ => (skipProd (fun ℓ => U ℓ * V ℓ) ℓ)⁻¹)
      (fun ℓ => (skipProd (fun ℓ => U ℓ * V ℓ) ℓ)⁻¹)) (fun ℓ => (U ℓ : Matrix d d ℝ))
      (fun ℓ => (V ℓ : Matrix d d ℝ)), ?_, ?_, ?_, ?_⟩
  · -- an affine map
    intro θ'
    have h := (differentiable_mix_gfm (A := A) (dIn := dIn) (dOut := dOut)
      (fun ℓ => (U ℓ : Matrix d d ℝ)) (fun ℓ => (V ℓ : Matrix d d ℝ)) _).comp θ'
      (differentiable_cob_gfm (fun ℓ => (skipProd (fun ℓ => U ℓ * V ℓ) ℓ)⁻¹)
        (fun ℓ => (skipProd (fun ℓ => U ℓ * V ℓ) ℓ)⁻¹) θ')
    exact h
  · -- `r(Φ θ) = Params.mix ((φ.cob Λ Λ).cob Λ⁻¹ Λ⁻¹) U V = θ`
    dsimp only
    rw [mixedToResidual_mix_gfm, cob_cob_gfm]
    simp only [mul_inv_cancel]
    rw [cob_one_gfm]
  · -- `Φ(r θ') = (θ'.cob Λ⁻¹ Λ⁻¹).cob Λ Λ = θ'`
    intro θ'
    rw [mixedToResidual_mix_gfm, cob_cob_gfm]
    simp only [inv_mul_cancel]
    exact cob_one_gfm θ'
  · intro θ' ℓ
    rw [Params.mixU_mix, Params.mixV_mix, ← Units.val_mul]
    exact Units.isUnit _

omit [Fintype T] in
/-- **Theorem A.5 (ii), "The derivative of `Φ` is onto at every `θ`"** (with invertible
skips). -/
theorem exists_hasFDerivAt_mixedToResidual_surjective (θ : Params A.mixed dIn dOut)
    (hθ : ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)) :
    ∃ Φ' : Params A.mixed dIn dOut →L[ℝ] Params A dIn dOut,
      HasFDerivAt (mixedToResidual (A := A) (dIn := dIn) (dOut := dOut)) Φ' θ
        ∧ Function.Surjective Φ' := by
  have hΦ := differentiableAt_mixedToResidual_gfm θ hθ
  refine ⟨fderiv ℝ mixedToResidual θ, hΦ.hasFDerivAt, fun η => ?_⟩
  obtain ⟨r, hr, hrθ, hΦr, -⟩ := exists_rightInverse_gfm θ hθ
  refine ⟨fderiv ℝ r (mixedToResidual θ) η, ?_⟩
  -- the chain rule for `Φ ∘ r = id` at `Φ θ`: `Φ' ∘ r' = id`
  have h1 : HasFDerivAt (mixedToResidual ∘ r)
      ((fderiv ℝ mixedToResidual θ).comp (fderiv ℝ r (mixedToResidual θ)))
      (mixedToResidual θ) := by
    have hΦ' : HasFDerivAt mixedToResidual (fderiv ℝ mixedToResidual θ)
        (r (mixedToResidual θ)) := by
      rw [hrθ]
      exact hΦ.hasFDerivAt
    exact hΦ'.comp (mixedToResidual θ) (hr _).hasFDerivAt
  have hid : mixedToResidual ∘ r = id := funext hΦr
  rw [hid] at h1
  have h2 := h1.unique (hasFDerivAt_id (mixedToResidual θ))
  have h3 := DFunLike.congr_fun h2 η
  exact h3

omit [Fintype T] [Fintype dOut] in
/-- **Theorem A.5 (i) and (ii), `F_θ = F^res_{Φ(θ)}`:** without normalization, a network of mixed
blocks with invertible skips computes the function of the residual network at `Φ(θ)`. -/
theorem evalMixed_eq_eval_mixedToResidual (hA : A.χ = id) (θ : Params A.mixed dIn dOut)
    (hθ : ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)) (x : Matrix T dIn ℝ) :
    evalMixed A θ x = eval A 1 (mixedToResidual θ) x := by
  -- write `θ` with invertible `U_ℓ`, `V_ℓ`; then this is Theorem A.5 (i)
  obtain ⟨φ, U, V, rfl⟩ := exists_mix_gfm θ hθ
  rw [evalMixed_eq_residual hA, mixedToResidual_mix_gfm]

omit [Fintype T] [Fintype dOut] in
/-- **Theorem A.5 (ii), "the networks of mixed blocks with invertible skips and the residual
networks compute the same set of functions"**, without normalization. -/
theorem image_evalMixed_eq_range_residual (hA : A.χ = id) :
    (fun θ : Params A.mixed dIn dOut => evalMixed A θ)
        '' {θ | ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)}
      = Set.range fun θ : Params A dIn dOut => eval A 1 θ := by
  ext F
  constructor
  · -- `F_θ = F^res_{Φ(θ)}`
    rintro ⟨θ, hθ, rfl⟩
    exact ⟨mixedToResidual θ, funext fun x => (evalMixed_eq_eval_mixedToResidual hA θ hθ x).symm⟩
  · -- `F^res_θ` is the network of mixed blocks with `U_ℓ = V_ℓ = I`
    rintro ⟨θ, rfl⟩
    refine ⟨Params.mix θ 1 1, fun ℓ => ?_, funext fun x => evalMixed_mix_one θ 1 x⟩
    rw [Params.mixU_mix, Params.mixV_mix]
    exact isUnit_one.mul isUnit_one

omit [Fintype T] in
/-- Near a parameter with invertible skips, the skips stay invertible. -/
private theorem eventually_isUnit_gfm (θ : Params A.mixed dIn dOut)
    (hθ : ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)) :
    ∀ᶠ θ' in nhds θ, ∀ ℓ, IsUnit (θ'.mixU ℓ * θ'.mixV ℓ) := by
  rw [Filter.eventually_all]
  intro ℓ
  -- the determinant of `U_ℓ V_ℓ` is continuous and nonzero at `θ`
  have hM : Differentiable ℝ fun θ' : Params A.mixed dIn dOut => θ'.mixU ℓ * θ'.mixV ℓ :=
    fun θ' => differentiableAt_matMul_gfm (differentiable_mixU_gfm ℓ θ')
      (differentiable_mixV_gfm ℓ θ')
  have hc : Continuous fun θ' : Params A.mixed dIn dOut => (θ'.mixU ℓ * θ'.mixV ℓ).det :=
    hM.continuous.matrix_det
  have hne : (θ.mixU ℓ * θ.mixV ℓ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (hθ ℓ)).ne_zero
  filter_upwards [hc.continuousAt.eventually_ne hne] with θ' h
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit h)

omit [Fintype T] in
/-- **Theorem A.5 (ii), "with the same functional dimension at `θ` and at `Φ(θ)`":** without
normalization, for any blocks, at a parameter `θ` of the network of mixed blocks with invertible
skips, the functional dimension of the network of mixed blocks (the skipless network of
`A.mixed`, in all its parameters, `U_ℓ` and `V_ℓ` included) is that of the residual network at
`Φ(θ)`. -/
theorem funDim_mixed_eq_funDim_residual (hA : A.χ = id) (θ : Params A.mixed dIn dOut)
    (hθ : ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)) :
    funDim A.mixed 0 θ = funDim A 1 (mixedToResidual θ) := by
  obtain ⟨r, hr, hrθ, hΦr, hru⟩ := exists_rightInverse_gfm θ hθ
  obtain ⟨Φ', hΦ', hsurj⟩ := exists_hasFDerivAt_mixedToResidual_surjective θ hθ
  -- on every batch the two Jacobians have the same rank
  have key : ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      jacobianRank A.mixed 0 X θ = jacobianRank A 1 X (mixedToResidual θ) := by
    intro n X
    -- near `θ`, the outputs of the mixed network are those of the residual one at `Φ`
    have hev : evalBatch A.mixed 0 X =ᶠ[nhds θ] evalBatch A 1 X ∘ mixedToResidual := by
      filter_upwards [eventually_isUnit_gfm θ hθ] with θ' hθ'
      funext i
      simp only [evalBatch, Function.comp]
      rw [← evalMixed_eq_eval hA, evalMixed_eq_eval_mixedToResidual hA θ' hθ']
    -- everywhere, the outputs of the residual network are those of the mixed one at `r`
    have hres : evalBatch A 1 X = evalBatch A.mixed 0 X ∘ r := by
      funext θ' i
      simp only [evalBatch, Function.comp]
      rw [← evalMixed_eq_eval hA, evalMixed_eq_eval_mixedToResidual hA (r θ') (hru θ'), hΦr]
    unfold jacobianRank
    by_cases hd : DifferentiableAt ℝ (evalBatch A 1 X) (mixedToResidual θ)
    · -- the chain rule: the derivative at `θ` is the one at `Φ θ` composed with the onto `Φ'`
      have h1 : HasFDerivAt (evalBatch A.mixed 0 X)
          ((fderiv ℝ (evalBatch A 1 X) (mixedToResidual θ)).comp Φ') θ := by
        have h := hd.hasFDerivAt.comp θ hΦ'
        exact h.congr_of_eventuallyEq hev
      rw [h1.fderiv, ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp_of_range_eq_top]
      exact LinearMap.range_eq_top.2 hsurj
    · -- neither is differentiable, and both derivatives are `0`
      have hd' : ¬ DifferentiableAt ℝ (evalBatch A.mixed 0 X) θ := by
        intro h
        apply hd
        rw [hres]
        have h' : DifferentiableAt ℝ (evalBatch A.mixed 0 X) (r (mixedToResidual θ)) := by
          rw [hrθ]
          exact h
        exact h'.comp _ (hr _)
      rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd',
        ContinuousLinearMap.toLinearMap_zero, ContinuousLinearMap.toLinearMap_zero,
        LinearMap.range_zero, LinearMap.range_zero, finrank_bot]
  simp only [funDim, key]

end Skips
