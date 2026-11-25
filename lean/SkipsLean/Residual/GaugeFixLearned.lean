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

/-- **Theorem A.5 (ii) for learned skips, "The derivative of `Φ` is onto at every `θ`"** (with
invertible skips). -/
theorem exists_hasFDerivAt_learnedToResidual_surjective
    (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) (hp : ∀ ℓ, IsUnit (p.2 ℓ)) :
    ∃ Φ' : (Params A dIn dOut × (Fin L → Matrix d d ℝ)) →L[ℝ] Params A dIn dOut,
      HasFDerivAt (learnedToResidual (A := A) (dIn := dIn) (dOut := dOut)) Φ' p
        ∧ Function.Surjective Φ' := by
  sorry

/-- **Theorem A.5 (i) and (ii) for learned skips, `F_θ = F^res_{Φ(θ)}`:** without normalization,
a network with invertible learned skips computes the function of the residual network at
`Φ(θ, A)`. -/
theorem eval_eq_eval_learnedToResidual (hA : A.χ = id)
    (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) (hp : ∀ ℓ, IsUnit (p.2 ℓ))
    (x : Matrix T dIn ℝ) :
    eval A p.2 p.1 x = eval A 1 (learnedToResidual p) x := by
  sorry

/-- **Theorem A.5 (ii) for learned skips, the same set of functions:** without normalization,
the networks with invertible learned skips and the residual networks compute the same set of
functions. -/
theorem image_eval_learned_eq_range_residual (hA : A.χ = id) :
    (fun p : Params A dIn dOut × (Fin L → Matrix d d ℝ) => eval A p.2 p.1)
        '' {p | ∀ ℓ, IsUnit (p.2 ℓ)}
      = Set.range fun θ : Params A dIn dOut => eval A 1 θ := by
  sorry

/-- **Theorem A.5 (ii) for learned skips, "with the same functional dimension at `θ` and at
`Φ(θ)`":** without normalization, for any blocks, the functional dimension of the network with
full learned skips at `(θ, A)` with invertible `A_ℓ` (in the weights and the skips) is that of
the residual network at `Φ(θ, A)`. -/
theorem funDimLearned_eq_funDim_residual (hA : A.χ = id)
    (p : Params A dIn dOut × (Fin L → Matrix d d ℝ)) (hp : ∀ ℓ, IsUnit (p.2 ℓ)) :
    funDimLearned A p = funDim A 1 (learnedToResidual p) := by
  sorry

end Skips
