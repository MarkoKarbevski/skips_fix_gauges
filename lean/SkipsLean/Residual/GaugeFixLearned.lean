import SkipsLean.Residual.GaugeFixMixed
import SkipsLean.OneBlock.LearnedSkip

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

/-- **Equation (12) for invertible learned skips:** `Φ(θ, A) = θ.cob Λ Λ`. -/
theorem learnedToResidual_coe (θ : Params A dIn dOut) (S : Fin L → GL d ℝ) :
    learnedToResidual (θ, fun ℓ => (S ℓ : Matrix d d ℝ)) = θ.cob (skipProd S) (skipProd S) := by
  sorry

/-- **Theorem A.5 (ii) for learned skips, "Every parameter of the residual network is `Φ(θ)` for
some `θ`":** the same weights with the skips `A_ℓ = I`. -/
theorem learnedToResidual_one (θ : Params A dIn dOut) :
    learnedToResidual (θ, (1 : Fin L → Matrix d d ℝ)) = θ := by
  sorry

/-- **Theorem A.5 (ii) for learned skips, "`Φ(θ̃) = Φ(θ)` exactly when `θ̃ = T_G(θ)` for some `G`
with `G_L = I`"** ("without the `K_ℓ`"), for invertible skips: `T_G` multiplies the weights as
the changes of basis `G_ℓ` do and sends `A_ℓ` to `G_{ℓ−1}^{-1} A_ℓ G_ℓ`. -/
theorem learnedToResidual_eq_iff (p p' : Params A dIn dOut × (Fin L → Matrix d d ℝ))
    (hp : ∀ ℓ, IsUnit (p.2 ℓ)) (hp' : ∀ ℓ, IsUnit (p'.2 ℓ)) :
    learnedToResidual p' = learnedToResidual p
      ↔ ∃ G : Fin (L + 1) → GL d ℝ,
          G (Fin.last L) = 1 ∧ p' = (p.1.cob G G, cobSkip p.2 G) := by
  sorry

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
