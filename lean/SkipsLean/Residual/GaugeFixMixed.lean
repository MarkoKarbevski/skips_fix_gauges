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
/-- For invertible matrices, `skipProdMat` is `skipProd`. -/
theorem skipProdMat_coe (S : Fin L → GL d ℝ) (ℓ : Fin (L + 1)) :
    skipProdMat (fun ℓ => (S ℓ : Matrix d d ℝ)) ℓ = (skipProd S ℓ : Matrix d d ℝ) := by
  sorry

/-- **Equation (12):** for invertible `U_ℓ` and `V_ℓ`, `Φ` of the network of mixed blocks with
the hidden units of `θ` is `θ.cob Λ Λ`. -/
theorem mixedToResidual_mix (θ : Params A dIn dOut) (U V : Fin L → GL d ℝ) :
    mixedToResidual
        (Params.mix θ (fun ℓ => (U ℓ : Matrix d d ℝ)) (fun ℓ => (V ℓ : Matrix d d ℝ)))
      = θ.cob (skipProd fun ℓ => U ℓ * V ℓ) (skipProd fun ℓ => U ℓ * V ℓ) := by
  sorry

/-- **Theorem A.5 (ii), "Every parameter of the residual network is `Φ(θ)` for some `θ`":** the
`θ` with the same entries and `U_ℓ = V_ℓ = I`. -/
theorem mixedToResidual_mix_one (θ : Params A dIn dOut) :
    mixedToResidual (Params.mix θ 1 1) = θ := by
  sorry

/-- **Theorem A.5 (ii), "`Φ(θ̃) = Φ(θ)` exactly when `θ̃ = T_{G,K}(θ)` for some `G` and `K` with
`G_L = I`"**, for parameters of the network of mixed blocks whose skips `A_ℓ = U_ℓ V_ℓ` are
invertible. -/
theorem mixedToResidual_eq_iff (θ θ' : Params A.mixed dIn dOut)
    (hθ : ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)) (hθ' : ∀ ℓ, IsUnit (θ'.mixU ℓ * θ'.mixV ℓ)) :
    mixedToResidual θ' = mixedToResidual θ
      ↔ ∃ (G : Fin (L + 1) → GL d ℝ) (K : Fin L → GL d ℝ),
          G (Fin.last L) = 1 ∧ θ' = θ.cobMixed G G K := by
  sorry

/-- **Theorem A.5 (ii), "The derivative of `Φ` is onto at every `θ`"** (with invertible
skips). -/
theorem exists_hasFDerivAt_mixedToResidual_surjective (θ : Params A.mixed dIn dOut)
    (hθ : ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)) :
    ∃ Φ' : Params A.mixed dIn dOut →L[ℝ] Params A dIn dOut,
      HasFDerivAt (mixedToResidual (A := A) (dIn := dIn) (dOut := dOut)) Φ' θ
        ∧ Function.Surjective Φ' := by
  sorry

omit [Fintype T] [Fintype dOut] in
/-- **Theorem A.5 (i) and (ii), `F_θ = F^res_{Φ(θ)}`:** without normalization, a network of mixed
blocks with invertible skips computes the function of the residual network at `Φ(θ)`. -/
theorem evalMixed_eq_eval_mixedToResidual (hA : A.χ = id) (θ : Params A.mixed dIn dOut)
    (hθ : ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)) (x : Matrix T dIn ℝ) :
    evalMixed A θ x = eval A 1 (mixedToResidual θ) x := by
  sorry

omit [Fintype T] [Fintype dOut] in
/-- **Theorem A.5 (ii), "the networks of mixed blocks with invertible skips and the residual
networks compute the same set of functions"**, without normalization. -/
theorem image_evalMixed_eq_range_residual (hA : A.χ = id) :
    (fun θ : Params A.mixed dIn dOut => evalMixed A θ)
        '' {θ | ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)}
      = Set.range fun θ : Params A dIn dOut => eval A 1 θ := by
  sorry

/-- **Theorem A.5 (ii), "with the same functional dimension at `θ` and at `Φ(θ)`":** without
normalization, for any blocks, at a parameter `θ` of the network of mixed blocks with invertible
skips, the functional dimension of the network of mixed blocks (the skipless network of
`A.mixed`, in all its parameters, `U_ℓ` and `V_ℓ` included) is that of the residual network at
`Φ(θ)`. -/
theorem funDim_mixed_eq_funDim_residual (hA : A.χ = id) (θ : Params A.mixed dIn dOut)
    (hθ : ∀ ℓ, IsUnit (θ.mixU ℓ * θ.mixV ℓ)) :
    funDim A.mixed 0 θ = funDim A 1 (mixedToResidual θ) := by
  sorry

end Skips
