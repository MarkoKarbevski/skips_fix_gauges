import SkipsLean.OneBlock.LearnedSkipTriangular
import SkipsLean.OneBlock.LearnedSkipAttention

/-!
# One block with an upper triangular learned skip under pre-RMSNorm: the general step, attention

Paper (skips paper): Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. For generic parameters and `ε > 0`, its functional
dimension exceeds that of the residual network of part (ii) by exactly `d_model (d_model + 1)/2`,
and it satisfies the equality condition." Its proof, Step 5: "For an upper triangular `A`,
`A Y − X_a A` must be upper triangular, which determines `Y` from `X_a` […]. They then have
dimension `d_model (d_model − 1)/2`. So `K(θ)` is larger than for the residual network by
`d_model (d_model − 1)/2`, respectively `0`, while the network has `d_model²`, respectively
`d_model (d_model + 1)/2`, more parameters. In both cases the functional dimension is larger by
`d_model (d_model + 1)/2`."

`OneBlock/LearnedSkipTriangular.lean` has the definitions (`upperTriangular`, `triSkips`,
`funDimLearnedTri`), the statement that at an invertible upper triangular skip the triangular
family has the functional dimension of the full family (`funDimLearnedTri_eq_funDimLearned`), and
the values for tanh, GELU, SwiGLU and GeGLU blocks of width at least `d`. Here:

* once for all continuously differentiable blocks, at one parameter: if `E` and `D` have rank `d`,
  the upper triangular skip is invertible and Step 4 holds (`NoSymmetricPart`,
  `OneBlock/LearnedSkipGain.lean`), the network with the upper triangular learned skip has the
  functional dimension of the residual network at the same weights plus `d (d + 1)/2`;
* for an attention block: the same at one parameter (some token sees a token, `S ≠ 0`), and for
  `d_in, d_out ≥ d ≥ 2`, at least one head, heads of width `1 ≤ d_h ≤ d` and a token that sees
  itself and another token: at almost every `(θ, A)`, `A` upper triangular, the functional
  dimension is `P + d (d + 1)/2 − d (d − 1)/2 − 2 H d_h²` (the equality condition: the network has
  `P + d (d + 1)/2` parameters and its symmetries have dimension `d (d − 1)/2 + 2 H d_h²`), which is
  `d (d + 1)/2` more than the residual network at almost every `θ'`.

ReLU, ReLU² and ReGLU blocks: `OneBlock/LearnedSkipTriangularRescale.lean`. Not stated: `ε = 0`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [LinearOrder d] [Fintype dIn] [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)] {ε : ℝ}

/-- **Theorem B.1 (iii) for the upper triangular skip, at one parameter, for a continuously
differentiable block (`ε > 0`):** if `E` and `D` have rank `d`, the upper triangular skip
`A = R 0` is invertible and Step 4 holds at `θ` (`NoSymmetricPart` at all inputs), the network
with the upper triangular learned skip has at `(θ, A)` the functional dimension of the residual
network at `θ` plus `d (d + 1)/2`. -/
theorem funDimLearnedTri_eq_funDim_residual_add_of_noSymmetricPart {A : Arch T d 1} {ε : ℝ}
    (hε : 0 < ε) (hA : A.χ = rmsNorm ε) (hf : ContDiff ℝ 1 (A.f 0)) (θ : Params A dIn dOut)
    (R : Fin 1 → upperTriangular d) (hE : θ.E.rank = Fintype.card d)
    (hD : θ.D.rank = Fintype.card d) (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    (hX : NoSymmetricPart A ε θ Set.univ) :
    funDimLearnedTri A (θ, R)
      = funDim A 1 θ + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the block is differentiable (`Fin 1` has the one block `0`)
  have hf' : ∀ ℓ, Differentiable ℝ (A.f ℓ) := fun ℓ => by
    obtain rfl : ℓ = 0 := Subsingleton.elim ℓ 0
    exact hf.differentiable one_ne_zero
  -- at the invertible triangular skip the triangular family has the value of the full family,
  -- and the full family has the residual value plus `d (d + 1)/2`
  rw [funDimLearnedTri_eq_funDimLearned hε hA hf' θ R hR]
  exact funDimLearned_eq_funDim_residual_add_of_noSymmetricPart hε hA hf θ _ hE hD hR hX

/-- **Theorem B.1 (iii) for an attention block with an upper triangular learned skip, at one
parameter (`ε > 0`):** if `E` and `D` have rank `d`, some token sees a token,
`S = ∑_i W_{V,i} W_{O,i}` is not `0` and the upper triangular skip is invertible, the functional
dimension is that of the residual network at the same weights plus `d (d + 1)/2`. -/
theorem funDimLearnedTri_attention_rmsNorm_eq_residual_add (hε : 0 < ε)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hsees : ∃ t s, sees t s) (hS : ∑ i, headValueModel θ 0 i ≠ 0)
    (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det) :
    funDimLearnedTri (Arch.attention sees (rmsNorm ε) H dh) (θ, R)
      = funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  -- the attention block is analytic, hence `C¹`; Step 4 is `noSymmetricPart_attention_rmsNorm`
  have hf : ContDiff ℝ 1 ((Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh).f 0) :=
    (analyticOnNhd_f_attention (d := d) sees (rmsNorm ε) H dh 0).contDiff
  exact funDimLearnedTri_eq_funDim_residual_add_of_noSymmetricPart hε rfl hf θ R hE hD hR
    (noSymmetricPart_attention_rmsNorm hε θ hE hsees hS)

/-- **Theorem B.1 (iii) of the skips paper for one attention block with an upper triangular
learned skip, `ε > 0`:** for `d_in, d_out ≥ d ≥ 2`, at least one head, heads of width
`1 ≤ d_h ≤ d` and a token that sees itself and another token, at almost every `(θ, A)`, `A` upper
triangular, the functional dimension is `P + d (d + 1)/2 − d (d − 1)/2 − 2 H d_h²`, with `P` the
number of weights without the skip. -/
theorem ae_funDimLearnedTri_attention_rmsNorm (hε : 0 < ε) [Nonempty (H 0)]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ p ∂μ, funDimLearnedTri (Arch.attention sees (rmsNorm ε) H dh) p
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii), "exceeds that of the residual network of part (ii) by exactly
`d (d + 1)/2`", for one attention block with an upper triangular learned skip, `ε > 0`:** at
almost every `(θ, A)`, `A` upper triangular, and almost every `θ'`. -/
theorem ae_funDimLearnedTri_attention_rmsNorm_eq_residual_add (hε : 0 < ε) [Nonempty (H 0)]
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure]
    (ν : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [ν.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ p ∂μ, ∀ᵐ θ' ∂ν, funDimLearnedTri (Arch.attention sees (rmsNorm ε) H dh) p
      = funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ'
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

end Skips
