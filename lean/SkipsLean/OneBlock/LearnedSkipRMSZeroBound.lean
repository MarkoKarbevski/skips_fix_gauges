import SkipsLean.OneBlock.LearnedSkipTriangularRescale
import SkipsLean.OneBlock.ResidualRMSZeroValue

/-!
# One block with a learned skip under pre-RMSNorm with `ε = 0`: "at most"

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. […] For `ε = 0` it exceeds that of the residual
network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and
ReGLU blocks."

Its proof, "The case `ε = 0`": "the scalings of `h_0` and `h_1` are symmetries too, since
`N_ε(c h) = N_ε(h)` for `c > 0`. […] For the residual network […] Its flat directions are the
rotation and the scaling of all hidden states, and the space `K_B` of directions of the block along
which `B` has derivative zero on the sphere. For the learned skip, `η^rot` and `K_B` are flat,
which gives at least `d_model (d_model − 1) + 2`, respectively `d_model (d_model − 1)/2 + 2`,
dimensions besides `K_B`, against `d_model (d_model − 1)/2 + 1` for the residual network. So the
difference is at most `d_model (d_model + 1)/2 − 1`."

Here, for a full learned skip and a block whose fixed map is analytic (tanh, GELU, SwiGLU, GeGLU,
attention), at one parameter:

* `learnedZeroDomain A θ R`: the inputs at which no normalized row vanishes, for the network with
  the learned skip `R 0`: no row of `h_0 = x E` and no row of `h_1 = x E A + g(x)` is zero (the
  paper's "every input" for `ε = 0`).
* The bound for the learned skip: the rotation and the scaling of `h_0`, the rotation and the
  scaling of `h_1` (`d(d−1) + 2` dimensions) and the space `V_θ` (`blockFlatSphere`, the paper's
  `K_B`) are flat and independent, so the functional dimension on these inputs is at most
  `P + d² − (d(d−1) + 2) − dim V_θ`.
* With the value for the residual network (`funDimOn_residual_rmsNorm_zero_eq`,
  `OneBlock/ResidualRMSZeroValue.lean`): the difference is at most `d(d+1)/2 − 1`, the two
  networks at the same weights.

The functional dimensions are those on the inputs at which no normalized row vanishes
(`funDimSkipsOn`, `funDimOn`): `V_θ` is flat only where the block reads rows on the sphere. Not
stated here: the upper triangular skip; ReLU, ReLU², ReGLU blocks and the equality for them; the
statements at almost every parameter.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The inputs at which no normalized row vanishes, for one block with the learned skip `R 0`
under pre-RMSNorm with `ε = 0`:** no row of `h_0 = x E` and no row of
`h_1 = x E A + f(N_0(x E) W_read) W_write` is zero (`A = R 0`). For `A = I` this is
`residualZeroDomain`. -/
def learnedZeroDomain (A : Arch T d 1) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ) :
    Set (Matrix T dIn ℝ) :=
  {x | (∀ t, (x * θ.E) t ≠ 0) ∧
    ∀ t, (x * θ.E * R 0 + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) t ≠ 0}

/-- **Proof of Theorem B.1 (iii) of the skips paper, "The case `ε = 0`", the bound for the learned
skip:** for one block with an analytic fixed map and a full learned skip `A` that is invertible,
under pre-RMSNorm with `ε = 0`, if `E` has rank `d ≥ 1`, the functional dimension on the inputs
at which no normalized row vanishes is at most `P + d² − (d(d−1) + 2) − dim V_θ`. -/
theorem funDimSkipsOn_add_le_learned_rmsNorm_zero {A : Arch T d 1} [Nonempty d]
    (hA : A.χ = rmsNorm 0) (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (R : Fin 1 → Matrix d d ℝ) (hE : θ.E.rank = Fintype.card d) (hR : IsUnit (R 0).det) :
    funDimSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
        (learnedZeroDomain A θ R)
        + ((Fintype.card d * (Fintype.card d - 1) + 2)
          + Module.finrank ℝ (blockFlatSphere A θ))
      ≤ Module.finrank ℝ (Params A dIn dOut) + Fintype.card d ^ 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "at most", at one parameter:** under the
conditions of the value for the residual network (`d ≥ 2`, `E`, `D` of rank `d`, one input `w`
with the rows of `w E` and `g(w)` independent for every token) and for an invertible full learned
skip, the functional dimension of the network with the learned skip exceeds that of the residual
network with the same weights by at most `d(d+1)/2 − 1`; both on the inputs at which no
normalized row vanishes. -/
theorem funDimSkipsOn_learned_le_funDimOn_residual_add_rmsNorm_zero {A : Arch T d 1}
    [Nonempty T] (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (R : Fin 1 → Matrix d d ℝ) (hE : θ.E.rank = Fintype.card d)
    (hD : θ.D.rank = Fintype.card d) (hR : IsUnit (R 0).det)
    (hw : ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t]) :
    funDimSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
        (learnedZeroDomain A θ R)
      ≤ funDimOn A 1 θ (residualZeroDomain A θ)
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  have h1 := funDimSkipsOn_add_le_learned_rmsNorm_zero hA hf θ R hE hR
  have h2 := funDimOn_residual_rmsNorm_zero_eq hA hd hf θ hE hD hw
  -- `d(d−1)` is even, and `d(d+1)/2 + d(d−1)/2 = d²`
  have e1 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  have e2 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (Fintype.card d))
  have e3 : Fintype.card d * (Fintype.card d + 1) + Fintype.card d * (Fintype.card d - 1)
      = 2 * Fintype.card d ^ 2 := by
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card d = m + 1 := ⟨Fintype.card d - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    ring
  generalize Fintype.card d * (Fintype.card d + 1) = y at e2 e3 ⊢
  generalize Fintype.card d * (Fintype.card d - 1) = x at h1 h2 e1 e3
  generalize Fintype.card d ^ 2 = q at h1 e3
  omega

end Skips
