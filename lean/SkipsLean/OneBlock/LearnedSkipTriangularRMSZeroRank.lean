import SkipsLean.OneBlock.LearnedSkipTriangularRMSZeroBound
import SkipsLean.OneBlock.LearnedSkipTriangularRescale

/-!
# An upper triangular learned skip against a full one, on a batch: the same rank

Paper (skips paper), proof of Theorem B.1 (iii): "For an upper triangular `A`, view the network
as the network with a full `A` restricted to triangular skips: its flat directions are those of
the full network whose entry `η_A` is upper triangular." And Step 5: "For an upper triangular
`A`, `A Y − X_a A` must be upper triangular, which determines `Y` from `X_a` […]. So `K(θ)` is
larger than for the residual network by `d_model (d_model − 1)/2`, respectively `0`, while the
network has `d_model²`, respectively `d_model (d_model + 1)/2`, more parameters. In both cases
the functional dimension is larger by `d_model (d_model + 1)/2`."

In Lean the comparison of the two families is made on a batch of inputs, as in
`OneBlock/LearnedSkipTriangularRescale.lean` for `ε > 0` (the private
`jacobianRankSkips_tri_eq_ltr`): at an invertible upper triangular skip `R`, the Jacobian of the
family of upper triangular skips on a batch is the Jacobian `J` of the family of all skips
composed with the inclusion, and every direction of the skip is a triangular one plus `−X_0 R`
with `X_0` antisymmetric, the direction of the rotation of `h_0` by `X_0`, which is flat for every
`ε` and which `J` kills. So the two Jacobians have the same range. Here this is stated

* for every real `ε`, on a batch at whose inputs the output with a full skip is a differentiable
  function of the weights and the skip;
* for `ε = 0`, on a batch of inputs at which no normalized row vanishes (`learnedZeroDomain`) and
  the fixed map of the block is differentiable at the normalized read.

With it the values for the full skip at `ε = 0` carry over to the upper triangular skip:
`P + d² − (d(d−1) + 2) − s = P + d(d+1)/2 − (d(d−1)/2 + 2) − s`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [LinearOrder d] [Fintype dIn] [Fintype dOut]

/-- **One block under pre-RMSNorm (every real `ε`), at an invertible upper triangular skip `R`,
on a batch:** if at every input of the batch the output with a full skip is a differentiable
function of the weights and the skip at `(θ, R)`, the Jacobian of the family of upper triangular
skips on the batch has the rank of the Jacobian of the family of all skips. -/
theorem jacobianRankSkips_tri_eq_of_differentiableAt {A : Arch T d 1} {ε : ℝ}
    (hA : A.χ = rmsNorm ε) (θ : Params A dIn dOut) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hdiff : ∀ i, DifferentiableAt ℝ
      (fun p' : Params A dIn dOut × (Fin 1 → Matrix d d ℝ) =>
        evalSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) p' (X i))
      (θ, fun ℓ => (R ℓ : Matrix d d ℝ))) :
    jacobianRankSkips A (triSkips d 1) X (θ, R)
      = jacobianRankSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X
          (θ, fun ℓ => (R ℓ : Matrix d d ℝ)) := by
  sorry

/-- **One block under pre-RMSNorm with `ε = 0`, at an invertible upper triangular skip `R`, on a
batch of inputs at which no normalized row vanishes and the fixed map of the block is
differentiable at the normalized read:** the Jacobian of the family of upper triangular skips has
the rank of the Jacobian of the family of all skips. -/
theorem jacobianRankSkips_tri_eq_learned_rmsNorm_zero {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (θ : Params A dIn dOut) (R : Fin 1 → upperTriangular d)
    (hR : IsUnit (R 0 : Matrix d d ℝ).det) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i, X i ∈ learnedZeroDomain A θ fun ℓ => (R ℓ : Matrix d d ℝ))
    (hfx : ∀ i, DifferentiableAt ℝ (A.f 0) (rmsNorm 0 (X i * θ.E) * θ.read 0)) :
    jacobianRankSkips A (triSkips d 1) X (θ, R)
      = jacobianRankSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X
          (θ, fun ℓ => (R ℓ : Matrix d d ℝ)) := by
  sorry

end Skips
