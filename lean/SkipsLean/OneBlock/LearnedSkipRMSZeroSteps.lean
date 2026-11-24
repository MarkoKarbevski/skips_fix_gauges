import SkipsLean.OneBlock.LearnedSkipSteps
import SkipsLean.OneBlock.ResidualRMSZeroStepsOn
import SkipsLean.OneBlock.LearnedSkipRMSZeroBound
import SkipsLean.OneBlock.SkiplessRMSZeroReadout

/-!
# One block with a full learned skip under pre-RMSNorm with `ε = 0`: Steps 1 to 3 of Part (iii)

Paper (skips paper), proof of Theorem B.1 (iii), "The case `ε = 0`". The network is

  `h_1 = x E A + g(x)`, `g(x) = B(N_0(x E))`, `B(n) = f(n W_read) W_write`, `y = N_0(h_1) D`,

with a full learned skip `A`. "Now `N_ε` maps onto the sphere of radius `√d_model`, and the
scalings of `h_0` and `h_1` are symmetries too, since `N_ε(c h) = N_ε(h)` for `c > 0`. In Step 1,
`DN_ε(h)` vanishes along `h`, so `D_θ h_1 η = h_1 Y + μ h_1` with a number `μ` at each input. `Y`
is again antisymmetric, since `N_ε(h_1) Y` must be orthogonal to `h_1`, which is
`t w E A + O(1)` at the inputs `t w`. At these inputs `g` and its derivative along `η` do not
depend on `t`, since `N_ε(t w E) = N_ε(w E)`. The terms of order `t` give `w Λ = μ_w w E A` with
`Λ = η_E A + E η_A − E A Y` and a number `μ_w`, for all `w` in an open set. Adding to `w` a
vector `w_0` with `w_0 E = 0` leaves `w E A` unchanged, so `w_0 Λ` is a multiple of `w E A` for
every such `w`, hence `w_0 Λ = 0`, and `Λ = E Λ′` with `Λ′ = E⁺ Λ`. Every vector `v = w E` of an
open set is then a left eigenvector of `Λ′ A⁻¹`, which is therefore `c I` for a number `c`, as in
the proof of Lemma A.2: `η_E A + E η_A = E A (Y + c I)`. The constant terms then give `μ = c`
wherever `w E A` and `g(w)` are linearly independent. Steps 3 and 4 run with `Y + c I` in place
of `Y`".

Stated here once, in the generality of `exists_of_flatSkipsOn_learned_rmsNorm`
(`OneBlock/LearnedSkipSteps.lean`, the same steps for `ε > 0`) and of
`exists_antisymm_scale_of_flatOn_residual_rmsNorm_zero_on` (`OneBlock/ResidualRMSZeroStepsOn.lean`,
the case `ε = 0` for the identity skip): for a fixed map `f` that is continuously differentiable
on an open set `V` of pre-activations which is invariant under the scaling of every row by a
positive number (ReLU, ReLU² and ReGLU blocks off their kinks; everything for a smooth block), and
for a direction `(η, η_A)` of the weights and the skip that is flat at the inputs `x` at which no
normalized row vanishes (`learnedZeroDomain`) and `x E W_read ∈ V`. The skip is `R 0` (the paper's
`A`), and `ρ 0` is the paper's `η_A`.

The conclusion is that of Step 3 with `Y + c I` in place of `Y`: a matrix `X`, an antisymmetric
`Y` and a number `c` with `η_E = E X`, `η_A = A (Y + c I) − X A`, `η_D = −Y D`, and
`D_θ g η = g(x) (Y + c I)` at every input `x` with `x E W_read ∈ V` at which, for every token, the
rows of `x E A` and of `g(x)` are linearly independent, where
`D_θ g η = 𝐃f(n W_read)(𝐃N_0(x E)(x E X) W_read + n η_read) W_write + f(n W_read) η_write` at
`n = N_0(x E)`. (No more is claimed: where the rows are not independent, the proof gives only
that the difference is parallel to `h_1`.) The condition on generic parameters is a hypothesis:
one such input exists. With the identity skip and `η_A = 0` this gives `X = Y + c I`, the
statement for the residual network. Step 4 (the symmetric part of `X` is a multiple of `I`)
depends on the kind of block.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **Proof of Theorem B.1 (iii) of the skips paper, "The case `ε = 0`", Steps 1 to 3, for one
block with a full learned skip:** let `ε = 0`, `d ≥ 2`, let `f` be continuously differentiable on
an open set `V` that is invariant under positive scalings of the rows, let `E` and `D` have rank
`d`, let the skip `A = R 0` be invertible, and let some input `w` with `w E W_read ∈ V` have, for
every token, the rows of `w E A` and of `g(w) = f(N_0(w E) W_read) W_write` linearly independent.
If the direction `(η, η_A)` of the weights and the skip is flat at every input `x` at which no
normalized row vanishes and `x E W_read ∈ V`, there are a matrix `X`, an antisymmetric `Y` and a
number `c` with `η_E = E X`, `η_A = A (Y + c I) − X A`, `η_D = −Y D`, and at every input `x` with
`x E W_read ∈ V` whose rows of `x E A` and of `g(x)` are linearly independent for every token,
the derivative of the output `g(x)` of the block along `η` is `g(x) (Y + c I)`. -/
theorem exists_of_flatSkipsOn_learned_rmsNorm_zero_on {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (V : Set (Matrix T (A.r 0) ℝ)) (hV : IsOpen V)
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    (hf : ContDiffOn ℝ 1 (A.f 0) V) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) (hR : IsUnit (R 0).det)
    (hw : ∃ w : Matrix T dIn ℝ, w * θ.E * θ.read 0 ∈ V ∧ ∀ t, LinearIndependent ℝ
      ![(w * θ.E * R 0) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t])
    (η : Params A dIn dOut) (ρ : Fin 1 → Matrix d d ℝ)
    (hη : (η, ρ) ∈ flatSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
      (learnedZeroDomain A θ R ∩ {x | x * θ.E * θ.read 0 ∈ V})) :
    ∃ (X Y : Matrix d d ℝ) (c : ℝ), Yᵀ = -Y ∧ η.E = θ.E * X ∧
      ρ 0 = R 0 * (Y + c • 1) - X * R 0 ∧ η.D = -(Y * θ.D) ∧
      ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
        (∀ t, LinearIndependent ℝ
          ![(x * θ.E * R 0) t, (A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) t]) →
        fderiv ℝ (A.f 0) (rmsNorm 0 (x * θ.E) * θ.read 0)
            (fderiv ℝ (rmsNorm 0 : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * θ.E * X)
                * θ.read 0
              + rmsNorm 0 (x * θ.E) * η.read 0) * θ.write 0
          + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * η.write 0
          = A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0 * (Y + c • 1) := by
  sorry

end Skips
