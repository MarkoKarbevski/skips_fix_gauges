import SkipsLean.OneBlock.LearnedSkipOn
import SkipsLean.OneBlock.ResidualRMSStepsOn

/-!
# One block with a full learned skip under pre-RMSNorm: Steps 1 to 3 of Part (iii)

Paper (skips paper): proof of Theorem B.1 (iii) (the last sentence of Theorem 4.6 (ii) in the main
text), for `ε > 0` and no biases. The network is

  `h_1 = x E A + g(x)`, `g(x) = B(N_ε(x E))`, `B(n) = f(n W_read) W_write`, `y = N_ε(h_1) D`,

with a full learned skip `A`. "Let `η` be flat. […] Steps 1 and 2 of part (ii) run with `E A` in
place of `E`, which has rank `d_model` since `A` is invertible for generic parameters:
`η_D = −Y D` with `Y` antisymmetric, and `D_θ h_1 η = h_1 Y` at every input. Step 3: the skip. At
the inputs `t w` of Step 2, `D_θ h_1 η = t w (η_E A + E η_A) + O(1)` and
`h_1 Y = t w E A Y + O(1)`, so `η_E A + E η_A = E A Y`. Multiplying on the left by `I − E E⁺` gives
`(I − E E⁺) η_E = 0`, as `A` is invertible, so `η_E = E X` with `X = E⁺ η_E`, and then
`η_A = A Y − X A`. At every input `D_θ h_1 η = x E A Y + D_θ g η` and
`h_1 Y = x E A Y + g(x) Y`, so `D_θ g η = g(x) Y`."

Stated here once, in the generality of `exists_antisymm_of_flatOn_residual_rmsNorm`
(`OneBlock/ResidualRMSStepsOn.lean`, the same steps for the identity skip): for a fixed map `f`
that is continuously differentiable on an open set `V` of pre-activations which is invariant under
the scaling of every row by a positive number, and for a direction `(η, η_A)` of the weights and
the skip that is flat at the inputs `x` with `x E W_read ∈ V`. For a ReLU-type block `V` is the set
of the matrices with no zero entry (no hidden unit at its kink); for a block that is continuously
differentiable everywhere `V` is everything and the direction is flat at every input. The skip is
`R 0` (the paper's `A`), and `ρ 0` is the paper's `η_A`.

The conclusion is that of Step 3: an antisymmetric `Y` and a matrix `X` with `η_E = E X`,
`η_A = A Y − X A`, `η_D = −Y D`, and `D_θ g η = g(x) Y` at these inputs, where
`D_θ g η = 𝐃f(n W_read)(𝐃N_ε(x E)(x E X) W_read + n η_read) W_write + f(n W_read) η_write` at
`n = N_ε(x E)`. With the identity skip and `η_A = 0` this gives `X = Y`, and the statement is
`exists_antisymm_of_flatOn_residual_rmsNorm`. Step 4 of the paper (the symmetric part of `X`
vanishes) depends on the kind of block: `OneBlock/LearnedSkipRescale.lean` and its siblings.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **Proof of Theorem B.1 (iii) of the skips paper, Steps 1 to 3, for one block with a full
learned skip under pre-RMSNorm, `ε > 0`:** let `f` be continuously differentiable on an open set
`V` that is invariant under positive scalings of the rows, let `E` and `D` have rank `d`, let the
skip `A = R 0` be invertible, and let some input with equal rows have its pre-activation
`x E W_read` in `V`. If the direction `(η, η_A)` of the weights and the skip is flat at every input
`x` with `x E W_read ∈ V`, there are a matrix `X` and an antisymmetric `Y` with `η_E = E X`,
`η_A = A Y − X A`, `η_D = −Y D`, and at every such input the derivative of the output
`g(x) = f(N_ε(x E) W_read) W_write` of the block along `η` is `g(x) Y`. -/
theorem exists_of_flatSkipsOn_learned_rmsNorm {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (V : Set (Matrix T (A.r 0) ℝ)) (hV : IsOpen V)
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    (hf : ContDiffOn ℝ 1 (A.f 0) V) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) (hR : IsUnit (R 0).det)
    (hw : ∃ w : dIn → ℝ, (Matrix.of fun _ : T => w) * θ.E * θ.read 0 ∈ V)
    (η : Params A dIn dOut) (ρ : Fin 1 → Matrix d d ℝ)
    (hη : (η, ρ) ∈ flatSkipsOn A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) (θ, R)
      {x | x * θ.E * θ.read 0 ∈ V}) :
    ∃ X Y : Matrix d d ℝ, Yᵀ = -Y ∧ η.E = θ.E * X ∧ ρ 0 = R 0 * Y - X * R 0 ∧
      η.D = -(Y * θ.D) ∧
      ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
        fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
            (fderiv ℝ (rmsNorm ε : Matrix T d ℝ → Matrix T d ℝ) (x * θ.E) (x * θ.E * X)
                * θ.read 0
              + rmsNorm ε (x * θ.E) * η.read 0) * θ.write 0
          + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * η.write 0
          = A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * θ.write 0 * Y := by
  sorry

end Skips
