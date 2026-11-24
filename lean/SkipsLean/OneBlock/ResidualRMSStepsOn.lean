import SkipsLean.OneBlock.ResidualRMSSteps

/-!
# One residual block under pre-RMSNorm, Steps 1 to 3, for a block that is smooth on an open cone

Paper (skips paper): proof of Theorem B.1 (ii), Steps 1 to 3, for `ε > 0` and no biases, as in
`OneBlock/ResidualRMSSteps.lean`, where the fixed map `f` of the block is continuously
differentiable everywhere and the direction `η` is flat at every input.

For ReLU, ReLU² and ReGLU blocks the paper takes the same steps at the inputs at which no hidden
unit sits at its kink ("Notation and flat directions": "For these activations, every input means
every input at which no hidden unit sits at its kink"), and in Step 4: "For the ReLU-type
activations without biases the kinks lie on hyperplanes through the center of the ball".

Stated here: the statement of `exists_antisymm_of_flat_residual_rmsNorm` for a fixed map `f` that
is continuously differentiable on an open set `V` of pre-activations that is invariant under the
scaling of every row by a positive number (for a ReLU block: the matrices with no zero entry),
and for a direction `η` that is flat at the inputs `x` with `x E W_read ∈ V`. One input with equal
rows must lie in this set (the steps use the rays `x = s w`, `s → ∞`, with `w` in an open set).
The conclusion is that of the earlier statement, at these inputs: an antisymmetric `Y` with
`η_E = E Y`, `η_D = −Y D`, and the derivative of `n ↦ f(n W_read) W_write` along the entries of
`η' = η − η^Y` vanishes at `n = N_ε(x E)`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **Proof of Theorem B.1 (ii), Steps 1 to 3, for a block that is smooth on an open cone of
pre-activations:** let `ε > 0`, let `f` be continuously differentiable on an open set `V` that is
invariant under positive scalings of the rows, let `E` and `D` have rank `d`, and let some input
with equal rows have its pre-activation `x E W_read` in `V`. If `η` is flat at every input `x`
with `x E W_read ∈ V`, there is an antisymmetric `Y` with `η_E = E Y`, `η_D = −Y D`, and at every
such input the derivative of `n ↦ f(n W_read) W_write` along `η_read + Y W_read`,
`η_write − W_write Y` vanishes at `n = N_ε(x E)`. -/
theorem exists_antisymm_of_flatOn_residual_rmsNorm {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (V : Set (Matrix T (A.r 0) ℝ)) (hV : IsOpen V)
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    (hf : ContDiffOn ℝ 1 (A.f 0) V) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∃ w : dIn → ℝ, (Matrix.of fun _ : T => w) * θ.E * θ.read 0 ∈ V)
    (η : Params A dIn dOut) (hη : η ∈ flatOn A 1 θ {x | x * θ.E * θ.read 0 ∈ V}) :
    ∃ Y : Matrix d d ℝ, Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D) ∧
      ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
        fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
            (rmsNorm ε (x * θ.E) * (η.read 0 + Y * θ.read 0)) * θ.write 0
          + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * (η.write 0 - θ.write 0 * Y) = 0 := by
  sorry

end Skips
