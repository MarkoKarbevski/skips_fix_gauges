import SkipsLean.OneBlock.ResidualRMSZeroSteps

/-!
# One residual block under pre-RMSNorm with `ε = 0`: the flat directions, for a block that is
smooth on an open cone of pre-activations

Paper (skips paper), proof of Theorem B.1 (iii), "The case `ε = 0`": "In Step 1, `DN_ε(h)`
vanishes along `h`, so `D_θ h_1 η = h_1 Y + μ h_1` with a number `μ` at each input. `Y` is again
antisymmetric, since `N_ε(h_1) Y` must be orthogonal to `h_1`, which is `t w E A + O(1)` at the
inputs `t w`. At these inputs `g` and its derivative along `η` do not depend on `t`, since
`N_ε(t w E) = N_ε(w E)`. […] The constant terms then give `μ = c` wherever `w E A` and `g(w)` are
linearly independent. […] For the residual network the same steps give `η_E = E (Y + c I)`".
Proof of Theorem B.1 (iv), "The residual network": "The case `ε = 0` of part (iii), with `A = I`,
shows that a flat direction is the sum of a direction of the rotation and scaling of all hidden
states and a direction `ψ` of the weights of the block along which `B` has derivative zero on the
sphere of radius `√d_model`."

`OneBlock/ResidualRMSZeroSteps.lean` has this for a map `f` of the block that is analytic
everywhere, where the derivative along `ψ` vanishes on the whole sphere. Here: the same for a map
`f` that is continuously differentiable on an open set `V` of pre-activations that is invariant
under positive scalings of the rows (ReLU, ReLU² and ReGLU blocks off their kinks; the twin for
`ε > 0` is `exists_antisymm_of_flatOn_residual_rmsNorm`, `OneBlock/ResidualRMSStepsOn.lean`). The
direction `η` is flat at the inputs `x` at which no normalized row vanishes and `x E W_read ∈ V`.
The conclusion: an antisymmetric `Y` and a number `c` with `η_E = E (Y + c I)`, `η_D = −Y D`, and
the derivative of `n ↦ f(n W_read) W_write` along `η_read + Y W_read`,
`η_write − W_write (Y + c I)` vanishes at `n = N_0(x E)` for every input `x` with `x E W_read ∈ V`
at which, for every token, the rows of `x E` and of `g(x)` are linearly independent. (No more is
claimed: where the rows are not independent, the proof gives only that the derivative is parallel
to `x E`.) The condition on generic parameters is a hypothesis: one such input exists.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **Proof of Theorem B.1 (iii), "The case `ε = 0`", for the residual network, for a block that
is smooth on an open cone of pre-activations:** let `ε = 0`, `d ≥ 2`, let `f` be continuously
differentiable on an open set `V` that is invariant under positive scalings of the rows, let `E`
and `D` have rank `d`, and let some input `w` with `w E W_read ∈ V` have, for every token, the
rows of `w E` and of `g(w) = f(N_0(w E) W_read) W_write` linearly independent. If `η` is flat at
every input `x` at which no normalized row vanishes and `x E W_read ∈ V`, there are an
antisymmetric `Y` and a number `c` with `η_E = E (Y + c I)`, `η_D = −Y D`, and at every input `x`
with `x E W_read ∈ V` whose rows of `x E` and of `g(x)` are linearly independent for every token,
the derivative of `n ↦ f(n W_read) W_write` along `η_read + Y W_read`,
`η_write − W_write (Y + c I)` vanishes at `n = N_0(x E)`. -/
theorem exists_antisymm_scale_of_flatOn_residual_rmsNorm_zero_on {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (V : Set (Matrix T (A.r 0) ℝ)) (hV : IsOpen V)
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    (hf : ContDiffOn ℝ 1 (A.f 0) V) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∃ w : Matrix T dIn ℝ, w * θ.E * θ.read 0 ∈ V ∧ ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t])
    (η : Params A dIn dOut)
    (hη : η ∈ flatOn A 1 θ (residualZeroDomain A θ ∩ {x | x * θ.E * θ.read 0 ∈ V})) :
    ∃ (Y : Matrix d d ℝ) (c : ℝ), Yᵀ = -Y ∧ η.E = θ.E * (Y + c • 1) ∧ η.D = -(Y * θ.D) ∧
      ∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
        (∀ t, LinearIndependent ℝ
          ![(x * θ.E) t, (A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) t]) →
        fderiv ℝ (A.f 0) (rmsNorm 0 (x * θ.E) * θ.read 0)
            (rmsNorm 0 (x * θ.E) * (η.read 0 + Y * θ.read 0)) * θ.write 0
          + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * (η.write 0 - θ.write 0 * (Y + c • 1))
            = 0 := by
  sorry

end Skips
