import SkipsLean.OneBlock.ResidualRMSStepsOn
import SkipsLean.Dimension.UpperBoundResidualRMSNormZero

/-!
# One residual block under pre-RMSNorm with `ε = 0`: the flat directions

Paper (skips paper), proof of Theorem B.1 (v): "With `ε = 0`, `N_ε(h) = √d_model h/‖h‖` ignores the
length of each token, so the block reads only rows on the sphere of radius `√d_model`. Let `V_θ`
be the space of directions that move only the weights of the block and leave its output unchanged
to first order at every input whose rows lie on this sphere; it contains the symmetries inside the
block. We show that the flat directions of the residual network are those of `CO(d_model)` and
those of `V_θ` […].
The residual network. Write `h_1 = x E + g(x)`, with `g(x) = f(N_ε(x E) W_read) W_write`, and
`y = N_ε(h_1) D`, and let `η` be flat. Step 1 of part (ii) runs as before, except that with
`ε = 0` the derivative `DN_ε(h)` projects onto the vectors orthogonal to `h` and scales by
`√d_model/‖h‖`, so its kernel is spanned by `h`. Hence `N_ε(h_1) Y` is orthogonal to `h_1`; as
`h_1` takes every value in an open set, `Y_s = 0`, and `D_θ h_1 η = h_1 Y + μ(x) h_1` with a
number `μ(x)`, for attention one per token. […] Take the inputs `x = t w` with `t > 0`. […] For
generic parameters `w E` and `g(w)` are linearly independent for all `w` in an open set, since
otherwise the block would map every point of the sphere to a multiple of itself. […] and
`η′_E = c E` with one number `c`. The scaling `E ↦ (1 + τ) E`, `W_write ↦ (1 + τ) W_write`
multiplies `h_1` by `1 + τ` and is the scale in `CO(d_model)`. Subtracting `c` times its direction
leaves a flat `η″` that moves only the weights of the block, with `D_θ g η″ = 0` at the inputs
`t w`. Their normalized rows cover an open set of the sphere, and the derivative of the block along
`η″` is analytic on the sphere, so `η″ ∈ V_θ`."

"Notation and flat directions" (Appendix B): with `ε = 0`, "every input" excludes the inputs at
which a row of a hidden state that is normalized vanishes.

Stated here, for a fixed map `f` of the block that is analytic everywhere (tanh, GELU, SwiGLU,
GeGLU and attention blocks): the set `U_θ` of the inputs at which no row of `x E` and no row of
`h_1` vanishes (`residualZeroDomain`); and the conclusion of the passage for a direction `η` that
is flat at the inputs of `U_θ`: an antisymmetric `Y` and a number `c` with `η_E = E (Y + c I)`,
`η_D = −Y D`, and the direction `η − η^Y − c η^{scale}`, which moves only the weights of the block
(read `η_read + Y W_read`, write `η_write − W_write (Y + c I)`), has derivative zero at every `n`
whose rows lie on the sphere of radius `√d`. The condition of the paper on generic parameters is
a hypothesis: some input `w` at which, for every token, the rows of `w E` and of `g(w)` are
linearly independent. `d ≥ 2` is the Scope's and is needed (for `d = 1` the step "`η′_E = c E`"
fails).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The inputs of a residual network of one block under pre-RMSNorm with `ε = 0` at which no
normalized row vanishes:** no row of `h_0 = x E` and no row of
`h_1 = x E + f(N_0(x E) W_read) W_write` is zero. -/
def residualZeroDomain (A : Arch T d 1) (θ : Params A dIn dOut) : Set (Matrix T dIn ℝ) :=
  {x | (∀ t, (x * θ.E) t ≠ 0) ∧
    ∀ t, (x * θ.E + A.f 0 (rmsNorm 0 (x * θ.E) * θ.read 0) * θ.write 0) t ≠ 0}

/-- **Proof of Theorem B.1 (v) of the skips paper, "The residual network":** let `ε = 0`, `d ≥ 2`,
let the fixed map `f` of the block be analytic, let `E` and `D` have rank `d`, and let some input
`w` have, for every token, the rows of `w E` and of `g(w) = f(N_0(w E) W_read) W_write` linearly
independent. If `η` is flat at every input at which no normalized row vanishes, there are an
antisymmetric `Y` and a number `c` with `η_E = E (Y + c I)`, `η_D = −Y D`, and at every `n` with
all rows on the sphere of radius `√d` the derivative of `n ↦ f(n W_read) W_write` along
`η_read + Y W_read`, `η_write − W_write (Y + c I)` vanishes. -/
theorem exists_antisymm_scale_of_flatOn_residual_rmsNorm_zero {A : Arch T d 1}
    (hA : A.χ = rmsNorm 0) (hd : 2 ≤ Fintype.card d)
    (hf : AnalyticOnNhd ℝ (A.f 0) Set.univ) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hw : ∃ w : Matrix T dIn ℝ, ∀ t, LinearIndependent ℝ
      ![(w * θ.E) t, (A.f 0 (rmsNorm 0 (w * θ.E) * θ.read 0) * θ.write 0) t])
    (η : Params A dIn dOut) (hη : η ∈ flatOn A 1 θ (residualZeroDomain A θ)) :
    ∃ (Y : Matrix d d ℝ) (c : ℝ), Yᵀ = -Y ∧ η.E = θ.E * (Y + c • 1) ∧ η.D = -(Y * θ.D) ∧
      ∀ n : Matrix T d ℝ, (∀ t, n t ⬝ᵥ n t = Fintype.card d) →
        fderiv ℝ (A.f 0) (n * θ.read 0) (n * (η.read 0 + Y * θ.read 0)) * θ.write 0
          + A.f 0 (n * θ.read 0) * (η.write 0 - θ.write 0 * (Y + c • 1)) = 0 := by
  sorry

end Skips
