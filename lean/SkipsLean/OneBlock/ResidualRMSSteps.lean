import SkipsLean.Depth.SuffixRMS
import SkipsLean.Residual.UpperBoundSymmetries

/-!
# One residual block under pre-RMSNorm: the final normalization, large inputs, the skip

Paper (skips paper): proof of Theorem B.1 (ii) (Theorem 4.6 (ii) of the main text), Steps 1 to 3,
for `ε > 0` and no biases. The network is

  `h_1 = x E + g(x)`, `g(x) = f(N_ε(x E) W_read) W_write`, `y = N_ε(h_1) D`,

with `N_ε` applied to every token. For a flat direction `η`:

* Step 1 (the final normalization): `η_D = -Y D` for a matrix `Y`, and
  `D_θ h_1 η = h_1 Y + (h_1 Y_s h_1^⊤ / (d ε)) h_1` at every token, `Y_s = (Y + Y^⊤)/2`;
* Step 2 (large inputs): at the inputs `x = t w`, `t → ∞`, the term of order `t³` gives `Y_s = 0`:
  `Y` is antisymmetric;
* Step 3 (the skip): with `η^Y` the direction of the orthogonal changes of basis `I + τ Y + O(τ²)`
  shared by `h_0` and `h_1` (`cobDir θ (fun _ => Y)`), the direction `η' = η - η^Y` is flat, has
  `η'_D = 0` and `D_θ h_1 η' = 0` at every input, and the inputs `t w` give `η'_E = 0`.

What is left of `D_θ h_1 η' = 0` is the last clause of the statement below: the derivative of
`n ↦ f(n W_read) W_write` along the entries of `η'` at the weights of the block vanishes at every
`n = N_ε(x E)`. Step 4 of the paper starts there (`OneBlock/ResidualRMSMlp.lean`,
`OneBlock/ResidualRMSGated.lean`).

The steps do not depend on the kind of block: they are stated for an arbitrary continuously
differentiable map `f`, and for hidden states with the rows `T`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **Proof of Theorem B.1 (ii) of the skips paper, Steps 1 to 3, for one residual block under
pre-RMSNorm with `ε > 0`:** let `E` and `D` have rank `d`, and let `η` be flat. Then there is an
antisymmetric `Y` with `η_E = E Y` and `η_D = -Y D`, and the direction `η' = η - η^Y`, whose
entries at the block are `η_read + Y W_read` and `η_write - W_write Y`, satisfies: the derivative
of `n ↦ f(n W_read) W_write` along these entries vanishes at every `n = N_ε(x E)`. -/
theorem exists_antisymm_of_flat_residual_rmsNorm {A : Arch T d 1} {ε : ℝ} (hε : 0 < ε)
    (hA : A.χ = rmsNorm ε) (hf : ContDiff ℝ 1 (A.f 0)) (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (η : Params A dIn dOut) (hη : η ∈ flat A 1 θ) :
    ∃ Y : Matrix d d ℝ, Yᵀ = -Y ∧ η.E = θ.E * Y ∧ η.D = -(Y * θ.D) ∧
      ∀ x : Matrix T dIn ℝ,
        fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
            (rmsNorm ε (x * θ.E) * (η.read 0 + Y * θ.read 0)) * θ.write 0
          + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * (η.write 0 - θ.write 0 * Y) = 0 := by
  sorry

end Skips
