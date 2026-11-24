import SkipsLean.OneBlock.LearnedSkipSteps
import SkipsLean.Depth.StepTanhRMS

/-!
# One block under pre-RMSNorm: a full learned skip against the identity skip

Paper (skips paper): Theorem 4.6 (ii): "A learned skip raises it by exactly
`d_model (d_model + 1)/2` more than an identity skip." Proof of Theorem B.1 (iii), `ε > 0`,
Step 4: "The flat direction `η′ = η − η^rot` has the entries `E X_s`, `−X_s A` and `0` at `E`, `A`
and `D`, so Step 3 applies to it with `X_s` in place of `X` and `0` in place of `Y`, and
`D_θ g η′ = 0`. The change `n X_s` of the input moves the block as the entries `X_s W_read` at
`W_read` do […]. So, with `ψ` the entries of `η′` at the weights of the block plus these,
`∂_ψ B(n) = q(n) 𝐃B(n) n` (17) for every `n` in the image of `N_ε` […]. We show that `q = 0`,
hence `X_s = 0`." Step 5: "With `X_s = 0`, the direction `η′` moves only the weights of the block,
and by (17) `B(n)` has derivative zero along it on the whole ball. So `η′` lies in the space `K_B`
of such directions, which is the space found in Step 4 of part (ii), and every direction of `K_B`
is flat. Hence `K(θ)` is spanned by the directions `η^rot` and `K_B`, as for the residual network
with its single rotation […]. So `K(θ)` is larger than for the residual network by
`d_model (d_model − 1)/2` […] while the network has `d_model²` […] more parameters. In both
cases the functional dimension is larger by `d_model (d_model + 1)/2`."

Here, with `q(n) = n X_s nᵀ / d` and `B(n) = f(n W_read) W_write`:

* `NoSymmetricPart A ε θ U`: the conclusion of Step 4 as a condition on the weights `θ` of the
  block, "equation (17) at the inputs of `U` forces `X_s = 0`". Equation (17) is written with the
  derivative of `N_ε`: `𝐃B(n)(n X − q(n) n) + ∂_ψ B(n) = 0` at `n = N_ε(x E)`, where
  `n X − q(n) n = tangentRMS X n` (`fderiv_rmsNorm_mul`).
* Steps 3 and 5, once for all kinds of block: under this condition, with `E` and `D` of rank `d`
  and an invertible skip `A`, the network with the full learned skip has at `(θ, A)` exactly
  `d (d + 1)/2` more functional dimension than the residual network at the same `θ`
  (`funDimLearned_eq_funDim_residual_add_of_noSymmetricPart`, for a block that is continuously
  differentiable).
* The same for a block that is continuously differentiable on an open cone `V` of pre-activations
  (ReLU, ReLU², ReGLU blocks: the matrices with no hidden unit at its kink), where "flat" is taken
  at the inputs `x` with `x E W_read ∈ V`: there the directions of the block along which `B` has
  derivative zero at these inputs must be symmetries inside the block (the hypothesis `hK`; for
  these blocks they are the rescalings of the hidden units, by Lemma B.3). The statement also gives
  a batch of such inputs on which the Jacobian has the functional dimension as its rank, which is
  the paper's functional dimension for these blocks.

The condition `NoSymmetricPart` is proved kind by kind: by homogeneity for ReLU, ReLU² and ReGLU
blocks (`OneBlock/LearnedSkipRescale.lean`, `OneBlock/LearnedSkipReGLU.lean`), and on inputs of two
tokens for attention blocks (`OneBlock/LearnedSkipAttention.lean`).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The conclusion of Step 4 of the proof of Theorem B.1 (iii), as a condition on `θ`:** if for
a symmetric `X` and entries `ψ_read`, `ψ_write` at the weights of the block equation (17) holds at
every input `x` of `U`, that is

  `𝐃f(n W_read)((n X − q(n) n) W_read + n ψ_read) W_write + f(n W_read) ψ_write = 0`

at `n = N_ε(x E)`, with `q(n) = n X nᵀ / d` row by row, then `X = 0`. -/
def NoSymmetricPart (A : Arch T d 1) (ε : ℝ) (θ : Params A dIn dOut) (U : Set (Matrix T dIn ℝ)) :
    Prop :=
  ∀ (X : Matrix d d ℝ) (ψr : Matrix d (A.r 0) ℝ) (ψw : Matrix (A.w 0) d ℝ), Xᵀ = X →
    (∀ x ∈ U,
      fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0)
          (tangentRMS X (rmsNorm ε (x * θ.E)) * θ.read 0 + rmsNorm ε (x * θ.E) * ψr)
          * θ.write 0
        + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * ψw = 0) →
    X = 0

/-- **Theorem 4.6 (ii), "A learned skip raises it by exactly `d (d + 1)/2` more than an identity
skip", at one parameter, for a continuously differentiable block (`ε > 0`):** if `E` and `D` have
rank `d`, the skip `A = R 0` is invertible and Step 4 holds at `θ` (`NoSymmetricPart` at all
inputs), the network with the full learned skip has at `(θ, A)` the functional dimension of the
residual network at `θ` plus `d (d + 1)/2`. -/
theorem funDimLearned_eq_funDim_residual_add_of_noSymmetricPart {A : Arch T d 1} {ε : ℝ}
    (hε : 0 < ε) (hA : A.χ = rmsNorm ε) (hf : ContDiff ℝ 1 (A.f 0)) (θ : Params A dIn dOut)
    (R : Fin 1 → Matrix d d ℝ) (hE : θ.E.rank = Fintype.card d)
    (hD : θ.D.rank = Fintype.card d) (hR : IsUnit (R 0).det)
    (hX : NoSymmetricPart A ε θ Set.univ) :
    funDimLearned A (θ, R)
      = funDim A 1 θ + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **The same for a block that is continuously differentiable on an open cone `V` of
pre-activations (`ε > 0`):** let `V` be open and invariant under positive scalings of the rows,
let some input with equal rows have its pre-activation `x E W_read` in `V`, let `E` and `D` have
rank `d` and the skip `A = R 0` be invertible. If Step 4 holds at the inputs with
`x E W_read ∈ V`, and every direction of the weights of the block along which
`B(n) = f(n W_read) W_write` has derivative zero at `n = N_ε(x E)` for these inputs is spanned by
directions of symmetries inside the block, then the network with the full learned skip has at
`(θ, A)` the functional dimension of the residual network at `θ` plus `d (d + 1)/2`, and a finite
batch of such inputs has a Jacobian of this rank. -/
theorem funDimLearned_eq_funDim_residual_add_of_noSymmetricPart_on {A : Arch T d 1} {ε : ℝ}
    (hε : 0 < ε) (hA : A.χ = rmsNorm ε) (V : Set (Matrix T (A.r 0) ℝ)) (hV : IsOpen V)
    (hVs : ∀ M ∈ V, ∀ c : T → ℝ, (∀ t, 0 < c t) → (Matrix.of fun t i => c t * M t i) ∈ V)
    (hf : ContDiffOn ℝ 1 (A.f 0) V) (θ : Params A dIn dOut) (R : Fin 1 → Matrix d d ℝ)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d) (hR : IsUnit (R 0).det)
    (hw : ∃ w : dIn → ℝ, (Matrix.of fun _ : T => w) * θ.E * θ.read 0 ∈ V)
    (hX : NoSymmetricPart A ε θ {x | x * θ.E * θ.read 0 ∈ V})
    (hK : ∀ ψ : Params A dIn dOut, ψ.E = 0 → ψ.D = 0 →
      (∀ x : Matrix T dIn ℝ, x * θ.E * θ.read 0 ∈ V →
        fderiv ℝ (A.f 0) (rmsNorm ε (x * θ.E) * θ.read 0) (rmsNorm ε (x * θ.E) * ψ.read 0)
            * θ.write 0
          + A.f 0 (rmsNorm ε (x * θ.E) * θ.read 0) * ψ.write 0 = 0) →
      ψ ∈ Submodule.span ℝ {η | InsideBlocks A θ η}) :
    funDimLearned A (θ, R) = funDim A 1 θ + Fintype.card d * (Fintype.card d + 1) / 2 ∧
      ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ), (∀ i, X i * θ.E * θ.read 0 ∈ V) ∧
        jacobianRankSkips A (ContinuousLinearMap.id ℝ (Fin 1 → Matrix d d ℝ)) X (θ, R)
          = funDimLearned A (θ, R) := by
  sorry

end Skips
