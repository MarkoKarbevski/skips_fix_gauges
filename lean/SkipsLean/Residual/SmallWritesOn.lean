import SkipsLean.Residual.SmallWrites
import SkipsLean.Residual.SmallParameterOn

/-!
# Residual networks with small writes, for blocks that are smooth on an open set

Paper (skips paper): proof of Lemma A.30 (ReLU-type blocks with small writes), second and third
paragraph: "With the writes `τ V_ℓ`, the pre-activations of block `ℓ` are `h_{ℓ−1} W_read^ℓ` with
`h_{ℓ−1} = x E + O(τ)`. So for `|τ|` below some `τ_0 > 0`, which depends on the parameters and on
the batch, every pre-activation on the batch has the sign of its limit. The outputs on the batch
are then polynomial in the parameters and in `τ`, the Jacobian on the batch, with its read columns
divided by `τ`, tends to `J_0`, and by lower semicontinuity it has rank at least
`P − d_model² − s` for all small `τ ≠ 0`. Near such parameters the signs on the batch do not
change […]. So the rank on the batch, which is at least `P − d_model² − s` by lower
semicontinuity, is exactly `P − d_model² − s`".

Stated here for any blocks without normalization whose fixed maps `f_ℓ` are twice continuously
differentiable on open sets `V_ℓ` of pre-activations (for ReLU-type blocks: the matrices with no
entry at the kink), and a finite batch `X` of inputs whose limit pre-activations
`x E W_read^ℓ` lie in the `V_ℓ`:

* for all small `τ ≠ 0` the pre-activations on the batch at `θ_τ` stay in the `V_ℓ`, and if every
  direction that is flat for the limit `J_0` (`smallWritesLimit`, `Residual/SmallWrites.lean`) on
  the batch lies in a subspace `W`, the Jacobian on the batch at `θ_τ` has rank at least
  `P − dim W`;
* at parameters whose pre-activations on a batch lie in the `V_ℓ`, the same holds nearby, and
  the rank of the Jacobian on the batch does not drop nearby.

The first is `eventually_funDim_smallWrites_ge` of `Residual/SmallWrites.lean` (analytic blocks,
all inputs) on one batch.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable (A : Arch T d L) (θ : Params A dIn dOut)

/-- **Proof of Lemma A.30, the rank at `θ_τ` on a batch:** blocks without normalization, `f_ℓ`
twice continuously differentiable on the open set `V ℓ`, a batch `X` with
`x E W_read^ℓ ∈ V ℓ`. For all small `τ ≠ 0` the pre-activations on the batch at `θ_τ` lie in the
`V ℓ`, and if every direction `η` with `(J_0 η)(x) = 0` on the batch lies in a subspace `W`, the
Jacobian of the residual network on the batch at `θ_τ` has rank at least `P − dim W`. -/
theorem eventually_jacobianRank_smallWrites_ge_of_contDiffOn (hA : A.χ = id)
    (V : ∀ ℓ, Set (Matrix T (A.r ℓ) ℝ)) (hVo : ∀ ℓ, IsOpen (V ℓ))
    (hf : ∀ ℓ, ContDiffOn ℝ 2 (A.f ℓ) (V ℓ))
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ) (hX : ∀ i ℓ, X i * θ.E * θ.read ℓ ∈ V ℓ)
    (W : Submodule ℝ (Params A dIn dOut))
    (hW : ∀ η : Params A dIn dOut, (∀ i, smallWritesLimit A θ η (X i) = 0) → η ∈ W) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      (∀ i ℓ, hidden A 1 (θ.smallWrites τ) (X i) ℓ.castSucc * θ.read ℓ ∈ V ℓ) ∧
      Module.finrank ℝ (Params A dIn dOut)
        ≤ jacobianRank A 1 X (θ.smallWrites τ) + Module.finrank ℝ W := by
  sorry

/-- **Proof of Lemma A.30, "Near such parameters the signs on the batch do not change" and the
lower semicontinuity of the rank:** blocks without normalization, any stream matrices, `f_ℓ`
continuously differentiable on the open set `V ℓ`, and parameters `θ` at which the
pre-activations on a batch `X` lie in the `V ℓ`. At every `θ'` near `θ` they still do, and the
rank of the Jacobian on the batch is at least its value at `θ`. -/
theorem eventually_jacobianRank_ge_of_contDiffOn (hA : A.χ = id) (S : Fin L → Matrix d d ℝ)
    (V : ∀ ℓ, Set (Matrix T (A.r ℓ) ℝ)) (hVo : ∀ ℓ, IsOpen (V ℓ))
    (hf : ∀ ℓ, ContDiffOn ℝ 1 (A.f ℓ) (V ℓ))
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i ℓ, hidden A S θ (X i) ℓ.castSucc * θ.read ℓ ∈ V ℓ) :
    ∀ᶠ θ' in 𝓝 θ,
      (∀ i ℓ, hidden A S θ' (X i) ℓ.castSucc * θ'.read ℓ ∈ V ℓ) ∧
      jacobianRank A S X θ ≤ jacobianRank A S X θ' := by
  sorry

end Skips
