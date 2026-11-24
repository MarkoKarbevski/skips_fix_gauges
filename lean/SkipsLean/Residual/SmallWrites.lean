import SkipsLean.Residual.SmallParameter
import SkipsLean.Dimension.GenericRank

/-!
# Residual networks with small writes

Paper (skips paper): Lemma A.27 (Small writes) and its proof, for blocks without normalization
and without biases. For parameters `θ` and a number `τ`, the parameters `θ_τ` hold `τ W_write^ℓ` in
place of every write. At `θ_τ` every hidden state is `x E + O(τ)`, and the output is

  `y = x E D + τ ∑_ℓ f_ℓ(x E W_read^ℓ) W_write^ℓ D + O(τ²)`.

With `J_τ` the Jacobian of the outputs at `θ_τ` and `S_τ` the map that divides the coordinates of
the reads by `τ`, the limit `J_0 = lim_{τ → 0} J_τ S_τ` is, at one input `x`,

  `(J_0 η)(x) = x (η_E D + E η_D)
      + ∑_ℓ (D f_ℓ(x E W_read^ℓ)(x E η_read^ℓ) W_write^ℓ + f_ℓ(x E W_read^ℓ) η_write^ℓ) D`,

the formula of the paper with `ψ_M = η_E D + E η_D`, `ψ_C = E η_read` and `ψ_A = η_write D`,
written for arbitrary differentiable maps `f_ℓ`. A direction `η` is flat for `J_0` if
`(J_0 η)(x) = 0` for every input `x`. The last paragraph of the proof ("The rank") gives: if the
flat directions of `J_0` form a space of dimension `m`, then `fd(θ_τ) ≥ P - m` for all small
`τ ≠ 0`.

Here the limit is taken as in `Residual/SmallParameter.lean`: with `G τ θ` the outputs at `θ_τ` on
a batch, `G 0 θ = (x E D)_x` does not depend on the reads and the writes, and `∂_τ G(0, θ)` is the
sum over the blocks above. That the same `τ` multiplies the directions of the writes as well does
not change the rank for `τ ≠ 0`.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The parameters `θ_τ` of Lemma A.27:** the embedding, the reads and the readout of `θ`, and
the writes `τ W_write^ℓ`. -/
def Params.smallWrites {A : Arch T d L} (θ : Params A dIn dOut) (τ : ℝ) : Params A dIn dOut where
  E := θ.E
  read := θ.read
  write ℓ := τ • θ.write ℓ
  D := θ.D

/-- **The limit `J_0` of the proof of Lemma A.27, at one input `x`,** without normalization and
without biases: `(J_0 η)(x) = x (η_E D + E η_D) + ∑_ℓ (D f_ℓ(x E W_read^ℓ)(x E η_read^ℓ) W_write^ℓ
+ f_ℓ(x E W_read^ℓ) η_write^ℓ) D`. -/
noncomputable def smallWritesLimit (A : Arch T d L) (θ η : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  x * (η.E * θ.D + θ.E * η.D)
    + ∑ ℓ, (fderiv ℝ (A.f ℓ) (x * θ.E * θ.read ℓ) (x * θ.E * η.read ℓ) * θ.write ℓ
        + A.f ℓ (x * θ.E * θ.read ℓ) * η.write ℓ) * θ.D

variable (A : Arch T d L) (θ : Params A dIn dOut)

/-- At `τ = 0` the residual network without normalization computes `x ↦ x E D`
(proof of Lemma A.27: "`y = x E D + τ (…) + O(τ²)`"). -/
theorem eval_smallWrites_zero (hA : A.χ = id) (x : Matrix T dIn ℝ) :
    eval A 1 (θ.smallWrites 0) x = x * θ.E * θ.D := by
  sorry

/-- **The term of order `τ` of the output at `θ_τ`** (proof of Lemma A.27, the expansion of `y`):
the derivative of `τ ↦ F_{θ_τ}(x)` at `τ = 0` is `∑_ℓ f_ℓ(x E W_read^ℓ) W_write^ℓ D`. -/
theorem hasDerivAt_eval_smallWrites (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (x : Matrix T dIn ℝ) :
    HasDerivAt (fun τ : ℝ => eval A 1 (θ.smallWrites τ) x)
      ((∑ ℓ, A.f ℓ (x * θ.E * θ.read ℓ) * θ.write ℓ) * θ.D) 0 := by
  sorry

/-- **Proof of Lemma A.27, "The rank", for real-analytic blocks without normalization:** if every
direction that is flat for `J_0` lies in a subspace `V` of the parameters, then for all small
`τ ≠ 0` the residual network has `fd(θ_τ) ≥ P - dim V`. -/
theorem eventually_funDim_smallWrites_ge (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (V : Submodule ℝ (Params A dIn dOut))
    (hV : ∀ η : Params A dIn dOut, (∀ x, smallWritesLimit A θ η x = 0) → η ∈ V) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      Module.finrank ℝ (Params A dIn dOut)
        ≤ funDim A 1 (θ.smallWrites τ) + Module.finrank ℝ V := by
  sorry

end Skips
