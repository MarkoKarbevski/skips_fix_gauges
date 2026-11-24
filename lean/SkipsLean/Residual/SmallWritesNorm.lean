import SkipsLean.Residual.SmallWrites

/-!
# Residual networks with small writes, with a normalization

Paper (skips paper): proof of Lemma A.27, paragraph "Under pre-RMSNorm". At `θ_τ` every hidden
state is `x E + O(τ)` and every block reads `N_ε(x E) + O(τ)`, so the output is

  `y = N_ε(x E) D + τ 𝐃N_ε(x E) (g(N_ε(x E))) D + O(τ²)`,  `g(n) = ∑_ℓ f_ℓ(n W_read^ℓ) W_write^ℓ`,

and, with `h = x E` and `n = N_ε(h)`,

  `(J_0 η)(x) = 𝐃N_ε(h) (x η_E + D_θ g(n) η) D + N_ε(h) η_D`,

"where `D_θ g(n) η` is the derivative of the wide block at the input `n` along the entries of `η`
at its reads and writes".

This file states the expansion, the limit `J_0` and the paragraph "The rank" as
`Residual/SmallWrites.lean` does without normalization, for an arbitrary map `χ` in the place of
`N_ε` (differentiable, resp. real-analytic). For `χ = id` the limit below is `smallWritesLimit`.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The limit `J_0` of the proof of Lemma A.27 under pre-RMSNorm, at one input `x`,** for a
map `χ` in the place of `N_ε`: `(J_0 η)(x) = 𝐃χ(h) (x η_E + D_θ g(n) η) D + χ(h) η_D` with
`h = x E`, `n = χ(h)` and
`D_θ g(n) η = ∑_ℓ (D f_ℓ(n W_read^ℓ)(n η_read^ℓ) W_write^ℓ + f_ℓ(n W_read^ℓ) η_write^ℓ)`. -/
noncomputable def smallWritesLimitNorm (A : Arch T d L) (θ η : Params A dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  fderiv ℝ A.χ (x * θ.E)
      (x * η.E + ∑ ℓ, (fderiv ℝ (A.f ℓ) (A.χ (x * θ.E) * θ.read ℓ) (A.χ (x * θ.E) * η.read ℓ)
            * θ.write ℓ
          + A.f ℓ (A.χ (x * θ.E) * θ.read ℓ) * η.write ℓ)) * θ.D
    + A.χ (x * θ.E) * η.D

variable (A : Arch T d L) (θ : Params A dIn dOut)

/-- At `τ = 0` the residual network computes `x ↦ χ(x E) D`
(proof of Lemma A.27 under pre-RMSNorm: "`y = N_ε(x E) D + τ (…) + O(τ²)`"). -/
theorem eval_smallWrites_zero_norm (x : Matrix T dIn ℝ) :
    eval A 1 (θ.smallWrites 0) x = A.χ (x * θ.E) * θ.D := by
  sorry

/-- **The term of order `τ` of the output at `θ_τ`, with a normalization** (proof of Lemma A.27
under pre-RMSNorm, the expansion of `y`): the derivative of `τ ↦ F_{θ_τ}(x)` at `τ = 0` is
`𝐃χ(x E) (∑_ℓ f_ℓ(χ(x E) W_read^ℓ) W_write^ℓ) D`. -/
theorem hasDerivAt_eval_smallWrites_norm (hχ : Differentiable ℝ A.χ)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (x : Matrix T dIn ℝ) :
    HasDerivAt (fun τ : ℝ => eval A 1 (θ.smallWrites τ) x)
      (fderiv ℝ A.χ (x * θ.E) (∑ ℓ, A.f ℓ (A.χ (x * θ.E) * θ.read ℓ) * θ.write ℓ) * θ.D) 0 := by
  sorry

/-- **Proof of Lemma A.27, "The rank", for real-analytic blocks and a real-analytic `χ`:** if
every direction that is flat for `J_0` lies in a subspace `V` of the parameters, then for all
small `τ ≠ 0` the residual network has `fd(θ_τ) ≥ P - dim V`. -/
theorem eventually_funDim_smallWrites_ge_norm (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (V : Submodule ℝ (Params A dIn dOut))
    (hV : ∀ η : Params A dIn dOut, (∀ x, smallWritesLimitNorm A θ η x = 0) → η ∈ V) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      Module.finrank ℝ (Params A dIn dOut)
        ≤ funDim A 1 (θ.smallWrites τ) + Module.finrank ℝ V := by
  sorry

end Skips
