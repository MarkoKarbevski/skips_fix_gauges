import SkipsLean.Residual.SmallWrites
import SkipsLean.Dimension.FunctionalBiases

/-!
# Residual networks with biases and small writes

Paper (skips paper), Lemma A.27 (Small writes): "With biases, `θ` also holds `b_E`, `b_read^ℓ`,
`b_write^ℓ` and `b_D`, and `θ_τ` holds `τ b_write^ℓ` in place of `b_write^ℓ`." Its proof, "MLP
blocks without normalization": "At `θ_τ` every hidden state is `h_ℓ = xE + b_E + O(τ)`, so the
output is

`y = xED + b_E D + b_D
  + τ ∑_ℓ (f((xE + b_E) W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ) D + O(τ²)`."

"Differentiating along `η` and letting `τ → 0`,
`(J_0 η)(x) = x ψ_M + ψ_γ + ∑_i (σ(z_i) ψ_{a_i} + σ'(z_i) (x ψ_{c_i} + ψ_{β_i}) a_i)`, where […]
`ψ_M = η_E D + E η_D`, `ψ_γ = η_{b_E} D + b_E η_D + η_{b_D} + ∑_ℓ η_{b_write^ℓ} D`,
`ψ_C = E η_read`, `ψ_β = b_E η_read + η_{b_read}`, `ψ_A = η_write D`."

Here, for the networks with biases of `Network/Biases.lean`, the twins of the definitions and
statements of `Residual/SmallWrites.lean`:

* `smallWritesB p τ`: the weights and biases `θ_τ`: the writes `τ W_write^ℓ` and the write biases
  `τ b_write^ℓ`, everything else as in `p = (θ, b)`.
* `smallWritesLimitB A p η x`: the limit `(J_0 η)(x)`, written for arbitrary differentiable maps
  `f_ℓ`: with `h = xE + b_E`,
  `x ψ_M + ψ_γ + ∑_ℓ (D f_ℓ(h W_read^ℓ + b_read^ℓ)(h η_read^ℓ + η_{b_read^ℓ}) W_write^ℓ
  + f_ℓ(h W_read^ℓ + b_read^ℓ) η_write^ℓ) D` (here `x ψ_C + ψ_β = h η_read + η_{b_read}`).
* `evalB_smallWritesB_zero`, `hasDerivAt_evalB_smallWritesB`: the two terms of the expansion of
  `y`.
* `eventually_funDimB_smallWritesB_ge`: the last paragraph of the proof ("The rank"): if the flat
  directions of `J_0` lie in a space `V`, then `fd(θ_τ) ≥ P − dim V` for all small `τ ≠ 0`, `P`
  counting the biases.

Numeric check: `ai_notes/small_writes_biases_check_2026-11-25.py`.
-/

namespace Skips

open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **The weights and biases `θ_τ` of Lemma A.27 with biases:** the embedding, the reads, the
readout, the embedding bias, the read biases and the readout bias of `p = (θ, b)`, the writes
`τ W_write^ℓ` and the write biases `τ b_write^ℓ`. -/
def smallWritesB {A : Arch T d L} (p : ParamsB A dIn dOut) (τ : ℝ) : ParamsB A dIn dOut :=
  (p.1.smallWrites τ,
    { E := p.2.E
      read := p.2.read
      write := fun ℓ => τ • p.2.write ℓ
      D := p.2.D })

/-- **The limit `J_0` of the proof of Lemma A.27 with biases, at one input `x`,** without
normalization: with `h = xE + b_E`,
`(J_0 η)(x) = x (η_E D + E η_D) + (η_{b_E} D + b_E η_D + η_{b_D} + ∑_ℓ η_{b_write^ℓ} D)
+ ∑_ℓ (D f_ℓ(h W_read^ℓ + b_read^ℓ)(h η_read^ℓ + η_{b_read^ℓ}) W_write^ℓ
+ f_ℓ(h W_read^ℓ + b_read^ℓ) η_write^ℓ) D`, the row `ψ_γ` added to every token. -/
noncomputable def smallWritesLimitB (A : Arch T d L) (p η : ParamsB A dIn dOut)
    (x : Matrix T dIn ℝ) : Matrix T dOut ℝ :=
  x * (η.1.E * p.1.D + p.1.E * η.1.D)
    + Matrix.of (fun _ => η.2.E ᵥ* p.1.D + p.2.E ᵥ* η.1.D + η.2.D + ∑ ℓ, η.2.write ℓ ᵥ* p.1.D)
    + ∑ ℓ, (fderiv ℝ (A.f ℓ)
          ((x * p.1.E + Matrix.of fun _ => p.2.E) * p.1.read ℓ + Matrix.of fun _ => p.2.read ℓ)
          ((x * p.1.E + Matrix.of fun _ => p.2.E) * η.1.read ℓ + Matrix.of fun _ => η.2.read ℓ)
          * p.1.write ℓ
        + A.f ℓ
          ((x * p.1.E + Matrix.of fun _ => p.2.E) * p.1.read ℓ + Matrix.of fun _ => p.2.read ℓ)
          * η.1.write ℓ) * p.1.D

variable (A : Arch T d L) (p : ParamsB A dIn dOut)

/-- At `τ = 0` the residual network with biases, without normalization, computes
`x ↦ (xE + b_E) D + b_D` (proof of Lemma A.27: "`y = xED + b_E D + b_D + τ (…) + O(τ²)`"). -/
theorem evalB_smallWritesB_zero (hA : A.χ = id) (x : Matrix T dIn ℝ) :
    evalB A 1 (smallWritesB p 0).1 (smallWritesB p 0).2 x
      = (x * p.1.E + Matrix.of fun _ => p.2.E) * p.1.D + Matrix.of fun _ => p.2.D := by
  sorry

/-- **The term of order `τ` of the output at `θ_τ`, with biases** (proof of Lemma A.27, the
expansion of `y`): the derivative of `τ ↦ F_{θ_τ}(x)` at `τ = 0` is
`∑_ℓ (f_ℓ((xE + b_E) W_read^ℓ + b_read^ℓ) W_write^ℓ + b_write^ℓ) D`. -/
theorem hasDerivAt_evalB_smallWritesB (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (x : Matrix T dIn ℝ) :
    HasDerivAt (fun τ : ℝ => evalB A 1 (smallWritesB p τ).1 (smallWritesB p τ).2 x)
      ((∑ ℓ, (A.f ℓ ((x * p.1.E + Matrix.of fun _ => p.2.E) * p.1.read ℓ
            + Matrix.of fun _ => p.2.read ℓ) * p.1.write ℓ
          + Matrix.of fun _ => p.2.write ℓ)) * p.1.D) 0 := by
  sorry

/-- **Proof of Lemma A.27, "The rank", with biases, for real-analytic blocks without
normalization:** if every direction of weights and biases that is flat for `J_0` lies in a
subspace `V`, then for all small `τ ≠ 0` the residual network has `fd(θ_τ) ≥ P − dim V`, with `P`
counting the biases. -/
theorem eventually_funDimB_smallWritesB_ge (hA : A.χ = id)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (V : Submodule ℝ (ParamsB A dIn dOut))
    (hV : ∀ η : ParamsB A dIn dOut, (∀ x, smallWritesLimitB A p η x = 0) → η ∈ V) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      Module.finrank ℝ (ParamsB A dIn dOut)
        ≤ funDimB A 1 (smallWritesB p τ) + Module.finrank ℝ V := by
  sorry

end Skips
