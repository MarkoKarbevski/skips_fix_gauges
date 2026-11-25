import SkipsLean.OneBlock.KeepsProducts
import SkipsLean.Symmetry.BiasesFlat

/-!
# One block with biases: the directions that keep `M`, `A`, `C`, `β` and `γ`

Paper (skips paper), Lemma B.2 (The directions that keep `M`, `A` and `C`): "With biases, it keeps
`β` and `γ_0`, respectively `β` and `γ`, fixed as well if and only if moreover
`η_{b_E} = b_E X + g_0`, `η_{b_read} = −g_0 W_read`, `η_{b_write} = b_write Y + g_1` and
`η_{b_D} = −g_1 D`, respectively `η_{b_D} = −(g_0 + g_1) D`, for some row vectors
`g_0, g_1 ∈ ℝ^{1×d_model}`. The matrices `X`, `Y` and vectors `g_0`, `g_1` are determined by the
direction, so these directions form a space of dimension `2 d_model²` without the skip and
`d_model²` with it, and `2 d_model` more with biases."

Here (Appendix B, "Reduction") `C = E W_read`, `A = W_write D`, `M = E D`,
`β = b_E W_read + b_read`, `γ_0 = b_write D + b_D`, `γ = b_E D + γ_0`, with the derivatives along
a direction `η` of weights and biases

`D β η = η_{b_E} W_read + b_E η_read + η_{b_read}`,
`D γ_0 η = η_{b_write} D + b_write η_D + η_{b_D}`,
`D γ η = η_{b_E} D + b_E η_D + D γ_0 η`.

The clauses without biases are in `OneBlock/Factorization.lean` and `OneBlock/KeepsProducts.lean`.
In this file, for one block of any kind with biases (`Network/Biases.lean`):

* `keeps_products_biases_iff`: `η` keeps `C`, `A`, `β`, `γ_0` to first order if and only if it is
  the direction of two changes of basis and two translations,
  `η = cobDirB p X + (0, translateAtDir θ g)` (`Symmetry/BiasesFlat.lean`);
* `keeps_products_and_ED_biases_iff`: `η` keeps `C`, `A`, `M`, `β`, `γ` if and only if
  `η = cobDirB p (X, X) + (0, translateDir θ g)`;
* the two dimensions with biases, `2 d² + 2 d` and `d² + 2 d` (the dimension of the span of the
  set of these directions, which is a subspace).
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {A : Arch T d 1}

/-- **Lemma B.2 of the skips paper with biases, without the skip:** for `E`, `D`, `W_read`,
`W_write` of rank `d`, a direction `η` of weights and biases keeps `C = E W_read`,
`A = W_write D`, `β = b_E W_read + b_read` and `γ_0 = b_write D + b_D` fixed to first order if and
only if it is the direction of changes of basis `X_0, X_1` and translations `g_0, g_1` of the two
hidden states: `η_E = E X_0`, `η_read = −X_0 W_read`, `η_write = W_write X_1`, `η_D = −X_1 D`,
`η_{b_E} = b_E X_0 + g_0`, `η_{b_read} = −g_0 W_read`, `η_{b_write} = b_write X_1 + g_1`,
`η_{b_D} = −g_1 D`. -/
theorem keeps_products_biases_iff (p η : ParamsB A dIn dOut)
    (hE : p.1.E.rank = Fintype.card d) (hD : p.1.D.rank = Fintype.card d)
    (hr : (p.1.read 0).rank = Fintype.card d) (hw : (p.1.write 0).rank = Fintype.card d) :
    (η.1.E * p.1.read 0 + p.1.E * η.1.read 0 = 0 ∧
      η.1.write 0 * p.1.D + p.1.write 0 * η.1.D = 0 ∧
      η.2.E ᵥ* p.1.read 0 + p.2.E ᵥ* η.1.read 0 + η.2.read 0 = 0 ∧
      η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D + η.2.D = 0) ↔
    ∃ (X : Fin 2 → Matrix d d ℝ) (g : Fin 2 → d → ℝ),
      η = cobDirB p X + (0, translateAtDir p.1 g) := by
  sorry

/-- **Lemma B.2 of the skips paper with biases, with the skip:** for `E`, `D`, `W_read`,
`W_write` of rank `d`, a direction `η` of weights and biases keeps `C`, `A`, `M = E D`, `β` and
`γ = b_E D + b_write D + b_D` fixed to first order if and only if it is the direction of one
change of basis `X` of both hidden states and of the translations `g_0, g_1` of Lemma A.8:
`η_{b_E} = b_E X + g_0`, `η_{b_read} = −g_0 W_read`, `η_{b_write} = b_write X + g_1`,
`η_{b_D} = −(g_0 + g_1) D`. -/
theorem keeps_products_and_ED_biases_iff (p η : ParamsB A dIn dOut)
    (hE : p.1.E.rank = Fintype.card d) (hD : p.1.D.rank = Fintype.card d)
    (hr : (p.1.read 0).rank = Fintype.card d) (hw : (p.1.write 0).rank = Fintype.card d) :
    (η.1.E * p.1.read 0 + p.1.E * η.1.read 0 = 0 ∧
      η.1.write 0 * p.1.D + p.1.write 0 * η.1.D = 0 ∧
      η.1.E * p.1.D + p.1.E * η.1.D = 0 ∧
      η.2.E ᵥ* p.1.read 0 + p.2.E ᵥ* η.1.read 0 + η.2.read 0 = 0 ∧
      η.2.E ᵥ* p.1.D + p.2.E ᵥ* η.1.D
        + (η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D + η.2.D) = 0) ↔
    ∃ (X : Matrix d d ℝ) (g : Fin 2 → d → ℝ),
      η = cobDirB p (fun _ => X) + (0, translateDir p.1 g) := by
  sorry

/-- **Lemma B.2 with biases, "a space of dimension `2 d_model²` without the skip […] and
`2 d_model` more with biases":** for `E`, `D`, `W_read`, `W_write` of rank `d`, the directions
that keep `C`, `A`, `β` and `γ_0` fixed to first order span a space of dimension `2 d² + 2 d`
(they form a subspace; `X_0`, `X_1`, `g_0`, `g_1` are determined by the direction). -/
theorem finrank_span_keeps_products_biases (p : ParamsB A dIn dOut)
    (hE : p.1.E.rank = Fintype.card d) (hD : p.1.D.rank = Fintype.card d)
    (hr : (p.1.read 0).rank = Fintype.card d) (hw : (p.1.write 0).rank = Fintype.card d) :
    Module.finrank ℝ (Submodule.span ℝ {η : ParamsB A dIn dOut |
      η.1.E * p.1.read 0 + p.1.E * η.1.read 0 = 0 ∧
      η.1.write 0 * p.1.D + p.1.write 0 * η.1.D = 0 ∧
      η.2.E ᵥ* p.1.read 0 + p.2.E ᵥ* η.1.read 0 + η.2.read 0 = 0 ∧
      η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D + η.2.D = 0})
      = 2 * Fintype.card d ^ 2 + 2 * Fintype.card d := by
  sorry

/-- **Lemma B.2 with biases, "`d_model²` with it, and `2 d_model` more with biases":** for `E`,
`D`, `W_read`, `W_write` of rank `d`, the directions that keep `C`, `A`, `M`, `β` and `γ` fixed
to first order span a space of dimension `d² + 2 d`. -/
theorem finrank_span_keeps_products_and_ED_biases (p : ParamsB A dIn dOut)
    (hE : p.1.E.rank = Fintype.card d) (hD : p.1.D.rank = Fintype.card d)
    (hr : (p.1.read 0).rank = Fintype.card d) (hw : (p.1.write 0).rank = Fintype.card d) :
    Module.finrank ℝ (Submodule.span ℝ {η : ParamsB A dIn dOut |
      η.1.E * p.1.read 0 + p.1.E * η.1.read 0 = 0 ∧
      η.1.write 0 * p.1.D + p.1.write 0 * η.1.D = 0 ∧
      η.1.E * p.1.D + p.1.E * η.1.D = 0 ∧
      η.2.E ᵥ* p.1.read 0 + p.2.E ᵥ* η.1.read 0 + η.2.read 0 = 0 ∧
      η.2.E ᵥ* p.1.D + p.2.E ᵥ* η.1.D
        + (η.2.write 0 ᵥ* p.1.D + p.2.write 0 ᵥ* η.1.D + η.2.D) = 0})
      = Fintype.card d ^ 2 + 2 * Fintype.card d := by
  sorry

end Skips
