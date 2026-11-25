import SkipsLean.OneBlock.Factorization

/-!
# One block: the directions that keep `M`, `A` and `C`

Paper (skips paper), Lemma B.2 (The directions that keep `M`, `A` and `C`): "Let `E`, `D`,
`W_read` and `W_write` have rank `d_model`. A direction `η` keeps `C` and `A` fixed to first
order, `D_θ C η = 0` and `D_θ A η = 0`, if and only if

`η_E = E X`, `η_read = −X W_read`, `η_write = W_write Y`, `η_D = −Y D`

for some `X, Y ∈ ℝ^{d_model × d_model}`, and it keeps `M` fixed as well, `D_θ M η = 0`, if and only
if moreover `X = Y`. […] The matrices `X`, `Y` and vectors `g_0`, `g_1` are determined by the
direction, so these directions form a space of dimension `2 d_model²` without the skip and
`d_model²` with it, and `2 d_model` more with biases."

Here `C = E W_read`, `A = W_write D` and, in the residual network, `M = E D`, with the derivatives
`D_θ C η = η_E W_read + E η_read`, `D_θ A η = η_write D + W_write η_D` and
`D_θ M η = η_E D + E η_D`. The first "if and only if" is `keeps_products_iff_mem_range_cobDir`
(`OneBlock/Factorization.lean`, Lemma C.2 of the dimension paper), with
`η = cobDir θ ![X, Y]`. In this file: the second "if and only if", and the two dimensions (the
dimension of the span of the set of these directions, which is a subspace). Not stated: the
clauses with biases.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]
variable {A : Arch T d 1}

/-- **Lemma B.2 of the skips paper, "and it keeps `M` fixed as well […] if and only if moreover
`X = Y`":** for `E`, `D`, `W_read`, `W_write` of rank `d`, a direction `η` keeps `C = E W_read`,
`A = W_write D` and `M = E D` fixed to first order if and only if it is the direction of one
change of basis `X` at both hidden states: `η_E = E X`, `η_read = −X W_read`,
`η_write = W_write X`, `η_D = −X D`. -/
theorem keeps_products_and_ED_iff_mem_range_cobDir (θ η : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hr : (θ.read 0).rank = Fintype.card d) (hw : (θ.write 0).rank = Fintype.card d) :
    (η.E * θ.read 0 + θ.E * η.read 0 = 0 ∧ η.write 0 * θ.D + θ.write 0 * η.D = 0
        ∧ η.E * θ.D + θ.E * η.D = 0)
      ↔ ∃ X : Matrix d d ℝ, η = cobDir θ ![X, X] := by
  sorry

/-- **Lemma B.2, "these directions form a space of dimension `2 d_model²` without the skip":**
for `E`, `D`, `W_read`, `W_write` of rank `d`, the directions that keep `C` and `A` fixed to first
order span a space of dimension `2 d²` (they form a subspace; `X` and `Y` are determined by the
direction). -/
theorem finrank_span_keeps_products (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hr : (θ.read 0).rank = Fintype.card d) (hw : (θ.write 0).rank = Fintype.card d) :
    Module.finrank ℝ (Submodule.span ℝ {η : Params A dIn dOut |
        η.E * θ.read 0 + θ.E * η.read 0 = 0 ∧ η.write 0 * θ.D + θ.write 0 * η.D = 0})
      = 2 * Fintype.card d ^ 2 := by
  sorry

/-- **Lemma B.2, "and `d_model²` with it":** for `E`, `D`, `W_read`, `W_write` of rank `d`, the
directions that keep `C`, `A` and `M` fixed to first order span a space of dimension `d²`. -/
theorem finrank_span_keeps_products_and_ED (θ : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hr : (θ.read 0).rank = Fintype.card d) (hw : (θ.write 0).rank = Fintype.card d) :
    Module.finrank ℝ (Submodule.span ℝ {η : Params A dIn dOut |
        η.E * θ.read 0 + θ.E * η.read 0 = 0 ∧ η.write 0 * θ.D + θ.write 0 * η.D = 0
          ∧ η.E * θ.D + θ.E * η.D = 0})
      = Fintype.card d ^ 2 := by
  sorry

end Skips
