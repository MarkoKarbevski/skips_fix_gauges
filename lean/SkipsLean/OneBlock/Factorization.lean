import SkipsLean.Dimension.UpperBound

/-!
# One block: the directions that keep `C = E W_read` and `A = W_write D`

Paper (dimension paper): Lemma C.2. With one block and without normalization the parameters enter
the function only through `C = E W_read` and `A = W_write D`. A direction `η` keeps `C` and `A`
fixed to first order,

  `η_E W_read + E η_read = 0`  and  `η_write D + W_write η_D = 0`,

if and only if it is the direction of two changes of basis, `X` at `h_0` and `Y` at `h_1`:
`η_E = E X`, `η_read = -X W_read`, `η_write = W_write Y`, `η_D = -Y D`, that is,
`η = cobDir θ (X, Y)`. The direction "only if" uses that `E`, `D`, `W_read` and `W_write` have
rank `d`.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]
variable {A : Arch T d 1}

/-- **Lemma C.2.** -/
theorem keeps_products_iff_mem_range_cobDir (θ η : Params A dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hr : (θ.read 0).rank = Fintype.card d) (hw : (θ.write 0).rank = Fintype.card d) :
    (η.E * θ.read 0 + θ.E * η.read 0 = 0 ∧ η.write 0 * θ.D + θ.write 0 * η.D = 0)
      ↔ ∃ X : Fin 2 → Matrix d d ℝ, η = cobDir θ X := by
  sorry

end Skips
