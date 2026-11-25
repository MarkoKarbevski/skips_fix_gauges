import SkipsLean.OneBlock.UnitsNoSymmetricPart
import SkipsLean.OneBlock.UnitsSwiGLU
import SkipsLean.OneBlock.UnitsGeGLU
import SkipsLean.OneBlock.UnitsReGLU

/-!
# Step 4 of the proof of Theorem B.1 (iii) for SwiGLU and GeGLU units: `X_s = 0`

Paper (skips paper), proof of Theorem B.1 (iii), Step 4, equation (17),
`∂_ψ B(n) = q(n) 𝐃B(n) n` "for every `n` in the image of `N_ε`, the open ball of radius
`√d_model`", and then: "For the other blocks both sides are analytic in `n`, so (17) holds for all
`n`, and we take `n = t n̂` with a fixed row `n̂` and `t → ∞`, as in the proof of Lemma B.3. […]
SwiGLU and GeGLU units `σ(n c_i) (n e_i) a_i` give
`2 t⁴ q(n̂) ∑_{i: n̂ c_i > 0} (n̂ c_i)(n̂ e_i) a_i` against a polynomial of degree two. […] In every
case `q` vanishes on an open set for generic parameters, so `X_s = 0`."

Here this step as a statement on vectors, the twin for gated units of `UnitsNoSymmetricPart`
(`OneBlock/UnitsNoSymmetricPart.lean`). For units `σ(x c_i) (x e_i) a_i` with gate columns `c_i`,
value columns `e_i` and rows `a_i`, `B(x) = ∑_i σ(x c_i) (x e_i) a_i`, a direction
`(ψc, ψe, ψa)` and a symmetric `X` (the paper's `X_s / d_model`), equation (17) reads

`∑_i [σ(x c_i)(x e_i) ψa_i + σ'(x c_i)(x ψc_i)(x e_i) a_i + σ(x c_i)(x ψe_i) a_i]`
`  = (x X xᵀ) ∑_i [σ'(x c_i)(x c_i)(x e_i) + σ(x c_i)(x e_i)] a_i`.

The statement asks it on a nonempty open set of rows `x` and concludes `X = 0`, for at least one
unit, nonzero rows `a_i`, nonzero and pairwise non-collinear gate columns `c_i` and nonzero value
columns `e_i` (the hypotheses of `GatedUnitsRescale`, Lemma B.3 for gated units). No width is
asked. Numeric check at 60 digits, also with fewer units than coordinates:
`gated_units_no_symmetric_part_check_2026-11-25.py` (12 cases: the solutions are the rescalings
of the values, with `X = 0`).
-/

namespace Skips

open Matrix

/-- **Step 4 of the proof of Theorem B.1 (iii) of the skips paper for gated units, as a property
of a gate activation `σ` with derivative `σ'`:** for units `σ(x c_i) (x e_i) a_i` with nonzero rows
`a_i`, nonzero and pairwise non-collinear gate columns `c_i` and nonzero value columns `e_i`, a
symmetric `X` and a direction `(ψc, ψe, ψa)`: if the derivative of `B` along the direction equals
`(x X xᵀ)` times the derivative of `B` along `x` at every `x` of a nonempty open set, then
`X = 0`. -/
def GatedUnitsNoSymmetricPart (σ σ' : ℝ → ℝ) (n k q : Type*) [Fintype n] [Fintype k]
    [Fintype q] : Prop :=
  ∀ (c e : q → n → ℝ) (a : q → k → ℝ) (X : Matrix n n ℝ) (ψc ψe : q → n → ℝ) (ψa : q → k → ℝ)
    (O : Set (n → ℝ)),
    (∀ i, a i ≠ 0) → (∀ i, c i ≠ 0) → (∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) →
    (∀ i, e i ≠ 0) → Xᵀ = X → IsOpen O → O.Nonempty →
    (∀ x ∈ O, ∑ i, ((σ (x ⬝ᵥ c i) * (x ⬝ᵥ e i)) • ψa i
        + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i) * (x ⬝ᵥ e i)) • a i
        + (σ (x ⬝ᵥ c i) * (x ⬝ᵥ ψe i)) • a i)
      = ((x ᵥ* X) ⬝ᵥ x) • ∑ i,
          (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ c i) * (x ⬝ᵥ e i) + σ (x ⬝ᵥ c i) * (x ⬝ᵥ e i)) • a i) →
    X = 0

/-- **Step 4 for SwiGLU units** (at least one unit): on a ray `x = t n̂` the term of order `t⁴`
gives `(n̂ X n̂ᵀ) ∑_i max(n̂ c_i, 0) (n̂ e_i) a_i = 0`, and the sum is nonzero on an open set of
directions. -/
theorem silu_gatedUnitsNoSymmetricPart (n k q : Type*) [Fintype n] [Fintype k] [Fintype q]
    [Nonempty q] : GatedUnitsNoSymmetricPart silu siluDeriv n k q := by
  sorry

/-- **Step 4 for GeGLU units** (at least one unit). -/
theorem gelu_gatedUnitsNoSymmetricPart (n k q : Type*) [Fintype n] [Fintype k] [Fintype q]
    [Nonempty q] : GatedUnitsNoSymmetricPart gelu geluDeriv n k q := by
  sorry

end Skips
