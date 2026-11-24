import SkipsLean.OneBlock.UnitsTanh
import SkipsLean.OneBlock.UnitsGELU

/-!
# Step 4 of the proof of Theorem B.1 (iii) for tanh and GELU units: `X_s = 0`

Paper (skips paper), proof of Theorem B.1 (iii), Step 4: "The change `n X_s` of the input moves
the block as the entries `X_s W_read` at `W_read` do […] So, with `ψ` the entries of `η′` at the
weights of the block plus these,

`∂_ψ B(n) = q(n) 𝐃B(n) n` (17)

for every `n` in the image of `N_ε`, the open ball of radius `√d_model`" (with
`q(n) = n X_s nᵀ / d_model`, `X_s` symmetric), and then: "For the other blocks both sides are analytic in `n`, so (17) holds for all `n`, and we
take `n = t n̂` with a fixed row `n̂` and `t → ∞`, as in the proof of Lemma B.3. For GELU the right
side is `t³ q(n̂) max(n̂ W_read, 0) W_write` up to terms that decay faster than any power of `t`,
and the left side is a polynomial of degree at most one in `t` up to such terms, so
`q(n̂) max(n̂ W_read, 0) W_write = 0`. […] For tanh the right side is
`4 t³ q(n̂) ∑_i (n̂ c_i) e^{−2|n̂ c_i| t} a_i` up to terms `O(t³ e^{−4|n̂ c_i| t})`; for the unit
`j` with the smallest `|n̂ c_j|`, the left side contributes a polynomial of degree one times
`e^{−2|n̂ c_j| t}` (proof of Lemma B.3), so `q(n̂)(n̂ c_j) a_j = 0`. […] In every case `q` vanishes
on an open set for generic parameters, so `X_s = 0`."

Here this step as a statement on vectors, with no network in it (a twin of Lemma B.3,
`UnitsRigid` in `OneBlock/Mlp.lean`, with the multiple `q(n) 𝐃B(n) n` on the right side in place
of `0`; the twin for positively homogeneous units and `ε = 0` is `UnitsRescaleSphere`). For units
`σ(x c_i) a_i`, `B(x) = ∑_i σ(x c_i) a_i`: with `ψc_i = X_s c_i + (ψ_read)_i` and `ψa = ψ_write`,
and with `X = X_s / d_model`, equation (17) reads

`∑_i [σ(x c_i) ψa_i + σ'(x c_i) (x ψc_i) a_i] = (x X xᵀ) ∑_i σ'(x c_i) (x c_i) a_i`.

The statement asks it on a nonempty open set of rows `x` (the paper: the ball) and concludes
`X = 0`, for at least one unit, nonzero rows `a_i`, and nonzero, pairwise non-collinear columns
`c_i` (the hypotheses of Lemma B.3; they hold at generic parameters). **No width is asked:** the
number of units and of coordinates are independent. Numeric check at 60 digits, also with fewer
units than coordinates: `units_no_symmetric_part_check_2026-11-24.py` (24 cases).
-/

namespace Skips

open Matrix

/-- **Step 4 of the proof of Theorem B.1 (iii) of the skips paper, as a property of an activation
`σ` with derivative `σ'`:** for units `σ(x c_i) a_i` with nonzero rows `a_i` and nonzero, pairwise
non-collinear columns `c_i`, a symmetric `X` and a direction `(ψc, ψa)`: if
`∑_i [σ(x c_i) ψa_i + σ'(x c_i) (x ψc_i) a_i] = (x X xᵀ) ∑_i σ'(x c_i) (x c_i) a_i` at every `x`
of a nonempty open set, then `X = 0`. Rows of the input are indexed by `n`, the coordinates of the
output by `k`, the hidden units by `q`. -/
def UnitsNoSymmetricPart (σ σ' : ℝ → ℝ) (n k q : Type*) [Fintype n] [Fintype k] [Fintype q] :
    Prop :=
  ∀ (c : q → n → ℝ) (a : q → k → ℝ) (X : Matrix n n ℝ) (ψc : q → n → ℝ) (ψa : q → k → ℝ)
    (O : Set (n → ℝ)),
    (∀ i, a i ≠ 0) → (∀ i, c i ≠ 0) → (∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) → Xᵀ = X →
    IsOpen O → O.Nonempty →
    (∀ x ∈ O, ∑ i, (σ (x ⬝ᵥ c i) • ψa i + (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ ψc i)) • a i)
      = ((x ᵥ* X) ⬝ᵥ x) • ∑ i, (σ' (x ⬝ᵥ c i) * (x ⬝ᵥ c i)) • a i) →
    X = 0

/-- **Step 4 for tanh units** (at least one unit): on a ray `x = t n̂` with distinct nonzero
`|n̂ c_i|`, the term of order `t³ e^{−2|n̂ c_j| t}`, for the unit `j` with the smallest `|n̂ c_j|`,
gives `(n̂ X n̂ᵀ)(n̂ c_j) a_j = 0`. -/
theorem tanh_unitsNoSymmetricPart (n k q : Type*) [Fintype n] [Fintype k] [Fintype q]
    [Nonempty q] : UnitsNoSymmetricPart Real.tanh (fun z => 1 - Real.tanh z ^ 2) n k q := by
  sorry

/-- **Step 4 for GELU units** (at least one unit): on a ray `x = t n̂` off the hyperplanes, the
term of order `t³` gives `(n̂ X n̂ᵀ) ∑_i max(n̂ c_i, 0) a_i = 0`, and the sum is nonzero on an open
set of directions. -/
theorem gelu_unitsNoSymmetricPart (n k q : Type*) [Fintype n] [Fintype k] [Fintype q]
    [Nonempty q] : UnitsNoSymmetricPart gelu geluDeriv n k q := by
  sorry

end Skips
