import SkipsLean.Absorb.BiasesConstructions
import SkipsLean.Absorb.SameWidth

/-!
# Gated blocks with biases along rays: the two identities of Lemma C.8

Paper (absorb paper), Appendix C.2. "For a unit `j` of a gated block with biases, let
`Δ_j = (b^g_j v_j + b^v_j g_j) ŵ_j`, a `d_model × d_model` matrix of rank at most one."

Proof of Lemma C.8 (Gated blocks with biases), "Outline. Along rays `x = t u` with `t → ∞`, every
gate becomes a ReLU gate. The terms of order `t²` and `t` of (2) then split hyperplane by
hyperplane […]. Expansion along rays. […] For `x ∉ H` and `t → ∞`,
`σ(t x g + b^g) = t η ReLU(s x ν) + b^g [s x ν > 0] + o(1/t)`, exactly for large `t` when `σ` is
ReLU, and up to terms that decay exponentially in `t` when `σ` is SiLU or GELU. So the unit
contributes `t² ReLU(s x ν) (x v) η ŵ + t (ReLU(s x ν) η b^v ŵ + [s x ν > 0] (x v) b^g ŵ) + O(1)`,
and a unit with gate read `0` contributes `t σ(b^g) (x v) ŵ + O(1)`. Put `t x` into (2) and compare
the coefficients of `t²` and of `t` at each `x` off all the hyperplanes."

Here this step is stated in the following form. At an input `x` off the hyperplanes `x g_j = 0` of
the units with a nonzero gate read (of both blocks), a unit whose gate is open at `x` (`x g_j > 0`)
contributes `t² (x g_j)(x v_j) ŵ_j + t x Δ_j + O(1)` at `t x`, a unit whose gate is closed
contributes `O(1)`, and a unit with gate read `0` contributes `t σ(b^g_j) (x v_j) ŵ_j + O(1)`. The
set of open gates is the same at all inputs near `x`, so the coefficients of `t` and of `t²` give
an identity of matrices and an identity of quadratic maps:

* `M + Λ_θ(x) = Λ_{θ′}(x)`, with `Λ_θ(x)` the sum of the `Δ_j` over the units open at `x`, plus
  the sum of `σ(b^g_j) v_j ŵ_j` over the units with gate read `0` (`gateLinear`);
* `Q_θ(x, y) = Q_{θ′}(x, y)` for every `y`, with `Q_θ(x, y)` the sum of `(y g_j)(y v_j) ŵ_j` over
  the units open at `x` (`gateQuadratic`).

The paper's two identities (sums over the hyperplanes of `ReLU(±x ν)` terms) are these, read on
the two sides of each hyperplane. What the step uses of the gate is that it is at a distance
`O(1/|z|)` from ReLU (`NearReLU`): ReLU, SiLU and GELU are. `NearReLU`, `gateLinear` and
`gateQuadratic` are not notions of the paper.
-/

namespace Skips

open Matrix

variable {p q m m' : Type*} [Fintype p] [Fintype m] [Fintype m']

/-- **A gate at a distance `O(1/|z|)` from ReLU:** `(1 + |z|) |σ(z) − ReLU(z)|` is bounded. (ReLU,
SiLU and GELU: for the last two the distance decays exponentially.) -/
def NearReLU (σ : ℝ → ℝ) : Prop := ∃ K : ℝ, ∀ z, (1 + |z|) * |σ z - relu z| ≤ K

/-- ReLU is at a distance `O(1/|z|)` from ReLU. -/
theorem nearReLU_relu : NearReLU relu := by
  sorry

/-- SiLU is at a distance `O(1/|z|)` from ReLU: `|SiLU(z) − ReLU(z)| = |z| / (1 + e^{|z|})`. -/
theorem nearReLU_silu : NearReLU silu := by
  sorry

/-- GELU is at a distance `O(1/|z|)` from ReLU: `|GELU(z) − ReLU(z)| = |z| Φ(−|z|)`. -/
theorem nearReLU_gelu : NearReLU gelu := by
  sorry

/-- **The matrix `Δ_j = (b^g_j v_j + b^v_j g_j) ŵ_j` of a unit of a gated block with biases**
(absorb paper, Appendix C.2), of rank at most one: the column `b^g_j v_j + b^v_j g_j` times the
row `ŵ_j`. -/
def gateDelta (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ)
    (Ww : Matrix m q ℝ) (j : m) : Matrix p q ℝ :=
  Matrix.of fun a o => (bg j * Wv a j + bv j * Wg a j) * Ww j o

open scoped Classical in
/-- **The coefficient of `t` of a gated block with biases at `t x`,** for `x` off the hyperplanes,
as a matrix `Λ` with coefficient `x Λ`: the sum of the `Δ_j` over the units whose gate is open at
`x` (`x g_j > 0`), plus the sum of `σ(b^g_j) v_j ŵ_j` over the units with gate read `0`. -/
noncomputable def gateLinear (σ : ℝ → ℝ) (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ)
    (bv : m → ℝ) (Ww : Matrix m q ℝ) (x : p → ℝ) : Matrix p q ℝ :=
  (∑ j, if 0 < (x ᵥ* Wg) j then gateDelta Wg bg Wv bv Ww j else 0)
    + ∑ j, if Wgᵀ j = 0 then Matrix.of (fun a o => σ (bg j) * Wv a j * Ww j o) else 0

open scoped Classical in
/-- **The coefficient of `t²` of a gated block with biases at `t y`,** for `y` in the cell of `x`:
the sum of `(y g_j)(y v_j) ŵ_j` over the units whose gate is open at `x`. -/
noncomputable def gateQuadratic (Wg Wv : Matrix p m ℝ) (Ww : Matrix m q ℝ) (x y : p → ℝ) :
    q → ℝ :=
  ∑ j, if 0 < (x ᵥ* Wg) j then ((y ᵥ* Wg) j * (y ᵥ* Wv) j) • Ww j else 0

/-- **Proof of Lemma C.8 of the absorb paper, "Expansion along rays", with the comparison of the
coefficients of `t²` and of `t`:** let the gate `σ` be at a distance `O(1/|z|)` from ReLU, and let
gated blocks with biases `B_θ` and `B_{θ′}`, of any widths, satisfy `x M + B_θ(x) = B_{θ′}(x)` for
all `x`. Then at every `x` off the hyperplanes `x g_j = 0` of the units of both blocks with a
nonzero gate read: `M + Λ_θ(x) = Λ_{θ′}(x)`, and `Q_θ(x, y) = Q_{θ′}(x, y)` for every `y`. -/
theorem gateLinear_gateQuadratic_of_gatedBlockB_absorb {σ : ℝ → ℝ} (hσ : NearReLU σ)
    (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (Wg' : Matrix p m' ℝ) (bg' : m' → ℝ) (Wv' : Matrix p m' ℝ) (bv' : m' → ℝ)
    (Ww' : Matrix m' q ℝ) (c' : q → ℝ) (M : Matrix p q ℝ)
    (h : ∀ x : p → ℝ, x ᵥ* M + gatedBlockB σ Wg bg Wv bv Ww c x
      = gatedBlockB σ Wg' bg' Wv' bv' Ww' c' x)
    (x : p → ℝ) (hx : ∀ j, (x ᵥ* Wg) j = 0 → Wgᵀ j = 0)
    (hx' : ∀ j, (x ᵥ* Wg') j = 0 → Wg'ᵀ j = 0) :
    M + gateLinear σ Wg bg Wv bv Ww x = gateLinear σ Wg' bg' Wv' bv' Ww' x ∧
      ∀ y : p → ℝ, gateQuadratic Wg Wv Ww x y = gateQuadratic Wg' Wv' Ww' x y := by
  sorry

end Skips
