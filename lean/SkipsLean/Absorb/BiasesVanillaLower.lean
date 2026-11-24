import SkipsLean.Absorb.BiasesConstructions
import SkipsLean.Absorb.FewerUnits

/-!
# ReLU and GELU blocks with biases: the lower bounds

Paper (absorb paper), Appendix C. Theorem C.1 (Exact absorption with biases): "Let blocks have
biases, and let `M ≠ 0`. […] (iii) For generic `θ`, no block `B_{θ′}` of these kinds and of the
same width as `B_θ` satisfies (2)." Theorem C.2 (Extra units with biases): "Let blocks have biases,
let `M` be invertible and let `θ` be generic. […] (ii) A ReLU or GELU block with at least `d_model`
hidden units absorbs `x M` with `d_model` more hidden units, and not with fewer."

Proof of Theorem C.2 (ii): "The argument also gives Theorem C.1 (iii) for ReLU and GELU blocks. The
construction above gives `d_model` units. For the lower bound, let `B_{θ′}` satisfy (2). ReLU
changes by at most `|b|` when its argument changes by `b`, and GELU differs from ReLU by at most
`κ < 0.17` (proof of Theorem 4.5). So for both activations and all `t > 0`,
`|σ(t z + b) − t ReLU(z)| ≤ |b| + κ`, and `σ(t z + b)/t → ReLU(z)` as `t → ∞`. Put `t x` into (2),
divide by `t`, and let `t → ∞`: the ReLU blocks without biases that have the reads and writes of
`B_θ` and `B_{θ′}` satisfy (2). For generic `θ` these reads and writes are generic, so `B_{θ′}` has
at least `d_model` more units by Proposition A.11 (ii), and for any `M ≠ 0` it is not of the same
width, by Theorem 3.1 (i)."

Here: the step along rays, for every activation at a bounded distance from ReLU (ReLU itself, and
GELU by `abs_gelu_sub_relu_le`); the lower bound of Theorem C.2 (ii) and Theorem C.2 (ii) as the
paper states it (with the construction of `Absorb/BiasesConstructions.lean`); Theorem C.1 (iii) for
ReLU and GELU blocks. The parameters of a block with biases are the tuple
`θ = (W_read, b, W_write, c)`, and "generic `θ`" is almost every `θ` for a Haar measure on these
tuples. The lower bound is for blocks of every width (the paper's "at least `d_model` hidden units"
serves the construction); `d ≥ 2` is the Scope's.
-/

namespace Skips

open Matrix MeasureTheory

section Rays

variable {p q m : Type*} [Fintype p] [Fintype m]

/-- **Proof of Theorem C.2 (ii) of the absorb paper, the step along rays:** let `σ` be at a bounded
distance from ReLU. If a block with biases absorbs `x M` into a block with biases, of any width,
then the ReLU blocks without biases that have the same reads and writes satisfy the same equation.
(Evaluate at `t x`, divide by `t`, and let `t → ∞`.) -/
theorem relu_absorb_of_vanillaBlockB_absorb {σ : ℝ → ℝ} (hσ : ∃ κ : ℝ, ∀ z, |σ z - relu z| ≤ κ)
    {m' : Type*} [Fintype m'] (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ)
    (Wr' : Matrix p m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' q ℝ) (c' : q → ℝ) (M : Matrix p q ℝ)
    (h : ∀ x : p → ℝ, x ᵥ* M + vanillaBlockB σ Wr b Ww c x = vanillaBlockB σ Wr' b' Ww' c' x) :
    ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x := by
  sorry

/-- **The step along rays for ReLU blocks with biases.** -/
theorem relu_absorb_of_vanillaBlockB_relu_absorb {m' : Type*} [Fintype m'] (Wr : Matrix p m ℝ)
    (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ) (Wr' : Matrix p m' ℝ) (b' : m' → ℝ)
    (Ww' : Matrix m' q ℝ) (c' : q → ℝ) (M : Matrix p q ℝ)
    (h : ∀ x : p → ℝ,
      x ᵥ* M + vanillaBlockB relu Wr b Ww c x = vanillaBlockB relu Wr' b' Ww' c' x) :
    ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x := by
  sorry

/-- **The step along rays for GELU blocks with biases.** -/
theorem relu_absorb_of_vanillaBlockB_gelu_absorb {m' : Type*} [Fintype m'] (Wr : Matrix p m ℝ)
    (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ) (Wr' : Matrix p m' ℝ) (b' : m' → ℝ)
    (Ww' : Matrix m' q ℝ) (c' : q → ℝ) (M : Matrix p q ℝ)
    (h : ∀ x : p → ℝ,
      x ᵥ* M + vanillaBlockB gelu Wr b Ww c x = vanillaBlockB gelu Wr' b' Ww' c' x) :
    ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x := by
  sorry

/-- **Theorem C.1 (iii) of the absorb paper for ReLU blocks with biases:** fix `M ≠ 0`. For generic
`θ = (W_read, b, W_write, c)` no ReLU block with biases of the same width computes
`x M + B_θ(x)`. -/
theorem ae_not_relu_absorbB_same_width (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ) (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ¬ ∃ (Wr' : Matrix p m ℝ) (b' : m → ℝ) (Ww' : Matrix m q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* M + vanillaBlockB relu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
        = vanillaBlockB relu Wr' b' Ww' c' x := by
  sorry

/-- **Theorem C.1 (iii) of the absorb paper for GELU blocks with biases.** -/
theorem ae_not_gelu_absorbB_same_width (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ) (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ¬ ∃ (Wr' : Matrix p m ℝ) (b' : m → ℝ) (Ww' : Matrix m q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* M + vanillaBlockB gelu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
        = vanillaBlockB gelu Wr' b' Ww' c' x := by
  sorry

end Rays

section Square

variable {d m : Type*} [Fintype d] [DecidableEq d] [Fintype m]

/-- **Theorem C.2 (ii) of the absorb paper, "and not with fewer", for ReLU blocks with biases:**
let `M` be invertible. For generic `θ = (W_read, b, W_write, c)` no ReLU block with biases and
fewer than `d` more hidden units computes `x M + B_θ(x)`. -/
theorem ae_not_relu_absorbB_of_card_lt (hd : 2 ≤ Fintype.card d) (M : Matrix d d ℝ)
    (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
      ∀ (Wr' : Matrix d m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' d ℝ) (c' : d → ℝ),
        ∃ x : d → ℝ, x ᵥ* M + vanillaBlockB relu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
          ≠ vanillaBlockB relu Wr' b' Ww' c' x := by
  sorry

/-- **Theorem C.2 (ii) of the absorb paper, "and not with fewer", for GELU blocks with biases.** -/
theorem ae_not_gelu_absorbB_of_card_lt (hd : 2 ≤ Fintype.card d) (M : Matrix d d ℝ)
    (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
      ∀ (Wr' : Matrix d m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' d ℝ) (c' : d → ℝ),
        ∃ x : d → ℝ, x ᵥ* M + vanillaBlockB gelu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
          ≠ vanillaBlockB gelu Wr' b' Ww' c' x := by
  sorry

/-- **Theorem C.2 (ii) of the absorb paper for ReLU blocks:** let `M` be invertible. For generic
`θ = (W_read, b, W_write, c)`, a ReLU block with biases and at least `d` hidden units absorbs `x M`
with `d` more hidden units, and not with fewer. -/
theorem ae_relu_absorbB_add_card (hd : 2 ≤ Fintype.card d)
    (hm : Fintype.card d ≤ Fintype.card m) (M : Matrix d d ℝ) (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ,
      (∃ (Wr' : Matrix d (m ⊕ d) ℝ) (b' : m ⊕ d → ℝ) (Ww' : Matrix (m ⊕ d) d ℝ) (c' : d → ℝ),
        ∀ x : d → ℝ, x ᵥ* M + vanillaBlockB relu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
          = vanillaBlockB relu Wr' b' Ww' c' x) ∧
      ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
        ∀ (Wr' : Matrix d m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' d ℝ) (c' : d → ℝ),
          ∃ x : d → ℝ, x ᵥ* M + vanillaBlockB relu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
            ≠ vanillaBlockB relu Wr' b' Ww' c' x := by
  sorry

/-- **Theorem C.2 (ii) of the absorb paper for GELU blocks:** let `M` be invertible. For generic
`θ = (W_read, b, W_write, c)`, a GELU block with biases and at least `d` hidden units absorbs `x M`
with `d` more hidden units, and not with fewer. -/
theorem ae_gelu_absorbB_add_card (hd : 2 ≤ Fintype.card d)
    (hm : Fintype.card d ≤ Fintype.card m) (M : Matrix d d ℝ) (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ,
      (∃ (Wr' : Matrix d (m ⊕ d) ℝ) (b' : m ⊕ d → ℝ) (Ww' : Matrix (m ⊕ d) d ℝ) (c' : d → ℝ),
        ∀ x : d → ℝ, x ᵥ* M + vanillaBlockB gelu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
          = vanillaBlockB gelu Wr' b' Ww' c' x) ∧
      ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
        ∀ (Wr' : Matrix d m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' d ℝ) (c' : d → ℝ),
          ∃ x : d → ℝ, x ᵥ* M + vanillaBlockB gelu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
            ≠ vanillaBlockB gelu Wr' b' Ww' c' x := by
  sorry

end Square

end Skips
