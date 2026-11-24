import SkipsLean.Absorb.ReluSqBiasesCount

/-!
# ReLU² blocks with biases: the lower bounds

Paper (absorb paper), Appendix C. Theorem C.2 (Extra units with biases): "Let blocks have biases,
let `M` be invertible and let `θ` be generic. […] (iii) A ReLU² block with at least `d_model`
hidden units absorbs `x M` with `3 d_model` more hidden units, and not with fewer than
`2 d_model`." Theorem C.1 (iii): "For generic `θ`, no block `B_{θ′}` of these kinds and of the same
width as `B_θ` satisfies (2)."

Proof of Theorem C.2 (iii): "The argument also gives Theorem C.1 (iii) for ReLU² blocks. The
construction above gives `3 d_model` units. For the lower bound, let `B_{θ′}`, with `n` more units
than `B_θ`, satisfy (2) […]. Genericity. For each of the finitely many pairs of disjoint sets `S`
and `U` of units of `B_θ`, these `d_model + |U|` vectors span a space of dimension at least
`min(d_model (d_model + 3)/2, d_model + |U|)` for generic `θ`. The condition is that some minor of
the matrix with these columns, a polynomial in `θ`, does not vanish. It holds when the writes
`ŵ_i`, `i ∈ S`, vanish and the reads are generic: then the `τ_o = (0, M_{:,o})` span all linear
parts, as `M` is invertible, and for generic columns `w_i`, any
`min(|U|, d_model (d_model + 1)/2)` of the forms `w_i w_i^⊤` are linearly independent. […] For
`M ≠ 0` of any rank, the same argument with `rank M` in place of `d_model` gives `n ≥ 2`."

Here: the generic condition in the two forms that `Absorb/ReluSqBiasesCount.lean` uses (for
disjoint `S`, `U` with `|U| < 2 d` the vectors `τ_o` and `φ(w_i, b_i)`, `i ∈ U`, are linearly
independent; for `M ≠ 0`, for every `S` some `τ_o` is nonzero); the lower bound of Theorem C.2
(iii); Theorem C.2 (iii) as the paper states it (with the construction of
`Absorb/BiasesConstructions.lean`); Theorem C.1 (iii) for ReLU² blocks, in the form "not of the
same width" (the paper's proof gives two more units). The parameters are the tuple
`θ = (W_read, b, W_write, c)`, and "generic `θ`" is almost every `θ` for a Haar measure on these
tuples. With biases the hyperplanes of the units of a generic block are distinct also for one
input, so the statements ask for at least one input and not for `d ≥ 2`.
-/

namespace Skips

open Matrix MeasureTheory

section SameWidth

variable {p q m : Type*} [Fintype p] [Fintype q] [Fintype m]

/-- **The generic condition of the proof of Theorem C.2 (iii) for `M ≠ 0`:** for generic
`θ = (W_read, b, W_write, c)` and every set `S` of units, some `τ_o` is nonzero (when the writes
vanish, `τ_o = (0, M_{:,o})`). -/
theorem ae_exists_sqTarget_ne_zero (M : Matrix p q ℝ) (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ S : Finset m, ∃ o : q, sqTarget M θ.1 θ.2.1 θ.2.2.1 S o ≠ 0 := by
  sorry

/-- **Theorem C.1 (iii) of the absorb paper for ReLU² blocks with biases:** fix `M ≠ 0`. For
generic `θ = (W_read, b, W_write, c)` no ReLU² block with biases of the same width computes
`x M + B_θ(x)`. -/
theorem ae_not_reluSq_absorbB_same_width (M : Matrix p q ℝ) (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ¬ ∃ (Wr' : Matrix p m ℝ) (b' : m → ℝ) (Ww' : Matrix m q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* M + vanillaBlockB reluSq θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
        = vanillaBlockB reluSq Wr' b' Ww' c' x := by
  sorry

end SameWidth

section Square

variable {d m : Type*} [Fintype d] [DecidableEq d] [Fintype m]

/-- **Proof of Theorem C.2 (iii) of the absorb paper, "Genericity":** let `M` be invertible. For
generic `θ = (W_read, b, W_write, c)` and all disjoint sets `S`, `U` of units with `|U| < 2 d`, the
`d + |U|` vectors `τ_o` and `φ(w_i, b_i)`, `i ∈ U`, are linearly independent. -/
theorem ae_linearIndependent_sqTarget (M : Matrix d d ℝ) (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ S U : Finset m, Disjoint S U → U.card < 2 * Fintype.card d →
      LinearIndependent ℝ (Sum.elim (fun o : d => sqTarget M θ.1 θ.2.1 θ.2.2.1 S o)
        (fun i : U => sqForm (θ.1ᵀ (i : m)) (θ.2.1 i))) := by
  sorry

/-- **Theorem C.2 (iii) of the absorb paper, "and not with fewer than `2 d_model`":** let `M` be
invertible. For generic `θ = (W_read, b, W_write, c)` no ReLU² block with biases and fewer than
`2 d` more hidden units computes `x M + B_θ(x)`. -/
theorem ae_not_reluSq_absorbB_of_card_lt [Nonempty d] (M : Matrix d d ℝ) (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ (m' : Type) [Fintype m'],
      Fintype.card m' < Fintype.card m + 2 * Fintype.card d →
      ∀ (Wr' : Matrix d m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' d ℝ) (c' : d → ℝ),
        ∃ x : d → ℝ, x ᵥ* M + vanillaBlockB reluSq θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
          ≠ vanillaBlockB reluSq Wr' b' Ww' c' x := by
  sorry

/-- **Theorem C.2 (iii) of the absorb paper:** let `M` be invertible. For generic
`θ = (W_read, b, W_write, c)`, a ReLU² block with biases and at least `d` hidden units absorbs
`x M` with `3 d` more hidden units, and not with fewer than `2 d`. -/
theorem ae_reluSq_absorbB_add_card [Nonempty d] (hm : Fintype.card d ≤ Fintype.card m)
    (M : Matrix d d ℝ) (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ,
      (∃ (Wr' : Matrix d (m ⊕ (d × Fin 3)) ℝ) (b' : m ⊕ (d × Fin 3) → ℝ)
        (Ww' : Matrix (m ⊕ (d × Fin 3)) d ℝ) (c' : d → ℝ),
        ∀ x : d → ℝ, x ᵥ* M + vanillaBlockB reluSq θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
          = vanillaBlockB reluSq Wr' b' Ww' c' x) ∧
      ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + 2 * Fintype.card d →
        ∀ (Wr' : Matrix d m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' d ℝ) (c' : d → ℝ),
          ∃ x : d → ℝ, x ᵥ* M + vanillaBlockB reluSq θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
            ≠ vanillaBlockB reluSq Wr' b' Ww' c' x := by
  sorry

end Square

end Skips
