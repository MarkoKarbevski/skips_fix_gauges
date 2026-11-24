import SkipsLean.Absorb.GatedBiasesCount

/-!
# Gated blocks with biases: Lemma C.8 and the lower bounds

Paper (absorb paper), Appendix C.

Lemma C.8 (Gated blocks with biases): "Let ReGLU, SwiGLU or GeGLU blocks `B_θ` and `B_{θ′}` with
biases satisfy (2), where `B_{θ′}` has `n` more units than `B_θ`. Let the gate reads of `B_θ` be
nonzero and pairwise non-collinear, and its value reads and writes nonzero. Then for some set `S`
of units of `B_θ`, the matrix `M + ∑_{i∈S} Δ_i` is a sum of at most `n` matrices of rank one."

Theorem C.2 (Extra units with biases): "Let blocks have biases, let `M` be invertible and let `θ`
be generic. (i) A ReGLU, SwiGLU or GeGLU block absorbs `x M` with `d_model` more hidden units, and
not with fewer." Theorem C.1 (iii): "For generic `θ`, no block `B_{θ′}` of these kinds and of the
same width as `B_θ` satisfies (2)."

Proof of Theorem C.2 (i): "The argument also gives Theorem C.1 (iii) for gated blocks. The
construction above gives `d_model` units. For each set `S` of units of `B_θ`, the determinant of
`M + ∑_{i∈S} Δ_i` is a polynomial in `θ`, and it equals `det M ≠ 0` when all biases vanish. So for
generic `θ` it is nonzero for each of the finitely many sets `S`, the hypotheses of Lemma C.8
hold, and the lemma gives `n ≥ d_model`. For `M ≠ 0` of any rank, a minor of size `rank M` that
does not vanish at `M` plays the role of the determinant, and gives `n ≥ rank M ≥ 1`."

Here: Lemma C.8 for every gate at a distance `O(1/|z|)` from ReLU (`NearReLU`), from the two parts
of its proof (`Absorb/GatedBiasesCells.lean`, `Absorb/GatedBiasesCount.lean`), and for ReGLU,
SwiGLU and GeGLU blocks by name; the lower bound of Theorem C.2 (i), Theorem C.2 (i) as the paper
states it (with the construction of `Absorb/BiasesConstructions.lean`), and Theorem C.1 (iii) for
gated blocks. "A sum of at most `n` matrices of rank one" is "of rank at most `n`", and the lemma
is stated as: the rank of `M + ∑_{i∈S} Δ_i` plus the number of units of `B_θ` is at most the
number of units of `B_{θ′}`. The parameters of a gated block with biases are the tuple
`θ = (W_g, b^g, W_v, b^v, W_write, c)`, and "generic `θ`" is almost every `θ` for a Haar measure
on these tuples. `d ≥ 2` is the Scope's.
-/

namespace Skips

open Matrix MeasureTheory

section Lemma

variable {p q m m' : Type*} [Fintype p] [Fintype q] [Fintype m] [Fintype m']

/-- **Lemma C.8 of the absorb paper (Gated blocks with biases), for every gate at a distance
`O(1/|z|)` from ReLU:** let gated blocks `B_θ` and `B_{θ′}` with biases satisfy
`x M + B_θ(x) = B_{θ′}(x)` for all `x`. Let the gate reads of `B_θ` be nonzero and pairwise
non-collinear, and its value reads and writes nonzero. Then for some set `S` of units of `B_θ`,
the rank of `M + ∑_{i∈S} Δ_i` is at most the number of units that `B_{θ′}` has more than `B_θ`. -/
theorem exists_rank_add_card_le_of_gatedBlockB_absorb {σ : ℝ → ℝ} (hσ : NearReLU σ)
    (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (Wg' : Matrix p m' ℝ) (bg' : m' → ℝ) (Wv' : Matrix p m' ℝ) (bv' : m' → ℝ)
    (Ww' : Matrix m' q ℝ) (c' : q → ℝ) (M : Matrix p q ℝ)
    (hg : ∀ j, Wgᵀ j ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, Wgᵀ i ≠ r • Wgᵀ j)
    (hv : ∀ j, Wvᵀ j ≠ 0) (hw : ∀ j, Ww j ≠ 0)
    (h : ∀ x : p → ℝ, x ᵥ* M + gatedBlockB σ Wg bg Wv bv Ww c x
      = gatedBlockB σ Wg' bg' Wv' bv' Ww' c' x) :
    ∃ S : Finset m, (M + ∑ i ∈ S, gateDelta Wg bg Wv bv Ww i).rank + Fintype.card m
      ≤ Fintype.card m' := by
  sorry

/-- **Lemma C.8 of the absorb paper for ReGLU blocks.** -/
theorem exists_rank_add_card_le_of_reglu_absorbB
    (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (Wg' : Matrix p m' ℝ) (bg' : m' → ℝ) (Wv' : Matrix p m' ℝ) (bv' : m' → ℝ)
    (Ww' : Matrix m' q ℝ) (c' : q → ℝ) (M : Matrix p q ℝ)
    (hg : ∀ j, Wgᵀ j ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, Wgᵀ i ≠ r • Wgᵀ j)
    (hv : ∀ j, Wvᵀ j ≠ 0) (hw : ∀ j, Ww j ≠ 0)
    (h : ∀ x : p → ℝ, x ᵥ* M + gatedBlockB relu Wg bg Wv bv Ww c x
      = gatedBlockB relu Wg' bg' Wv' bv' Ww' c' x) :
    ∃ S : Finset m, (M + ∑ i ∈ S, gateDelta Wg bg Wv bv Ww i).rank + Fintype.card m
      ≤ Fintype.card m' := by
  sorry

/-- **Lemma C.8 of the absorb paper for SwiGLU blocks.** -/
theorem exists_rank_add_card_le_of_swiglu_absorbB
    (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (Wg' : Matrix p m' ℝ) (bg' : m' → ℝ) (Wv' : Matrix p m' ℝ) (bv' : m' → ℝ)
    (Ww' : Matrix m' q ℝ) (c' : q → ℝ) (M : Matrix p q ℝ)
    (hg : ∀ j, Wgᵀ j ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, Wgᵀ i ≠ r • Wgᵀ j)
    (hv : ∀ j, Wvᵀ j ≠ 0) (hw : ∀ j, Ww j ≠ 0)
    (h : ∀ x : p → ℝ, x ᵥ* M + gatedBlockB silu Wg bg Wv bv Ww c x
      = gatedBlockB silu Wg' bg' Wv' bv' Ww' c' x) :
    ∃ S : Finset m, (M + ∑ i ∈ S, gateDelta Wg bg Wv bv Ww i).rank + Fintype.card m
      ≤ Fintype.card m' := by
  sorry

/-- **Lemma C.8 of the absorb paper for GeGLU blocks.** -/
theorem exists_rank_add_card_le_of_geglu_absorbB
    (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (Wg' : Matrix p m' ℝ) (bg' : m' → ℝ) (Wv' : Matrix p m' ℝ) (bv' : m' → ℝ)
    (Ww' : Matrix m' q ℝ) (c' : q → ℝ) (M : Matrix p q ℝ)
    (hg : ∀ j, Wgᵀ j ≠ 0) (hcol : ∀ i j, i ≠ j → ∀ r : ℝ, Wgᵀ i ≠ r • Wgᵀ j)
    (hv : ∀ j, Wvᵀ j ≠ 0) (hw : ∀ j, Ww j ≠ 0)
    (h : ∀ x : p → ℝ, x ᵥ* M + gatedBlockB gelu Wg bg Wv bv Ww c x
      = gatedBlockB gelu Wg' bg' Wv' bv' Ww' c' x) :
    ∃ S : Finset m, (M + ∑ i ∈ S, gateDelta Wg bg Wv bv Ww i).rank + Fintype.card m
      ≤ Fintype.card m' := by
  sorry

end Lemma

section SameWidth

variable {p q m : Type*} [Fintype p] [Fintype q] [Fintype m]

/-- **Theorem C.1 (iii) of the absorb paper for gated blocks with biases, for every gate at a
distance `O(1/|z|)` from ReLU:** fix `M ≠ 0`. For generic `θ = (W_g, b^g, W_v, b^v, W_write, c)`
no gated block with biases of the same width computes `x M + B_θ(x)`. -/
theorem ae_not_gatedBlockB_absorb_same_width {σ : ℝ → ℝ} (hσ : NearReLU σ)
    (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ) (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ¬ ∃ (Wg' : Matrix p m ℝ) (bg' : m → ℝ) (Wv' : Matrix p m ℝ) (bv' : m → ℝ)
      (Ww' : Matrix m q ℝ) (c' : q → ℝ), ∀ x : p → ℝ,
        x ᵥ* M + gatedBlockB σ θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2 x
          = gatedBlockB σ Wg' bg' Wv' bv' Ww' c' x := by
  sorry

/-- **Theorem C.1 (iii) of the absorb paper for ReGLU blocks with biases.** -/
theorem ae_not_reglu_absorbB_same_width (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ)
    (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ¬ ∃ (Wg' : Matrix p m ℝ) (bg' : m → ℝ) (Wv' : Matrix p m ℝ) (bv' : m → ℝ)
      (Ww' : Matrix m q ℝ) (c' : q → ℝ), ∀ x : p → ℝ,
        x ᵥ* M + gatedBlockB relu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2 x
          = gatedBlockB relu Wg' bg' Wv' bv' Ww' c' x := by
  sorry

/-- **Theorem C.1 (iii) of the absorb paper for SwiGLU blocks with biases.** -/
theorem ae_not_swiglu_absorbB_same_width (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ)
    (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ¬ ∃ (Wg' : Matrix p m ℝ) (bg' : m → ℝ) (Wv' : Matrix p m ℝ) (bv' : m → ℝ)
      (Ww' : Matrix m q ℝ) (c' : q → ℝ), ∀ x : p → ℝ,
        x ᵥ* M + gatedBlockB silu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2 x
          = gatedBlockB silu Wg' bg' Wv' bv' Ww' c' x := by
  sorry

/-- **Theorem C.1 (iii) of the absorb paper for GeGLU blocks with biases.** -/
theorem ae_not_geglu_absorbB_same_width (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ)
    (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ¬ ∃ (Wg' : Matrix p m ℝ) (bg' : m → ℝ) (Wv' : Matrix p m ℝ) (bv' : m → ℝ)
      (Ww' : Matrix m q ℝ) (c' : q → ℝ), ∀ x : p → ℝ,
        x ᵥ* M + gatedBlockB gelu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2 x
          = gatedBlockB gelu Wg' bg' Wv' bv' Ww' c' x := by
  sorry

end SameWidth

section Square

variable {d m : Type*} [Fintype d] [DecidableEq d] [Fintype m]

/-- **Theorem C.2 (i) of the absorb paper, "and not with fewer", for every gate at a distance
`O(1/|z|)` from ReLU:** let `M` be invertible. For generic
`θ = (W_g, b^g, W_v, b^v, W_write, c)` no gated block with biases and fewer than `d` more hidden
units computes `x M + B_θ(x)`. -/
theorem ae_not_gatedBlockB_absorb_of_card_lt {σ : ℝ → ℝ} (hσ : NearReLU σ)
    (hd : 2 ≤ Fintype.card d) (M : Matrix d d ℝ) (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
      ∀ (Wg' : Matrix d m' ℝ) (bg' : m' → ℝ) (Wv' : Matrix d m' ℝ) (bv' : m' → ℝ)
        (Ww' : Matrix m' d ℝ) (c' : d → ℝ), ∃ x : d → ℝ,
          x ᵥ* M + gatedBlockB σ θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2 x
            ≠ gatedBlockB σ Wg' bg' Wv' bv' Ww' c' x := by
  sorry

/-- **Theorem C.2 (i) of the absorb paper, for every gate at a distance `O(1/|z|)` from ReLU with
`σ(1) ≠ 0`:** let `M` be invertible. For generic `θ`, a gated block with biases absorbs `x M` with
`d` more hidden units, and not with fewer. -/
theorem ae_gatedBlockB_absorb_add_card {σ : ℝ → ℝ} (hσ : NearReLU σ) (hσ1 : σ 1 ≠ 0)
    (hd : 2 ≤ Fintype.card d) (M : Matrix d d ℝ) (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ,
      (∃ (Wg' : Matrix d (m ⊕ d) ℝ) (bg' : m ⊕ d → ℝ) (Wv' : Matrix d (m ⊕ d) ℝ)
        (bv' : m ⊕ d → ℝ) (Ww' : Matrix (m ⊕ d) d ℝ) (c' : d → ℝ), ∀ x : d → ℝ,
          x ᵥ* M + gatedBlockB σ θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2 x
            = gatedBlockB σ Wg' bg' Wv' bv' Ww' c' x) ∧
      ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
        ∀ (Wg' : Matrix d m' ℝ) (bg' : m' → ℝ) (Wv' : Matrix d m' ℝ) (bv' : m' → ℝ)
          (Ww' : Matrix m' d ℝ) (c' : d → ℝ), ∃ x : d → ℝ,
            x ᵥ* M + gatedBlockB σ θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2 x
              ≠ gatedBlockB σ Wg' bg' Wv' bv' Ww' c' x := by
  sorry

/-- **Theorem C.2 (i) of the absorb paper for ReGLU blocks:** let `M` be invertible. For generic
`θ`, a ReGLU block with biases absorbs `x M` with `d` more hidden units, and not with fewer. -/
theorem ae_reglu_absorbB_add_card (hd : 2 ≤ Fintype.card d) (M : Matrix d d ℝ)
    (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ,
      (∃ (Wg' : Matrix d (m ⊕ d) ℝ) (bg' : m ⊕ d → ℝ) (Wv' : Matrix d (m ⊕ d) ℝ)
        (bv' : m ⊕ d → ℝ) (Ww' : Matrix (m ⊕ d) d ℝ) (c' : d → ℝ), ∀ x : d → ℝ,
          x ᵥ* M + gatedBlockB relu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2 x
            = gatedBlockB relu Wg' bg' Wv' bv' Ww' c' x) ∧
      ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
        ∀ (Wg' : Matrix d m' ℝ) (bg' : m' → ℝ) (Wv' : Matrix d m' ℝ) (bv' : m' → ℝ)
          (Ww' : Matrix m' d ℝ) (c' : d → ℝ), ∃ x : d → ℝ,
            x ᵥ* M + gatedBlockB relu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2 x
              ≠ gatedBlockB relu Wg' bg' Wv' bv' Ww' c' x := by
  sorry

/-- **Theorem C.2 (i) of the absorb paper for SwiGLU blocks:** let `M` be invertible. For generic
`θ`, a SwiGLU block with biases absorbs `x M` with `d` more hidden units, and not with fewer. -/
theorem ae_swiglu_absorbB_add_card (hd : 2 ≤ Fintype.card d) (M : Matrix d d ℝ)
    (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ,
      (∃ (Wg' : Matrix d (m ⊕ d) ℝ) (bg' : m ⊕ d → ℝ) (Wv' : Matrix d (m ⊕ d) ℝ)
        (bv' : m ⊕ d → ℝ) (Ww' : Matrix (m ⊕ d) d ℝ) (c' : d → ℝ), ∀ x : d → ℝ,
          x ᵥ* M + gatedBlockB silu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2 x
            = gatedBlockB silu Wg' bg' Wv' bv' Ww' c' x) ∧
      ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
        ∀ (Wg' : Matrix d m' ℝ) (bg' : m' → ℝ) (Wv' : Matrix d m' ℝ) (bv' : m' → ℝ)
          (Ww' : Matrix m' d ℝ) (c' : d → ℝ), ∃ x : d → ℝ,
            x ᵥ* M + gatedBlockB silu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2 x
              ≠ gatedBlockB silu Wg' bg' Wv' bv' Ww' c' x := by
  sorry

/-- **Theorem C.2 (i) of the absorb paper for GeGLU blocks:** let `M` be invertible. For generic
`θ`, a GeGLU block with biases absorbs `x M` with `d` more hidden units, and not with fewer. -/
theorem ae_geglu_absorbB_add_card (hd : 2 ≤ Fintype.card d) (M : Matrix d d ℝ)
    (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ,
      (∃ (Wg' : Matrix d (m ⊕ d) ℝ) (bg' : m ⊕ d → ℝ) (Wv' : Matrix d (m ⊕ d) ℝ)
        (bv' : m ⊕ d → ℝ) (Ww' : Matrix (m ⊕ d) d ℝ) (c' : d → ℝ), ∀ x : d → ℝ,
          x ᵥ* M + gatedBlockB gelu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2 x
            = gatedBlockB gelu Wg' bg' Wv' bv' Ww' c' x) ∧
      ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
        ∀ (Wg' : Matrix d m' ℝ) (bg' : m' → ℝ) (Wv' : Matrix d m' ℝ) (bv' : m' → ℝ)
          (Ww' : Matrix m' d ℝ) (c' : d → ℝ), ∃ x : d → ℝ,
            x ᵥ* M + gatedBlockB gelu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2 x
              ≠ gatedBlockB gelu Wg' bg' Wv' bv' Ww' c' x := by
  sorry

end Square

end Skips
