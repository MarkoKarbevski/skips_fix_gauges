import SkipsLean.Absorb.GatedBiasesCount
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

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
  -- the two identities on every cell (off the hyperplanes of both blocks), then the count
  exact exists_rank_add_card_le_of_gateLinear_gateQuadratic σ Wg bg Wv bv Ww Wg' bg' Wv' bv' Ww' M
    hg hcol hv hw fun x hx hx' => gateLinear_gateQuadratic_of_gatedBlockB_absorb hσ Wg bg Wv bv
      Ww c Wg' bg' Wv' bv' Ww' c' M h x (fun j h0 => absurd h0 (hx j)) hx'

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
  exact exists_rank_add_card_le_of_gatedBlockB_absorb nearReLU_relu Wg bg Wv bv Ww c Wg' bg' Wv'
    bv' Ww' c' M hg hcol hv hw h

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
  exact exists_rank_add_card_le_of_gatedBlockB_absorb nearReLU_silu Wg bg Wv bv Ww c Wg' bg' Wv'
    bv' Ww' c' M hg hcol hv hw h

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
  exact exists_rank_add_card_le_of_gatedBlockB_absorb nearReLU_gelu Wg bg Wv bv Ww c Wg' bg' Wv'
    bv' Ww' c' M hg hcol hv hw h

end Lemma

/-- A condition that holds for every Haar measure on `F` holds at `Φ x` for `μ`-almost every `x`,
for an onto linear map `Φ` (`ae_comp_linearMap_mem_iff`). -/
private theorem ae_comp_of_surjective_gbl {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] (hBE : BorelSpace E) (hBF : BorelSpace F)
    (μ : Measure E) (hμ : μ.IsAddHaarMeasure) (Φ : E →ₗ[ℝ] F) (hΦ : Function.Surjective Φ)
    {P : F → Prop} (hP : ∀ ν : Measure F, ν.IsAddHaarMeasure → ∀ᵐ y ∂ν, P y) :
    ∀ᵐ x ∂μ, P (Φ x) := by
  have hp := hP Measure.addHaar inferInstance
  rw [ae_iff] at hp
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null hp
  have hc : ∀ᵐ y ∂(Measure.addHaar : Measure F), y ∈ Nᶜ :=
    measure_eq_zero_iff_ae_notMem.1 hN0
  have h := (ae_comp_linearMap_mem_iff Φ μ Measure.addHaar hΦ hN.compl).2 hc
  refine h.mono fun θ hθ => ?_
  by_contra hn
  exact hθ (hsub hn)

/-- `ae_ne_zero_of_analytic` with the Borel structure given explicitly. -/
private theorem ae_ne_zero_of_analytic_gbl {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasurableSpace P] (hB : BorelSpace P) (μ : Measure P)
    (hμ : μ.IsAddHaarMeasure) {g : P → ℝ} (hg : AnalyticOnNhd ℝ g Set.univ)
    (hne : ∃ y, g y ≠ 0) : ∀ᵐ y ∂μ, g y ≠ 0 :=
  ae_ne_zero_of_analytic μ hg hne

/-- The zero matrix written with `Matrix.of`. -/
private theorem matrix_of_zero_gbl {p q : Type*} :
    (Matrix.of fun (_ : p) (_ : q) => (0 : ℝ)) = 0 := rfl

section Generic

variable {p q m : Type*} [Fintype p] [Fintype q] [Fintype m]

open scoped Matrix.Norms.Elementwise in
/-- A condition that holds at generic pairs `(W, W_write)` holds at `(W_g, W_write)` and at
`(W_v, W_write)` of generic tuples `(W_g, b^g, W_v, b^v, W_write, c)`: the projections are linear
and onto. -/
private theorem ae_tuple_gbl
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)))
    [μ.IsAddHaarMeasure] {P : Matrix p m ℝ × Matrix m q ℝ → Prop}
    (hP : ∀ ν : Measure (Matrix p m ℝ × Matrix m q ℝ), ν.IsAddHaarMeasure → ∀ᵐ W ∂ν, P W) :
    ∀ᵐ θ ∂μ, P (θ.1, θ.2.2.2.2.1) ∧ P (θ.2.2.1, θ.2.2.2.2.1) := by
  have h1 : SecondCountableTopology (Matrix p m ℝ) :=
    inferInstanceAs (SecondCountableTopology (p → m → ℝ))
  have h2 : SecondCountableTopology (Matrix m q ℝ) :=
    inferInstanceAs (SecondCountableTopology (m → q → ℝ))
  have hBF : BorelSpace (Matrix p m ℝ × Matrix m q ℝ) := Prod.borelSpace
  have hBE : BorelSpace
      (Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)) :=
    Prod.borelSpace
  -- the projections `θ ↦ (W_g, W_write)` and `θ ↦ (W_v, W_write)` are linear and onto
  let Φg : (Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)) →ₗ[ℝ]
      Matrix p m ℝ × Matrix m q ℝ :=
    { toFun := fun θ => (θ.1, θ.2.2.2.2.1), map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }
  let Φv : (Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)) →ₗ[ℝ]
      Matrix p m ℝ × Matrix m q ℝ :=
    { toFun := fun θ => (θ.2.2.1, θ.2.2.2.2.1), map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }
  have hg : Function.Surjective Φg := fun W => ⟨(W.1, 0, 0, 0, W.2, 0), rfl⟩
  have hv : Function.Surjective Φv := fun W => ⟨(0, 0, W.1, 0, W.2, 0), rfl⟩
  filter_upwards [ae_comp_of_surjective_gbl hBE hBF μ ‹_› Φg hg hP,
    ae_comp_of_surjective_gbl hBE hBF μ ‹_› Φv hv hP] with θ h1 h2
  exact ⟨h1, h2⟩

/-- **(G1), (G2):** at generic tuples `(W_g, b^g, W_v, b^v, W_write, c)` the pairs
`(W_g, W_write)` and `(W_v, W_write)` are nondegenerate. -/
private theorem ae_nondegenerate_tuple_gbl (hp : 2 ≤ Fintype.card p) [Nonempty q]
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, Nondegenerate θ.1 θ.2.2.2.2.1 ∧ Nondegenerate θ.2.2.1 θ.2.2.2.2.1 := by
  classical
  exact ae_tuple_gbl μ (P := fun W => Nondegenerate W.1 W.2) fun ν _ => ae_nondegenerate hp ν

open scoped Matrix.Norms.Elementwise in
/-- An entry of `M + ∑_{i∈S} Δ_i` is a polynomial in the tuple `θ`, so analytic. -/
private theorem analyticOnNhd_entry_gbl (M : Matrix p q ℝ) (S : Finset m) (a : p) (o : q) :
    AnalyticOnNhd ℝ (fun θ : Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ
      × (q → ℝ) => (M + ∑ i ∈ S, gateDelta θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 i) a o)
      Set.univ := by
  simp only [Matrix.add_apply, Matrix.sum_apply, gateDelta, Matrix.of_apply]
  refine analyticOnNhd_const.add (Finset.analyticOnNhd_fun_sum _ fun i _ => ?_)
  -- the coordinates of `θ` are linear
  have hbg := analyticOnNhd_linear (P := Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ)
      × Matrix m q ℝ × (q → ℝ))
    { toFun := fun θ => θ.2.1 i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hWv := analyticOnNhd_linear (P := Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ)
      × Matrix m q ℝ × (q → ℝ))
    { toFun := fun θ => θ.2.2.1 a i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hbv := analyticOnNhd_linear (P := Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ)
      × Matrix m q ℝ × (q → ℝ))
    { toFun := fun θ => θ.2.2.2.1 i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hWg := analyticOnNhd_linear (P := Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ)
      × Matrix m q ℝ × (q → ℝ))
    { toFun := fun θ => θ.1 a i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hWw := analyticOnNhd_linear (P := Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ)
      × Matrix m q ℝ × (q → ℝ))
    { toFun := fun θ => θ.2.2.2.2.1 i o, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }
  exact ((hbg.mul hWv).add (hbv.mul hWg)).mul hWw

open scoped Matrix.Norms.Elementwise in
/-- **(G3) for `M ≠ 0`:** let `M a o ≠ 0`. At generic tuples, the entry `(a, o)` of
`M + ∑_{i∈S} Δ_i` is nonzero for every set `S` of units: it is a polynomial in `θ`, equal to
`M a o` at `θ = 0`. -/
private theorem ae_entry_ne_zero_gbl (M : Matrix p q ℝ) {a : p} {o : q} (hM : M a o ≠ 0)
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ S : Finset m,
      (M + ∑ i ∈ S, gateDelta θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 i) a o ≠ 0 := by
  refine ae_all_iff.2 fun S => ?_
  have h1 : SecondCountableTopology (Matrix p m ℝ) :=
    inferInstanceAs (SecondCountableTopology (p → m → ℝ))
  have h2 : SecondCountableTopology (Matrix m q ℝ) :=
    inferInstanceAs (SecondCountableTopology (m → q → ℝ))
  have hB : BorelSpace
      (Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)) :=
    Prod.borelSpace
  -- at `θ = 0` every `Δ_i` vanishes
  have h0 : (M + ∑ i ∈ S, gateDelta (0 : Matrix p m ℝ) 0 0 0 (0 : Matrix m q ℝ) i) a o ≠ 0 := by
    simpa only [gateDelta, Pi.zero_apply, Matrix.zero_apply, zero_mul, add_zero, mul_zero,
      matrix_of_zero_gbl, Finset.sum_const_zero] using hM
  exact ae_ne_zero_of_analytic_gbl hB μ ‹_› (analyticOnNhd_entry_gbl M S a o) ⟨0, h0⟩

end Generic

section Det

variable {d m : Type*} [Fintype d] [DecidableEq d] [Fintype m]

open scoped Matrix.Norms.Elementwise in
/-- **(G3) for `M` invertible:** at generic tuples, `M + ∑_{i∈S} Δ_i` is invertible for every set
`S` of units: its determinant is a polynomial in `θ`, equal to `det M ≠ 0` at `θ = 0`. -/
private theorem ae_det_ne_zero_gbl (M : Matrix d d ℝ) (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ S : Finset m,
      IsUnit (M + ∑ i ∈ S, gateDelta θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 i).det := by
  refine ae_all_iff.2 fun S => ?_
  have h1 : SecondCountableTopology (Matrix d m ℝ) :=
    inferInstanceAs (SecondCountableTopology (d → m → ℝ))
  have h2 : SecondCountableTopology (Matrix m d ℝ) :=
    inferInstanceAs (SecondCountableTopology (m → d → ℝ))
  have hB : BorelSpace
      (Matrix d m ℝ × (m → ℝ) × Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ)) :=
    Prod.borelSpace
  -- the determinant is a signed sum of products of entries
  have hg : AnalyticOnNhd ℝ (fun θ : Matrix d m ℝ × (m → ℝ) × Matrix d m ℝ × (m → ℝ)
      × Matrix m d ℝ × (d → ℝ) =>
      (M + ∑ i ∈ S, gateDelta θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 i).det) Set.univ := by
    simp only [Matrix.det_apply']
    exact Finset.analyticOnNhd_fun_sum _ fun τ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => analyticOnNhd_entry_gbl M S (τ i) i)
  -- at `θ = 0` it is `det M`
  have h0 : (M + ∑ i ∈ S, gateDelta (0 : Matrix d m ℝ) 0 0 0 (0 : Matrix m d ℝ) i).det ≠ 0 := by
    have e : ∑ i ∈ S, gateDelta (0 : Matrix d m ℝ) 0 0 0 (0 : Matrix m d ℝ) i = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      ext a o
      simp only [gateDelta, Pi.zero_apply, Matrix.zero_apply, Matrix.of_apply, add_zero,
        mul_zero]
    rw [e, add_zero]
    exact hM.ne_zero
  filter_upwards [ae_ne_zero_of_analytic_gbl hB μ ‹_› hg ⟨0, h0⟩] with θ hθ
  exact isUnit_iff_ne_zero.2 hθ

end Det

/-- A matrix with a nonzero entry has rank at least one: the `1 × 1` submatrix of that entry is
invertible. -/
private theorem one_le_rank_gbl {p q : Type*} [Fintype q] {A : Matrix p q ℝ} {a : p} {o : q}
    (h : A a o ≠ 0) : 1 ≤ A.rank := by
  have h1 := Matrix.rank_submatrix_le A (fun _ : Unit => a) (fun _ : Unit => o)
  have h2 : IsUnit (A.submatrix (fun _ : Unit => a) (fun _ : Unit => o)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique]
    exact isUnit_iff_ne_zero.2 h
  rw [Matrix.rank_of_isUnit _ h2, Fintype.card_unit] at h1
  exact h1

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
  classical
  -- `M ≠ 0` has a nonzero entry `(a, o)`; in particular there is an output
  obtain ⟨a, o, hao⟩ : ∃ a o, M a o ≠ 0 := by
    by_contra hn
    exact hM (Matrix.ext fun a o => not_not.1 fun h' => hn ⟨a, o, h'⟩)
  have : Nonempty q := ⟨o⟩
  -- generic `θ`: (G1), (G2), and the entry `(a, o)` of every `M + ∑_{i∈S} Δ_i` is nonzero
  filter_upwards [ae_nondegenerate_tuple_gbl hp μ, ae_entry_ne_zero_gbl M hao μ] with θ hθ hS
  rintro ⟨Wg', bg', Wv', bv', Ww', c', h⟩
  -- Lemma C.8 with no extra unit: some `M + ∑_{i∈S} Δ_i` has rank `0`, against its entry
  obtain ⟨S, hS'⟩ := exists_rank_add_card_le_of_gatedBlockB_absorb hσ _ _ _ _ _ _ Wg' bg' Wv'
    bv' Ww' c' M hθ.1.col_ne_zero hθ.1.col_not_collinear hθ.2.col_ne_zero hθ.1.row_ne_zero h
  have h1 := one_le_rank_gbl (hS S)
  omega

/-- **Theorem C.1 (iii) of the absorb paper for ReGLU blocks with biases.** -/
theorem ae_not_reglu_absorbB_same_width (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ)
    (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ¬ ∃ (Wg' : Matrix p m ℝ) (bg' : m → ℝ) (Wv' : Matrix p m ℝ) (bv' : m → ℝ)
      (Ww' : Matrix m q ℝ) (c' : q → ℝ), ∀ x : p → ℝ,
        x ᵥ* M + gatedBlockB relu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2 x
          = gatedBlockB relu Wg' bg' Wv' bv' Ww' c' x := by
  exact ae_not_gatedBlockB_absorb_same_width nearReLU_relu hp M hM μ

/-- **Theorem C.1 (iii) of the absorb paper for SwiGLU blocks with biases.** -/
theorem ae_not_swiglu_absorbB_same_width (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ)
    (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ¬ ∃ (Wg' : Matrix p m ℝ) (bg' : m → ℝ) (Wv' : Matrix p m ℝ) (bv' : m → ℝ)
      (Ww' : Matrix m q ℝ) (c' : q → ℝ), ∀ x : p → ℝ,
        x ᵥ* M + gatedBlockB silu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2 x
          = gatedBlockB silu Wg' bg' Wv' bv' Ww' c' x := by
  exact ae_not_gatedBlockB_absorb_same_width nearReLU_silu hp M hM μ

/-- **Theorem C.1 (iii) of the absorb paper for GeGLU blocks with biases.** -/
theorem ae_not_geglu_absorbB_same_width (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ)
    (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ¬ ∃ (Wg' : Matrix p m ℝ) (bg' : m → ℝ) (Wv' : Matrix p m ℝ) (bv' : m → ℝ)
      (Ww' : Matrix m q ℝ) (c' : q → ℝ), ∀ x : p → ℝ,
        x ᵥ* M + gatedBlockB gelu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2 x
          = gatedBlockB gelu Wg' bg' Wv' bv' Ww' c' x := by
  exact ae_not_gatedBlockB_absorb_same_width nearReLU_gelu hp M hM μ

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
  classical
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- generic `θ`: (G1), (G2), and every `M + ∑_{i∈S} Δ_i` is invertible
  filter_upwards [ae_nondegenerate_tuple_gbl hd μ, ae_det_ne_zero_gbl M hM μ] with θ hθ hS
  intro m' _ hm' Wg' bg' Wv' bv' Ww' c'
  by_contra hc
  -- Lemma C.8: `rank (M + ∑_{i∈S} Δ_i) = d` extra units at least
  obtain ⟨S, hS'⟩ := exists_rank_add_card_le_of_gatedBlockB_absorb hσ _ _ _ _ _ _ Wg' bg' Wv'
    bv' Ww' c' M hθ.1.col_ne_zero hθ.1.col_not_collinear hθ.2.col_ne_zero hθ.1.row_ne_zero
    fun x => not_not.1 (not_exists.1 hc x)
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (hS S))] at hS'
  omega

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
  -- the construction at every `θ`, and the lower bound at generic `θ`
  filter_upwards [ae_not_gatedBlockB_absorb_of_card_lt hσ hd M hM μ] with θ hθ
  exact ⟨exists_gatedBlockB_add_linear hσ1 _ _ _ _ _ _ M, hθ⟩

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
  have h1 : relu 1 ≠ 0 := by
    -- `relu 1 = 1`
    rw [relu, max_eq_left zero_le_one]; exact one_ne_zero
  exact ae_gatedBlockB_absorb_add_card nearReLU_relu h1 hd M hM μ

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
  have h1 : silu 1 ≠ 0 := by
    -- `silu 1 = 1 / (1 + e⁻¹) > 0`
    rw [silu]; positivity
  exact ae_gatedBlockB_absorb_add_card nearReLU_silu h1 hd M hM μ

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
  have h1 : gelu 1 ≠ 0 := by
    -- `gelu 1 = Φ(1) > 0`
    rw [gelu, one_mul]; exact (gaussCdf_pos 1).ne'
  exact ae_gatedBlockB_absorb_add_card nearReLU_gelu h1 hd M hM μ

end Square

end Skips
