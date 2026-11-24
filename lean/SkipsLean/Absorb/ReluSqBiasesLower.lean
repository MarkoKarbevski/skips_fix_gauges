import SkipsLean.Absorb.ReluSqBiasesCount
import SkipsLean.Generic.AnalyticZeroSet

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

/-- `ae_ne_zero_of_analytic` with the Borel structure given explicitly. -/
private theorem ae_ne_zero_of_analytic_rsl {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasurableSpace P] (hB : BorelSpace P) (μ : Measure P)
    (hμ : μ.IsAddHaarMeasure) {g : P → ℝ} (hg : AnalyticOnNhd ℝ g Set.univ)
    (hne : ∃ y, g y ≠ 0) : ∀ᵐ y ∂μ, g y ≠ 0 := by
  rw [ae_iff]
  simpa only [ne_eq, not_not] using measure_zeroSet_of_analytic μ hg hne

/-- A linear functional on a finite-dimensional space is analytic. -/
private theorem analyticOnNhd_linear_rsl {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (l : P →ₗ[ℝ] ℝ) : AnalyticOnNhd ℝ l Set.univ := by
  rw [← LinearMap.coe_toContinuousLinearMap' l]
  exact (LinearMap.toContinuousLinearMap l).analyticOnNhd _

open scoped Matrix.Norms.Elementwise in
/-- A polynomial in the tuple `θ = (W_read, b, W_write, c)` that is not identically zero is
nonzero at almost every `θ` (the Borel structure of the product is given by hand). -/
private theorem ae_ne_zero_rsl
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ))) [μ.IsAddHaarMeasure]
    {g : Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ) → ℝ}
    (hg : AnalyticOnNhd ℝ g Set.univ) (hne : ∃ y, g y ≠ 0) : ∀ᵐ θ ∂μ, g θ ≠ 0 := by
  have h1 : SecondCountableTopology (Matrix p m ℝ) :=
    inferInstanceAs (SecondCountableTopology (p → m → ℝ))
  have h2 : SecondCountableTopology (Matrix m q ℝ) :=
    inferInstanceAs (SecondCountableTopology (m → q → ℝ))
  have hB : BorelSpace (Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)) := Prod.borelSpace
  exact ae_ne_zero_of_analytic_rsl hB μ ‹_› hg hne

open scoped Matrix.Norms.Elementwise in
/-- An entry of the read is a coordinate of `θ`, so analytic. -/
private theorem analyticOnNhd_read_rsl (a : p) (i : m) :
    AnalyticOnNhd ℝ (fun θ : Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ) => θ.1 a i)
      Set.univ :=
  analyticOnNhd_linear_rsl (P := Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ))
    { toFun := fun θ => θ.1 a i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

open scoped Matrix.Norms.Elementwise in
/-- A bias is a coordinate of `θ`, so analytic. -/
private theorem analyticOnNhd_bias_rsl (i : m) :
    AnalyticOnNhd ℝ (fun θ : Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ) => θ.2.1 i)
      Set.univ :=
  analyticOnNhd_linear_rsl (P := Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ))
    { toFun := fun θ => θ.2.1 i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

open scoped Matrix.Norms.Elementwise in
/-- An entry of the write is a coordinate of `θ`, so analytic. -/
private theorem analyticOnNhd_write_rsl (i : m) (o : q) :
    AnalyticOnNhd ℝ (fun θ : Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ) => θ.2.2.1 i o)
      Set.univ :=
  analyticOnNhd_linear_rsl (P := Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ))
    { toFun := fun θ => θ.2.2.1 i o, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

open scoped Matrix.Norms.Elementwise in
/-- **(h1), (h2), (h3):** for an input `a` and an output `o`, at generic `θ` the reads and the
writes are nonzero (their coordinates `a` and `o` are) and the hyperplanes of the units are
distinct (the polynomial `w_{a,i} b_k − w_{a,k} b_i` is nonzero). -/
private theorem ae_units_rsl (a : p) (o : q)
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, (∀ i, θ.1ᵀ i ≠ 0) ∧ (∀ i, θ.2.2.1 i ≠ 0) ∧
      ∀ i k, i ≠ k → ∀ r : ℝ, ¬ (θ.1ᵀ i = r • θ.1ᵀ k ∧ θ.2.1 i = r * θ.2.1 k) := by
  classical
  have h1 : ∀ᵐ θ ∂μ, ∀ i, θ.1 a i ≠ 0 := ae_all_iff.2 fun i =>
    ae_ne_zero_rsl μ (analyticOnNhd_read_rsl a i)
      ⟨(Matrix.of fun _ _ => 1, 0, 0, 0), one_ne_zero⟩
  have h2 : ∀ᵐ θ ∂μ, ∀ i, θ.2.2.1 i o ≠ 0 := ae_all_iff.2 fun i =>
    ae_ne_zero_rsl μ (analyticOnNhd_write_rsl i o)
      ⟨(0, 0, Matrix.of fun _ _ => 1, 0), one_ne_zero⟩
  have h3 : ∀ᵐ θ ∂μ, ∀ i k, i ≠ k → θ.1 a i * θ.2.1 k - θ.1 a k * θ.2.1 i ≠ 0 := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun k => ?_
    by_cases hik : i = k
    · exact Filter.Eventually.of_forall fun _ h => absurd hik h
    have hg := ((analyticOnNhd_read_rsl (q := q) a i).mul (analyticOnNhd_bias_rsl k)).sub
      ((analyticOnNhd_read_rsl a k).mul (analyticOnNhd_bias_rsl i))
    refine (ae_ne_zero_rsl μ hg ⟨(Matrix.of fun _ j => if j = i then 1 else 0,
      fun j => if j = k then 1 else 0, 0, 0), ?_⟩).mono fun θ h _ => h
    simp [hik, Ne.symm hik]
  filter_upwards [h1, h2, h3] with θ h1 h2 h3
  refine ⟨fun i h0 => h1 i (congrFun h0 a), fun i h0 => h2 i (congrFun h0 o),
    fun i k hik r h => h3 i k hik ?_⟩
  have e : θ.1 a i = r * θ.1 a k := congrFun h.1 a
  rw [e, h.2]
  ring

omit [Fintype p] [Fintype q] [Fintype m] in
/-- The entry `a` of the linear part of `τ_o`. -/
private theorem sqTarget_snd_rsl (M : Matrix p q ℝ) (Wr : Matrix p m ℝ) (b : m → ℝ)
    (Ww : Matrix m q ℝ) (S : Finset m) (o : q) (a : p) :
    (sqTarget M Wr b Ww S o).2 a = M a o + ∑ i ∈ S, Ww i o * (2 * b i * Wr a i) := by
  simp only [sqTarget, sqForm, Prod.snd_add, Prod.snd_sum, Prod.smul_snd, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, transpose_apply]

omit [Fintype p] [Fintype q] [Fintype m] in
/-- The entry `(a, a')` of the quadratic part of `τ_o`. -/
private theorem sqTarget_fst_rsl (M : Matrix p q ℝ) (Wr : Matrix p m ℝ) (b : m → ℝ)
    (Ww : Matrix m q ℝ) (S : Finset m) (o : q) (a a' : p) :
    (sqTarget M Wr b Ww S o).1 a a' = ∑ i ∈ S, Ww i o * (Wr a i * Wr a' i) := by
  simp only [sqTarget, sqForm, Prod.fst_add, Prod.fst_sum, Prod.smul_fst, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, transpose_apply,
    Matrix.zero_apply, zero_add]

open scoped Matrix.Norms.Elementwise in
/-- The entry `a` of the linear part of `τ_o` is a polynomial in `θ`, so analytic. -/
private theorem analyticOnNhd_sqTarget_snd_rsl (M : Matrix p q ℝ) (S : Finset m) (o : q)
    (a : p) :
    AnalyticOnNhd ℝ (fun θ : Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ) =>
      (sqTarget M θ.1 θ.2.1 θ.2.2.1 S o).2 a) Set.univ := by
  simp only [sqTarget_snd_rsl]
  exact analyticOnNhd_const.add (Finset.analyticOnNhd_fun_sum _ fun i _ =>
    (analyticOnNhd_write_rsl i o).mul
      ((analyticOnNhd_const.mul (analyticOnNhd_bias_rsl i)).mul (analyticOnNhd_read_rsl a i)))

open scoped Matrix.Norms.Elementwise in
/-- The entry `(a, a')` of the quadratic part of `τ_o` is a polynomial in `θ`, so analytic. -/
private theorem analyticOnNhd_sqTarget_fst_rsl (M : Matrix p q ℝ) (S : Finset m) (o : q)
    (a a' : p) :
    AnalyticOnNhd ℝ (fun θ : Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ) =>
      (sqTarget M θ.1 θ.2.1 θ.2.2.1 S o).1 a a') Set.univ := by
  simp only [sqTarget_fst_rsl]
  exact Finset.analyticOnNhd_fun_sum _ fun i _ => (analyticOnNhd_write_rsl i o).mul
    ((analyticOnNhd_read_rsl a i).mul (analyticOnNhd_read_rsl a' i))

omit [Fintype p] [Fintype q] in
/-- An entry of a nonzero matrix is nonzero. -/
private theorem exists_ne_zero_rsl {M : Matrix p q ℝ} (hM : M ≠ 0) : ∃ a o, M a o ≠ 0 := by
  by_contra h
  exact hM (Matrix.ext fun a o => by_contra fun h' => h ⟨a, o, h'⟩)

open scoped Matrix.Norms.Elementwise in
/-- For `M a o ≠ 0`: at generic `θ`, for every `S` the entry `a` of the linear part of `τ_o` is
nonzero (a polynomial in `θ`, equal to `M a o` at `θ = 0`). -/
private theorem ae_sqTarget_snd_ne_zero_rsl (M : Matrix p q ℝ) {a : p} {o : q} (hM : M a o ≠ 0)
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ S : Finset m, (sqTarget M θ.1 θ.2.1 θ.2.2.1 S o).2 a ≠ 0 := by
  refine ae_all_iff.2 fun S => ae_ne_zero_rsl μ (analyticOnNhd_sqTarget_snd_rsl M S o a)
    ⟨0, ?_⟩
  simpa only [sqTarget_snd_rsl, Prod.fst_zero, Prod.snd_zero, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero] using hM

/-- **The generic condition of the proof of Theorem C.2 (iii) for `M ≠ 0`:** for generic
`θ = (W_read, b, W_write, c)` and every set `S` of units, some `τ_o` is nonzero (when the writes
vanish, `τ_o = (0, M_{:,o})`). -/
theorem ae_exists_sqTarget_ne_zero (M : Matrix p q ℝ) (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ S : Finset m, ∃ o : q, sqTarget M θ.1 θ.2.1 θ.2.2.1 S o ≠ 0 := by
  -- the entry `a` of the linear part of `τ_o` is a nonzero polynomial in `θ`
  obtain ⟨a, o, hao⟩ := exists_ne_zero_rsl hM
  filter_upwards [ae_sqTarget_snd_ne_zero_rsl M hao μ] with θ hθ
  exact fun S => ⟨o, fun h => hθ S (by rw [h]; rfl)⟩

/-- **Theorem C.1 (iii) of the absorb paper for ReLU² blocks with biases:** fix `M ≠ 0`. For
generic `θ = (W_read, b, W_write, c)` no ReLU² block with biases of the same width computes
`x M + B_θ(x)`. -/
theorem ae_not_reluSq_absorbB_same_width (M : Matrix p q ℝ) (hM : M ≠ 0)
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ¬ ∃ (Wr' : Matrix p m ℝ) (b' : m → ℝ) (Ww' : Matrix m q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* M + vanillaBlockB reluSq θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
        = vanillaBlockB reluSq Wr' b' Ww' c' x := by
  obtain ⟨a, o, -⟩ := exists_ne_zero_rsl hM
  filter_upwards [ae_units_rsl a o μ, ae_exists_sqTarget_ne_zero M hM μ] with θ hu hG
  rintro ⟨Wr', b', Ww', c', h⟩
  -- the polynomials of the cells satisfy (2), so the absorbing block has more units
  have hcell := fun x₀ (hx₀ : ∀ i, (x₀ ᵥ* θ.1) i + θ.2.1 i ≠ 0) hx₀' =>
    reluSqCell_eq_of_vanillaBlockB_absorb _ _ _ _ _ _ _ _ M h x₀
      (fun i hi => absurd hi (hx₀ i)) hx₀'
  exact lt_irrefl _ (card_lt_card_of_reluSqCell _ _ _ _ _ _ _ _ M hu.1 hu.2.1 hu.2.2 hG hcell)

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
