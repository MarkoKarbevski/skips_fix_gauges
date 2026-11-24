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

section Gram

variable {n ι : Type*} [Fintype n] [Fintype ι]

/-- The coordinates of a family of pairs `(A, ℓ)` of a matrix and a row, as the columns of a
matrix. -/
private def coordMat_rsl (v : ι → Matrix n n ℝ × (n → ℝ)) : Matrix ((n × n) ⊕ n) ι ℝ :=
  Matrix.of fun k s => Sum.elim (fun aa : n × n => (v s).1 aa.1 aa.2) (fun a => (v s).2 a) k

omit [Fintype n] in
/-- A combination of the family vanishes if and only if the matrix of the coordinates kills its
coefficients. -/
private theorem coordMat_mulVec_eq_zero_iff_rsl (v : ι → Matrix n n ℝ × (n → ℝ)) (g : ι → ℝ) :
    coordMat_rsl v *ᵥ g = 0 ↔ ∑ s, g s • v s = 0 := by
  have e1 : ∀ a a', (coordMat_rsl v *ᵥ g) (Sum.inl (a, a')) = (∑ s, g s • v s).1 a a' := by
    intro a a'
    simp only [mulVec, dotProduct, coordMat_rsl, of_apply, Sum.elim_inl, Prod.fst_sum,
      Matrix.sum_apply, Prod.smul_fst, Matrix.smul_apply, smul_eq_mul, mul_comm]
  have e2 : ∀ a, (coordMat_rsl v *ᵥ g) (Sum.inr a) = (∑ s, g s • v s).2 a := by
    intro a
    simp only [mulVec, dotProduct, coordMat_rsl, of_apply, Sum.elim_inr, Prod.snd_sum,
      Finset.sum_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_comm]
  constructor
  · intro h
    refine Prod.ext (Matrix.ext fun a a' => ?_) (funext fun a => ?_)
    · rw [← e1, h]
      rfl
    · rw [← e2, h]
      rfl
  · intro h
    funext k
    rcases k with ⟨a, a'⟩ | a
    · rw [e1, h]
      rfl
    · rw [e2, h]
      rfl

variable [DecidableEq ι]

/-- If the Gram matrix `CᵀC` of the coordinates is invertible, the family is linearly
independent: a vanishing combination with coefficients `g` has `C g = 0`, so `CᵀC g = 0`. -/
private theorem linearIndependent_of_det_ne_zero_rsl (v : ι → Matrix n n ℝ × (n → ℝ))
    (h : ((coordMat_rsl v)ᵀ * coordMat_rsl v).det ≠ 0) : LinearIndependent ℝ v := by
  refine Fintype.linearIndependent_iff.2 fun g hg => ?_
  have h1 := (coordMat_mulVec_eq_zero_iff_rsl v g).2 hg
  have h2 : ((coordMat_rsl v)ᵀ * coordMat_rsl v) *ᵥ g = 0 := by
    rw [← mulVec_mulVec, h1, mulVec_zero]
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero h h2
  intro s
  rw [h3]
  rfl

/-- If the family is linearly independent, the Gram matrix `CᵀC` of the coordinates is
invertible: `CᵀC g = 0` gives `|C g|² = gᵀCᵀC g = 0`, so `C g = 0` and `g = 0`. -/
private theorem det_ne_zero_of_linearIndependent_rsl (v : ι → Matrix n n ℝ × (n → ℝ))
    (h : LinearIndependent ℝ v) : ((coordMat_rsl v)ᵀ * coordMat_rsl v).det ≠ 0 := by
  intro h0
  obtain ⟨g, hg, hg0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h1 : coordMat_rsl v *ᵥ g ⬝ᵥ coordMat_rsl v *ᵥ g = 0 := by
    have e : g ⬝ᵥ (((coordMat_rsl v)ᵀ * coordMat_rsl v) *ᵥ g) = 0 := by
      rw [hg0, dotProduct_zero]
    rwa [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose] at e
  have h2 := (coordMat_mulVec_eq_zero_iff_rsl v g).1 (dotProduct_self_eq_zero.1 h1)
  exact hg (funext (Fintype.linearIndependent_iff.1 h g h2))

end Gram

section Square

variable {d m : Type*} [Fintype d] [DecidableEq d] [Fintype m]

/-- The family of the generic condition: the `τ_o` and the `φ(w_i, b_i)`, `i ∈ U`. -/
private def sqFamily_rsl (M : Matrix d d ℝ) (S U : Finset m)
    (θ : Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ)) : d ⊕ U → Matrix d d ℝ × (d → ℝ) :=
  Sum.elim (fun o : d => sqTarget M θ.1 θ.2.1 θ.2.2.1 S o)
    (fun i : U => sqForm (θ.1ᵀ (i : m)) (θ.2.1 i))

open scoped Matrix.Norms.Elementwise in
omit [DecidableEq d] in
/-- The coordinates of the family are polynomials in `θ`, so analytic. -/
private theorem analyticOnNhd_coordMat_rsl (M : Matrix d d ℝ) (S U : Finset m)
    (k : (d × d) ⊕ d) (s : d ⊕ U) :
    AnalyticOnNhd ℝ (fun θ : Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ) =>
      coordMat_rsl (sqFamily_rsl M S U θ) k s) Set.univ := by
  rcases k with ⟨a, a'⟩ | a <;> rcases s with o | i <;>
    simp only [coordMat_rsl, sqFamily_rsl, of_apply, Sum.elim_inl, Sum.elim_inr]
  · exact analyticOnNhd_sqTarget_fst_rsl M S o a a'
  · simp only [sqForm, vecMulVec_apply, transpose_apply]
    exact (analyticOnNhd_read_rsl a (i : m)).mul (analyticOnNhd_read_rsl a' (i : m))
  · exact analyticOnNhd_sqTarget_snd_rsl M S o a
  · simp only [sqForm, Pi.smul_apply, smul_eq_mul, transpose_apply]
    exact (analyticOnNhd_const.mul (analyticOnNhd_bias_rsl (i : m))).mul
      (analyticOnNhd_read_rsl a (i : m))

/-- The reads of the special tuple: `e_a`, and `e_{a₀} + e_a` for `a ≠ a₀`. -/
private def sqVec_rsl (a₀ : d) : d ⊕ {a : d // a ≠ a₀} → d → ℝ :=
  Sum.elim (fun a => Pi.single a 1) (fun a => Pi.single a₀ 1 + Pi.single (a : d) 1)

/-- The matrices `e_a e_aᵀ` and `(e_{a₀} + e_a)(e_{a₀} + e_a)ᵀ`, `a ≠ a₀`, are linearly
independent: in a vanishing combination the entry `(a₀, a)` is the coefficient of the second kind,
and then the diagonal entries are the coefficients of the first kind. -/
private theorem linearIndependent_sqVec_rsl (a₀ : d) :
    LinearIndependent ℝ (fun j => vecMulVec (sqVec_rsl a₀ j) (sqVec_rsl a₀ j)) := by
  refine Fintype.linearIndependent_iff.2 fun c hc => ?_
  have h1 : ∀ a : {a : d // a ≠ a₀}, c (Sum.inr a) = 0 := by
    intro a
    have e := congrFun (congrFun hc a₀) (a : d)
    rw [Fintype.sum_sum_type] at e
    have hx : ∀ x : {a : d // a ≠ a₀}, a₀ ≠ (x : d) := fun x => x.2.symm
    simpa [sqVec_rsl, vecMulVec_apply, Pi.single_apply, hx, a.2, Subtype.val_inj] using e
  have h2 : ∀ a : d, c (Sum.inl a) = 0 := by
    intro a
    have e := congrFun (congrFun hc a) a
    rw [Fintype.sum_sum_type] at e
    simpa [sqVec_rsl, vecMulVec_apply, Pi.single_apply, h1] using e
  rintro (a | a)
  exacts [h2 a, h1 a]

omit [Fintype m] in
/-- **The special tuple:** for `|U| < 2 d`, at the tuple with all writes and biases `0` and the
reads `e_a`, `e_{a₀} + e_a` on `U` (through an injection of `U`), the family is linearly
independent: the first components give the coefficients on `U`, then `M` invertible the others. -/
private theorem exists_linearIndependent_sqFamily_rsl (M : Matrix d d ℝ) (hM : IsUnit M.det)
    (S U : Finset m) (hU : U.card < 2 * Fintype.card d) :
    ∃ θ : Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ),
      LinearIndependent ℝ (sqFamily_rsl M S U θ) := by
  classical
  -- an input `a₀` and an injection `ι : U ↪ d ⊕ {a // a ≠ a₀}`
  obtain ⟨a₀⟩ := Fintype.card_pos_iff.1 (by omega : 0 < Fintype.card d)
  have hcard : Fintype.card U ≤ Fintype.card (d ⊕ {a : d // a ≠ a₀}) := by
    have h' : Fintype.card {a : d // a ≠ a₀} = Fintype.card d - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    rw [Fintype.card_sum, Fintype.card_coe, h']
    omega
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  -- the special tuple
  let W : Matrix d m ℝ := Matrix.of fun a i =>
    if h : i ∈ U then sqVec_rsl a₀ (ι ⟨i, h⟩) a else 0
  have hW : ∀ i : U, Wᵀ (i : m) = sqVec_rsl a₀ (ι i) := by
    intro i
    funext a
    simp only [W, transpose_apply, of_apply, i.2, dite_true]
  refine ⟨(W, 0, 0, 0), Fintype.linearIndependent_iff.2 fun g hg => ?_⟩
  rw [Fintype.sum_sum_type] at hg
  -- the quadratic parts: `∑_{i ∈ U} g_i (e e^⊤)(ι i) = 0`
  have h1 : ∑ i : U, g (Sum.inr i) • vecMulVec (sqVec_rsl a₀ (ι i)) (sqVec_rsl a₀ (ι i)) = 0 := by
    have e := congrArg Prod.fst hg
    simp only [sqFamily_rsl, sqTarget, sqForm, Sum.elim_inl, Sum.elim_inr, hW] at e
    simpa only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, Prod.fst_zero, Matrix.zero_apply,
      Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero, smul_zero, zero_add] using e
  -- the linear parts: `M g_d = 0`
  have h2 : M *ᵥ (fun o => g (Sum.inl o)) = 0 := by
    have e := congrArg Prod.snd hg
    simp only [sqFamily_rsl, sqTarget, sqForm, Sum.elim_inl, Sum.elim_inr, hW] at e
    simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, Prod.snd_zero, Matrix.zero_apply,
      Pi.zero_apply, mul_zero, zero_smul, Finset.sum_const_zero, add_zero, smul_zero] at e
    funext a
    have e' := congrFun e a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e'
    simp only [mulVec, dotProduct, Pi.zero_apply]
    rw [← e']
    exact Finset.sum_congr rfl fun o _ => mul_comm _ _
  have hi := Fintype.linearIndependent_iff.1
    ((linearIndependent_sqVec_rsl a₀).comp ι ι.injective) _ h1
  have ho := Matrix.eq_zero_of_mulVec_eq_zero hM.ne_zero h2
  rintro (o | i)
  · exact congrFun ho o
  · exact hi i

open scoped Matrix.Norms.Elementwise in
/-- For `|U| < 2 d`: at generic `θ` the family is linearly independent, since the determinant of
the Gram matrix of its coordinates is a polynomial in `θ`, nonzero at the special tuple. -/
private theorem ae_linearIndependent_sqFamily_rsl (M : Matrix d d ℝ) (hM : IsUnit M.det)
    (S U : Finset m) (hU : U.card < 2 * Fintype.card d)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, LinearIndependent ℝ (sqFamily_rsl M S U θ) := by
  classical
  have hg : AnalyticOnNhd ℝ (fun θ : Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ) =>
      ((coordMat_rsl (sqFamily_rsl M S U θ))ᵀ * coordMat_rsl (sqFamily_rsl M S U θ)).det)
      Set.univ := by
    simp only [Matrix.det_apply', Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun s _ => Finset.analyticOnNhd_fun_sum _ fun k _ =>
        (analyticOnNhd_coordMat_rsl M S U k (σ s)).mul (analyticOnNhd_coordMat_rsl M S U k s))
  obtain ⟨θ₀, h₀⟩ := exists_linearIndependent_sqFamily_rsl M hM S U hU
  filter_upwards [ae_ne_zero_rsl μ hg ⟨θ₀, det_ne_zero_of_linearIndependent_rsl _ h₀⟩]
    with θ hθ
  exact linearIndependent_of_det_ne_zero_rsl _ hθ

/-- **Proof of Theorem C.2 (iii) of the absorb paper, "Genericity":** let `M` be invertible. For
generic `θ = (W_read, b, W_write, c)` and all disjoint sets `S`, `U` of units with `|U| < 2 d`, the
`d + |U|` vectors `τ_o` and `φ(w_i, b_i)`, `i ∈ U`, are linearly independent. -/
theorem ae_linearIndependent_sqTarget (M : Matrix d d ℝ) (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ S U : Finset m, Disjoint S U → U.card < 2 * Fintype.card d →
      LinearIndependent ℝ (Sum.elim (fun o : d => sqTarget M θ.1 θ.2.1 θ.2.2.1 S o)
        (fun i : U => sqForm (θ.1ᵀ (i : m)) (θ.2.1 i))) := by
  -- for each of the finitely many pairs `(S, U)` with `|U| < 2 d`, a polynomial condition
  refine ae_all_iff.2 fun S => ae_all_iff.2 fun U => ?_
  by_cases hU : U.card < 2 * Fintype.card d
  · filter_upwards [ae_linearIndependent_sqFamily_rsl M hM S U hU μ] with θ hθ
    exact fun _ _ => hθ
  · exact Filter.Eventually.of_forall fun _ _ h => absurd h hU

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
  classical
  obtain ⟨a⟩ := ‹Nonempty d›
  filter_upwards [ae_units_rsl a a μ, ae_linearIndependent_sqTarget M hM μ] with θ hu hG
  intro m' _ hm' Wr' b' Ww' c'
  by_contra hc
  have h : ∀ x : d → ℝ, x ᵥ* M + vanillaBlockB reluSq θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
      = vanillaBlockB reluSq Wr' b' Ww' c' x := fun x => not_not.1 (not_exists.1 hc x)
  -- the polynomials of the cells satisfy (2), so the absorbing block has `2 d` more units
  have hcell := fun x₀ (hx₀ : ∀ i, (x₀ ᵥ* θ.1) i + θ.2.1 i ≠ 0) hx₀' =>
    reluSqCell_eq_of_vanillaBlockB_absorb _ _ _ _ _ _ _ _ M h x₀
      (fun i hi => absurd hi (hx₀ i)) hx₀'
  have hle := card_add_two_mul_card_le_of_reluSqCell _ _ _ _ _ _ _ _ M hu.1 hu.2.1 hu.2.2 hG
    hcell
  omega

open scoped Matrix.Norms.Elementwise in
/-- At generic `θ`, a read with at least as many columns as rows has full rank. -/
private theorem ae_rank_rsl (hm : Fintype.card d ≤ Fintype.card m)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, θ.1.rank = Fintype.card d := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hm
  -- `θ ↦ det W_read[:, e]` is a polynomial, equal to `1` when `W_read[:, e] = 1`
  have hg : AnalyticOnNhd ℝ (fun θ : Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ) =>
      (θ.1.submatrix id e).det) Set.univ := by
    simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq]
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => analyticOnNhd_read_rsl (σ i) (e i))
  have h0 : ((Matrix.of fun a i => if i = e a then (1 : ℝ) else 0 : Matrix d m ℝ).submatrix
      id e).det ≠ 0 := by
    have h1 : (Matrix.of fun a i => if i = e a then (1 : ℝ) else 0 : Matrix d m ℝ).submatrix
        id e = 1 := by
      ext a b
      simp only [Matrix.submatrix_apply, id_eq, Matrix.of_apply, Matrix.one_apply,
        e.injective.eq_iff, eq_comm]
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  filter_upwards [ae_ne_zero_rsl μ hg ⟨(_, 0, 0, 0), h0⟩] with θ hW
  -- an invertible `d × d` column submatrix gives rank `d`
  refine le_antisymm (Matrix.rank_le_card_height _) ?_
  have h3 := Matrix.rank_submatrix_le θ.1 id e
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hW))]
    at h3
  exact h3

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
  -- generic reads have rank `d`: the construction gives `3 d` more units
  filter_upwards [ae_rank_rsl hm μ, ae_not_reluSq_absorbB_of_card_lt M hM μ] with θ hr hlt
  exact ⟨exists_vanillaBlockB_add_linear_reluSq_of_rank θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 hr M, hlt⟩

end Square

end Skips
