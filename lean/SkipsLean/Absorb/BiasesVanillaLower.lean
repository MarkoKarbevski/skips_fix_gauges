import SkipsLean.Absorb.BiasesConstructions
import SkipsLean.Absorb.FewerUnits
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

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

/-- A condition that holds for every Haar measure on `F` holds at `Φ x` for `μ`-almost every `x`,
for an onto linear map `Φ` (`ae_comp_linearMap_mem_iff`). -/
private theorem ae_comp_of_surjective_bvl {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

/-- The projection `(W_read, b, W_write, c) ↦ (W_read, W_write)`. -/
private def projLin_bvl (A B C D : Type*) [AddCommGroup A] [Module ℝ A] [AddCommGroup B]
    [Module ℝ B] [AddCommGroup C] [Module ℝ C] [AddCommGroup D] [Module ℝ D] :
    A × B × C × D →ₗ[ℝ] A × C :=
  (LinearMap.fst ℝ A (B × C × D)).prod ((LinearMap.fst ℝ C D).comp
    ((LinearMap.snd ℝ B (C × D)).comp (LinearMap.snd ℝ A (B × C × D))))

open scoped Matrix.Norms.Elementwise in
/-- **A condition that holds at generic pairs `(W_read, W_write)` holds at the reads and writes of
generic tuples `(W_read, b, W_write, c)`.** -/
private theorem ae_tuple_bvl {p q m : Type*} [Fintype p] [Fintype q] [Fintype m]
    (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ))) [μ.IsAddHaarMeasure]
    {P : Matrix p m ℝ × Matrix m q ℝ → Prop}
    (hP : ∀ ν : Measure (Matrix p m ℝ × Matrix m q ℝ), ν.IsAddHaarMeasure → ∀ᵐ W ∂ν, P W) :
    ∀ᵐ θ ∂μ, P (θ.1, θ.2.2.1) := by
  have h1 : SecondCountableTopology (Matrix p m ℝ) :=
    inferInstanceAs (SecondCountableTopology (p → m → ℝ))
  have h2 : SecondCountableTopology (Matrix m q ℝ) :=
    inferInstanceAs (SecondCountableTopology (m → q → ℝ))
  have hBF : BorelSpace (Matrix p m ℝ × Matrix m q ℝ) := Prod.borelSpace
  have hBE : BorelSpace (Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)) := Prod.borelSpace
  have hs : Function.Surjective (projLin_bvl (Matrix p m ℝ) (m → ℝ) (Matrix m q ℝ) (q → ℝ)) :=
    fun W => ⟨(W.1, 0, W.2, 0), rfl⟩
  exact ae_comp_of_surjective_bvl hBE hBF μ ‹_› _ hs hP

section Rays

variable {p q m : Type*} [Fintype p] [Fintype m]

/-- An output coordinate of a block with biases. -/
private theorem vanillaBlockB_apply_bvl {k : Type*} [Fintype k] (σ : ℝ → ℝ) (W : Matrix p k ℝ)
    (b : k → ℝ) (V : Matrix k q ℝ) (c : q → ℝ) (z : p → ℝ) (o : q) :
    vanillaBlockB σ W b V c z o = ∑ i, σ ((z ᵥ* W) i + b i) * V i o + c o := rfl

/-- An output coordinate of a block without biases. -/
private theorem vanillaBlock_apply_bvl {k : Type*} [Fintype k] (σ : ℝ → ℝ) (W : Matrix p k ℝ)
    (V : Matrix k q ℝ) (z : p → ℝ) (o : q) :
    vanillaBlock σ W V z o = ∑ i, σ ((z ᵥ* W) i) * V i o := rfl

/-- `|σ(t y + β) − t ReLU(y)| ≤ κ + |β|` for `t > 0`: ReLU changes by at most `|β|` when its
argument changes by `β`, and `ReLU(t y) = t ReLU(y)`. -/
private theorem abs_sub_relu_le_bvl {σ : ℝ → ℝ} {κ : ℝ} (hκ : ∀ z, |σ z - relu z| ≤ κ) {t : ℝ}
    (ht : 0 < t) (y β : ℝ) : |σ (t * y + β) - t * relu y| ≤ κ + |β| := by
  have h1 := hκ (t * y + β)
  have h2 : |relu (t * y + β) - relu (t * y)| ≤ |β| := by
    have h3 := abs_max_sub_max_le_abs (t * y + β) (t * y) 0
    rw [add_sub_cancel_left] at h3
    exact h3
  have h4 : relu (t * y) = t * relu y := by
    rw [relu, relu, mul_max_of_nonneg _ _ ht.le, mul_zero]
  rw [← h4, ← sub_add_sub_cancel _ (relu (t * y + β))]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- `|∑ᵢ (σ(t yᵢ + βᵢ) − t ReLU(yᵢ)) wᵢ| ≤ ∑ᵢ (κ + |βᵢ|) |wᵢ|` for `t > 0`. -/
private theorem abs_sum_sub_relu_le_bvl {ι : Type*} [Fintype ι] {σ : ℝ → ℝ} {κ : ℝ}
    (hκ : ∀ z, |σ z - relu z| ≤ κ) {t : ℝ} (ht : 0 < t) (y β w : ι → ℝ) :
    |∑ i, (σ (t * y i + β i) - t * relu (y i)) * w i| ≤ ∑ i, (κ + |β i|) * |w i| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_sub_relu_le_bvl hκ ht _ _) (abs_nonneg _)

/-- **Proof of Theorem C.2 (ii) of the absorb paper, the step along rays:** let `σ` be at a bounded
distance from ReLU. If a block with biases absorbs `x M` into a block with biases, of any width,
then the ReLU blocks without biases that have the same reads and writes satisfy the same equation.
(Evaluate at `t x`, divide by `t`, and let `t → ∞`.) -/
theorem relu_absorb_of_vanillaBlockB_absorb {σ : ℝ → ℝ} (hσ : ∃ κ : ℝ, ∀ z, |σ z - relu z| ≤ κ)
    {m' : Type*} [Fintype m'] (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ)
    (Wr' : Matrix p m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' q ℝ) (c' : q → ℝ) (M : Matrix p q ℝ)
    (h : ∀ x : p → ℝ, x ᵥ* M + vanillaBlockB σ Wr b Ww c x = vanillaBlockB σ Wr' b' Ww' c' x) :
    ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x := by
  obtain ⟨κ, hκ⟩ := hσ
  have hκ0 : 0 ≤ κ := (abs_nonneg _).trans (hκ 0)
  intro x
  funext o
  -- the equation at `t x`, coordinate `o`
  have hG : ∀ t : ℝ, t * (x ᵥ* M) o + (∑ i, σ (t * (x ᵥ* Wr) i + b i) * Ww i o + c o)
      = ∑ j, σ (t * (x ᵥ* Wr') j + b' j) * Ww' j o + c' o := by
    intro t
    have h1 := congrFun (h (t • x)) o
    simpa only [Pi.add_apply, vanillaBlockB_apply_bvl, Matrix.smul_vecMul, Pi.smul_apply,
      smul_eq_mul] using h1
  -- the defect `D` of the ReLU equation at `o` has `|t D| ≤ C` for all `t > 0`
  obtain ⟨D, hD⟩ : ∃ D, D = (x ᵥ* M) o + ∑ i, relu ((x ᵥ* Wr) i) * Ww i o
      - ∑ j, relu ((x ᵥ* Wr') j) * Ww' j o := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = ∑ i, (κ + |b i|) * |Ww i o| + ∑ j, (κ + |b' j|) * |Ww' j o|
      + (|c' o| + |c o|) := ⟨_, rfl⟩
  have hbound : ∀ t : ℝ, 0 < t → |t * D| ≤ C := by
    intro t ht
    -- `t D = ∑ⱼ (σ(t y'ⱼ + b'ⱼ) - t ReLU(y'ⱼ)) ŵ'ⱼ - ∑ᵢ (σ(t yᵢ + bᵢ) - t ReLU(yᵢ)) ŵᵢ + c' - c`
    have e : t * D = ∑ j, (σ (t * (x ᵥ* Wr') j + b' j) - t * relu ((x ᵥ* Wr') j)) * Ww' j o
        - ∑ i, (σ (t * (x ᵥ* Wr) i + b i) - t * relu ((x ᵥ* Wr) i)) * Ww i o
        + (c' o - c o) := by
      simp only [sub_mul, Finset.sum_sub_distrib, hD, mul_add, mul_sub, Finset.mul_sum,
        mul_assoc]
      linarith [hG t]
    rw [e, hC]
    refine (abs_add_le _ _).trans ((add_le_add (abs_sub _ _) (abs_sub _ _)).trans ?_)
    linarith [abs_sum_sub_relu_le_bvl hκ ht (fun j => (x ᵥ* Wr') j) b' (fun j => Ww' j o),
      abs_sum_sub_relu_le_bvl hκ ht (fun i => (x ᵥ* Wr) i) b (fun i => Ww i o)]
  -- hence `D = 0`: else `t = (C + 1)/|D|` gives `|t D| = C + 1`
  have hD0 : D = 0 := by
    by_contra hne
    have hC0 : 0 ≤ C := hC ▸ add_nonneg (add_nonneg
      (Finset.sum_nonneg fun _ _ => mul_nonneg (add_nonneg hκ0 (abs_nonneg _)) (abs_nonneg _))
      (Finset.sum_nonneg fun _ _ => mul_nonneg (add_nonneg hκ0 (abs_nonneg _)) (abs_nonneg _)))
      (add_nonneg (abs_nonneg _) (abs_nonneg _))
    have hDpos : 0 < |D| := abs_pos.2 hne
    have ht : 0 < (C + 1) / |D| := div_pos (by linarith) hDpos
    have h1 := hbound _ ht
    rw [abs_mul, abs_of_pos ht, div_mul_cancel₀ _ hDpos.ne'] at h1
    linarith
  rw [Pi.add_apply, vanillaBlock_apply_bvl, vanillaBlock_apply_bvl]
  linarith

/-- **The step along rays for ReLU blocks with biases.** -/
theorem relu_absorb_of_vanillaBlockB_relu_absorb {m' : Type*} [Fintype m'] (Wr : Matrix p m ℝ)
    (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ) (Wr' : Matrix p m' ℝ) (b' : m' → ℝ)
    (Ww' : Matrix m' q ℝ) (c' : q → ℝ) (M : Matrix p q ℝ)
    (h : ∀ x : p → ℝ,
      x ᵥ* M + vanillaBlockB relu Wr b Ww c x = vanillaBlockB relu Wr' b' Ww' c' x) :
    ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x := by
  -- ReLU is at distance `0` from itself
  exact relu_absorb_of_vanillaBlockB_absorb ⟨0, fun z => by rw [sub_self, abs_zero]⟩ Wr b Ww c
    Wr' b' Ww' c' M h

/-- **The step along rays for GELU blocks with biases.** -/
theorem relu_absorb_of_vanillaBlockB_gelu_absorb {m' : Type*} [Fintype m'] (Wr : Matrix p m ℝ)
    (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ) (Wr' : Matrix p m' ℝ) (b' : m' → ℝ)
    (Ww' : Matrix m' q ℝ) (c' : q → ℝ) (M : Matrix p q ℝ)
    (h : ∀ x : p → ℝ,
      x ᵥ* M + vanillaBlockB gelu Wr b Ww c x = vanillaBlockB gelu Wr' b' Ww' c' x) :
    ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu Wr Ww x = vanillaBlock relu Wr' Ww' x := by
  -- GELU is at distance at most `1` from ReLU
  exact relu_absorb_of_vanillaBlockB_absorb ⟨1, abs_gelu_sub_relu_le⟩ Wr b Ww c Wr' b' Ww' c' M h

/-- **Theorem C.1 (iii) for an activation at a bounded distance from ReLU, with finitely many
outputs.** (The statements below do not assume `[Fintype q]`; for an infinite `q` they fail for
some additive Haar measures, see the report of `lean-bvl`. With `[Fintype q]` each of them is this
lemma with `κ = 0` for ReLU and `κ = 1` for GELU.) -/
private theorem ae_not_absorbB_same_width_bvl [Fintype q] {σ : ℝ → ℝ}
    (hσ : ∃ κ : ℝ, ∀ z, |σ z - relu z| ≤ κ) (hp : 2 ≤ Fintype.card p) (M : Matrix p q ℝ)
    (hM : M ≠ 0) (μ : Measure (Matrix p m ℝ × (m → ℝ) × Matrix m q ℝ × (q → ℝ)))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ¬ ∃ (Wr' : Matrix p m ℝ) (b' : m → ℝ) (Ww' : Matrix m q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* M + vanillaBlockB σ θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
        = vanillaBlockB σ Wr' b' Ww' c' x := by
  classical
  -- generic tuples have generic reads and writes, where no ReLU block of the same width absorbs
  filter_upwards [ae_tuple_bvl (P := fun W : Matrix p m ℝ × Matrix m q ℝ =>
      ¬ ∃ (Wr' : Matrix p m ℝ) (Ww' : Matrix m q ℝ),
        ∀ x : p → ℝ, x ᵥ* M + vanillaBlock relu W.1 W.2 x = vanillaBlock relu Wr' Ww' x) μ
      fun ν _ => ae_not_relu_absorb_same_width hp M hM ν] with θ hθ
  -- the step along rays
  rintro ⟨Wr', b', Ww', c', h⟩
  exact hθ ⟨Wr', Ww', relu_absorb_of_vanillaBlockB_absorb hσ _ _ _ _ _ _ _ _ M h⟩

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

/-- `ae_ne_zero_of_analytic` with the Borel structure given explicitly. -/
private theorem ae_ne_zero_of_analytic_bvl {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasurableSpace P] (hB : BorelSpace P) (μ : Measure P)
    (hμ : μ.IsAddHaarMeasure) {g : P → ℝ} (hg : AnalyticOnNhd ℝ g Set.univ)
    (hne : ∃ y, g y ≠ 0) : ∀ᵐ y ∂μ, g y ≠ 0 :=
  ae_ne_zero_of_analytic μ hg hne

open scoped Matrix.Norms.Elementwise in
/-- At generic weights, a read with at least as many columns as rows has full rank. -/
private theorem ae_rank_bvl (hm : Fintype.card d ≤ Fintype.card m)
    (ν : Measure (Matrix d m ℝ × Matrix m d ℝ)) [ν.IsAddHaarMeasure] :
    ∀ᵐ W ∂ν, W.1.rank = Fintype.card d := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hm
  -- `W ↦ det W_read[:, e]` is a polynomial, equal to `1` when `W_read[:, e] = 1`
  have he : ∀ a i, AnalyticOnNhd ℝ (fun W : Matrix d m ℝ × Matrix m d ℝ => W.1 a i) Set.univ :=
    fun a i => analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ a i).comp
      (LinearMap.fst ℝ (Matrix d m ℝ) (Matrix m d ℝ)))
  have hg : AnalyticOnNhd ℝ (fun W : Matrix d m ℝ × Matrix m d ℝ =>
      (W.1.submatrix id e).det) Set.univ := by
    simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq]
    exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
      (Finset.analyticOnNhd_fun_prod _ fun i _ => he (σ i) (e i))
  have h0 : ((Matrix.of fun a i => if i = e a then (1 : ℝ) else 0 : Matrix d m ℝ).submatrix
      id e).det ≠ 0 := by
    have h1 : (Matrix.of fun a i => if i = e a then (1 : ℝ) else 0 : Matrix d m ℝ).submatrix
        id e = 1 := by
      ext a b
      simp only [Matrix.submatrix_apply, id_eq, Matrix.of_apply, Matrix.one_apply,
        e.injective.eq_iff, eq_comm]
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  have h1 : SecondCountableTopology (Matrix d m ℝ) :=
    inferInstanceAs (SecondCountableTopology (d → m → ℝ))
  have h2 : SecondCountableTopology (Matrix m d ℝ) :=
    inferInstanceAs (SecondCountableTopology (m → d → ℝ))
  have hB : BorelSpace (Matrix d m ℝ × Matrix m d ℝ) := Prod.borelSpace
  filter_upwards [ae_ne_zero_of_analytic_bvl hB ν ‹_› hg ⟨(_, 0), h0⟩] with W hW
  -- an invertible `d × d` column submatrix gives rank `d`
  refine le_antisymm (Matrix.rank_le_card_height _) ?_
  have h3 := Matrix.rank_submatrix_le W.1 id e
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hW))]
    at h3
  exact h3

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
  classical
  -- the reads and writes of generic tuples are generic pairs; there no ReLU block without biases
  -- with fewer units absorbs, and an absorbing block with biases would give one (step along rays)
  filter_upwards [ae_tuple_bvl (P := fun W : Matrix d m ℝ × Matrix m d ℝ =>
      ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
        ∀ (Wr' : Matrix d m' ℝ) (Ww' : Matrix m' d ℝ),
          ∃ x : d → ℝ, x ᵥ* M + vanillaBlock relu W.1 W.2 x ≠ vanillaBlock relu Wr' Ww' x) μ
      fun ν _ => ae_not_relu_absorb_of_card_lt hd M hM ν] with θ hθ
  intro m' _ hm' Wr' b' Ww' c'
  obtain ⟨x, hx⟩ := hθ m' hm' Wr' Ww'
  by_contra hc
  exact hx (relu_absorb_of_vanillaBlockB_relu_absorb _ _ _ _ _ _ _ _ M
    (fun y => not_not.1 (not_exists.1 hc y)) x)

/-- **Theorem C.2 (ii) of the absorb paper, "and not with fewer", for GELU blocks with biases.** -/
theorem ae_not_gelu_absorbB_of_card_lt (hd : 2 ≤ Fintype.card d) (M : Matrix d d ℝ)
    (hM : IsUnit M.det)
    (μ : Measure (Matrix d m ℝ × (m → ℝ) × Matrix m d ℝ × (d → ℝ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
      ∀ (Wr' : Matrix d m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' d ℝ) (c' : d → ℝ),
        ∃ x : d → ℝ, x ᵥ* M + vanillaBlockB gelu θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 x
          ≠ vanillaBlockB gelu Wr' b' Ww' c' x := by
  classical
  -- the reads and writes of generic tuples are generic pairs; there no ReLU block without biases
  -- with fewer units absorbs, and an absorbing block with biases would give one (step along rays)
  filter_upwards [ae_tuple_bvl (P := fun W : Matrix d m ℝ × Matrix m d ℝ =>
      ∀ (m' : Type) [Fintype m'], Fintype.card m' < Fintype.card m + Fintype.card d →
        ∀ (Wr' : Matrix d m' ℝ) (Ww' : Matrix m' d ℝ),
          ∃ x : d → ℝ, x ᵥ* M + vanillaBlock relu W.1 W.2 x ≠ vanillaBlock relu Wr' Ww' x) μ
      fun ν _ => ae_not_relu_absorb_of_card_lt hd M hM ν] with θ hθ
  intro m' _ hm' Wr' b' Ww' c'
  obtain ⟨x, hx⟩ := hθ m' hm' Wr' Ww'
  by_contra hc
  exact hx (relu_absorb_of_vanillaBlockB_gelu_absorb _ _ _ _ _ _ _ _ M
    (fun y => not_not.1 (not_exists.1 hc y)) x)

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
  classical
  -- generic reads have rank `d`: the construction gives `d` more units
  filter_upwards [ae_tuple_bvl (P := fun W : Matrix d m ℝ × Matrix m d ℝ =>
      W.1.rank = Fintype.card d) μ fun ν _ => ae_rank_bvl hm ν,
      ae_not_relu_absorbB_of_card_lt hd M hM μ]
    with θ hr hlt
  exact ⟨exists_vanillaBlockB_add_linear_relu_of_rank θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 hr M, hlt⟩

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
  classical
  -- generic reads have rank `d`: the construction gives `d` more units
  filter_upwards [ae_tuple_bvl (P := fun W : Matrix d m ℝ × Matrix m d ℝ =>
      W.1.rank = Fintype.card d) μ fun ν _ => ae_rank_bvl hm ν,
      ae_not_gelu_absorbB_of_card_lt hd M hM μ]
    with θ hr hlt
  exact ⟨exists_vanillaBlockB_add_linear_gelu_of_rank θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 hr M, hlt⟩

end Square

end Skips
