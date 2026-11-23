import SkipsLean.OneBlock.Common
import SkipsLean.OneBlock.Factorization

/-!
# The one-block theorem for an MLP block without symmetries inside its hidden units

Paper (dimension paper): Theorem 5.1 (Theorem C.1 in the appendix), for the kinds of MLP block
with `s = 0`, which are the `tanh` and the GELU blocks: with one block, without normalization and
without biases, at generic parameters the functional dimension is `P - 2 d²`.

The network is `x ↦ σ(x E W_read) W_write D`. With `C = E W_read` and `A = W_write D`, let `c_i`
be the columns of `C` and `a_i` the rows of `A`. The conditions that the proof uses are: `E`, `D`,
`W_read` and `W_write` have rank `d`, every `a_i` is nonzero, and the `c_i` are nonzero and pairwise
non-collinear (`OneBlockGeneric`). They hold at generic parameters when
`d_in, d_out, d_hidden ≥ d ≥ 2`.

The proof of the paper has three steps, and only Step 2 (Lemma C.3) depends on the activation. So
the theorem is stated here for every activation `σ` with derivative `σ'` for which the conclusion
of Lemma C.3 holds (`UnitsRigid σ σ'`). `Tanh.lean` and `GELU.lean` apply it.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- **The conclusion of Lemma C.3 for an activation without symmetries inside its hidden units**
(`tanh` and GELU), as a property of the activation `σ` and of its derivative `σ'`. Rows are indexed
by `n` (the coordinates of an input `x`), hidden units by `q`, and the coordinates of the output by
`k`. The function is `G(φ, x) = x M + γ + ∑_i σ(x c_i + β_i) a_i`; if every `a_i` is nonzero and
the `c_i` are nonzero and pairwise non-collinear, then a direction `ψ` of the weights along which
the derivative of `G` vanishes at every input `x` is zero. -/
def UnitsRigid (σ σ' : ℝ → ℝ) (n k q : Type*) [Fintype n] [Fintype k] [Fintype q] : Prop :=
  ∀ (c : q → n → ℝ) (β : q → ℝ) (a : q → k → ℝ)
    (ψM : Matrix n k ℝ) (ψγ : k → ℝ) (ψc : q → n → ℝ) (ψβ : q → ℝ) (ψa : q → k → ℝ),
    (∀ i, a i ≠ 0) → (∀ i, c i ≠ 0) → (∀ i j, i ≠ j → ∀ r : ℝ, c i ≠ r • c j) →
    (∀ x : n → ℝ,
      x ᵥ* ψM + ψγ + ∑ i, (σ (x ⬝ᵥ c i + β i) • ψa i
        + (σ' (x ⬝ᵥ c i + β i) * (x ⬝ᵥ ψc i + ψβ i)) • a i) = 0) →
    ψM = 0 ∧ ψγ = 0 ∧ ψc = 0 ∧ ψβ = 0 ∧ ψa = 0

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- The conditions on the parameters of one MLP block that the proof of the one-block theorem
uses. They do not depend on the activation. -/
structure OneBlockGeneric (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Prop where
  rank_E : θ.E.rank = Fintype.card d
  rank_D : θ.D.rank = Fintype.card d
  rank_read : (θ.read 0).rank = Fintype.card d
  rank_write : (θ.write 0).rank = Fintype.card d
  /-- every row `a_i` of `A = W_write D` is nonzero -/
  row_ne_zero : ∀ i, (θ.write 0 * θ.D) i ≠ 0
  /-- every column `c_i` of `C = E W_read` is nonzero -/
  col_ne_zero : ∀ i, (θ.E * θ.read 0)ᵀ i ≠ 0
  /-- the columns of `C` are pairwise non-collinear -/
  col_not_collinear : ∀ i j, i ≠ j → ∀ r : ℝ, (θ.E * θ.read 0)ᵀ i ≠ r • (θ.E * θ.read 0)ᵀ j

/-! ### Helpers: the function of one MLP block and its derivative -/

/-- Helper: the read of the block, with its columns indexed by the hidden units. -/
private def rd (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix d (hid 0) ℝ :=
  θ.read 0

/-- Helper: the write of the block, with its rows indexed by the hidden units. -/
private def wr (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) d ℝ :=
  θ.write 0

/-- Helper: `C = E W_read`. -/
private def Cm (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0) ℝ :=
  θ.E * rd θ

/-- Helper: `A = W_write D`. -/
private def Am (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wr θ * θ.D

/-- Helper: the derivative `∂C = η_E W_read + E η_read` of `C` along `η`. -/
private def dCm (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix dIn (hid 0) ℝ :=
  η.E * rd θ + θ.E * rd η

/-- Helper: the derivative `∂A = η_write D + W_write η_D` of `A` along `η`. -/
private def dAm (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :
    Matrix (hid 0) dOut ℝ :=
  wr η * θ.D + wr θ * η.D

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the read is linear in the parameters. -/
private theorem rd_line (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : rd (θ + τ • η) = rd θ + τ • rd η := rfl

omit [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the write is linear in the parameters. -/
private theorem wr_line (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) : wr (θ + τ • η) = wr θ + τ • wr η := rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the function of one MLP block, `F_θ(x) = σ(x C) A` (the stream matrix is `0`). -/
private theorem eval_mlp_eq (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) :
    eval (Arch.mlp σ id hid) 0 θ x = (x * Cm θ).map σ * Am θ := by
  have h1 : (Fin.last 1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hχ : (Arch.mlp (T := T) (d := d) σ id hid).χ = id := rfl
  have hf : (Arch.mlp (T := T) (d := d) σ id hid).f 0 = fun M => M.map σ := rfl
  -- `h_1 = h_0 0 + σ(h_0 W_read) W_write` with `h_0 = x E`
  rw [eval, h1, hidden_succ, Fin.castSucc_zero, hidden_zero, hχ, hf]
  simp only [Pi.zero_apply, Matrix.mul_zero, zero_add, id_eq]
  rw [Matrix.mul_assoc x θ.E (θ.read 0)]
  exact Matrix.mul_assoc _ _ _

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F_θ(x)`, `∑_i σ((x C)_{t i}) A_{i o}`. -/
private theorem eval_mlp_apply
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) :
    eval (Arch.mlp σ id hid) 0 θ x t o
      = ∑ i : hid 0, σ ((x * Cm θ) t i) * Am θ i o := by
  rw [eval_mlp_eq, Matrix.mul_apply]
  rfl

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `C(τ) = C + τ ∂C + τ² η_E η_read`. -/
private theorem Cm_line (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    Cm (θ + τ • η) = Cm θ + τ • dCm θ η + (τ * τ) • Cm η := by
  simp only [Cm, dCm, rd_line, Params.add_E, Params.smul_E, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: along the line, `A(τ) = A + τ ∂A + τ² η_write η_D`. -/
private theorem Am_line (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (τ : ℝ) :
    Am (θ + τ • η) = Am θ + τ • dAm θ η + (τ * τ) • Am η := by
  simp only [Am, dAm, wr_line, Params.add_D, Params.smul_D, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
  abel

omit [Fintype T] [Nonempty T] [DecidableEq d] [Fintype dOut] in
/-- Helper: the entries of `F_{θ + τ η}(x)` as functions of `τ`. -/
private theorem eval_line_apply
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) (τ : ℝ) :
    eval (Arch.mlp σ id hid) 0 (θ + τ • η) x t o = ∑ i : hid 0,
      σ ((x * Cm θ) t i + τ * (x * dCm θ η) t i + τ * τ * (x * Cm η) t i) *
        (Am θ i o + τ * dAm θ η i o + τ * τ * Am η i o) := by
  rw [eval_mlp_apply, Cm_line, Am_line]
  simp only [Matrix.mul_add, Matrix.mul_smul]
  rfl

omit [Nonempty T] [DecidableEq d] in
/-- Helper (Step 3 of the paper, the chain rule): the derivative of `θ ↦ F_θ(x)` along `η` has
the entries `∑_i [σ(z_i) (∂A)_{i o} + σ'(z_i) (x ∂C)_{t i} A_{i o}]`, `z_i = (x C)_{t i}`. -/
private theorem fderiv_eval_apply (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (θ η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (x : Matrix T dIn ℝ) (t : T) (o : dOut) :
    fderiv ℝ (fun θ' => eval (Arch.mlp σ id hid) 0 θ' x) θ η t o = ∑ i : hid 0,
      (σ ((x * Cm θ) t i) * dAm θ η i o
        + σ' ((x * Cm θ) t i) * (x * dCm θ η) t i * Am θ i o) := by
  have hdiff := differentiable_eval (A := Arch.mlp (T := T) (d := d) σ id hid) (S := 0)
    (dIn := dIn) (dOut := dOut)
    (fun ℓ => differentiable_f_mlp (fun z => (hσ z).differentiableAt) ℓ) differentiable_id x
  -- the chain rule along the line `τ ↦ θ + τ η`
  have h1 := hasDerivAt_eval_line (A := Arch.mlp (T := T) (d := d) σ id hid) 0 θ η x (hdiff θ)
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 t) o
  -- the same derivative computed entrywise: products and sums of real functions of `τ`
  have h3 : HasDerivAt (fun τ : ℝ => eval (Arch.mlp σ id hid) 0 (θ + τ • η) x t o)
      (∑ i : hid 0, (σ ((x * Cm θ) t i) * dAm θ η i o
        + σ' ((x * Cm θ) t i) * (x * dCm θ η) t i * Am θ i o)) 0 := by
    rw [funext fun τ => eval_line_apply θ η x t o τ]
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hu := hasDerivAt_quad ((x * Cm θ) t i) ((x * dCm θ η) t i) ((x * Cm η) t i)
    have hv := hasDerivAt_quad (Am θ i o) (dAm θ η i o) (Am η i o)
    have h := ((hσ _).comp (0 : ℝ) hu).mul hv
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, zero_mul, mul_zero, add_zero]
      ring
  exact h2.unique h3

/-- Under the conditions, every flat direction of one MLP block whose activation satisfies
Lemma C.3 without rescalings is the direction of two changes of basis (Steps 1 to 3 of the proof
of Theorem C.1). -/
theorem flat_le_range_cobDir_mlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ)
    (η : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hη : η ∈ flat (Arch.mlp σ id hid) 0 θ) :
    ∃ X : Fin 2 → Matrix d d ℝ, η = cobDir θ X := by
  -- Step 3: the derivative of `F(θ, x)` along `η` vanishes at every input, entry by entry
  have hzero : ∀ (x : Matrix T dIn ℝ) (t : T) (o : dOut), ∑ i : hid 0,
      (σ ((x * Cm θ) t i) * dAm θ η i o
        + σ' ((x * Cm θ) t i) * (x * dCm θ η) t i * Am θ i o) = 0 := by
    intro x t o
    rw [← fderiv_eval_apply hσ θ η x t o]
    have h := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hη x)
    exact congrFun (congrFun h t) o
  -- Step 2, Lemma C.3 (inputs `x` with all rows equal to `v`): `∂C = 0` and `∂A = 0`
  obtain ⟨-, -, hc, -, ha⟩ := hU (fun i => (Cm θ)ᵀ i) 0 (fun i => Am θ i)
    0 0 (fun i => (dCm θ η)ᵀ i) 0 (fun i => dAm θ η i) (fun i => hθ.row_ne_zero i)
    (fun i => hθ.col_ne_zero i) (fun i j hij => hθ.col_not_collinear i j hij) (by
      intro v
      funext o
      have h := hzero (Matrix.of fun _ => v) (Classical.arbitrary T) o
      simp only [Matrix.vecMul_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, add_zero, zero_add]
      exact h)
  -- Step 1, Lemma C.2: a direction that keeps `C` and `A` is that of two changes of basis
  have hC : η.E * θ.read 0 + θ.E * η.read 0 = 0 := by
    ext a i
    exact congrFun (congrFun hc i) a
  have hA : η.write 0 * θ.D + θ.write 0 * η.D = 0 := by
    ext i o
    exact congrFun (congrFun ha i) o
  exact (keeps_products_iff_mem_range_cobDir θ η hθ.rank_E hθ.rank_D hθ.rank_read
    hθ.rank_write).1 ⟨hC, hA⟩

/-- **Theorem 5.1 for an MLP block with `s = 0`, under the conditions of its proof:** the
functional dimension is `P - 2 d²`. -/
theorem funDim_mlp_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) (hθ : OneBlockGeneric θ) :
    funDim (Arch.mlp σ id hid) 0 θ + 2 * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  have hσd : Differentiable ℝ σ := fun z => (hσ z).differentiableAt
  have hdiff : ∀ x : Matrix T dIn ℝ, DifferentiableAt ℝ
      (fun θ' : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
        eval (Arch.mlp σ id hid) 0 θ' x) θ := fun x =>
    (differentiable_eval (A := Arch.mlp (T := T) (d := d) σ id hid) (S := 0)
      (fun ℓ => differentiable_f_mlp hσd ℓ) differentiable_id x).differentiableAt
  -- the flat directions are exactly the directions `cobDir θ X` of the two changes of basis:
  -- `⊆` is the previous theorem, `⊇` holds since changes of basis are symmetries
  have hflat : flat (Arch.mlp σ id hid) 0 θ = LinearMap.range (cobDirLin θ) := by
    apply le_antisymm
    · intro η hη
      obtain ⟨X, rfl⟩ := flat_le_range_cobDir_mlp hσ hU θ hθ η hη
      exact LinearMap.mem_range.2 ⟨X, rfl⟩
    · rintro _ ⟨X, rfl⟩
      exact cobDir_mem_flat_skipless θ rfl (fun ℓ => differentiable_f_mlp hσd ℓ) X
  -- `X ↦ cobDir θ X` is injective (Lemma B.1): `K(θ)` has dimension `2 d²`
  have hinj : Function.Injective (cobDirLin θ) :=
    cobDir_injective θ hθ.rank_E fun ℓ => by
      obtain rfl := Subsingleton.elim ℓ 0
      exact hθ.rank_write
  -- `fd(θ) = P - dim K(θ)` (Appendix C)
  have h := funDim_add_finrank_flat θ hdiff
  rw [hflat, LinearMap.finrank_range_of_inj hinj,
    finrank_cobDomain (L := 1) (d := d)] at h
  simpa only [Nat.reduceAdd] using h

/-- The conditions hold at generic parameters, when `d_in, d_out, d_hidden ≥ d ≥ 2`. -/
theorem ae_oneBlockGeneric
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, OneBlockGeneric θ := by
  classical
  -- two distinct coordinates of `h`, two distinct input coordinates, one output coordinate
  obtain ⟨k₁, k₂, hk⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  obtain ⟨a₁, a₂, ha⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card dIn by omega)
  obtain ⟨o₀⟩ : Nonempty dOut := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨cD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  obtain ⟨cR⟩ := Function.Embedding.nonempty_of_card_le hhid
  -- the parameters with all entries `1`
  let θ₁ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut :=
    ⟨Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1, fun _ => Matrix.of fun _ _ => 1,
      Matrix.of fun _ _ => 1⟩
  -- the ranks: `E` and the write (`Generic/Params.lean`), `D` and the read (invertible minors)
  have h1 := ae_rank_E_write μ hdIn (fun ℓ => by obtain rfl := Subsingleton.elim ℓ 0; exact hhid)
  have h2 := ae_isUnit_det_submatrix μ
  -- the rows of `A = W_write D` are nonzero: their entries at `o₀` are
  have h3 : ∀ᵐ θ ∂μ, ∀ i : hid 0, (θ.write 0 * θ.D) i o₀ ≠ 0 := by
    refine ae_all_iff.2 fun i => ?_
    exact ae_ne_zero_of_analytic μ (analyticOnNhd_write_mul_D (A := Arch.mlp σ id hid)
      (dIn := dIn) 0 i o₀) ⟨θ₁, sum_one_mul_one_ne_zero hd⟩
  -- the columns of `C = E W_read` are nonzero: their entries at `a₁` are
  have h4 : ∀ᵐ θ ∂μ, ∀ i : hid 0, (θ.E * θ.read 0) a₁ i ≠ 0 := by
    refine ae_all_iff.2 fun i => ?_
    exact ae_ne_zero_of_analytic μ (analyticOnNhd_E_mul_read (A := Arch.mlp σ id hid)
      (dOut := dOut) 0 a₁ i) ⟨θ₁, sum_one_mul_one_ne_zero hd⟩
  -- two columns of `C` are not collinear: a `2 × 2` minor does not vanish
  have h5 : ∀ᵐ θ ∂μ, ∀ i j : hid 0, i ≠ j →
      (θ.E * θ.read 0) a₁ i * (θ.E * θ.read 0) a₂ j
        - (θ.E * θ.read 0) a₁ j * (θ.E * θ.read 0) a₂ i ≠ 0 := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hij h
    · obtain ⟨E₀, W₀, hEW⟩ := exists_minor_ne_zero ha hk hij
      let θ₀ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut :=
        ⟨E₀, fun ℓ => Fin.cases W₀ (fun l => l.elim0) ℓ, 0, 0⟩
      have hC : ∀ (a : dIn) (i : hid 0), AnalyticOnNhd ℝ
          (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
            (θ.E * θ.read 0) a i) Set.univ :=
        fun a i => analyticOnNhd_E_mul_read (A := Arch.mlp σ id hid) (dOut := dOut) 0 a i
      have hg : AnalyticOnNhd ℝ
          (fun θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut =>
            (θ.E * θ.read 0) a₁ i * (θ.E * θ.read 0) a₂ j
              - (θ.E * θ.read 0) a₁ j * (θ.E * θ.read 0) a₂ i) Set.univ :=
        ((hC a₁ i).mul (hC a₂ j)).sub ((hC a₁ j).mul (hC a₂ i))
      exact (ae_ne_zero_of_analytic μ hg ⟨θ₀, hEW⟩).mono fun _ h _ => h
  filter_upwards [h1, h2, h3, h4, h5] with θ h1 h2 h3 h4 h5
  refine ⟨h1.1, rank_eq_card_of_isUnit_det θ.D cD (h2.2.1 cD),
    rank_eq_card_of_isUnit_det (θ.read 0) cR (h2.1 0 cR), h1.2 0,
    fun i hi => h3 i (congrFun hi o₀), fun i hi => h4 i (congrFun hi a₁), ?_⟩
  -- if `c_i = r c_j`, the minor of the columns `i`, `j` vanishes
  intro i j hij r hr
  have e1 : (θ.E * θ.read 0) a₁ i = r * (θ.E * θ.read 0) a₁ j := congrFun hr a₁
  have e2 : (θ.E * θ.read 0) a₂ i = r * (θ.E * θ.read 0) a₂ j := congrFun hr a₂
  apply h5 i j hij
  rw [e1, e2]
  ring

/-- **Theorem 5.1 for an MLP block with `s = 0`:** with one block, without normalization and
without biases, with `d_in, d_out, d_hidden ≥ d ≥ 2`, the functional dimension is `P - 2 d²` at
generic parameters. -/
theorem ae_funDim_mlp_oneBlock (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hU : UnitsRigid σ σ' dIn dOut (hid 0))
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) (hhid : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 0 θ + 2 * Fintype.card d ^ 2
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) :=
  (ae_oneBlockGeneric μ hd hdIn hdOut hhid).mono fun θ hθ => funDim_mlp_oneBlock hσ hU θ hθ

end Skips
