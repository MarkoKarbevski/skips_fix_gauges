import SkipsLean.OneBlock.Attention
import SkipsLean.OneBlock.Common

/-!
# The one-block theorem for an attention block: the conditions hold at generic parameters

Paper (dimension paper), proof of Theorem C.1, "Attention blocks": "For generic parameters `E`
and `D` have rank `d_model`; every `W_{Q,i}`, `W_{K,i}`, `W_{V,i}` and `W_{O,i}^⊤` has rank
`d_h`, since `d_h ≤ d_model`; and the queries […] and the output projection […] of all heads
have rank `d_model`, since `H d_h ≥ d_model`" (Step 1), and "For generic parameters and generic
`v` the columns `B_i v^⊤` are nonzero and pairwise non-collinear, since `d_model ≥ 2`, and every
row `v C_i` is nonzero" (Step 2).

Here: for `d_in, d_out ≥ d ≥ 2`, `d_h ≤ d` and `H d_h ≥ d`, the conditions
`OneBlockGenericAttention θ` of `OneBlock/Attention.lean` hold at almost every `θ`, for every
additive Haar measure on the parameters.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin 1 → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-! ### Helpers: ranks of columns of a read and of rows of a write -/

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `analyticOnNhd_det` of `Generic/Params.lean`): the determinant of a square
matrix that depends linearly on the parameters is an analytic function of the parameters. -/
private theorem analyticOnNhd_det_obg {L : ℕ} {A : Arch T d L} {n : Type*} [Fintype n]
    [DecidableEq n] (Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ) :
    AnalyticOnNhd ℝ (fun θ => (Φ θ).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ =>
      analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ (σ i) i).comp Φ))

/-- Helper: a matrix whose submatrix on the rows `r` and the columns `c` (both injective) is the
identity. -/
private theorem exists_submatrix_eq_one_obg {m p n : Type*} [DecidableEq n] {r : n → m}
    (hr : Function.Injective r) {c : n → p} (hc : Function.Injective c) :
    ∃ M : Matrix m p ℝ, M.submatrix r c = 1 := by
  classical
  refine ⟨Matrix.of fun a b => if ∃ x, r x = a ∧ c x = b then 1 else 0, ?_⟩
  ext x y
  simp [Matrix.one_apply, hr.eq_iff, hc.eq_iff]

omit [Fintype T] [DecidableEq d] in
/-- Helper: at generic parameters, `n ≤ d` distinct columns `c` of the read of block `ℓ` form a
matrix of rank `n`: some `n` of its rows form a matrix that is invertible at generic parameters. -/
private theorem ae_rank_read_cols_obg {L : ℕ} {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*} [Fintype n] [DecidableEq n] {c : n → A.r ℓ}
    (hc : Function.Injective c) (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.read ℓ).submatrix id c).rank = Fintype.card n := by
  -- `n` rows `ρ`, and the square submatrix of the read on the rows `ρ` and the columns `c`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_obg ρ.injective hc
  let Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ :=
    { toFun := fun θ => ((θ.read ℓ).submatrix id c).submatrix ρ id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- it is the identity at the parameter whose read `ℓ` is `M`, so its determinant is not
  -- identically zero, and it is nonzero almost everywhere
  have hne : ∃ θ, (Φ θ).det ≠ 0 := by
    refine ⟨⟨0, Pi.single ℓ M, 0, 0⟩, ?_⟩
    show ((Pi.single (M := fun ℓ => Matrix d (A.r ℓ) ℝ) ℓ M ℓ).submatrix ρ c).det ≠ 0
    rw [Pi.single_eq_same, hM, Matrix.det_one]
    exact one_ne_zero
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_obg Φ) hne] with θ hθ
  -- an invertible `n × n` submatrix gives rank `≥ n`, and the rank is at most the width `n`
  have h1 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank = Fintype.card n :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hθ))
  have h2 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank
      ≤ ((θ.read ℓ).submatrix id c).rank :=
    Matrix.rank_submatrix_le _ ρ id
  have h3 := Matrix.rank_le_card_width ((θ.read ℓ).submatrix id c)
  omega

omit [Fintype T] [DecidableEq d] in
/-- Helper: at generic parameters, `n ≤ d` distinct rows `r` of the write of block `ℓ` form a
matrix of rank `n`: some `n` of its columns form a matrix that is invertible at generic
parameters. -/
private theorem ae_rank_write_rows_obg {L : ℕ} {A : Arch T d L}
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*} [Fintype n]
    [DecidableEq n] {r : n → A.w ℓ} (hr : Function.Injective r)
    (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.write ℓ).submatrix r id).rank = Fintype.card n := by
  -- `n` columns `ρ`, and the square submatrix of the write on the rows `r` and the columns `ρ`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_obg hr ρ.injective
  let Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ :=
    { toFun := fun θ => ((θ.write ℓ).submatrix r id).submatrix id ρ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- it is the identity at the parameter whose write `ℓ` is `M`
  have hne : ∃ θ, (Φ θ).det ≠ 0 := by
    refine ⟨⟨0, 0, Pi.single ℓ M, 0⟩, ?_⟩
    show ((Pi.single (M := fun ℓ => Matrix (A.w ℓ) d ℝ) ℓ M ℓ).submatrix r ρ).det ≠ 0
    rw [Pi.single_eq_same, hM, Matrix.det_one]
    exact one_ne_zero
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_obg Φ) hne] with θ hθ
  -- an invertible `n × n` submatrix gives rank `≥ n`, and the rank is at most the height `n`
  have h1 : (((θ.write ℓ).submatrix r id).submatrix id ρ).rank = Fintype.card n :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hθ))
  have h2 : (((θ.write ℓ).submatrix r id).submatrix id ρ).rank
      ≤ ((θ.write ℓ).submatrix r id).rank :=
    Matrix.rank_submatrix_le _ id ρ
  have h3 := Matrix.rank_le_card_height ((θ.write ℓ).submatrix r id)
  omega

/-! ### Helpers: the entries of `B_i v^⊤` and `v C_i` are analytic functions of the parameters -/

/-- Helper: an entry of the product of two matrices whose entries are analytic functions is an
analytic function. -/
private theorem analyticOnNhd_mul_entry_obg {P m n p : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [Fintype n] {f : P → Matrix m n ℝ} {g : P → Matrix n p ℝ}
    (hf : ∀ a b, AnalyticOnNhd ℝ (fun y => f y a b) Set.univ)
    (hg : ∀ a b, AnalyticOnNhd ℝ (fun y => g y a b) Set.univ) (a : m) (b : p) :
    AnalyticOnNhd ℝ (fun y => (f y * g y) a b) Set.univ := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticOnNhd_fun_sum _ fun k _ => (hf a k).mul (hg k b)

omit [Fintype T] [DecidableEq d] in
/-- Helper: an entry of `E` is an analytic function of the parameters. -/
private theorem analyticOnNhd_E_obg {L : ℕ} {A : Arch T d L} (a : dIn) (b : d) :
    AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => θ.E a b) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ a b).comp
    (Params.linE (A := A) (dIn := dIn) (dOut := dOut)))

omit [Fintype T] [DecidableEq d] in
/-- Helper: an entry of the read of block `ℓ` is an analytic function of the parameters. -/
private theorem analyticOnNhd_read_obg {L : ℕ} {A : Arch T d L} (ℓ : Fin L) (b : d)
    (x : A.r ℓ) : AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => θ.read ℓ b x) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ b x).comp
    (Params.linRead (A := A) (dIn := dIn) (dOut := dOut) ℓ))

omit [Fintype T] [DecidableEq d] in
/-- Helper: an entry of the write of block `ℓ` is an analytic function of the parameters. -/
private theorem analyticOnNhd_write_obg {L : ℕ} {A : Arch T d L} (ℓ : Fin L) (x : A.w ℓ)
    (b : d) : AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => θ.write ℓ x b) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ x b).comp
    (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) ℓ))

omit [Fintype T] [DecidableEq d] in
/-- Helper: an entry of `D` is an analytic function of the parameters. -/
private theorem analyticOnNhd_D_obg {L : ℕ} {A : Arch T d L} (b : d) (o : dOut) :
    AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => θ.D b o) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ b o).comp
    (Params.linD (A := A) (dIn := dIn) (dOut := dOut)))

omit [DecidableEq d] in
/-- Helper: an entry of `B_i v^⊤`, `(√d_h)⁻¹ ∑_b (E W_{Q,i} W_{K,i}^⊤ E^⊤)_{a b} v_b`, is an
analytic function of the parameters. -/
private theorem analyticOnNhd_score_obg (i : H 0) (v : dIn → ℝ) (a : dIn) :
    AnalyticOnNhd ℝ (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut =>
      (attnScore θ i *ᵥ v) a) Set.univ := by
  -- the entries of `E`, `W_{Q,i}`, `W_{K,i}^⊤`, `E^⊤`, then of their product
  have hE : ∀ a b, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut => θ.E a b)
      Set.univ := fun a b => analyticOnNhd_E_obg a b
  have hEt : ∀ b a, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut => θ.Eᵀ b a)
      Set.univ := fun b a => analyticOnNhd_E_obg a b
  have hQ : ∀ b k, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut =>
        attnQ θ i b k) Set.univ :=
    fun b k => analyticOnNhd_read_obg (A := Arch.attention sees id H dh) 0 b (i, Sum.inl k)
  have hK : ∀ k b, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut =>
        (attnK θ i)ᵀ k b) Set.univ :=
    fun k b => analyticOnNhd_read_obg (A := Arch.attention sees id H dh) 0 b
      (i, Sum.inr (Sum.inl k))
  have h4 := analyticOnNhd_mul_entry_obg
    (analyticOnNhd_mul_entry_obg (analyticOnNhd_mul_entry_obg hE hQ) hK) hEt
  simp only [attnScore, Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul]
  exact Finset.analyticOnNhd_fun_sum _ fun b _ =>
    (analyticOnNhd_const.mul (h4 a b)).mul analyticOnNhd_const

omit [DecidableEq d] in
/-- Helper: an entry of `v C_i`, `∑_a v_a (E W_{V,i} W_{O,i} D)_{a o}`, is an analytic function
of the parameters. -/
private theorem analyticOnNhd_value_obg (i : H 0) (v : dIn → ℝ) (o : dOut) :
    AnalyticOnNhd ℝ (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut =>
      (v ᵥ* attnValue θ i) o) Set.univ := by
  -- the entries of `E`, `W_{V,i}`, `W_{O,i}`, `D`, then of their product
  have hE : ∀ a b, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut => θ.E a b)
      Set.univ := fun a b => analyticOnNhd_E_obg a b
  have hV : ∀ b k, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut =>
        attnV θ i b k) Set.univ :=
    fun b k => analyticOnNhd_read_obg (A := Arch.attention sees id H dh) 0 b
      (i, Sum.inr (Sum.inr k))
  have hO : ∀ k b, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut =>
        attnO θ i k b) Set.univ :=
    fun k b => analyticOnNhd_write_obg (A := Arch.attention sees id H dh) 0 (i, k) b
  have hD : ∀ b o, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut => θ.D b o)
      Set.univ := fun b o => analyticOnNhd_D_obg b o
  have h4 := analyticOnNhd_mul_entry_obg
    (analyticOnNhd_mul_entry_obg (analyticOnNhd_mul_entry_obg hE hV) hO) hD
  simp only [attnValue, Matrix.vecMul, dotProduct]
  exact Finset.analyticOnNhd_fun_sum _ fun a _ => analyticOnNhd_const.mul (h4 a o)

/-- The conditions of the proof of Theorem C.1 for an attention block hold at generic
parameters, for `d_in, d_out ≥ d ≥ 2`, heads of width `d_h ≤ d` and total width `H d_h ≥ d`. -/
theorem ae_oneBlockGenericAttention
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0)) :
    ∀ᵐ θ ∂μ, OneBlockGenericAttention θ := by
  sorry

end Skips
