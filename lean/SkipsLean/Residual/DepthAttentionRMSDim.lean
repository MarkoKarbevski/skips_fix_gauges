import SkipsLean.Residual.DepthAttentionRMS
import SkipsLean.Dimension.GenericRank
import SkipsLean.OneBlock.Common
import SkipsLean.Generic.Params

/-!
# Residual networks of attention blocks at any depth under pre-RMSNorm: the dimension

Paper (skips paper): Theorem 4.7 (Equality for residual networks at any depth): "Let the blocks
be analytic, with or without pre-RMSNorm. The residual network satisfies the equality condition:
at generic parameters its functional dimension is `P − dim G − s`. So the skips raise the
functional dimension by at least `L dim G` […]", with `dim G = d_model (d_model − 1)/2` under
pre-RMSNorm; Lemma A.27, second value, at generic parameters.

Here, for attention blocks under pre-RMSNorm with `ε > 0`, heads of width `1 ≤ d_h ≤ d` (any
numbers of heads; `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`), `d_in, d_out ≥ d ≥ 2`, and a mask with a token that
sees itself and another token:

* `ae_smallWritesGenericAttentionRMS`: the conditions of the proof hold at almost every `θ`;
* `ae_eventually_funDim_smallWrites_attention_rmsNorm`: Lemma A.27, second value;
* `ae_funDim_attention_residual_rmsNorm`: Theorem 4.7, `fd = P − d(d−1)/2 − s`;
* `ae_funDim_attention_residual_rmsNorm_ge_add`: the skips raise the functional dimension by at
  least `L d(d−1)/2`, when every block has total width `H d_h ≥ d`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)] {ε : ℝ}

/-! ### Helpers: ranks of columns of a read and of rows of a write -/

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `analyticOnNhd_det_dpg` of `Residual/DepthAttentionGeneric.lean`): the
determinant of a square matrix that depends linearly on the parameters is an analytic function of
the parameters. -/
private theorem analyticOnNhd_det_rmd {A : Arch T d L} {n : Type*} [Fintype n]
    [DecidableEq n] (Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ) :
    AnalyticOnNhd ℝ (fun θ => (Φ θ).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ =>
      analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ (σ i) i).comp Φ))

/-- Helper: a matrix whose submatrix on the rows `r` and the columns `c` (both injective) is the
identity. -/
private theorem exists_submatrix_eq_one_rmd {m p n : Type*} [DecidableEq n] {r : n → m}
    (hr : Function.Injective r) {c : n → p} (hc : Function.Injective c) :
    ∃ M : Matrix m p ℝ, M.submatrix r c = 1 := by
  classical
  refine ⟨Matrix.of fun a b => if ∃ x, r x = a ∧ c x = b then 1 else 0, ?_⟩
  ext x y
  simp [Matrix.one_apply, hr.eq_iff, hc.eq_iff]

omit [Fintype T] [DecidableEq d] in
/-- Helper: at generic parameters, `n ≤ d` distinct columns `c` of the read of block `ℓ` form a
matrix of rank `n`: some `n` of its rows form a matrix that is invertible at generic parameters. -/
private theorem ae_rank_read_cols_rmd {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*} [Fintype n] [DecidableEq n] {c : n → A.r ℓ}
    (hc : Function.Injective c) (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.read ℓ).submatrix id c).rank = Fintype.card n := by
  -- `n` rows `ρ`, and the square submatrix of the read on the rows `ρ` and the columns `c`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_rmd ρ.injective hc
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
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_rmd Φ) hne] with θ hθ
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
private theorem ae_rank_write_rows_rmd {A : Arch T d L}
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*} [Fintype n]
    [DecidableEq n] {r : n → A.w ℓ} (hr : Function.Injective r)
    (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.write ℓ).submatrix r id).rank = Fintype.card n := by
  -- `n` columns `ρ`, and the square submatrix of the write on the rows `r` and the columns `ρ`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_rmd hr ρ.injective
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
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_rmd Φ) hne] with θ hθ
  -- an invertible `n × n` submatrix gives rank `≥ n`, and the rank is at most the height `n`
  have h1 : (((θ.write ℓ).submatrix r id).submatrix id ρ).rank = Fintype.card n :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hθ))
  have h2 : (((θ.write ℓ).submatrix r id).submatrix id ρ).rank
      ≤ ((θ.write ℓ).submatrix r id).rank :=
    Matrix.rank_submatrix_le _ id ρ
  have h3 := Matrix.rank_le_card_height ((θ.write ℓ).submatrix r id)
  omega

/-! ### Helpers: the entries of `W_Q W_K^⊤ v^⊤` and `v W_V W_O` are analytic functions of the
parameters -/

/-- Helper: an entry of the product of two matrices whose entries are analytic functions is an
analytic function. -/
private theorem analyticOnNhd_mul_entry_rmd {P m n p : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [Fintype n] {f : P → Matrix m n ℝ} {g : P → Matrix n p ℝ}
    (hf : ∀ a b, AnalyticOnNhd ℝ (fun y => f y a b) Set.univ)
    (hg : ∀ a b, AnalyticOnNhd ℝ (fun y => g y a b) Set.univ) (a : m) (b : p) :
    AnalyticOnNhd ℝ (fun y => (f y * g y) a b) Set.univ := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticOnNhd_fun_sum _ fun k _ => (hf a k).mul (hg k b)

omit [Fintype T] [DecidableEq d] in
/-- Helper: an entry of the read of block `ℓ` is an analytic function of the parameters. -/
private theorem analyticOnNhd_read_rmd {A : Arch T d L} (ℓ : Fin L) (b : d)
    (x : A.r ℓ) : AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => θ.read ℓ b x) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ b x).comp
    (Params.linRead (A := A) (dIn := dIn) (dOut := dOut) ℓ))

omit [Fintype T] [DecidableEq d] in
/-- Helper: an entry of the write of block `ℓ` is an analytic function of the parameters. -/
private theorem analyticOnNhd_write_rmd {A : Arch T d L} (ℓ : Fin L) (x : A.w ℓ)
    (b : d) : AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => θ.write ℓ x b) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ x b).comp
    (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) ℓ))

omit [DecidableEq d] in
/-- Helper: an entry of `W_Q W_K^⊤ v^⊤ / √d_h` for head `i` of block `ℓ` is an analytic function
of the parameters. -/
private theorem analyticOnNhd_score_rmd (ℓ : Fin L) (i : H ℓ) (v : d → ℝ) (a : d) :
    AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut =>
        (headScoreModel θ ℓ i *ᵥ v) a) Set.univ := by
  -- the entries of `W_Q`, `W_K^⊤`, then of their product
  have hQ : ∀ b k, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut =>
        ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)) b k) Set.univ :=
    fun b k => analyticOnNhd_read_rmd (A := Arch.attention sees (rmsNorm ε) H dh) ℓ b
      (i, Sum.inl k)
  have hK : ∀ k b, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut =>
        ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))ᵀ k b) Set.univ :=
    fun k b => analyticOnNhd_read_rmd (A := Arch.attention sees (rmsNorm ε) H dh) ℓ b
      (i, Sum.inr (Sum.inl k))
  have h2 := analyticOnNhd_mul_entry_rmd hQ hK
  simp only [headScoreModel, Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul]
  exact Finset.analyticOnNhd_fun_sum _ fun b _ =>
    (analyticOnNhd_const.mul (h2 a b)).mul analyticOnNhd_const

omit [DecidableEq d] in
/-- Helper: an entry of `v W_V W_O` for head `i` of block `ℓ` is an analytic function of the
parameters. -/
private theorem analyticOnNhd_value_rmd (ℓ : Fin L) (i : H ℓ) (v : d → ℝ) (o : d) :
    AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut =>
        (v ᵥ* headValueModel θ ℓ i) o) Set.univ := by
  -- the entries of `W_V`, `W_O`, then of their product
  have hV : ∀ b k, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut =>
        ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))) b k) Set.univ :=
    fun b k => analyticOnNhd_read_rmd (A := Arch.attention sees (rmsNorm ε) H dh) ℓ b
      (i, Sum.inr (Sum.inr k))
  have hO : ∀ k b, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut =>
        ((θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id) k b) Set.univ :=
    fun k b => analyticOnNhd_write_rmd (A := Arch.attention sees (rmsNorm ε) H dh) ℓ (i, k) b
  have h2 := analyticOnNhd_mul_entry_rmd hV hO
  simp only [headValueModel, Matrix.vecMul, dotProduct]
  exact Finset.analyticOnNhd_fun_sum _ fun a _ => analyticOnNhd_const.mul (h2 a o)

/-! ### Helpers: one parameter at which the conditions on `v₀ = (1, …, 1)` hold -/

/-- Helper: the witness. `E` and `D` are zero; in block `ℓ`, the query matrix of head `i` has the
single entry `1` at `(r ⟨ℓ, i⟩, k₀ ℓ)`, every key and value matrix has the single entry `1` at
`(p, k₀ ℓ)`, every output matrix has the single entry `1` at `(k₀ ℓ, p)`. -/
private noncomputable def wit_rmd [∀ ℓ, DecidableEq (dh ℓ)] (p : d) (k₀ : ∀ ℓ, dh ℓ)
    (r : (Σ ℓ, H ℓ) → d) :
    Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut where
  E := 0
  read ℓ := Matrix.of fun (b : d) (x : H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) =>
      Sum.elim (fun k => if b = r ⟨ℓ, x.1⟩ ∧ k = k₀ ℓ then (1 : ℝ) else 0)
        (fun k => if b = p ∧ Sum.elim id id k = k₀ ℓ then 1 else 0) x.2
  write ℓ := Matrix.of fun (x : H ℓ × dh ℓ) (b : d) =>
      if x.2 = k₀ ℓ ∧ b = p then (1 : ℝ) else 0
  D := 0

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: `W_K^⊤ (1, …, 1) = e_{k₀ ℓ}` for head `i` of block `ℓ`. -/
private theorem wit_Kt_rmd [∀ ℓ, DecidableEq (dh ℓ)] (p : d) (k₀ : ∀ ℓ, dh ℓ)
    (r : (Σ ℓ, H ℓ) → d) (ℓ : Fin L) (i : H ℓ) :
    ((wit_rmd (T := T) (sees := sees) (ε := ε) (dIn := dIn) (dOut := dOut) p k₀ r).read ℓ
        |>.submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))ᵀ *ᵥ (fun _ => (1 : ℝ))
      = fun k => if k = k₀ ℓ then 1 else 0 := by
  funext k
  show ∑ b, (if b = p ∧ k = k₀ ℓ then (1 : ℝ) else 0) * 1 = if k = k₀ ℓ then 1 else 0
  by_cases hk : k = k₀ ℓ <;> simp [hk]

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: `W_Q e_{k₀ ℓ} = e_{r ⟨ℓ, i⟩}` for head `i` of block `ℓ`. -/
private theorem wit_Q_rmd [∀ ℓ, DecidableEq (dh ℓ)] (p : d) (k₀ : ∀ ℓ, dh ℓ)
    (r : (Σ ℓ, H ℓ) → d) (ℓ : Fin L) (i : H ℓ) :
    ((wit_rmd (T := T) (sees := sees) (ε := ε) (dIn := dIn) (dOut := dOut) p k₀ r).read ℓ
        |>.submatrix id fun k : dh ℓ => (i, Sum.inl k)) *ᵥ (fun k => if k = k₀ ℓ then 1 else 0)
      = fun b => if b = r ⟨ℓ, i⟩ then 1 else 0 := by
  funext b
  show ∑ k, (if b = r ⟨ℓ, i⟩ ∧ k = k₀ ℓ then (1 : ℝ) else 0) * (if k = k₀ ℓ then 1 else 0)
    = if b = r ⟨ℓ, i⟩ then 1 else 0
  by_cases hb : b = r ⟨ℓ, i⟩ <;> simp [hb]

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: `(1, …, 1) W_V = e_{k₀ ℓ}` for head `i` of block `ℓ`. -/
private theorem wit_vV_rmd [∀ ℓ, DecidableEq (dh ℓ)] (p : d) (k₀ : ∀ ℓ, dh ℓ)
    (r : (Σ ℓ, H ℓ) → d) (ℓ : Fin L) (i : H ℓ) :
    (fun _ => (1 : ℝ)) ᵥ*
        ((wit_rmd (T := T) (sees := sees) (ε := ε) (dIn := dIn) (dOut := dOut) p k₀ r).read ℓ
          |>.submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
      = fun k => if k = k₀ ℓ then 1 else 0 := by
  funext k
  show ∑ b, 1 * (if b = p ∧ k = k₀ ℓ then (1 : ℝ) else 0) = if k = k₀ ℓ then 1 else 0
  by_cases hk : k = k₀ ℓ <;> simp [hk]

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: `e_{k₀ ℓ} W_O = e_p` for head `i` of block `ℓ`. -/
private theorem wit_vO_rmd [∀ ℓ, DecidableEq (dh ℓ)] (p : d) (k₀ : ∀ ℓ, dh ℓ)
    (r : (Σ ℓ, H ℓ) → d) (ℓ : Fin L) (i : H ℓ) :
    (fun k => if k = k₀ ℓ then (1 : ℝ) else 0)
        ᵥ* ((wit_rmd (T := T) (sees := sees) (ε := ε) (dIn := dIn) (dOut := dOut) p k₀ r).write ℓ
          |>.submatrix (fun k : dh ℓ => (i, k)) id)
      = fun b => if b = p then 1 else 0 := by
  funext b
  show ∑ k, (if k = k₀ ℓ then (1 : ℝ) else 0) * (if k = k₀ ℓ ∧ b = p then 1 else 0)
    = if b = p then 1 else 0
  by_cases hb : b = p <;> simp [hb]

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: at the witness, `W_Q W_K^⊤ v₀^⊤ / √d_h = (√d_{h,ℓ})⁻¹ e_{r P}` for the head
`P = ⟨ℓ, i⟩`. -/
private theorem wit_score_rmd [∀ ℓ, DecidableEq (dh ℓ)] (p : d) (k₀ : ∀ ℓ, dh ℓ)
    (r : (Σ ℓ, H ℓ) → d) (P : Σ ℓ, H ℓ) :
    headScoreModel (wit_rmd (T := T) (sees := sees) (ε := ε) (dIn := dIn) (dOut := dOut) p k₀ r)
        P.1 P.2 *ᵥ (fun _ => (1 : ℝ))
      = (Real.sqrt (Fintype.card (dh P.1)))⁻¹ • fun b => if b = r P then 1 else 0 := by
  rw [headScoreModel, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, wit_Kt_rmd, wit_Q_rmd,
    Sigma.eta]

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: at the witness, `v₀ W_V W_O = e_p` for every head `P`. -/
private theorem wit_value_rmd [∀ ℓ, DecidableEq (dh ℓ)] (p : d) (k₀ : ∀ ℓ, dh ℓ)
    (r : (Σ ℓ, H ℓ) → d) (P : Σ ℓ, H ℓ) :
    (fun _ => (1 : ℝ)) ᵥ*
        headValueModel (wit_rmd (T := T) (sees := sees) (ε := ε) (dIn := dIn) (dOut := dOut)
          p k₀ r) P.1 P.2
      = fun b => if b = p then 1 else 0 := by
  rw [headValueModel, ← Matrix.vecMul_vecMul, wit_vV_rmd, wit_vO_rmd]

/-- The conditions of Lemma A.27 under pre-RMSNorm for attention blocks hold at generic
parameters, for `d_in, d_out ≥ d ≥ 2` and heads of width `1 ≤ d_h ≤ d`. -/
theorem ae_smallWritesGenericAttentionRMS
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, SmallWritesGenericAttentionRMS θ := by
  classical
  -- the sizes: two distinct `p, q` in `d`, `c : d ↪ d_in`, `d ↪ d_out`, and some `k₀ ℓ : d_{h,ℓ}`
  -- in every block
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨cD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  obtain ⟨k₀⟩ : Nonempty (∀ ℓ, dh ℓ) := ⟨fun ℓ => (Fintype.card_pos_iff.1 (hdh0 ℓ)).some⟩
  have hs : ∀ ℓ, (Real.sqrt (Fintype.card (dh ℓ)))⁻¹ ≠ 0 := fun ℓ =>
    inv_ne_zero (Real.sqrt_ne_zero'.2 (by exact_mod_cast hdh0 ℓ))
  -- `d` rows of `E` and `d` columns of `D` are invertible (`Generic/Params.lean`)
  have h2 := ae_isUnit_det_submatrix μ
  -- the query, key, value and output matrices of every head of every block have rank `d_h`
  have hQ : ∀ᵐ θ ∂μ, ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank = Fintype.card (dh ℓ) :=
    ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i =>
      ae_rank_read_cols_rmd μ ℓ (c := fun k : dh ℓ => (i, Sum.inl k))
        (fun _ _ h => Sum.inl_injective (Prod.mk.inj h).2) (hdh ℓ)
  have hK : ∀ᵐ θ ∂μ, ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k))).rank
        = Fintype.card (dh ℓ) :=
    ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i =>
      ae_rank_read_cols_rmd μ ℓ (c := fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))
        (fun _ _ h => Sum.inl_injective (Sum.inr_injective (Prod.mk.inj h).2)) (hdh ℓ)
  have hV : ∀ᵐ θ ∂μ, ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ) :=
    ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i =>
      ae_rank_read_cols_rmd μ ℓ (c := fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
        (fun _ _ h => Sum.inr_injective (Sum.inr_injective (Prod.mk.inj h).2)) (hdh ℓ)
  have hO : ∀ᵐ θ ∂μ, ∀ ℓ (i : H ℓ),
      ((θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id).rank = Fintype.card (dh ℓ) :=
    ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i =>
      ae_rank_write_rows_rmd μ ℓ (r := fun k : dh ℓ => (i, k))
        (fun _ _ h => (Prod.mk.inj h).2) (hdh ℓ)
  -- (a) the entry `p` of every `B_P v₀` is nonzero: it is `(√d_h)⁻¹` at the witness
  have hA : ∀ᵐ θ ∂μ, ∀ P : Σ ℓ, H ℓ,
      (headScoreModel θ P.1 P.2 *ᵥ fun _ => (1 : ℝ)) p ≠ 0 := by
    refine ae_all_iff.2 fun P => ae_ne_zero_of_analytic μ (analyticOnNhd_score_rmd P.1 P.2 _ _)
      ⟨wit_rmd p k₀ fun _ => p, ?_⟩
    rw [wit_score_rmd]
    simpa using hs P.1
  -- (b) for `P ≠ P'`, the minor of `B_P v₀`, `B_{P'} v₀` on the rows `p`, `q` is nonzero: it is
  -- a product of two positive numbers at the witness whose query matrices put `B_P v₀` on `e_p`
  -- and every other `B_{P''} v₀` on `e_q`
  have hB : ∀ᵐ θ ∂μ, ∀ P P' : Σ ℓ, H ℓ, P ≠ P' →
      (headScoreModel θ P.1 P.2 *ᵥ fun _ => (1 : ℝ)) p
          * (headScoreModel θ P'.1 P'.2 *ᵥ fun _ => (1 : ℝ)) q
        - (headScoreModel θ P.1 P.2 *ᵥ fun _ => (1 : ℝ)) q
          * (headScoreModel θ P'.1 P'.2 *ᵥ fun _ => (1 : ℝ)) p ≠ 0 := by
    refine ae_all_iff.2 fun P => ae_all_iff.2 fun P' => ?_
    by_cases hPP : P = P'
    · exact Filter.Eventually.of_forall fun _ h => absurd hPP h
    · have hg : AnalyticOnNhd ℝ
          (fun θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut =>
            (headScoreModel θ P.1 P.2 *ᵥ fun _ => (1 : ℝ)) p
                * (headScoreModel θ P'.1 P'.2 *ᵥ fun _ => (1 : ℝ)) q
              - (headScoreModel θ P.1 P.2 *ᵥ fun _ => (1 : ℝ)) q
                * (headScoreModel θ P'.1 P'.2 *ᵥ fun _ => (1 : ℝ)) p) Set.univ :=
        ((analyticOnNhd_score_rmd P.1 P.2 _ _).mul (analyticOnNhd_score_rmd P'.1 P'.2 _ _)).sub
          ((analyticOnNhd_score_rmd P.1 P.2 _ _).mul (analyticOnNhd_score_rmd P'.1 P'.2 _ _))
      refine (ae_ne_zero_of_analytic μ hg
        ⟨wit_rmd p k₀ fun P'' => if P'' = P then p else q, ?_⟩).mono fun _ h _ => h
      rw [wit_score_rmd, wit_score_rmd]
      simp [Ne.symm hPP, hpq, Ne.symm hpq, hs]
  -- (c) the entry `p` of every `v₀ C_P` is nonzero: it is `1` at the witness
  have hC : ∀ᵐ θ ∂μ, ∀ P : Σ ℓ, H ℓ,
      ((fun _ => (1 : ℝ)) ᵥ* headValueModel θ P.1 P.2) p ≠ 0 := by
    refine ae_all_iff.2 fun P => ae_ne_zero_of_analytic μ (analyticOnNhd_value_rmd P.1 P.2 _ _)
      ⟨wit_rmd p k₀ fun _ => p, ?_⟩
    rw [wit_value_rmd]
    simp
  filter_upwards [h2, hQ, hK, hV, hO, hA, hB, hC] with θ h2 hQ hK hV hO hA hB hC
  refine ⟨?_, rank_eq_card_of_isUnit_det θ.D cD (h2.2.1 cD), hQ, hK, hV, hO,
    ⟨fun _ => 1, fun P h => hA P (by rw [h]; rfl), ?_, fun P h => hC P (congrFun h p)⟩⟩
  · -- `E` has rank `d`: at most its width, at least that of its invertible rows `c`
    exact le_antisymm (Matrix.rank_le_card_width _)
      ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (h2.2.2.1 c))).symm.le.trans
        (Matrix.rank_submatrix_le _ c id))
  -- if `B_P v₀ = r B_{P'} v₀`, the minor of the rows `p`, `q` vanishes
  intro P P' hPP r hr
  have e1 : (headScoreModel θ P.1 P.2 *ᵥ fun _ => (1 : ℝ)) p
      = r * (headScoreModel θ P'.1 P'.2 *ᵥ fun _ => (1 : ℝ)) p := congrFun hr p
  have e2 : (headScoreModel θ P.1 P.2 *ᵥ fun _ => (1 : ℝ)) q
      = r * (headScoreModel θ P'.1 P'.2 *ᵥ fun _ => (1 : ℝ)) q := congrFun hr q
  apply hB P P' hPP
  rw [e1, e2]
  ring

/-- **Lemma A.27 (Small writes), second value, for attention blocks:** under pre-RMSNorm with
`ε > 0`, for generic parameters `θ` and all small `τ ≠ 0`, the residual network has
`fd(θ_τ) = P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_eventually_funDim_smallWrites_attention_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDim (Arch.attention sees (rmsNorm ε) H dh) 1 (θ.smallWrites τ)
          + (Fintype.card d * (Fintype.card d - 1) / 2
            + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
        = Module.finrank ℝ
            (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  filter_upwards [ae_smallWritesGenericAttentionRMS μ hd hdIn hdOut hdh hdh0] with θ hθ
  exact eventually_funDim_smallWrites_attention_rmsNorm hε t₁ t₂ h12 hs2 hs1 θ hθ

/-- **Theorem 4.7 of the skips paper for attention blocks under pre-RMSNorm:** with
`d_in, d_out ≥ d ≥ 2`, `ε > 0`, `L` attention blocks with heads of width `1 ≤ d_h ≤ d`, and a
token that sees itself and another token, at almost every parameter the residual network has the
functional dimension `P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_attention_residual_rmsNorm (hε : 0 < ε)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  classical
  -- one parameter `θ₀` with the conditions of Lemma A.27, and one small `τ ≠ 0`:
  -- `fd(θ₀_τ) = P - d(d-1)/2 - s`
  obtain ⟨θ₀, hθ₀⟩ := (ae_smallWritesGenericAttentionRMS μ hd hdIn hdOut hdh hdh0).exists
  obtain ⟨τ, hτ⟩ :=
    (eventually_funDim_smallWrites_attention_rmsNorm hε t₁ t₂ h12 hs2 hs1 θ₀ hθ₀).exists
  -- at almost every `θ`, `fd(θ) ≥ fd(θ₀_τ)` (analytic outputs) and `fd(θ) ≤ P - d(d-1)/2 - s`
  filter_upwards [ae_funDim_ge (Arch.attention sees (rmsNorm ε) H dh) 1
      (fun ℓ => analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ) (analyticOnNhd_rmsNorm hε) μ
      (θ₀.smallWrites τ),
    ae_funDim_add_le_residual_attention_rmsNorm ε μ hdIn hdh] with θ h1 h2
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at hτ h2 ⊢
  omega

/-- **Theorem 4.7, the gain, for attention blocks under pre-RMSNorm:** if moreover every block
has total width `H d_h ≥ d`, at almost every parameter the skips raise the functional dimension
by at least `L d(d−1)/2`. -/
theorem ae_funDim_attention_residual_rmsNorm_ge_add (hε : 0 < ε)
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (hH : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ θ ∂μ, funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
        + L * (Fintype.card d * (Fintype.card d - 1) / 2)
      ≤ funDim (Arch.attention sees (rmsNorm ε) H dh) 1 θ := by
  classical
  -- `fd₁ = P - d(d-1)/2 - s` and `fd₀ ≤ P - (L + 1) d(d-1)/2 - s`
  filter_upwards [ae_funDim_attention_residual_rmsNorm hε μ hd hdIn hdOut hdh hdh0 t₁ t₂ h12 hs2
      hs1, ae_funDim_add_le_skipless_attention_rmsNorm ε μ hdIn hdh hH] with θ h1 h2
  rw [add_one_mul] at h2
  generalize Fintype.card d * (Fintype.card d - 1) / 2 = N at h1 h2 ⊢
  omega

end Skips
