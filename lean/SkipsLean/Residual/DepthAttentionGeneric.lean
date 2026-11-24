import SkipsLean.Residual.DepthAttention
import SkipsLean.OneBlock.Common
import SkipsLean.Generic.Params

/-!
# Residual networks of attention blocks: the conditions of Lemma A.27 at generic parameters

Paper (skips paper), Lemma A.27: "Let `d_model ≥ 2` […] an attention block with heads of width at
most `d_model` […]. For generic parameters […]", and the generic conditions of "Part (i) for
attention blocks" of Theorem B.1, for the heads of all blocks together.

Here: for `d_in, d_out ≥ d ≥ 2` and heads of width `1 ≤ d_h ≤ d` in every block (any numbers of
heads, any total widths), `SmallWritesGenericAttention θ` (`Residual/DepthAttention.lean`) holds
at almost every `θ`, for every additive Haar measure on the parameters.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-! ### Helpers: ranks of columns of a read and of rows of a write -/

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `analyticOnNhd_det_obg` of `OneBlock/AttentionGeneric.lean`): the
determinant of a square matrix that depends linearly on the parameters is an analytic function of
the parameters. -/
private theorem analyticOnNhd_det_dpg {A : Arch T d L} {n : Type*} [Fintype n]
    [DecidableEq n] (Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ) :
    AnalyticOnNhd ℝ (fun θ => (Φ θ).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ =>
      analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ (σ i) i).comp Φ))

/-- Helper: a matrix whose submatrix on the rows `r` and the columns `c` (both injective) is the
identity. -/
private theorem exists_submatrix_eq_one_dpg {m p n : Type*} [DecidableEq n] {r : n → m}
    (hr : Function.Injective r) {c : n → p} (hc : Function.Injective c) :
    ∃ M : Matrix m p ℝ, M.submatrix r c = 1 := by
  classical
  refine ⟨Matrix.of fun a b => if ∃ x, r x = a ∧ c x = b then 1 else 0, ?_⟩
  ext x y
  simp [Matrix.one_apply, hr.eq_iff, hc.eq_iff]

omit [Fintype T] [DecidableEq d] in
/-- Helper: at generic parameters, `n ≤ d` distinct columns `c` of the read of block `ℓ` form a
matrix of rank `n`: some `n` of its rows form a matrix that is invertible at generic parameters. -/
private theorem ae_rank_read_cols_dpg {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*} [Fintype n] [DecidableEq n] {c : n → A.r ℓ}
    (hc : Function.Injective c) (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.read ℓ).submatrix id c).rank = Fintype.card n := by
  -- `n` rows `ρ`, and the square submatrix of the read on the rows `ρ` and the columns `c`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_dpg ρ.injective hc
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
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_dpg Φ) hne] with θ hθ
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
private theorem ae_rank_write_rows_dpg {A : Arch T d L}
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*} [Fintype n]
    [DecidableEq n] {r : n → A.w ℓ} (hr : Function.Injective r)
    (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.write ℓ).submatrix r id).rank = Fintype.card n := by
  -- `n` columns `ρ`, and the square submatrix of the write on the rows `r` and the columns `ρ`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_dpg hr ρ.injective
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
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_dpg Φ) hne] with θ hθ
  -- an invertible `n × n` submatrix gives rank `≥ n`, and the rank is at most the height `n`
  have h1 : (((θ.write ℓ).submatrix r id).submatrix id ρ).rank = Fintype.card n :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hθ))
  have h2 : (((θ.write ℓ).submatrix r id).submatrix id ρ).rank
      ≤ ((θ.write ℓ).submatrix r id).rank :=
    Matrix.rank_submatrix_le _ id ρ
  have h3 := Matrix.rank_le_card_height ((θ.write ℓ).submatrix r id)
  omega

/-! ### Helpers: the entries of `B_P v^⊤` and `v C_P` are analytic functions of the parameters -/

/-- Helper: an entry of the product of two matrices whose entries are analytic functions is an
analytic function. -/
private theorem analyticOnNhd_mul_entry_dpg {P m n p : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [Fintype n] {f : P → Matrix m n ℝ} {g : P → Matrix n p ℝ}
    (hf : ∀ a b, AnalyticOnNhd ℝ (fun y => f y a b) Set.univ)
    (hg : ∀ a b, AnalyticOnNhd ℝ (fun y => g y a b) Set.univ) (a : m) (b : p) :
    AnalyticOnNhd ℝ (fun y => (f y * g y) a b) Set.univ := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticOnNhd_fun_sum _ fun k _ => (hf a k).mul (hg k b)

omit [Fintype T] [DecidableEq d] in
/-- Helper: an entry of `E` is an analytic function of the parameters. -/
private theorem analyticOnNhd_E_dpg {A : Arch T d L} (a : dIn) (b : d) :
    AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => θ.E a b) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ a b).comp
    (Params.linE (A := A) (dIn := dIn) (dOut := dOut)))

omit [Fintype T] [DecidableEq d] in
/-- Helper: an entry of the read of block `ℓ` is an analytic function of the parameters. -/
private theorem analyticOnNhd_read_dpg {A : Arch T d L} (ℓ : Fin L) (b : d)
    (x : A.r ℓ) : AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => θ.read ℓ b x) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ b x).comp
    (Params.linRead (A := A) (dIn := dIn) (dOut := dOut) ℓ))

omit [Fintype T] [DecidableEq d] in
/-- Helper: an entry of the write of block `ℓ` is an analytic function of the parameters. -/
private theorem analyticOnNhd_write_dpg {A : Arch T d L} (ℓ : Fin L) (x : A.w ℓ)
    (b : d) : AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => θ.write ℓ x b) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ x b).comp
    (Params.linWrite (A := A) (dIn := dIn) (dOut := dOut) ℓ))

omit [Fintype T] [DecidableEq d] in
/-- Helper: an entry of `D` is an analytic function of the parameters. -/
private theorem analyticOnNhd_D_dpg {A : Arch T d L} (b : d) (o : dOut) :
    AnalyticOnNhd ℝ (fun θ : Params A dIn dOut => θ.D b o) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ b o).comp
    (Params.linD (A := A) (dIn := dIn) (dOut := dOut)))

omit [DecidableEq d] in
/-- Helper: an entry of `B_P v^⊤`, `(√d_h)⁻¹ ∑_b (E W_Q W_K^⊤ E^⊤)_{a b} v_b` for head `i` of
block `ℓ`, is an analytic function of the parameters. -/
private theorem analyticOnNhd_score_dpg (ℓ : Fin L) (i : H ℓ) (v : dIn → ℝ) (a : dIn) :
    AnalyticOnNhd ℝ (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut =>
      (headScore θ ℓ i *ᵥ v) a) Set.univ := by
  -- the entries of `E`, `W_Q`, `W_K^⊤`, `E^⊤`, then of their product
  have hE : ∀ a b, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut => θ.E a b)
      Set.univ := fun a b => analyticOnNhd_E_dpg a b
  have hEt : ∀ b a, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut => θ.Eᵀ b a)
      Set.univ := fun b a => analyticOnNhd_E_dpg a b
  have hQ : ∀ b k, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut =>
        ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)) b k) Set.univ :=
    fun b k => analyticOnNhd_read_dpg (A := Arch.attention sees id H dh) ℓ b (i, Sum.inl k)
  have hK : ∀ k b, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut =>
        ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))ᵀ k b) Set.univ :=
    fun k b => analyticOnNhd_read_dpg (A := Arch.attention sees id H dh) ℓ b
      (i, Sum.inr (Sum.inl k))
  have h4 := analyticOnNhd_mul_entry_dpg
    (analyticOnNhd_mul_entry_dpg (analyticOnNhd_mul_entry_dpg hE hQ) hK) hEt
  simp only [headScore, Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul]
  exact Finset.analyticOnNhd_fun_sum _ fun b _ =>
    (analyticOnNhd_const.mul (h4 a b)).mul analyticOnNhd_const

omit [DecidableEq d] in
/-- Helper: an entry of `v C_P`, `∑_a v_a (E W_V W_O D)_{a o}` for head `i` of block `ℓ`, is an
analytic function of the parameters. -/
private theorem analyticOnNhd_value_dpg (ℓ : Fin L) (i : H ℓ) (v : dIn → ℝ) (o : dOut) :
    AnalyticOnNhd ℝ (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut =>
      (v ᵥ* headValue θ ℓ i) o) Set.univ := by
  -- the entries of `E`, `W_V`, `W_O`, `D`, then of their product
  have hE : ∀ a b, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut => θ.E a b)
      Set.univ := fun a b => analyticOnNhd_E_dpg a b
  have hV : ∀ b k, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut =>
        ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))) b k) Set.univ :=
    fun b k => analyticOnNhd_read_dpg (A := Arch.attention sees id H dh) ℓ b
      (i, Sum.inr (Sum.inr k))
  have hO : ∀ k b, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut =>
        ((θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id) k b) Set.univ :=
    fun k b => analyticOnNhd_write_dpg (A := Arch.attention sees id H dh) ℓ (i, k) b
  have hD : ∀ b o, AnalyticOnNhd ℝ
      (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut => θ.D b o)
      Set.univ := fun b o => analyticOnNhd_D_dpg b o
  have h4 := analyticOnNhd_mul_entry_dpg
    (analyticOnNhd_mul_entry_dpg (analyticOnNhd_mul_entry_dpg hE hV) hO) hD
  simp only [headValue, Matrix.vecMul, dotProduct]
  exact Finset.analyticOnNhd_fun_sum _ fun a _ => analyticOnNhd_const.mul (h4 a o)

/-! ### Helpers: one parameter at which the conditions on `v₀ = (1, …, 1)` hold -/

section Witness

variable [DecidableEq dIn] [DecidableEq dOut] [∀ ℓ, DecidableEq (dh ℓ)] (c : d ↪ dIn) (p : d)
  (k₀ : ∀ ℓ, dh ℓ) (o₀ : dOut) (r : (Σ ℓ, H ℓ) → d)

/-- Helper: the witness. `E` sends `e_b` to `e_{c b}`; in block `ℓ`, the query matrix of head `i`
has the single entry `1` at `(r ⟨ℓ, i⟩, k₀ ℓ)`, every key and value matrix has the single entry
`1` at `(p, k₀ ℓ)`, every output matrix has the single entry `1` at `(k₀ ℓ, p)`; `D` has the
single entry `1` at `(p, o₀)`. -/
private noncomputable def wit_dpg :
    Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut where
  E := Matrix.of fun a b => if a = c b then 1 else 0
  read ℓ := Matrix.of fun (b : d) (x : H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) =>
      Sum.elim (fun k => if b = r ⟨ℓ, x.1⟩ ∧ k = k₀ ℓ then (1 : ℝ) else 0)
        (fun k => if b = p ∧ Sum.elim id id k = k₀ ℓ then 1 else 0) x.2
  write ℓ := Matrix.of fun (x : H ℓ × dh ℓ) (b : d) =>
      if x.2 = k₀ ℓ ∧ b = p then (1 : ℝ) else 0
  D := Matrix.of fun b o => if b = p ∧ o = o₀ then 1 else 0

omit [Fintype d] [Fintype dOut] in
/-- Helper: `E^⊤ v₀` is the vector of ones. -/
private theorem wit_Et_dpg :
    (wit_dpg (T := T) (sees := sees) c p k₀ o₀ r).Eᵀ *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext b
  show ∑ a, (if a = c b then (1 : ℝ) else 0) * 1 = 1
  simp

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: `W_K^⊤ (1, …, 1) = e_{k₀ ℓ}` for head `i` of block `ℓ`. -/
private theorem wit_Kt_dpg (ℓ : Fin L) (i : H ℓ) :
    ((wit_dpg (T := T) (sees := sees) c p k₀ o₀ r).read ℓ |>.submatrix id
        fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))ᵀ *ᵥ (fun _ => (1 : ℝ))
      = fun k => if k = k₀ ℓ then 1 else 0 := by
  funext k
  show ∑ b, (if b = p ∧ k = k₀ ℓ then (1 : ℝ) else 0) * 1 = if k = k₀ ℓ then 1 else 0
  by_cases hk : k = k₀ ℓ <;> simp [hk]

omit [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `W_Q e_{k₀ ℓ} = e_{r ⟨ℓ, i⟩}` for head `i` of block `ℓ`. -/
private theorem wit_Q_dpg (ℓ : Fin L) (i : H ℓ) :
    ((wit_dpg (T := T) (sees := sees) c p k₀ o₀ r).read ℓ |>.submatrix id
        fun k : dh ℓ => (i, Sum.inl k)) *ᵥ (fun k => if k = k₀ ℓ then 1 else 0)
      = fun b => if b = r ⟨ℓ, i⟩ then 1 else 0 := by
  funext b
  show ∑ k, (if b = r ⟨ℓ, i⟩ ∧ k = k₀ ℓ then (1 : ℝ) else 0) * (if k = k₀ ℓ then 1 else 0)
    = if b = r ⟨ℓ, i⟩ then 1 else 0
  by_cases hb : b = r ⟨ℓ, i⟩ <;> simp [hb]

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: `E e_q = e_{c q}`. -/
private theorem wit_E_dpg (q : d) :
    (wit_dpg (T := T) (sees := sees) c p k₀ o₀ r).E *ᵥ (fun b => if b = q then 1 else 0)
      = fun a => if a = c q then 1 else 0 := by
  funext a
  show ∑ b, (if a = c b then (1 : ℝ) else 0) * (if b = q then 1 else 0)
    = if a = c q then 1 else 0
  simp

omit [Fintype d] [Fintype dOut] in
/-- Helper: `v₀ E` is the vector of ones. -/
private theorem wit_vE_dpg :
    (fun _ => (1 : ℝ)) ᵥ* (wit_dpg (T := T) (sees := sees) c p k₀ o₀ r).E = fun _ => 1 := by
  funext b
  show ∑ a, 1 * (if a = c b then (1 : ℝ) else 0) = 1
  simp

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: `(1, …, 1) W_V = e_{k₀ ℓ}` for head `i` of block `ℓ`. -/
private theorem wit_vV_dpg (ℓ : Fin L) (i : H ℓ) :
    (fun _ => (1 : ℝ)) ᵥ* ((wit_dpg (T := T) (sees := sees) c p k₀ o₀ r).read ℓ |>.submatrix id
        fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
      = fun k => if k = k₀ ℓ then 1 else 0 := by
  funext k
  show ∑ b, 1 * (if b = p ∧ k = k₀ ℓ then (1 : ℝ) else 0) = if k = k₀ ℓ then 1 else 0
  by_cases hk : k = k₀ ℓ <;> simp [hk]

omit [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `e_{k₀ ℓ} W_O = e_p` for head `i` of block `ℓ`. -/
private theorem wit_vO_dpg (ℓ : Fin L) (i : H ℓ) :
    (fun k => if k = k₀ ℓ then (1 : ℝ) else 0)
        ᵥ* ((wit_dpg (T := T) (sees := sees) c p k₀ o₀ r).write ℓ |>.submatrix
          (fun k : dh ℓ => (i, k)) id)
      = fun b => if b = p then 1 else 0 := by
  funext b
  show ∑ k, (if k = k₀ ℓ then (1 : ℝ) else 0) * (if k = k₀ ℓ ∧ b = p then 1 else 0)
    = if b = p then 1 else 0
  by_cases hb : b = p <;> simp [hb]

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: `e_p D = e_{o₀}`. -/
private theorem wit_vD_dpg :
    (fun b => if b = p then (1 : ℝ) else 0) ᵥ* (wit_dpg (T := T) (sees := sees) c p k₀ o₀ r).D
      = fun o => if o = o₀ then 1 else 0 := by
  funext o
  show ∑ b, (if b = p then (1 : ℝ) else 0) * (if b = p ∧ o = o₀ then 1 else 0)
    = if o = o₀ then 1 else 0
  by_cases ho : o = o₀ <;> simp [ho]

omit [Fintype dOut] in
/-- Helper: at the witness, `B_P v₀ = (√d_{h,ℓ})⁻¹ e_{c (r P)}` for the head `P = ⟨ℓ, i⟩`. -/
private theorem wit_score_dpg (P : Σ ℓ, H ℓ) :
    headScore (wit_dpg (T := T) (sees := sees) c p k₀ o₀ r) P.1 P.2 *ᵥ (fun _ => (1 : ℝ))
      = (Real.sqrt (Fintype.card (dh P.1)))⁻¹ • fun a => if a = c (r P) then 1 else 0 := by
  rw [headScore, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, wit_Et_dpg, wit_Kt_dpg, wit_Q_dpg, wit_E_dpg, Sigma.eta]

omit [Fintype dOut] in
/-- Helper: at the witness, `v₀ C_P = e_{o₀}` for every head `P`. -/
private theorem wit_value_dpg (P : Σ ℓ, H ℓ) :
    (fun _ => (1 : ℝ)) ᵥ* headValue (wit_dpg (T := T) (sees := sees) c p k₀ o₀ r) P.1 P.2
      = fun o => if o = o₀ then 1 else 0 := by
  rw [headValue, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
    wit_vE_dpg, wit_vV_dpg, wit_vO_dpg, wit_vD_dpg]

end Witness

/-- The conditions of Lemma A.27 for attention blocks hold at generic parameters, for
`d_in, d_out ≥ d ≥ 2` and heads of width `1 ≤ d_h ≤ d`. -/
theorem ae_smallWritesGenericAttention
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ)) :
    ∀ᵐ θ ∂μ, SmallWritesGenericAttention θ := by
  classical
  -- the sizes: two distinct `p, q` in `d`, `c : d ↪ d_in`, `d ↪ d_out`, some `k₀ ℓ : d_{h,ℓ}`
  -- in every block and some `o₀ : d_out`
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨cD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  obtain ⟨o₀⟩ : Nonempty dOut := ⟨cD p⟩
  obtain ⟨k₀⟩ : Nonempty (∀ ℓ, dh ℓ) := ⟨fun ℓ => (Fintype.card_pos_iff.1 (hdh0 ℓ)).some⟩
  have hs : ∀ ℓ, (Real.sqrt (Fintype.card (dh ℓ)))⁻¹ ≠ 0 := fun ℓ =>
    inv_ne_zero (Real.sqrt_ne_zero'.2 (by exact_mod_cast hdh0 ℓ))
  -- `d` rows of `E` and `d` columns of `D` are invertible (`Generic/Params.lean`)
  have h2 := ae_isUnit_det_submatrix μ
  -- the query, key, value and output matrices of every head of every block have rank `d_h`
  have hQ : ∀ᵐ θ ∂μ, ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank = Fintype.card (dh ℓ) :=
    ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i =>
      ae_rank_read_cols_dpg μ ℓ (c := fun k : dh ℓ => (i, Sum.inl k))
        (fun _ _ h => Sum.inl_injective (Prod.mk.inj h).2) (hdh ℓ)
  have hK : ∀ᵐ θ ∂μ, ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k))).rank
        = Fintype.card (dh ℓ) :=
    ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i =>
      ae_rank_read_cols_dpg μ ℓ (c := fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))
        (fun _ _ h => Sum.inl_injective (Sum.inr_injective (Prod.mk.inj h).2)) (hdh ℓ)
  have hV : ∀ᵐ θ ∂μ, ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ) :=
    ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i =>
      ae_rank_read_cols_dpg μ ℓ (c := fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
        (fun _ _ h => Sum.inr_injective (Sum.inr_injective (Prod.mk.inj h).2)) (hdh ℓ)
  have hO : ∀ᵐ θ ∂μ, ∀ ℓ (i : H ℓ),
      ((θ.write ℓ).submatrix (fun k : dh ℓ => (i, k)) id).rank = Fintype.card (dh ℓ) :=
    ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i =>
      ae_rank_write_rows_dpg μ ℓ (r := fun k : dh ℓ => (i, k))
        (fun _ _ h => (Prod.mk.inj h).2) (hdh ℓ)
  -- (a) the entry `c p` of every `B_P v₀` is nonzero: it is `(√d_h)⁻¹` at the witness
  have hA : ∀ᵐ θ ∂μ, ∀ P : Σ ℓ, H ℓ, (headScore θ P.1 P.2 *ᵥ fun _ => (1 : ℝ)) (c p) ≠ 0 := by
    refine ae_all_iff.2 fun P => ae_ne_zero_of_analytic μ (analyticOnNhd_score_dpg P.1 P.2 _ _)
      ⟨wit_dpg c p k₀ o₀ fun _ => p, ?_⟩
    rw [wit_score_dpg]
    simpa using hs P.1
  -- (b) for `P ≠ P'`, the minor of `B_P v₀`, `B_{P'} v₀` on the rows `c p`, `c q` is nonzero: it
  -- is a product of two positive numbers at the witness whose query matrices put `B_P v₀` on
  -- `e_{c p}` and every other `B_{P''} v₀` on `e_{c q}`
  have hB : ∀ᵐ θ ∂μ, ∀ P P' : Σ ℓ, H ℓ, P ≠ P' →
      (headScore θ P.1 P.2 *ᵥ fun _ => (1 : ℝ)) (c p)
          * (headScore θ P'.1 P'.2 *ᵥ fun _ => (1 : ℝ)) (c q)
        - (headScore θ P.1 P.2 *ᵥ fun _ => (1 : ℝ)) (c q)
          * (headScore θ P'.1 P'.2 *ᵥ fun _ => (1 : ℝ)) (c p) ≠ 0 := by
    refine ae_all_iff.2 fun P => ae_all_iff.2 fun P' => ?_
    by_cases hPP : P = P'
    · exact Filter.Eventually.of_forall fun _ h => absurd hPP h
    · have hg : AnalyticOnNhd ℝ
          (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut =>
            (headScore θ P.1 P.2 *ᵥ fun _ => (1 : ℝ)) (c p)
                * (headScore θ P'.1 P'.2 *ᵥ fun _ => (1 : ℝ)) (c q)
              - (headScore θ P.1 P.2 *ᵥ fun _ => (1 : ℝ)) (c q)
                * (headScore θ P'.1 P'.2 *ᵥ fun _ => (1 : ℝ)) (c p)) Set.univ :=
        ((analyticOnNhd_score_dpg P.1 P.2 _ _).mul (analyticOnNhd_score_dpg P'.1 P'.2 _ _)).sub
          ((analyticOnNhd_score_dpg P.1 P.2 _ _).mul (analyticOnNhd_score_dpg P'.1 P'.2 _ _))
      refine (ae_ne_zero_of_analytic μ hg
        ⟨wit_dpg c p k₀ o₀ fun P'' => if P'' = P then p else q, ?_⟩).mono fun _ h _ => h
      rw [wit_score_dpg, wit_score_dpg]
      simp [Ne.symm hPP, hpq, Ne.symm hpq, hs]
  -- (c) the entry `o₀` of every `v₀ C_P` is nonzero: it is `1` at the witness
  have hC : ∀ᵐ θ ∂μ, ∀ P : Σ ℓ, H ℓ, ((fun _ => (1 : ℝ)) ᵥ* headValue θ P.1 P.2) o₀ ≠ 0 := by
    refine ae_all_iff.2 fun P => ae_ne_zero_of_analytic μ (analyticOnNhd_value_dpg P.1 P.2 _ _)
      ⟨wit_dpg c p k₀ o₀ fun _ => p, ?_⟩
    rw [wit_value_dpg]
    simp
  filter_upwards [h2, hQ, hK, hV, hO, hA, hB, hC] with θ h2 hQ hK hV hO hA hB hC
  refine ⟨?_, rank_eq_card_of_isUnit_det θ.D cD (h2.2.1 cD), hQ, hK, hV, hO,
    ⟨fun _ => 1, fun P h => hA P (by rw [h]; rfl), ?_, fun P h => hC P (congrFun h o₀)⟩⟩
  · -- `E` has rank `d`: at most its width, at least that of its invertible rows `c`
    exact le_antisymm (Matrix.rank_le_card_width _)
      ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (h2.2.2.1 c))).symm.le.trans
        (Matrix.rank_submatrix_le _ c id))
  -- if `B_P v₀ = r B_{P'} v₀`, the minor of the rows `c p`, `c q` vanishes
  intro P P' hPP r hr
  have e1 : (headScore θ P.1 P.2 *ᵥ fun _ => (1 : ℝ)) (c p)
      = r * (headScore θ P'.1 P'.2 *ᵥ fun _ => (1 : ℝ)) (c p) := congrFun hr (c p)
  have e2 : (headScore θ P.1 P.2 *ᵥ fun _ => (1 : ℝ)) (c q)
      = r * (headScore θ P'.1 P'.2 *ᵥ fun _ => (1 : ℝ)) (c q) := congrFun hr (c q)
  apply hB P P' hPP
  rw [e1, e2]
  ring

end Skips
