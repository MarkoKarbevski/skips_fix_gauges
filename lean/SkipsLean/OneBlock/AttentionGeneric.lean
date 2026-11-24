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

/-! ### Helpers: one parameter at which the conditions on `v₀ = (1, …, 1)` hold -/

section Witness

variable [DecidableEq dIn] [DecidableEq dOut] [DecidableEq (dh 0)] (c : d ↪ dIn) (p : d)
  (k₀ : dh 0) (o₀ : dOut) (r : H 0 → d)

/-- Helper: the witness. `E` sends `e_b` to `e_{c b}`; the query matrix of head `i` has the single
entry `1` at `(r i, k₀)`; every key and value matrix has the single entry `1` at `(p, k₀)`; every
output matrix has the single entry `1` at `(k₀, p)`; `D` has the single entry `1` at `(p, o₀)`. -/
private noncomputable def wit_obg :
    Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut where
  E := Matrix.of fun a b => if a = c b then 1 else 0
  read ℓ := Fin.cases (Matrix.of fun (b : d) (x : H 0 × (dh 0 ⊕ (dh 0 ⊕ dh 0))) =>
      Sum.elim (fun k => if b = r x.1 ∧ k = k₀ then (1 : ℝ) else 0)
        (fun k => if b = p ∧ Sum.elim id id k = k₀ then 1 else 0) x.2) (fun l => l.elim0) ℓ
  write ℓ := Fin.cases (Matrix.of fun (x : H 0 × dh 0) (b : d) =>
      if x.2 = k₀ ∧ b = p then (1 : ℝ) else 0) (fun l => l.elim0) ℓ
  D := Matrix.of fun b o => if b = p ∧ o = o₀ then 1 else 0

omit [Fintype d] [Fintype dOut] in
/-- Helper: `E^⊤ v₀` is the vector of ones. -/
private theorem wit_Et_obg :
    (wit_obg (T := T) (sees := sees) c p k₀ o₀ r).Eᵀ *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext b
  show ∑ a, (if a = c b then (1 : ℝ) else 0) * 1 = 1
  simp

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: `W_{K,i}^⊤ (1, …, 1) = e_{k₀}`. -/
private theorem wit_Kt_obg (i : H 0) :
    (attnK (wit_obg (T := T) (sees := sees) c p k₀ o₀ r) i)ᵀ *ᵥ (fun _ => (1 : ℝ))
      = fun k => if k = k₀ then 1 else 0 := by
  funext k
  show ∑ b, (if b = p ∧ k = k₀ then (1 : ℝ) else 0) * 1 = if k = k₀ then 1 else 0
  by_cases hk : k = k₀ <;> simp [hk]

omit [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `W_{Q,i} e_{k₀} = e_{r i}`. -/
private theorem wit_Q_obg (i : H 0) :
    attnQ (wit_obg (T := T) (sees := sees) c p k₀ o₀ r) i *ᵥ (fun k => if k = k₀ then 1 else 0)
      = fun b => if b = r i then 1 else 0 := by
  funext b
  show ∑ k, (if b = r i ∧ k = k₀ then (1 : ℝ) else 0) * (if k = k₀ then 1 else 0)
    = if b = r i then 1 else 0
  by_cases hb : b = r i <;> simp [hb]

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: `E e_q = e_{c q}`. -/
private theorem wit_E_obg (q : d) :
    (wit_obg (T := T) (sees := sees) c p k₀ o₀ r).E *ᵥ (fun b => if b = q then 1 else 0)
      = fun a => if a = c q then 1 else 0 := by
  funext a
  show ∑ b, (if a = c b then (1 : ℝ) else 0) * (if b = q then 1 else 0)
    = if a = c q then 1 else 0
  simp

omit [Fintype d] [Fintype dOut] in
/-- Helper: `v₀ E` is the vector of ones. -/
private theorem wit_vE_obg :
    (fun _ => (1 : ℝ)) ᵥ* (wit_obg (T := T) (sees := sees) c p k₀ o₀ r).E = fun _ => 1 := by
  funext b
  show ∑ a, 1 * (if a = c b then (1 : ℝ) else 0) = 1
  simp

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: `(1, …, 1) W_{V,i} = e_{k₀}`. -/
private theorem wit_vV_obg (i : H 0) :
    (fun _ => (1 : ℝ)) ᵥ* attnV (wit_obg (T := T) (sees := sees) c p k₀ o₀ r) i
      = fun k => if k = k₀ then 1 else 0 := by
  funext k
  show ∑ b, 1 * (if b = p ∧ k = k₀ then (1 : ℝ) else 0) = if k = k₀ then 1 else 0
  by_cases hk : k = k₀ <;> simp [hk]

omit [Fintype d] [Fintype dIn] [Fintype dOut] in
/-- Helper: `e_{k₀} W_{O,i} = e_p`. -/
private theorem wit_vO_obg (i : H 0) :
    (fun k => if k = k₀ then (1 : ℝ) else 0)
        ᵥ* attnO (wit_obg (T := T) (sees := sees) c p k₀ o₀ r) i
      = fun b => if b = p then 1 else 0 := by
  funext b
  show ∑ k, (if k = k₀ then (1 : ℝ) else 0) * (if k = k₀ ∧ b = p then 1 else 0)
    = if b = p then 1 else 0
  by_cases hb : b = p <;> simp [hb]

omit [Fintype dIn] [Fintype dOut] in
/-- Helper: `e_p D = e_{o₀}`. -/
private theorem wit_vD_obg :
    (fun b => if b = p then (1 : ℝ) else 0) ᵥ* (wit_obg (T := T) (sees := sees) c p k₀ o₀ r).D
      = fun o => if o = o₀ then 1 else 0 := by
  funext o
  show ∑ b, (if b = p then (1 : ℝ) else 0) * (if b = p ∧ o = o₀ then 1 else 0)
    = if o = o₀ then 1 else 0
  by_cases ho : o = o₀ <;> simp [ho]

omit [Fintype dOut] in
/-- Helper: at the witness, `B_i v₀ = (√d_h)⁻¹ e_{c (r i)}`. -/
private theorem wit_score_obg (i : H 0) :
    attnScore (wit_obg (T := T) (sees := sees) c p k₀ o₀ r) i *ᵥ (fun _ => (1 : ℝ))
      = (Real.sqrt (Fintype.card (dh 0)))⁻¹ • fun a => if a = c (r i) then 1 else 0 := by
  rw [attnScore, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, wit_Et_obg, wit_Kt_obg, wit_Q_obg, wit_E_obg]

omit [Fintype dOut] in
/-- Helper: at the witness, `v₀ C_i = e_{o₀}`. -/
private theorem wit_value_obg (i : H 0) :
    (fun _ => (1 : ℝ)) ᵥ* attnValue (wit_obg (T := T) (sees := sees) c p k₀ o₀ r) i
      = fun o => if o = o₀ then 1 else 0 := by
  rw [attnValue, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
    wit_vE_obg, wit_vV_obg, wit_vO_obg, wit_vD_obg]

end Witness

/-- The conditions of the proof of Theorem C.1 for an attention block hold at generic
parameters, for `d_in, d_out ≥ d ≥ 2`, heads of width `d_h ≤ d` and total width `H d_h ≥ d`. -/
theorem ae_oneBlockGenericAttention
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : Fintype.card (dh 0) ≤ Fintype.card d)
    (hH : Fintype.card d ≤ Fintype.card (H 0) * Fintype.card (dh 0)) :
    ∀ᵐ θ ∂μ, OneBlockGenericAttention θ := by
  classical
  -- the sizes: `d_h ≥ 1` (as `H d_h ≥ d ≥ 2`), two distinct `p, q` in `d`, `c : d ↪ d_in`,
  -- `d ↪ d_out`, `d ↪ H × d_h`, some `k₀ : d_h` and some `o₀ : d_out`
  have hHd : Fintype.card d ≤ Fintype.card (H 0 × dh 0) := hH.trans (Fintype.card_prod _ _).symm.le
  have hdh0 : 0 < Fintype.card (dh 0) := by
    rcases Nat.eq_zero_or_pos (Fintype.card (dh 0)) with h | h
    · rw [h, Nat.mul_zero] at hH
      omega
    · exact h
  obtain ⟨k₀⟩ : Nonempty (dh 0) := Fintype.card_pos_iff.1 hdh0
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨cD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  obtain ⟨cH⟩ := Function.Embedding.nonempty_of_card_le hHd
  obtain ⟨o₀⟩ : Nonempty dOut := ⟨cD p⟩
  have hs : (Real.sqrt (Fintype.card (dh 0)))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_ne_zero'.2 (by exact_mod_cast hdh0))
  -- `E`, `D` and the write have rank `d` (`Generic/Params.lean`)
  have h1 := ae_rank_E_write μ hdIn (fun ℓ => by
    obtain rfl := Subsingleton.elim ℓ 0
    exact hHd)
  have h2 := ae_isUnit_det_submatrix μ
  -- the query, key, value and output matrices of every head have rank `d_h`
  have hQ : ∀ᵐ θ ∂μ, ∀ i, (attnQ θ i).rank = Fintype.card (dh 0) :=
    ae_all_iff.2 fun i => ae_rank_read_cols_obg μ 0 (c := fun k : dh 0 => (i, Sum.inl k))
      (fun _ _ h => Sum.inl_injective (Prod.mk.inj h).2) hdh
  have hK : ∀ᵐ θ ∂μ, ∀ i, (attnK θ i).rank = Fintype.card (dh 0) :=
    ae_all_iff.2 fun i => ae_rank_read_cols_obg μ 0 (c := fun k : dh 0 => (i, Sum.inr (Sum.inl k)))
      (fun _ _ h => Sum.inl_injective (Sum.inr_injective (Prod.mk.inj h).2)) hdh
  have hV : ∀ᵐ θ ∂μ, ∀ i, (attnV θ i).rank = Fintype.card (dh 0) :=
    ae_all_iff.2 fun i => ae_rank_read_cols_obg μ 0 (c := fun k : dh 0 => (i, Sum.inr (Sum.inr k)))
      (fun _ _ h => Sum.inr_injective (Sum.inr_injective (Prod.mk.inj h).2)) hdh
  have hO : ∀ᵐ θ ∂μ, ∀ i, (attnO θ i).rank = Fintype.card (dh 0) :=
    ae_all_iff.2 fun i => ae_rank_write_rows_obg μ 0 (r := fun k : dh 0 => (i, k))
      (fun _ _ h => (Prod.mk.inj h).2) hdh
  -- (a) the entry `c p` of every `B_i v₀` is nonzero: it is `(√d_h)⁻¹` at the witness
  have hA : ∀ᵐ θ ∂μ, ∀ i, (attnScore θ i *ᵥ fun _ => (1 : ℝ)) (c p) ≠ 0 := by
    refine ae_all_iff.2 fun i => ae_ne_zero_of_analytic μ (analyticOnNhd_score_obg i _ _)
      ⟨wit_obg c p k₀ o₀ fun _ => p, ?_⟩
    rw [wit_score_obg]
    simpa using hs
  -- (b) for `i ≠ j`, the minor of `B_i v₀`, `B_j v₀` on the rows `c p`, `c q` is nonzero: it is
  -- `(√d_h)⁻²` at the witness whose query matrices put `B_i v₀` on `e_{c p}`, `B_j v₀` on `e_{c q}`
  have hB : ∀ᵐ θ ∂μ, ∀ i j : H 0, i ≠ j →
      (attnScore θ i *ᵥ fun _ => (1 : ℝ)) (c p) * (attnScore θ j *ᵥ fun _ => (1 : ℝ)) (c q)
        - (attnScore θ i *ᵥ fun _ => (1 : ℝ)) (c q) * (attnScore θ j *ᵥ fun _ => (1 : ℝ)) (c p)
        ≠ 0 := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hij h
    · have hg : AnalyticOnNhd ℝ
          (fun θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut =>
            (attnScore θ i *ᵥ fun _ => (1 : ℝ)) (c p) * (attnScore θ j *ᵥ fun _ => (1 : ℝ)) (c q)
              - (attnScore θ i *ᵥ fun _ => (1 : ℝ)) (c q)
                * (attnScore θ j *ᵥ fun _ => (1 : ℝ)) (c p)) Set.univ :=
        ((analyticOnNhd_score_obg i _ _).mul (analyticOnNhd_score_obg j _ _)).sub
          ((analyticOnNhd_score_obg i _ _).mul (analyticOnNhd_score_obg j _ _))
      refine (ae_ne_zero_of_analytic μ hg
        ⟨wit_obg c p k₀ o₀ fun h => if h = i then p else q, ?_⟩).mono fun _ h _ => h
      rw [wit_score_obg, wit_score_obg]
      simp [Ne.symm hij, hpq, Ne.symm hpq, hs]
  -- (c) the entry `o₀` of every `v₀ C_i` is nonzero: it is `1` at the witness
  have hC : ∀ᵐ θ ∂μ, ∀ i, ((fun _ => (1 : ℝ)) ᵥ* attnValue θ i) o₀ ≠ 0 := by
    refine ae_all_iff.2 fun i => ae_ne_zero_of_analytic μ (analyticOnNhd_value_obg i _ _)
      ⟨wit_obg c p k₀ o₀ fun _ => p, ?_⟩
    rw [wit_value_obg]
    simp
  -- the queries of all heads: `d` of their columns, chosen by `cH`, are invertible
  let g : H 0 × dh 0 ↪ (Arch.attention (T := T) (d := d) sees id H dh).r 0 :=
    ⟨fun x => (x.1, Sum.inl x.2), fun x y h =>
      Prod.ext (Prod.mk.inj h).1 (Sum.inl_injective (Prod.mk.inj h).2)⟩
  filter_upwards [h1, h2, hQ, hK, hV, hO, hA, hB, hC] with θ h1 h2 hQ hK hV hO hA hB hC
  refine ⟨h1.1, rank_eq_card_of_isUnit_det θ.D cD (h2.2.1 cD), hQ, hK, hV, hO,
    rank_eq_card_of_isUnit_det _ cH (h2.1 0 (cH.trans g)), h1.2 0,
    ⟨fun _ => 1, fun i h => hA i (by rw [h]; rfl), ?_, fun i h => hC i (congrFun h o₀)⟩⟩
  -- if `B_i v₀ = r B_j v₀`, the minor of the rows `c p`, `c q` vanishes
  intro i j hij r hr
  have e1 : (attnScore θ i *ᵥ fun _ => (1 : ℝ)) (c p)
      = r * (attnScore θ j *ᵥ fun _ => (1 : ℝ)) (c p) := congrFun hr (c p)
  have e2 : (attnScore θ i *ᵥ fun _ => (1 : ℝ)) (c q)
      = r * (attnScore θ j *ᵥ fun _ => (1 : ℝ)) (c q) := congrFun hr (c q)
  apply hB i j hij
  rw [e1, e2]
  ring


end Skips
