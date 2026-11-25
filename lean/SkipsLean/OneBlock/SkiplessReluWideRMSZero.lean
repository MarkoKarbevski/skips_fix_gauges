import SkipsLean.OneBlock.SkiplessHomogeneousRMSZeroEqAt
import SkipsLean.OneBlock.UnitsGeneralPosition

/-!
# One skipless ReLU block of width at least `d` under pre-RMSNorm with `ε = 0`: the equality

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`, and the skipless
network at most `P − d_model² − d_model (d_model − 1)/2 − 1 − s`, with equality for ReLU and ReLU²
blocks. So the skip raises the functional dimension by at least `d_model²`, and by exactly
`d_model²` for ReLU and ReLU² blocks."

Here "with equality" and "by exactly `d_model²`" **for a ReLU block of width at least `d_model`**
(the file `OneBlock/SkiplessHomogeneousRMSZeroEq.lean` has width exactly `d_model`, for ReLU and
ReLU²):

* at almost every parameter of a block of width at least `d ≥ 2` the hidden units are in general
  position (`UnitsGeneralPosition`, `OneBlock/UnitsGeneralPosition.lean`);
* then the statements at one parameter (`OneBlock/SkiplessHomogeneousRMSZeroEqAt.lean`) apply.

The functional dimension: the value of Lean's `funDim`, and a finite batch of the paper's inputs
(no normalized row vanishes, no hidden unit at its kink) with this rank; the two together are the
paper's statement. ReLU² blocks wider than `d_model`: `OneBlock/SkiplessReluSqWideRMSZero.lean`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

omit [Fintype d] [DecidableEq d] in
/-- Helper: an entry of a matrix that depends linearly on `y` is analytic in `y`. -/
private theorem analyticOnNhd_entry_srw {P m n : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (F : P →ₗ[ℝ] Matrix m n ℝ) (a : m) (b : n) :
    AnalyticOnNhd ℝ (fun y => F y a b) Set.univ :=
  analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ a b).comp F)

omit [Fintype d] [DecidableEq d] in
/-- Helper: the determinant of a square matrix whose entries are analytic in `y` is analytic in
`y` (a finite sum of signed finite products of entries). -/
private theorem analyticOnNhd_det_srw {P n : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [Fintype n] [DecidableEq n] (N : P → Matrix n n ℝ)
    (h : ∀ a b, AnalyticOnNhd ℝ (fun y => N y a b) Set.univ) :
    AnalyticOnNhd ℝ (fun y => (N y).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ => h (σ i) i)

omit [Fintype d] [DecidableEq d] in
/-- Helper: the entries of the adjugate of a square matrix whose entries are analytic in `y` are
analytic in `y` (each is the determinant of the matrix with one row replaced by a constant). -/
private theorem analyticOnNhd_adjugate_srw {P n : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [Fintype n] [DecidableEq n] (N : P → Matrix n n ℝ)
    (h : ∀ a b, AnalyticOnNhd ℝ (fun y => N y a b) Set.univ) (a b : n) :
    AnalyticOnNhd ℝ (fun y => (N y).adjugate a b) Set.univ := by
  simp only [Matrix.adjugate_apply]
  refine analyticOnNhd_det_srw _ fun c e => ?_
  simp only [Matrix.updateRow_apply]
  by_cases hc : c = b
  · simp only [hc, ↓reduceIte]
    exact analyticOnNhd_const
  · simp only [hc, ↓reduceIte]
    exact h c e

omit [Fintype d] [DecidableEq d] in
/-- Helper: the entries of `M_S = ∑_{i∈S} w_i a_i`. -/
private theorem sum_vecMulVec_apply_srw {q : Type*} (R : Matrix d q ℝ) (W : Matrix q d ℝ)
    (S : Finset q) (a b : d) :
    (∑ i ∈ S, vecMulVec (Rᵀ i) (W i)) a b = ∑ i ∈ S, R a i * W i b := by
  rw [Matrix.sum_apply]
  rfl

omit [Fintype d] [DecidableEq d] in
/-- Helper: the entries of `M_S` are analytic in `y` when `W_read` and `W_write` are linear in
`y` (polynomials of degree two). -/
private theorem analyticOnNhd_sum_vecMulVec_srw {P q : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] (R : P →ₗ[ℝ] Matrix d q ℝ)
    (W : P →ₗ[ℝ] Matrix q d ℝ) (S : Finset q) (a b : d) :
    AnalyticOnNhd ℝ (fun y => (∑ i ∈ S, vecMulVec ((R y)ᵀ i) (W y i)) a b) Set.univ := by
  simp only [sum_vecMulVec_apply_srw]
  exact Finset.analyticOnNhd_fun_sum _ fun i _ =>
    (analyticOnNhd_entry_srw R a i).mul (analyticOnNhd_entry_srw W i b)

omit [DecidableEq d] in
/-- Helper: `card d ≤ |S|` gives an injection `ρ` of `d` into `S`. -/
private theorem exists_embedding_srw {q : Type*} {S : Finset q}
    (hS : Fintype.card d ≤ S.card) : ∃ ρ : d ↪ q, ∀ a, ρ a ∈ S := by
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le (α := d) (β := S)
    (by rwa [Fintype.card_coe])
  exact ⟨ρ.trans (Function.Embedding.subtype _), fun a => (ρ a).2⟩

omit [Fintype d] [DecidableEq d] in
/-- Helper: the weights of one point, `a_i = w_i = e_k` for the unit `i = ρ k` of `S`, `a_i =
w_i = 0` for the other units of `S`, and `a_i = w_i = v` for the units outside `S`. -/
private def pt_srw {q : Type*} [DecidableEq q] (S : Finset q) (ρ : d ↪ q) (v : d → ℝ) :
    Matrix q d ℝ :=
  Matrix.of fun l a => if l ∈ S then (if l = ρ a then 1 else 0) else v a

omit [Fintype d] in
/-- Helper: at the point `pt_srw`, `M_S = 1`. -/
private theorem sum_pt_srw {q : Type*} [DecidableEq q] (S : Finset q) (ρ : d ↪ q)
    (hρ : ∀ a, ρ a ∈ S) (v : d → ℝ) :
    ∑ l ∈ S, vecMulVec ((pt_srw S ρ v)ᵀᵀ l) (pt_srw S ρ v l) = 1 := by
  ext a b
  rw [sum_vecMulVec_apply_srw, Finset.sum_eq_single_of_mem (ρ a) (hρ a)]
  · simp only [pt_srw, transpose_apply, of_apply, hρ, ↓reduceIte, ρ.injective.eq_iff, mul_ite,
      mul_one, mul_zero, Matrix.one_apply]
  · intro l hl hne
    simp only [pt_srw, transpose_apply, of_apply, hl, ↓reduceIte, hne, mul_ite, mul_one, mul_zero,
      ite_self]

/-! ### The four conditions, each at almost every point -/

section Generic

variable {P q : Type*} [Fintype q] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P] (μ : Measure P) [μ.IsAddHaarMeasure]
  (R : P →ₗ[ℝ] Matrix d q ℝ) (W : P →ₗ[ℝ] Matrix q d ℝ)

omit [DecidableEq d] in
/-- Helper, clause 1: for `card d ≥ 2`, at almost every `y` no two columns of `R y` are
collinear. For two rows `a ≠ b` of `d`, the minor `w_i(a) w_j(b) − w_j(a) w_i(b)` is a polynomial
in `y`, equal to `1` where `w_i = e_a`, `w_j = e_b`, and zero if `w_i = r w_j`. -/
private theorem ae_cols_srw (hRW : ∀ R₀ W₀, ∃ y, R y = R₀ ∧ W y = W₀)
    (hd : 2 ≤ Fintype.card d) :
    ∀ᵐ y ∂μ, ∀ i j : q, i ≠ j → ∀ r : ℝ, (R y)ᵀ i ≠ r • (R y)ᵀ j := by
  classical
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card d by omega)
  refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ h => absurd hij h
  -- the point `w_i = e_a`, `w_j = e_b`, where the minor is `1`
  obtain ⟨y₀, hR₀, -⟩ :=
    hRW (Matrix.of fun k l => if (k = a ∧ l = i) ∨ (k = b ∧ l = j) then 1 else 0) 0
  have hne : R y₀ a i * R y₀ b j - R y₀ a j * R y₀ b i ≠ 0 := by
    rw [hR₀]
    simp only [of_apply, and_self, hab, hij, or_false, ↓reduceIte, Ne.symm hab, Ne.symm hij,
      or_true, mul_one, and_false, and_true, or_self, mul_zero, sub_zero, ne_eq, one_ne_zero,
      not_false_eq_true]
  have han : AnalyticOnNhd ℝ (fun y => R y a i * R y b j - R y a j * R y b i) Set.univ :=
    ((analyticOnNhd_entry_srw R a i).mul (analyticOnNhd_entry_srw R b j)).sub
      ((analyticOnNhd_entry_srw R a j).mul (analyticOnNhd_entry_srw R b i))
  -- a polynomial that is not identically zero is nonzero at almost every `y`
  filter_upwards [ae_ne_zero_of_analytic μ han ⟨y₀, hne⟩] with y hy _ r hr
  -- if `w_i = r w_j` the minor vanishes
  have h1 : R y a i = r * R y a j := by
    simpa only [transpose_apply, Pi.smul_apply, smul_eq_mul] using congrFun hr a
  have h2 : R y b i = r * R y b j := by
    simpa only [transpose_apply, Pi.smul_apply, smul_eq_mul] using congrFun hr b
  exact hy (by rw [h1, h2]; ring)

omit [DecidableEq d] in
/-- Helper, clause 2: for `card d ≤ card q`, at almost every `y` any at most `card d` rows of
`W y` are linearly independent. A set `S` of at most `card d` units lies in a set `S'` of exactly
`card d` units, and the rows `S'` form a matrix whose determinant is a polynomial in `y`, equal to
`1` where these rows are the unit vectors. -/
private theorem ae_rows_srw (hRW : ∀ R₀ W₀, ∃ y, R y = R₀ ∧ W y = W₀)
    (hq : Fintype.card d ≤ Fintype.card q) :
    ∀ᵐ y ∂μ, ∀ S : Finset q, S.card ≤ Fintype.card d →
      LinearIndependent ℝ fun i : S => W y i := by
  classical
  refine ae_all_iff.2 fun S => ?_
  by_cases hS : S.card ≤ Fintype.card d
  swap
  · exact Filter.Eventually.of_forall fun _ h => absurd h hS
  -- a set `S' ⊇ S` of `card d` units, and a bijection `e : d ≃ S'`
  obtain ⟨S', hSS', hS'⟩ := Finset.exists_superset_card_eq hS hq
  let e : d ≃ S' := Fintype.equivOfCardEq (by rw [Fintype.card_coe, hS'])
  let ρ : d ↪ q := e.toEmbedding.trans (Function.Embedding.subtype _)
  -- the point where the rows `ρ` of the write are the unit vectors
  obtain ⟨y₀, -, hW₀⟩ := hRW 0 (Matrix.of fun l b => if l = ρ b then 1 else 0)
  have hne : ((W y₀).submatrix ρ id).det ≠ 0 := by
    have h1 : (W y₀).submatrix ρ id = 1 := by
      ext a b
      simp only [hW₀, submatrix_apply, id_eq, of_apply, ρ.injective.eq_iff, Matrix.one_apply]
    rw [h1, det_one]
    exact one_ne_zero
  have han := analyticOnNhd_det_srw (fun y => (W y).submatrix ρ id) fun a b =>
    analyticOnNhd_entry_srw W (ρ a) b
  filter_upwards [ae_ne_zero_of_analytic μ han ⟨y₀, hne⟩] with y hy _
  -- the rows `ρ` are independent, and the rows `S` are among them
  have hli := Matrix.linearIndependent_rows_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hy))
  let g : S → d := fun s => e.symm ⟨s, hSS' s.2⟩
  have hg : Function.Injective g := fun s t h =>
    Subtype.ext (by simpa only [SetLike.coe_eq_coe] using congrArg Subtype.val (e.symm.injective h))
  convert hli.comp g hg using 1
  funext s
  show W y s = fun b => W y (e (e.symm ⟨s, hSS' s.2⟩)).1 b
  rw [Equiv.apply_symm_apply]

/-- Helper, clause 3: at almost every `y`, `M_S` is invertible for every set `S` of at least
`card d` units: its determinant is a polynomial in `y`, equal to `1` at `pt_srw`. -/
private theorem ae_det_srw (hRW : ∀ R₀ W₀, ∃ y, R y = R₀ ∧ W y = W₀) :
    ∀ᵐ y ∂μ, ∀ S : Finset q, Fintype.card d ≤ S.card →
      IsUnit (∑ i ∈ S, vecMulVec ((R y)ᵀ i) (W y i)).det := by
  classical
  refine ae_all_iff.2 fun S => ?_
  by_cases hS : Fintype.card d ≤ S.card
  swap
  · exact Filter.Eventually.of_forall fun _ h => absurd h hS
  obtain ⟨ρ, hρ⟩ := exists_embedding_srw hS
  obtain ⟨y₀, hR₀, hW₀⟩ := hRW (pt_srw S ρ 0)ᵀ (pt_srw S ρ 0)
  have hne : (∑ i ∈ S, vecMulVec ((R y₀)ᵀ i) (W y₀ i)).det ≠ 0 := by
    rw [hR₀, hW₀, sum_pt_srw S ρ hρ, det_one]
    exact one_ne_zero
  have han := analyticOnNhd_det_srw _ (analyticOnNhd_sum_vecMulVec_srw R W S)
  filter_upwards [ae_ne_zero_of_analytic μ han ⟨y₀, hne⟩] with y hy _
  exact isUnit_iff_ne_zero.2 hy

/-- Helper, clause 4 with the adjugate in place of the inverse: at almost every `y`,
`(a_i adj(M_S)) · w_i ≠ 0` for every set `S` of at least `card d` units and every unit `i` outside
`S`. It is a polynomial in `y`, equal to `1` at `pt_srw` with `a_i = w_i = e_k`. -/
private theorem ae_adjugate_srw (hRW : ∀ R₀ W₀, ∃ y, R y = R₀ ∧ W y = W₀) (k : d) :
    ∀ᵐ y ∂μ, ∀ (i : q) (S : Finset q), i ∉ S → Fintype.card d ≤ S.card →
      (W y i ᵥ* (∑ j ∈ S, vecMulVec ((R y)ᵀ j) (W y j)).adjugate) ⬝ᵥ (R y)ᵀ i ≠ 0 := by
  classical
  refine ae_all_iff.2 fun i => ae_all_iff.2 fun S => ?_
  by_cases hS : i ∉ S ∧ Fintype.card d ≤ S.card
  swap
  · exact Filter.Eventually.of_forall fun _ h h' => absurd ⟨h, h'⟩ hS
  obtain ⟨ρ, hρ⟩ := exists_embedding_srw hS.2
  let v : d → ℝ := fun a => if a = k then 1 else 0
  obtain ⟨y₀, hR₀, hW₀⟩ := hRW (pt_srw S ρ v)ᵀ (pt_srw S ρ v)
  have hne : (W y₀ i ᵥ* (∑ j ∈ S, vecMulVec ((R y₀)ᵀ j) (W y₀ j)).adjugate) ⬝ᵥ (R y₀)ᵀ i ≠ 0 := by
    rw [hR₀, hW₀, sum_pt_srw S ρ hρ, adjugate_one, vecMul_one, transpose_transpose]
    simp only [dotProduct, pt_srw, of_apply, hS.1, ↓reduceIte, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ne_eq, one_ne_zero, not_false_eq_true, v]
  have han : AnalyticOnNhd ℝ (fun y =>
      (W y i ᵥ* (∑ j ∈ S, vecMulVec ((R y)ᵀ j) (W y j)).adjugate) ⬝ᵥ (R y)ᵀ i) Set.univ := by
    have hadj := analyticOnNhd_adjugate_srw _ (analyticOnNhd_sum_vecMulVec_srw R W S)
    simp only [dotProduct, vecMul, transpose_apply]
    exact Finset.analyticOnNhd_fun_sum _ fun b _ =>
      (Finset.analyticOnNhd_fun_sum _ fun a _ =>
        (analyticOnNhd_entry_srw W i a).mul (hadj a b)).mul (analyticOnNhd_entry_srw R b i)
  filter_upwards [ae_ne_zero_of_analytic μ han ⟨y₀, hne⟩] with y hy _ _
  exact hy

/-- Helper: the four conditions at almost every `y`, for `W_read`, `W_write` linear in `y` and
taking every value. -/
private theorem ae_unitsGeneralPosition_srw (hRW : ∀ R₀ W₀, ∃ y, R y = R₀ ∧ W y = W₀)
    (hd : 2 ≤ Fintype.card d) (hq : Fintype.card d ≤ Fintype.card q) :
    ∀ᵐ y ∂μ, UnitsGeneralPosition (R y) (W y) := by
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  filter_upwards [ae_cols_srw μ R W hRW hd, ae_rows_srw μ R W hRW hq, ae_det_srw μ R W hRW,
    ae_adjugate_srw μ R W hRW (Classical.arbitrary d)] with y h1 h2 h3 h4
  refine ⟨h1, h2, h3, fun i S hi hS => ?_⟩
  -- `M_S⁻¹ = det(M_S)⁻¹ adj(M_S)`
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.vecMul_smul, smul_dotProduct, smul_eq_mul]
  exact mul_ne_zero (inv_ne_zero (h3 S hS).ne_zero) (h4 i S hi hS)

end Generic

omit [Fintype T] [Nonempty T] in
/-- **The conditions "for generic parameters" of the proof of Theorem B.1 (iv), "The skipless
network: equality":** for one MLP block with at least `d ≥ 2` hidden units, at almost every
parameter the hidden units are in general position. -/
theorem ae_unitsGeneralPosition {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, UnitsGeneralPosition (θ.read 0) (θ.write 0) := by
  -- the read and the write of the block take every value, at the parameter with `E = D = 0`
  have hRW : ∀ (R₀ : Matrix d (hid 0) ℝ) (W₀ : Matrix (hid 0) d ℝ),
      ∃ θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut,
        Params.linRead 0 θ = R₀ ∧ Params.linWrite 0 θ = W₀ := fun R₀ W₀ =>
    ⟨⟨0, Pi.single (M := fun ℓ => Matrix d (hid ℓ) ℝ) 0 R₀,
      Pi.single (M := fun ℓ => Matrix (hid ℓ) d ℝ) 0 W₀, 0⟩,
      Pi.single_eq_same (M := fun ℓ => Matrix d (hid ℓ) ℝ) 0 R₀,
      Pi.single_eq_same (M := fun ℓ => Matrix (hid ℓ) d ℝ) 0 W₀⟩
  exact ae_unitsGeneralPosition_srw (q := hid 0) μ _ _ hRW hd hcard

omit [Nonempty T] in
/-- Helper: at almost every parameter `E` and `D` have rank `d` (`d_in, d_out ≥ d`, width at
least `d`). -/
private theorem ae_rank_E_D_srw {σ : ℝ → ℝ}
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d ∧ θ.D.rank = Fintype.card d := by
  obtain ⟨ρD⟩ := Function.Embedding.nonempty_of_card_le hdOut
  filter_upwards [ae_rank_E_write μ hdIn
      (fun ℓ => by obtain rfl := Subsingleton.elim ℓ 0; exact hcard),
    ae_isUnit_det_submatrix μ] with θ h1 h2
  exact ⟨h1.1, rank_eq_card_of_isUnit_det θ.D ρD (h2.2.1 ρD)⟩

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, "with equality", for one ReLU
block of width at least `d`:** for `ε = 0`, `d_in, d_out ≥ d ≥ 2` and a block of at least `d`
hidden units, at almost every parameter `funDim = P − d² − d(d−1)/2 − 1 − s`. -/
theorem ae_funDim_relu_oneBlock_skipless_rmsNorm_zero_of_le
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_D_srw μ hdIn hdOut hcard,
    ae_unitsGeneralPosition μ hd hcard] with θ hθ hG
  obtain ⟨hR, hW, hc⟩ := rank_of_unitsGeneralPosition hd hcard hG
  exact funDim_mlp_oneBlock_rescale_skipless_rmsNorm_zero_of_unitsParallelAt
    (fun _ hz => hasDerivAt_relu hz) relu_homogeneous θ hd hθ.1 hθ.2 hR hW hc
    (relu_unitsParallelAt_of_unitsGeneralPosition θ.E hd hcard hθ.1 hG)
    (exists_open_relu_of_unitsGeneralPosition θ.E hd hcard hθ.1 hG)

/-- **The same in the paper's own sense:** at almost every parameter a finite batch of inputs at
which no normalized row vanishes and no hidden unit sits at its kink, on which the Jacobian has
the rank `P − d² − d(d−1)/2 − 1 − s`. -/
theorem ae_exists_jacobianRank_relu_oneBlock_skipless_rmsNorm_zero_of_le
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ skiplessZeroDomain (Arch.mlp relu (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp relu (rmsNorm 0) hid) 0 X θ
          + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
            + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_D_srw μ hdIn hdOut hcard,
    ae_unitsGeneralPosition μ hd hcard] with θ hθ hG
  obtain ⟨hR, hW, hc⟩ := rank_of_unitsGeneralPosition hd hcard hG
  exact exists_jacobianRank_mlp_oneBlock_rescale_skipless_rmsNorm_zero_of_unitsParallelAt
    (fun _ hz => hasDerivAt_relu hz) relu_homogeneous θ hd hθ.1 hθ.2 hR hW hc
    (relu_unitsParallelAt_of_unitsGeneralPosition θ.E hd hcard hθ.1 hG)
    (exists_open_relu_of_unitsGeneralPosition θ.E hd hcard hθ.1 hG)

/-- **Theorem B.1 (iv) of the skips paper, "by exactly `d_model²` for ReLU and ReLU² blocks", for
one ReLU block of width at least `d`:** at almost every parameter `funDim` of the residual
network is `funDim` of the skipless network plus `d²`. -/
theorem ae_funDim_relu_oneBlock_residual_rmsNorm_zero_eq_add_of_le
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card d ≤ Fintype.card (hid 0)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 1 θ
      = funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ + Fintype.card d ^ 2 := by
  have : Nonempty (hid 0) := Fintype.card_pos_iff.1 (by omega)
  filter_upwards [ae_funDim_relu_oneBlock_residual_rmsNorm_zero μ hd hdIn hdOut,
    ae_funDim_relu_oneBlock_skipless_rmsNorm_zero_of_le μ hd hdIn hdOut hcard] with θ h1 h0
  omega

end Skips
