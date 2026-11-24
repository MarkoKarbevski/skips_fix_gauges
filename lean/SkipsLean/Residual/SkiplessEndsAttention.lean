import SkipsLean.Residual.SkiplessEnds
import SkipsLean.Dimension.UpperBoundAttention
import SkipsLean.Network.AttentionAnalytic

/-!
# Skipless networks of attention blocks: the changes of basis at the two ends and inside the heads

Paper (skips paper): proof of Theorem A.28 (i) and (ii). "In a skipless network of the same
widths, with embedding `E′` and readout `D′`, the changes of basis at `h_0` and `h_L`, those inside
the heads and the rescalings have orbits of dimension `2 d_model² + s` at generic parameters, where
`E′` and `D′` have rank `d_model` and the queries and values of every head have full column rank."
And: "Under pre-RMSNorm with `ε > 0` […] the orthogonal changes of basis at `h_0` and `h_L`, which
commute with the normalization, have orbits of dimension `d_model (d_model − 1) + s` in the
skipless network". The proof of Lemma A.26 then uses the bound at every parameter ("the rank is
lower semicontinuous, so the bound holds at every `η`").

Here, for `Arch.attention sees χ H dh` (any mask), `L ≥ 1` blocks whose heads have any numbers and
widths, with `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²` (the changes of basis between queries and keys and between
values and outputs, `Symmetry/AttentionHeads.lean`). The total width `H d_h` of a block may be
smaller than `d`: the changes of basis at the hidden states in between are not used.

* `funDim_add_le_skipless_ends_attention`, `…_rmsNorm`: the bound on the functional dimension at a
  parameter whose `E` and `D` have rank `d` and whose query and value matrices have rank `d_h`.
* `jacobianRank_add_le_skipless_ends_attention`, `…_rmsNorm`: the same bound for the rank of the
  Jacobian on every batch at EVERY parameter, for heads of width `d_h ≤ d` and `d_in, d_out ≥ d`.

The twin statements for MLP and gated blocks are in `Residual/SkiplessEnds.lean`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, DecidableEq (dh ℓ)]

/-! ### Helpers: cancellation, the families supported on `h_0` and `h_L`, the head directions -/

/-- Helper (the private `mul_left_cancel_of_rank_se` of `Residual/SkiplessEnds.lean`): a matrix `M`
of rank equal to its number of columns cancels on the left, `M X = M Y → X = Y`. -/
private theorem mul_left_cancel_of_rank_sea {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
    (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ} (h : M * X = M * Y) : X = Y := by
  -- `v ↦ M v` is injective: `rank M + dim ker M = card n`
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [Matrix.rank] at hM
    omega
  -- compare `X` and `Y` column by column
  ext i j
  have hcol : M.mulVecLin (fun l => X l j) = M.mulVecLin (fun l => Y l j) := by
    funext p
    have := congrFun (congrFun h p) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  exact congrFun (hinj hcol) i

/-- Helper: a matrix `M` of rank equal to its number of rows cancels on the right,
`X M = Y M → X = Y` (transpose, and `rank Mᵀ = rank M`). -/
private theorem mul_right_cancel_of_rank_sea {m n k : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) (hM : M.rank = Fintype.card m) {X Y : Matrix k m ℝ} (h : X * M = Y * M) :
    X = Y := by
  have hT : Mᵀ * Xᵀ = Mᵀ * Yᵀ := by
    rw [← Matrix.transpose_mul, h, Matrix.transpose_mul]
  exact Matrix.transpose_injective
    (mul_left_cancel_of_rank_sea Mᵀ (by rw [Matrix.rank_transpose]; exact hM) hT)

omit [Fintype d] [DecidableEq d] in
/-- Helper: the family `X` with `X_0 = p.1`, `X_L = p.2` and `X_ℓ = 0` at the hidden states in
between, as a linear map of `p = (X_0, X_L)`. -/
private noncomputable def endsLin_sea (n : ℕ) :
    (Matrix d d ℝ × Matrix d d ℝ) →ₗ[ℝ] (Fin (n + 1) → Matrix d d ℝ) :=
  (LinearMap.single ℝ (fun _ : Fin (n + 1) => Matrix d d ℝ) 0).coprod
    (LinearMap.single ℝ (fun _ : Fin (n + 1) => Matrix d d ℝ) (Fin.last n))

/-- Helper: `0 ≠ L` as hidden states, for `L ≥ 1`. -/
private theorem zero_ne_last_sea {n : ℕ} (hn : 0 < n) : (0 : Fin (n + 1)) ≠ Fin.last n := by
  rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_last]
  omega

omit [Fintype d] [DecidableEq d] in
/-- Helper: the family `endsLin_sea n p` at `h_0` is `p.1`. -/
private theorem endsLin_zero_sea {n : ℕ} (hn : 0 < n) (p : Matrix d d ℝ × Matrix d d ℝ) :
    endsLin_sea n p 0 = p.1 := by
  simp [endsLin_sea, zero_ne_last_sea hn]

omit [Fintype d] [DecidableEq d] in
/-- Helper: the family `endsLin_sea n p` at `h_L` is `p.2`. -/
private theorem endsLin_last_sea {n : ℕ} (hn : 0 < n) (p : Matrix d d ℝ × Matrix d d ℝ) :
    endsLin_sea n p (Fin.last n) = p.2 := by
  simp [endsLin_sea, (zero_ne_last_sea hn).symm]

omit [DecidableEq d] in
/-- Helper: for antisymmetric `X_0`, `X_L`, every matrix of the family `endsLin_sea n (X_0, X_L)`
is antisymmetric. -/
private theorem endsLin_mem_antisymmetric_sea (n : ℕ) {a b : Matrix d d ℝ}
    (ha : a ∈ antisymmetric d) (hb : b ∈ antisymmetric d) (ℓ : Fin (n + 1)) :
    endsLin_sea n (a, b) ℓ ∈ antisymmetric d := by
  simp only [endsLin_sea, LinearMap.coprod_apply, LinearMap.coe_single, Pi.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · rw [Pi.single_apply]
    split_ifs
    · exact ha
    · exact Submodule.zero_mem _
  · rw [Pi.single_apply]
    split_ifs
    · exact hb
    · exact Submodule.zero_mem _

omit [Fintype T] [DecidableEq d] [Fintype dIn] in
/-- Helper: the embedding component `E X_0` determines `X_0` and the readout component `-X_L D`
determines `X_L`, when `E` and `D` have rank `d` (`L ≥ 1`, so `h_0 ≠ h_L`). -/
private theorem ends_eq_sea {n : ℕ} (hn : 0 < n) {E : Matrix dIn d ℝ} {D : Matrix d dOut ℝ}
    (hE : E.rank = Fintype.card d) (hD : D.rank = Fintype.card d)
    {p q : Matrix d d ℝ × Matrix d d ℝ}
    (h0 : E * endsLin_sea n p 0 = E * endsLin_sea n q 0)
    (h1 : -(endsLin_sea n p (Fin.last n) * D) = -(endsLin_sea n q (Fin.last n) * D)) :
    p = q := by
  rw [endsLin_zero_sea hn, endsLin_zero_sea hn] at h0
  rw [endsLin_last_sea hn, endsLin_last_sea hn, neg_inj] at h1
  exact Prod.ext (mul_left_cancel_of_rank_sea E hE h0) (mul_right_cancel_of_rank_sea D hD h1)

omit [DecidableEq d] in
/-- Helper: the pairs `(X_0, X_L)` form a space of dimension `2 d²`. -/
private theorem finrank_ends_sea :
    Module.finrank ℝ (Matrix d d ℝ × Matrix d d ℝ) = 2 * Fintype.card d ^ 2 := by
  rw [Module.finrank_prod, Module.finrank_matrix, Module.finrank_self]
  ring

/-- Helper: the pairs `(X_0, X_L)` of antisymmetric matrices form a space of dimension
`2 · d (d - 1) / 2 = d (d - 1)` (`d (d - 1)` is even). -/
private theorem finrank_ends_antisymmetric_sea :
    Module.finrank ℝ (antisymmetric d × antisymmetric d)
      = Fintype.card d * (Fintype.card d - 1) := by
  rw [Module.finrank_prod, finrank_antisymmetric]
  have h := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (Fintype.card d))
  generalize Fintype.card d * (Fintype.card d - 1) = k at h ⊢
  omega

/-- Helper (the private `headDirQKLin_uba` of `Dimension/UpperBoundAttention.lean`):
`Γ ↦ headDirQK θ Γ` is linear. -/
private noncomputable def headDirQKLin_sea {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  toFun := headDirQK θ
  map_add' Γ Δ := by
    apply Params.ext'
    · simp [headDirQK]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp only [headDirQK, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib]
      · simp only [headDirQK, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib, neg_add]
      · simp [headDirQK]
    · intro ℓ
      simp [headDirQK]
    · simp [headDirQK]
  map_smul' c Γ := by
    apply Params.ext'
    · simp [headDirQK]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp only [headDirQK, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      · simp only [headDirQK, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_neg]
        exact congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => by ring)
      · simp [headDirQK]
    · intro ℓ
      simp [headDirQK]
    · simp [headDirQK]

/-- Helper (the private `headDirVOLin_uba` of `Dimension/UpperBoundAttention.lean`):
`Γ' ↦ headDirVO θ Γ'` is linear. -/
private noncomputable def headDirVOLin_sea {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  toFun := headDirVO θ
  map_add' Γ Δ := by
    apply Params.ext'
    · simp [headDirVO]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp [headDirVO]
      · simp [headDirVO]
      · simp only [headDirVO, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib]
    · intro ℓ
      ext p b
      simp only [headDirVO, Params.add_write, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
        add_mul, Finset.sum_add_distrib, neg_add]
    · simp [headDirVO]
  map_smul' c Γ := by
    apply Params.ext'
    · simp [headDirVO]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp [headDirVO]
      · simp [headDirVO]
      · simp only [headDirVO, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    · intro ℓ
      ext p b
      simp only [headDirVO, Params.smul_write, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
        smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_neg]
      exact congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => by ring)
    · simp [headDirVO]

omit [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper: the families `Γ` of `d_h × d_h` matrices, one for each head of each block, form a
space of dimension `∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_sea :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper (the private `headDirLin_injective_uba` of `Dimension/UpperBoundAttention.lean`): if
the query and the value matrix of every head have rank `d_h`, the direction
`headDirQK θ Γ + headDirVO θ Γ'` determines `Γ` and `Γ'`: the query columns of head `i` move by
`W_{Q,i} Γ_i`, its value columns by `W_{V,i} Γ'_i`. -/
private theorem headDirLin_injective_sea {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    Function.Injective ((headDirQKLin_sea θ).coprod (headDirVOLin_sea θ)) := by
  rintro ⟨Γ, Γ'⟩ ⟨Δ, Δ'⟩ h
  have h' : headDirQK θ Γ + headDirVO θ Γ' = headDirQK θ Δ + headDirVO θ Δ' := h
  -- the entry `(a, p)` of the read of block `ℓ`
  have hr : ∀ ℓ a p, (headDirQK θ Γ + headDirVO θ Γ').read ℓ a p
      = (headDirQK θ Δ + headDirVO θ Δ').read ℓ a p := fun ℓ a p => by rw [h']
  refine Prod.ext ?_ ?_ <;> funext ℓ i
  · -- the query columns of head `i`: `W_{Q,i} Γ_i = W_{Q,i} Δ_i`, and `W_{Q,i}` has rank `d_h`
    refine mul_left_cancel_of_rank_sea _ (hQ ℓ i) (Matrix.ext fun a k => ?_)
    have := hr ℓ a (i, Sum.inl k)
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      add_zero] at this
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this
  · -- the value columns of head `i`: `W_{V,i} Γ'_i = W_{V,i} Δ'_i`
    refine mul_left_cancel_of_rank_sea _ (hV ℓ i) (Matrix.ext fun a k => ?_)
    have := hr ℓ a (i, Sum.inr (Sum.inr k))
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      zero_add] at this
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this

omit [DecidableEq d] [Fintype dIn] [∀ ℓ, DecidableEq (dh ℓ)] in
/-- Helper (Lemma B.1 with `X` supported on `h_0` and `h_L`): the direction
`cobDir θ X + headDirQK θ Γ + headDirVO θ Γ'` determines `(X_0, X_L)` and `(Γ, Γ')`, when `E` and
`D` have rank `d` and the query and value matrices of every head have rank `d_h`: the head
directions have `E` and `D` components `0`. -/
private theorem ends_heads_inj_sea {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) (hL : 0 < L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    {p q : Matrix d d ℝ × Matrix d d ℝ}
    {Γ Δ : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)}
    (h : cobDir θ (endsLin_sea L p) + (headDirQK θ Γ.1 + headDirVO θ Γ.2)
      = cobDir θ (endsLin_sea L q) + (headDirQK θ Δ.1 + headDirVO θ Δ.2)) :
    p = q ∧ Γ = Δ := by
  -- the embedding and readout components: the head directions leave `E` and `D` alone
  have hpq : p = q := by
    refine ends_eq_sea hL hE hD ?_ ?_
    · have h0 := congrArg Params.E h
      change θ.E * endsLin_sea L p 0 + (0 + 0) = θ.E * endsLin_sea L q 0 + (0 + 0) at h0
      simpa only [add_zero] using h0
    · have h1 := congrArg Params.D h
      change -(endsLin_sea L p (Fin.last L) * θ.D) + (0 + 0)
        = -(endsLin_sea L q (Fin.last L) * θ.D) + (0 + 0) at h1
      simpa only [add_zero] using h1
  subst hpq
  -- then the head part is determined by the query and value columns
  exact ⟨rfl, headDirLin_injective_sea θ hQ hV (add_left_cancel h)⟩

/-! ### Helpers: generic ranks, and the bound at every parameter -/

omit [Fintype T] in
/-- Helper (the private `rank_eq_of_isUnit_det_rows_se` of `Residual/SkiplessEnds.lean`): a matrix
with `d` columns has rank `d` if some `d` of its rows form an invertible matrix. -/
private theorem rank_eq_of_isUnit_det_rows_sea {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- Helper: at generic parameters `E` and `D` have rank `d`, when `d_in ≥ d` and `d_out ≥ d`. -/
private theorem ae_rank_E_D_sea {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d ∧ θ.D.rank = Fintype.card d := by
  -- `d` rows of `E` and `d` columns of `D`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hdOut
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  exact ⟨rank_eq_of_isUnit_det_rows_sea θ.E ρ (hθ.2.2.1 ρ),
    rank_eq_card_of_isUnit_det θ.D c (hθ.2.1 c)⟩

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `analyticOnNhd_det_uba` of `Dimension/UpperBoundAttention.lean`): the
determinant of a square matrix that depends linearly on the parameters is an analytic function of
the parameters. -/
private theorem analyticOnNhd_det_sea {A : Arch T d L} {n : Type*} [Fintype n] [DecidableEq n]
    (Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ) :
    AnalyticOnNhd ℝ (fun θ => (Φ θ).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ =>
      analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ (σ i) i).comp Φ))

/-- Helper: a matrix whose submatrix on the rows `r` and the columns `c` (both injective) is the
identity. -/
private theorem exists_submatrix_eq_one_sea {m p n : Type*} [DecidableEq n] {r : n → m}
    (hr : Function.Injective r) {c : n → p} (hc : Function.Injective c) :
    ∃ M : Matrix m p ℝ, M.submatrix r c = 1 := by
  classical
  refine ⟨Matrix.of fun a b => if ∃ x, r x = a ∧ c x = b then 1 else 0, ?_⟩
  ext x y
  simp [Matrix.one_apply, hr.eq_iff, hc.eq_iff]

omit [Fintype T] [DecidableEq d] in
/-- Helper: at generic parameters, `n ≤ d` distinct columns `c` of the read of block `ℓ` form a
matrix of rank `n`: some `n` of its rows form a matrix that is invertible at generic parameters. -/
private theorem ae_rank_read_cols_sea {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*} [Fintype n] [DecidableEq n] {c : n → A.r ℓ}
    (hc : Function.Injective c) (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.read ℓ).submatrix id c).rank = Fintype.card n := by
  -- `n` rows `ρ`, and the square submatrix of the read on the rows `ρ` and the columns `c`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_sea ρ.injective hc
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
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_sea Φ) hne] with θ hθ
  -- an invertible `n × n` submatrix gives rank `≥ n`, and the rank is at most the width `n`
  have h1 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank = Fintype.card n :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hθ))
  have h2 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank
      ≤ ((θ.read ℓ).submatrix id c).rank :=
    Matrix.rank_submatrix_le _ ρ id
  have h3 := Matrix.rank_le_card_width ((θ.read ℓ).submatrix id c)
  omega

omit [DecidableEq d] in
/-- Helper: at generic parameters the query matrix and the value matrix of every head have rank
`d_h`, when `d_h ≤ d`. -/
private theorem ae_rank_QV_sea {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, (∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ)) ∧
      ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ) := by
  -- finitely many conditions, two for each head of each block
  refine (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_).and
    (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_)
  · exact ae_rank_read_cols_sea μ ℓ (c := fun k : dh ℓ => (i, Sum.inl k))
      (fun _ _ h => Sum.inl_injective (Prod.mk.inj h).2) (hdh ℓ)
  · exact ae_rank_read_cols_sea μ ℓ (c := fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
      (fun _ _ h => Sum.inr_injective (Sum.inr_injective (Prod.mk.inj h).2)) (hdh ℓ)

omit [DecidableEq d] in
/-- Helper (the private `jacobianRank_add_le_of_ae_se` of `Residual/SkiplessEnds.lean`; the proof
of Lemma A.26: "the rank is lower semicontinuous, so the bound holds at every `η`"): for
real-analytic `f_ℓ` and `χ`, a bound `fd(θ') + k ≤ P` at almost every `θ'` gives the bound
`rank J_X(θ) + k ≤ P` on every batch `X` at every `θ`. -/
private theorem jacobianRank_add_le_of_ae_sea {A : Arch T d L}
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ) {k : ℕ}
    (θ : Params A dIn dOut) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (h : ∀ᵐ θ' ∂(Measure.addHaar : Measure (Params A dIn dOut)),
      funDim A 0 θ' + k ≤ Module.finrank ℝ (Params A dIn dOut)) :
    jacobianRank A 0 X θ + k ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- a parameter `θ'` with `rank J_X(θ) ≤ fd(θ')` and `fd(θ') + k ≤ P`
  obtain ⟨θ', h1, h2⟩ :=
    ((ae_jacobianRank_le_funDim A 0 hf hχ Measure.addHaar X θ).and h).exists
  omega

/-- **Proof of Theorem A.28 (ii) of the skips paper, "the changes of basis at `h_0` and `h_L`,
those inside the heads", for attention blocks without normalization:** for a skipless network of
`L ≥ 1` attention blocks whose `E` and `D` have rank `d` and whose query and value matrices have
rank `d_h`, the functional dimension is at most `P − 2 d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_skipless_ends_attention
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) (hL : 0 < L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attention sees id H dh) 0 θ
        + (2 * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  -- the linear map `((X_0, X_L), (Γ, Γ')) ↦ cobDir θ (ends X_0 X_L) + headDirQK θ Γ
  -- + headDirVO θ Γ'`
  let Φ : ((Matrix d d ℝ × Matrix d d ℝ) × ((∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut :=
    ((cobDirLin θ).comp (endsLin_sea L)).coprod
      ((headDirQKLin_sea θ).coprod (headDirVOLin_sea θ))
  -- its directions are flat, since the three summands are
  have hflat : LinearMap.range Φ ≤ flat (Arch.attention sees id H dh) 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply]
    exact Submodule.add_mem _ (cobDir_mem_flat_skipless' θ rfl (endsLin_sea L p.1))
      (Submodule.add_mem _ (headDirQK_mem_flat θ 0 p.2.1) (headDirVO_mem_flat θ 0 p.2.2))
  -- it is injective: `E X_0` gives `X_0`, `-X_L D` gives `X_L`, then the heads give `(Γ, Γ')`
  have hinj : Function.Injective Φ := by
    intro a b h
    have h' : cobDir θ (endsLin_sea L a.1) + (headDirQK θ a.2.1 + headDirVO θ a.2.2)
        = cobDir θ (endsLin_sea L b.1) + (headDirQK θ b.2.1 + headDirVO θ b.2.2) := h
    obtain ⟨h1, h2⟩ := ends_heads_inj_sea θ hL hE hD hQ hV h'
    exact Prod.ext h1 h2
  -- the domain has dimension `2 d² + 2 ∑_ℓ H_ℓ d_{h,ℓ}²`
  have h := funDim_add_finrank_le_of_le_flat' θ _ hflat
  rwa [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, finrank_ends_sea,
    Module.finrank_prod, finrank_headFun_sea, ← two_mul] at h

/-- **The same bound at every parameter, on every batch, for attention blocks without
normalization:** for `d_in, d_out ≥ d`, `L ≥ 1` and heads of width `d_h ≤ d`, the Jacobian of the
outputs of a skipless network of attention blocks on a batch has rank at most
`P − 2 d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²` at every parameter. -/
theorem jacobianRank_add_le_skipless_ends_attention (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank (Arch.attention sees id H dh) 0 X θ
        + (2 * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) dIn dOut) := by
  -- at almost every `θ'`, `E` and `D` have rank `d` and the query and value matrices of every
  -- head have rank `d_h`, so `fd(θ') + 2 d² + 2 ∑_ℓ H_ℓ d_{h,ℓ}² ≤ P`
  refine jacobianRank_add_le_of_ae_sea (fun ℓ => analyticOnNhd_f_attention sees id H dh ℓ)
    analyticOnNhd_id θ X ?_
  filter_upwards [ae_rank_E_D_sea Measure.addHaar hdIn hdOut,
    ae_rank_QV_sea Measure.addHaar hdh] with θ' h1 h2
  exact funDim_add_le_skipless_ends_attention θ' hL h1.1 h1.2 h2.1 h2.2

/-- **For attention blocks under pre-RMSNorm with `ε > 0`, "the orthogonal changes of basis at
`h_0` and `h_L`" and the changes of basis inside the heads:** for a skipless network of `L ≥ 1`
attention blocks whose `E` and `D` have rank `d` and whose query and value matrices have rank
`d_h`, the functional dimension is at most `P − d (d − 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_skipless_ends_attention_rmsNorm {ε : ℝ} (hε : 0 < ε)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) (hL : 0 < L)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attention sees (rmsNorm ε) H dh) 0 θ
        + (Fintype.card d * (Fintype.card d - 1)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  -- the same linear map, with `X_0`, `X_L` antisymmetric
  let Φ : ((antisymmetric d × antisymmetric d) × ((∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut :=
    (((cobDirLin θ).comp (endsLin_sea L)).comp
        ((antisymmetric d).subtype.prodMap (antisymmetric d).subtype)).coprod
      ((headDirQKLin_sea θ).coprod (headDirVOLin_sea θ))
  -- its directions are flat, since the three summands are (orthogonal changes of basis)
  have hflat : LinearMap.range Φ ≤ flat (Arch.attention sees (rmsNorm ε) H dh) 0 θ := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply]
    exact Submodule.add_mem _
      (cobDir_mem_flat_skipless_rmsNorm' θ ε rfl
        (endsLin_sea L ((p.1.1 : Matrix d d ℝ), (p.1.2 : Matrix d d ℝ)))
        fun ℓ => endsLin_mem_antisymmetric_sea L p.1.1.2 p.1.2.2 ℓ)
      (Submodule.add_mem _ (headDirQK_mem_flat θ 0 p.2.1) (headDirVO_mem_flat θ 0 p.2.2))
  -- it is injective: `E X_0` gives `X_0`, `-X_L D` gives `X_L`, then the heads give `(Γ, Γ')`
  have hinj : Function.Injective Φ := by
    intro a b h
    have h' : cobDir θ (endsLin_sea L ((a.1.1 : Matrix d d ℝ), (a.1.2 : Matrix d d ℝ)))
          + (headDirQK θ a.2.1 + headDirVO θ a.2.2)
        = cobDir θ (endsLin_sea L ((b.1.1 : Matrix d d ℝ), (b.1.2 : Matrix d d ℝ)))
          + (headDirQK θ b.2.1 + headDirVO θ b.2.2) := h
    obtain ⟨h1, h2⟩ := ends_heads_inj_sea θ hL hE hD hQ hV h'
    exact Prod.ext (Prod.ext (Subtype.ext (congrArg Prod.fst h1))
      (Subtype.ext (congrArg Prod.snd h1))) h2
  -- the domain has dimension `d (d - 1) + 2 ∑_ℓ H_ℓ d_{h,ℓ}²`
  have h := funDim_add_finrank_le_of_le_flat' θ _ hflat
  rwa [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, finrank_ends_antisymmetric_sea,
    Module.finrank_prod, finrank_headFun_sea, ← two_mul] at h

/-- **The same bound at every parameter, on every batch, for attention blocks under pre-RMSNorm
with `ε > 0`:** the Jacobian of the outputs of a skipless network of attention blocks on a batch
has rank at most `P − d (d − 1) − 2 ∑_ℓ H_ℓ d_{h,ℓ}²` at every parameter. -/
theorem jacobianRank_add_le_skipless_ends_attention_rmsNorm {ε : ℝ} (hε : 0 < ε) (hL : 0 < L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (θ : Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) {n : ℕ}
    (X : Fin n → Matrix T dIn ℝ) :
    jacobianRank (Arch.attention sees (rmsNorm ε) H dh) 0 X θ
        + (Fintype.card d * (Fintype.card d - 1)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attention (T := T) (d := d) sees (rmsNorm ε) H dh) dIn dOut) := by
  -- at almost every `θ'`, `E` and `D` have rank `d` and the query and value matrices of every
  -- head have rank `d_h`, so `fd(θ') + d (d - 1) + 2 ∑_ℓ H_ℓ d_{h,ℓ}² ≤ P`
  refine jacobianRank_add_le_of_ae_sea
    (fun ℓ => analyticOnNhd_f_attention sees (rmsNorm ε) H dh ℓ) (analyticOnNhd_rmsNorm hε)
    θ X ?_
  filter_upwards [ae_rank_E_D_sea Measure.addHaar hdIn hdOut,
    ae_rank_QV_sea Measure.addHaar hdh] with θ' h1 h2
  exact funDim_add_le_skipless_ends_attention_rmsNorm hε θ' hL h1.1 h1.2 h2.1 h2.2

end Skips
