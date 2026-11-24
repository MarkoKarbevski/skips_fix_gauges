import SkipsLean.Symmetry.InsideBlocksSum
import SkipsLean.Symmetry.InsideBlocksKinds
import SkipsLean.Network.Transformer
import SkipsLean.Dimension.UpperBoundAttention
import SkipsLean.Generic.Gated

/-!
# The upper bounds for networks of attention blocks and MLP blocks

Papers. Skips paper, Theorem 4.2 (Upper bounds): "Let `G` be the group of changes of basis of one
hidden state, and `s` the dimension of the symmetries inside the blocks, the same with and without
skips. With or without pre-RMSNorm, at generic parameters, the functional dimension is at most
`P − (L + 1) dim G − s` without skips and at most `P − dim G − s` with identity skips." Dimension
paper, Theorem 4.3 and Lemma B.1. Section 2 of the skips paper: "A transformer layer has two
blocks, its attention and MLP sub-layers".

Here for the networks of `Network/Transformer.lean`, whose blocks are attention blocks and MLP
blocks (`Arch.attentionMlp`), or attention blocks and gated blocks (`Arch.attentionGated`), in any
order (a block may also have heads and hidden units side by side):

* attention and MLP blocks, any activation `σ`: `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`, the changes of basis
  inside the heads (for tanh and GELU blocks the hidden units add nothing to `s`; for ReLU and
  ReLU² blocks the rescalings of the hidden units are not counted here, so the bound is not the
  paper's for them);
* attention and gated blocks, any gate activation `σ`:
  `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}² + ∑_ℓ d_hidden,ℓ`, with the rescalings of the values of the gated units
  (for a ReGLU block the rescalings of the gates are not counted here).

At one parameter under the rank conditions of Lemma B.1 (stated on the two parts
`θ.sumFst`, `θ.sumSnd` of the parameters, `Symmetry/InsideBlocksSum.lean`), and at almost every
parameter: `d_in ≥ d`, heads of width `d_h ≤ d`, and, without skips, blocks of total width
`H d_h + d_hidden ≥ d`. Under pre-RMSNorm (any `ε`) `dim G = d(d−1)/2`. The twins for networks
of one kind of block: `Dimension/UpperBoundAttention.lean`, `Generic/Params.lean`,
`Generic/Gated.lean`, `Residual/UpperBoundSymmetries.lean`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ}


/-! ### Helpers: the changes of basis inside the heads -/

/-- Helper (the private `headDirQKLin_uba` of `Dimension/UpperBoundAttention.lean`):
`Γ ↦ headDirQK θ Γ` is linear. -/
private noncomputable def headDirQKLin_ubt {χ : Matrix T d ℝ → Matrix T d ℝ}
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

/-- Helper (the private `headDirVOLin_uba`): `Γ' ↦ headDirVO θ Γ'` is linear. -/
private noncomputable def headDirVOLin_ubt {χ : Matrix T d ℝ → Matrix T d ℝ}
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

/-- Helper (the private `finrank_headFun_uba`): the families `Γ` of `d_h × d_h` matrices, one for
each head of each block, form a space of dimension `∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_ubt :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

/-- Helper (the private `cancel_left_of_rank_uba`): a matrix `M` of rank equal to its number of
columns cancels on the left, `M X = M Y → X = Y` (its kernel is `0` by rank–nullity). -/
private theorem cancel_left_of_rank_ubt {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `headDirLin_injective_uba`): if the query and the value matrix of every
head have rank `d_h`, the direction `headDirQK θ Γ + headDirVO θ Γ'` determines `Γ` and `Γ'`. -/
private theorem headDirLin_injective_ubt {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    Function.Injective ((headDirQKLin_ubt θ).coprod (headDirVOLin_ubt θ)) := by
  rintro ⟨Γ, Γ'⟩ ⟨Δ, Δ'⟩ h
  have h' : headDirQK θ Γ + headDirVO θ Γ' = headDirQK θ Δ + headDirVO θ Δ' := h
  -- the entry `(a, p)` of the read of block `ℓ`
  have hr : ∀ ℓ a p, (headDirQK θ Γ + headDirVO θ Γ').read ℓ a p
      = (headDirQK θ Δ + headDirVO θ Δ').read ℓ a p := fun ℓ a p => by rw [h']
  refine Prod.ext ?_ ?_ <;> funext ℓ i
  · -- the query columns of head `i`: `W_{Q,i} Γ_i = W_{Q,i} Δ_i`, and `W_{Q,i}` has rank `d_h`
    refine cancel_left_of_rank_ubt _ (hQ ℓ i) (Matrix.ext fun a k => ?_)
    have := hr ℓ a (i, Sum.inl k)
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      add_zero] at this
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this
  · -- the value columns of head `i`: `W_{V,i} Γ'_i = W_{V,i} Δ'_i`
    refine cancel_left_of_rank_ubt _ (hV ℓ i) (Matrix.ext fun a k => ?_)
    have := hr ℓ a (i, Sum.inr (Sum.inr k))
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      zero_add] at this
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if the value matrices of the heads of block `ℓ` have rank `d_h` and the read of block
`ℓ` of `headDirQK θ Γ + headDirVO θ Γ'` is `0`, its write of block `ℓ` is `0`: the value columns
of head `i` give `W_{V,i} Γ'_{ℓ,i} = 0`, so `Γ'_{ℓ,i} = 0`, and the write is `−Γ'_{ℓ,i} W_{O,i}`
at the rows of head `i`. -/
private theorem headDir_write_eq_zero_ubt {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) (ℓ : Fin L)
    (h0 : (headDirQK θ Γ + headDirVO θ Γ').read ℓ = 0) :
    (headDirQK θ Γ + headDirVO θ Γ').write ℓ = 0 := by
  -- `Γ'_{ℓ,i} = 0` for every head `i` of block `ℓ`
  have hΓ : ∀ i, Γ' ℓ i = 0 := fun i => by
    refine cancel_left_of_rank_ubt _ (hV ℓ i) (Matrix.ext fun a k => ?_)
    have := congrFun (congrFun h0 a) (i, Sum.inr (Sum.inr k))
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      zero_add, Matrix.zero_apply] at this
    rw [Matrix.mul_zero, Matrix.zero_apply]
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this
  -- hence the write `−Γ'_{ℓ,i} W_{O,i}` is `0`
  ext p b
  simp [headDirQK, headDirVO, hΓ]

omit [DecidableEq d] in
/-- Helper: the directions of the changes of basis inside the heads span a space `V_A` of
directions of symmetries inside the blocks, of dimension `2 ∑_ℓ H_ℓ d_{h,ℓ}²` (Lemma B.1), in
which a direction whose read of a block is `0` has the write of that block `0`. -/
private theorem attn_part_ubt {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    ∃ V : Submodule ℝ (Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut),
      V ≤ Submodule.span ℝ {η | InsideBlocks (Arch.attention sees χ H dh) θ η} ∧
      (∀ η ∈ V, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0) ∧
      Module.finrank ℝ V = 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  refine ⟨LinearMap.range ((headDirQKLin_ubt θ).coprod (headDirVOLin_ubt θ)), ?_, ?_, ?_⟩
  · -- each of the two summands is a direction of a symmetry inside the blocks
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply]
    exact Submodule.add_mem _ (Submodule.subset_span (insideBlocks_headDirQK θ p.1))
      (Submodule.subset_span (insideBlocks_headDirVO θ p.2))
  · rintro _ ⟨p, rfl⟩ ℓ h0
    rw [LinearMap.coprod_apply] at h0 ⊢
    exact headDir_write_eq_zero_ubt θ hV p.1 p.2 ℓ h0
  · -- the map `(Γ, Γ') ↦ headDirQK θ Γ + headDirVO θ Γ'` is injective
    rw [LinearMap.finrank_range_of_inj (headDirLin_injective_ubt θ hQ hV), Module.finrank_prod,
      finrank_headFun_ubt, two_mul]

/-! ### Helpers: the rescalings of the values of gated units -/

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `rescaleDirLin_se` of `Residual/SkiplessEnds.lean`): `α ↦ rescaleDir θ α`
is linear. -/
private noncomputable def rescaleDirLin_ubt {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  toFun := rescaleDir θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext k j
      cases j with
      | inl i => simp [rescaleDir]
      | inr i =>
        simp only [rescaleDir, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply,
          Sum.elim_inr]
        ring
    · intro ℓ
      ext i k
      simp [rescaleDir, add_mul]
    · simp [rescaleDir]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext k j
      cases j <;> simp [rescaleDir, mul_assoc]
    · intro ℓ
      ext i k
      simp [rescaleDir, mul_assoc]
    · simp [rescaleDir]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if no value column of the read of block `ℓ` vanishes and the read of block `ℓ` of
`rescaleDir θ α` is `0`, then `α_{ℓ,i} = 0` for every hidden unit `i` of block `ℓ` (the value
column `i` of that read is `−α_{ℓ,i}` times the value column `i` of `θ`). -/
private theorem rescale_eq_zero_ubt {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) (α : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L)
    (h0 : (rescaleDir θ α).read ℓ = 0) (i : hid ℓ) : α ℓ i = 0 := by
  by_contra hα
  refine hv ℓ i (funext fun k => ?_)
  have := congrFun (congrFun h0 k) (Sum.inr i)
  simp only [rescaleDir, Matrix.of_apply, Sum.elim_inr, Matrix.zero_apply] at this
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (neg_eq_zero.1 h) hα
  · exact h

omit [Fintype T] [DecidableEq d] in
/-- Helper: the directions of the rescalings of the values of the gated units span a space `V_B`
of directions of symmetries inside the blocks, of dimension `∑_ℓ d_hidden,ℓ`, in which a
direction whose read of a block is `0` has the write of that block `0`. -/
private theorem gated_part_ubt {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hv : ∀ ℓ i, (fun k => θ.read ℓ k (Sum.inr i)) ≠ 0) :
    ∃ V : Submodule ℝ (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut),
      V ≤ Submodule.span ℝ {η | InsideBlocks (Arch.gated σ χ hid) θ η} ∧
      (∀ η ∈ V, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0) ∧
      Module.finrank ℝ V = ∑ ℓ, Fintype.card (hid ℓ) := by
  -- `α ↦ rescaleDir θ α` is injective, since its kernel is `0`
  have hinj : Function.Injective (rescaleDirLin_ubt θ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro α hα
    have hα' : rescaleDir θ α = 0 := hα
    funext ℓ i
    exact rescale_eq_zero_ubt θ hv α ℓ (by rw [hα']; rfl) i
  refine ⟨LinearMap.range (rescaleDirLin_ubt θ), ?_, ?_, ?_⟩
  · rintro _ ⟨α, rfl⟩
    exact Submodule.subset_span (insideBlocks_rescaleDir θ α)
  · -- read `0` gives `α_{ℓ,i} = 0`, so the write `α_{ℓ,i} · (row i)` is `0`
    rintro _ ⟨α, rfl⟩ ℓ h0
    have hα := rescale_eq_zero_ubt θ hv α ℓ h0
    ext i k
    show α ℓ i * θ.write ℓ i k = 0
    rw [hα i, zero_mul]
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype]
    simp [Module.finrank_fintype_fun_eq_card]

/-! ### Helpers: generic parameters -/

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `analyticOnNhd_det_uba`): the determinant of a square matrix that depends
linearly on the parameters is an analytic function of the parameters. -/
private theorem analyticOnNhd_det_ubt {A : Arch T d L} {n : Type*} [Fintype n] [DecidableEq n]
    (Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ) :
    AnalyticOnNhd ℝ (fun θ => (Φ θ).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ =>
      analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ (σ i) i).comp Φ))

/-- Helper (the private `exists_submatrix_eq_one_uba`): a matrix whose submatrix on the rows `r`
and the columns `c` (both injective) is the identity. -/
private theorem exists_submatrix_eq_one_ubt {m p n : Type*} [DecidableEq n] {r : n → m}
    (hr : Function.Injective r) {c : n → p} (hc : Function.Injective c) :
    ∃ M : Matrix m p ℝ, M.submatrix r c = 1 := by
  classical
  refine ⟨Matrix.of fun a b => if ∃ x, r x = a ∧ c x = b then 1 else 0, ?_⟩
  ext x y
  simp [Matrix.one_apply, hr.eq_iff, hc.eq_iff]

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `ae_rank_read_cols_uba`): at generic parameters, `n ≤ d` distinct columns
`c` of the read of block `ℓ` form a matrix of rank `n`. -/
private theorem ae_rank_read_cols_ubt {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*} [Fintype n] [DecidableEq n] {c : n → A.r ℓ}
    (hc : Function.Injective c) (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.read ℓ).submatrix id c).rank = Fintype.card n := by
  -- `n` rows `ρ`, and the square submatrix of the read on the rows `ρ` and the columns `c`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_ubt ρ.injective hc
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
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_ubt Φ) hne] with θ hθ
  -- an invertible `n × n` submatrix gives rank `≥ n`, and the rank is at most the width `n`
  have h1 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank = Fintype.card n :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hθ))
  have h2 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank
      ≤ ((θ.read ℓ).submatrix id c).rank :=
    Matrix.rank_submatrix_le _ ρ id
  have h3 := Matrix.rank_le_card_width ((θ.read ℓ).submatrix id c)
  omega

omit [DecidableEq d] in
/-- Helper (the private `ae_rank_QV_uba`, for the first part of a sum): at generic parameters the
query matrix and the value matrix of every head have rank `d_h`, when `d_h ≤ d`. The read of the
first part is made of columns of the read of the sum. -/
private theorem ae_rank_QV_ubt {B : Arch T d L} {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees χ H dh).sum B) dIn dOut))
    [μ.IsAddHaarMeasure] (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, (∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ)) ∧
      ∀ ℓ (i : H ℓ),
        ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
          = Fintype.card (dh ℓ) := by
  classical
  -- finitely many conditions, two for each head of each block
  refine (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_).and
    (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_)
  · exact ae_rank_read_cols_ubt μ ℓ (c := fun k : dh ℓ => Sum.inl (i, Sum.inl k))
      (fun _ _ h => Sum.inl_injective (Prod.mk.inj (Sum.inl_injective h)).2) (hdh ℓ)
  · exact ae_rank_read_cols_ubt μ ℓ (c := fun k : dh ℓ => Sum.inl (i, Sum.inr (Sum.inr k)))
      (fun _ _ h => Sum.inr_injective (Sum.inr_injective (Prod.mk.inj (Sum.inl_injective h)).2))
      (hdh ℓ)

/-- Helper (the private `ae_rank_E_uba`): at generic parameters `E` has rank `d`, when
`d_in ≥ d`. -/
private theorem ae_rank_E_ubt {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d := by
  -- `d` rows `ρ` of `E`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  have h1 : (θ.E.submatrix ρ id).rank = Fintype.card d :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (hθ.2.2.1 ρ))
  have h2 := Matrix.rank_submatrix_le θ.E ρ id
  have h3 := Matrix.rank_le_card_width θ.E
  omega

omit [Fintype T] [DecidableEq d] in
/-- Helper (`ae_value_ne_zero` of `Generic/Gated.lean`, for the second part of a sum): at generic
parameters no value column of the gated part of a read vanishes. -/
private theorem ae_value_ne_zero_ubt [Nonempty d] {A : Arch T d L}
    {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params (A.sum (Arch.gated (T := T) (d := d) σ χ hid)) dIn dOut))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0 := by
  -- finitely many conditions, one for each hidden unit `i` of each block `ℓ`
  refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_
  -- an entry `k₀` of the value column
  obtain k₀ : d := Classical.arbitrary d
  -- the entry `θ ↦ θ.read ℓ k₀ (inr (inr i))` is a linear functional of the parameters
  let l : Params (A.sum (Arch.gated (T := T) (d := d) σ χ hid)) dIn dOut →ₗ[ℝ] ℝ :=
    (Matrix.entryLinearMap ℝ ℝ k₀ (Sum.inr (Sum.inr i))).comp
      (Params.linRead (A := A.sum (Arch.gated (T := T) (d := d) σ χ hid)) (dIn := dIn)
        (dOut := dOut) ℓ)
  have hl : ∀ θ, l θ = θ.read ℓ k₀ (Sum.inr (Sum.inr i)) := fun θ => rfl
  -- it is not zero at the parameters whose reads have all entries `1`
  have h₁ : l ⟨0, fun _ => Matrix.of fun _ _ => 1, 0, 0⟩ ≠ 0 := by
    rw [hl]
    exact one_ne_zero
  -- an analytic function that is not identically zero is nonzero almost everywhere
  have hne : ∀ᵐ θ ∂μ, l θ ≠ 0 :=
    ae_ne_zero_of_analytic μ (analyticOnNhd_linear l) ⟨_, h₁⟩
  -- and a function with a nonzero entry is not zero
  filter_upwards [hne] with θ h hz
  exact h (by rw [hl]; exact congrFun hz k₀)

/-! ### Attention blocks and MLP blocks -/

/-- **Theorem 4.3 of the dimension paper for attention blocks and MLP blocks, without
normalization, under the conditions of Lemma B.1:**
`fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_skipless_attentionMlp
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attentionMlp sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  -- `V_A`: the changes of basis inside the heads; `V_B = 0` for the MLP part
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubt θ.sumFst hQ hV
  have h := funDim_add_le_skipless_sum_of_insideBlocks θ rfl VA ⊥ hVA bot_le hrwA
    (fun η hη _ _ => by rw [(Submodule.mem_bot ℝ).1 hη]; rfl) hE hw
  rwa [hdimA, finrank_bot, add_zero] at h

/-- **Theorem 4.3 of the dimension paper for attention blocks and MLP blocks, under pre-RMSNorm,
under the conditions of Lemma B.1:**
`fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_skipless_attentionMlp_rmsNorm (ε : ℝ)
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  -- `V_A`: the changes of basis inside the heads; `V_B = 0` for the MLP part
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubt θ.sumFst hQ hV
  have h := funDim_add_le_skipless_sum_of_insideBlocks_rmsNorm θ ε rfl VA ⊥ hVA bot_le hrwA
    (fun η hη _ _ => by rw [(Submodule.mem_bot ℝ).1 hη]; rfl) hE hw
  rwa [hdimA, finrank_bot, add_zero] at h

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and MLP blocks,
without normalization, under the conditions of Lemma B.1:**
`fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_residual_attentionMlp
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  -- `V_A`: the changes of basis inside the heads; `V_B = 0` for the MLP part
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubt θ.sumFst hQ hV
  have h := funDim_add_le_residual_sum_of_insideBlocks θ rfl VA ⊥ hVA bot_le hE
  rwa [hdimA, finrank_bot, add_zero] at h

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and MLP blocks,
under pre-RMSNorm, under the conditions of Lemma B.1:**
`fd ≤ P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem funDim_add_le_residual_attentionMlp_rmsNorm (ε : ℝ)
    (θ : Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  -- `V_A`: the changes of basis inside the heads; `V_B = 0` for the MLP part
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubt θ.sumFst hQ hV
  have h := funDim_add_le_residual_sum_of_insideBlocks_rmsNorm θ ε rfl VA ⊥ hVA bot_le hE
  rwa [hdimA, finrank_bot, add_zero] at h

/-- **Theorem 4.3 of the dimension paper for attention blocks and MLP blocks, without
normalization, at generic parameters:**
`fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_add_le_skipless_attentionMlp
    (μ : Measure (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  -- the pointwise bound holds wherever the rank conditions of Lemma B.1 hold
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubt μ hdh] with θ h1 h2
  exact funDim_add_le_skipless_attentionMlp θ h1.1 h1.2 h2.1 h2.2

/-- **Theorem 4.3 of the dimension paper for attention blocks and MLP blocks, under pre-RMSNorm,
at generic parameters:**
`fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_add_le_skipless_attentionMlp_rmsNorm (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  -- the pointwise bound holds wherever the rank conditions of Lemma B.1 hold
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubt μ hdh] with θ h1 h2
  exact funDim_add_le_skipless_attentionMlp_rmsNorm ε θ h1.1 h1.2 h2.1 h2.2

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and MLP blocks,
without normalization, at generic parameters:**
`fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_add_le_residual_attentionMlp
    (μ : Measure (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  -- the pointwise bound holds wherever the rank conditions of Lemma B.1 hold
  filter_upwards [ae_rank_E_ubt μ hdIn, ae_rank_QV_ubt μ hdh] with θ h1 h2
  exact funDim_add_le_residual_attentionMlp θ h1 h2.1 h2.2

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and MLP blocks,
under pre-RMSNorm, at generic parameters:**
`fd ≤ P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDim_add_le_residual_attentionMlp_rmsNorm (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      ≤ Module.finrank ℝ
          (Params (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  -- the pointwise bound holds wherever the rank conditions of Lemma B.1 hold
  filter_upwards [ae_rank_E_ubt μ hdIn, ae_rank_QV_ubt μ hdh] with θ h1 h2
  exact funDim_add_le_residual_attentionMlp_rmsNorm ε θ h1 h2.1 h2.2


/-! ### Attention blocks and gated blocks -/

/-- **Theorem 4.3 of the dimension paper for attention blocks and gated blocks, without
normalization, under the conditions of Lemma B.1:**
`fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_skipless_attentionGated
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
          (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the values
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubt θ.sumFst hQ hV
  obtain ⟨VB, hVB, hrwB, hdimB⟩ := gated_part_ubt θ.sumSnd hv
  have h := funDim_add_le_skipless_sum_of_insideBlocks θ rfl VA VB hVA hVB hrwA hrwB hE hw
  rwa [hdimA, hdimB] at h

/-- **Theorem 4.3 of the dimension paper for attention blocks and gated blocks, under pre-RMSNorm,
under the conditions of Lemma B.1:**
`fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_skipless_attentionGated_rmsNorm (ε : ℝ)
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
        (Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the values
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubt θ.sumFst hQ hV
  obtain ⟨VB, hVB, hrwB, hdimB⟩ := gated_part_ubt θ.sumSnd hv
  have h := funDim_add_le_skipless_sum_of_insideBlocks_rmsNorm θ ε rfl VA VB hVA hVB hrwA hrwB hE hw
  rwa [hdimA, hdimB] at h

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and gated blocks,
without normalization, under the conditions of Lemma B.1:**
`fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_residual_attentionGated
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
          (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the values
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubt θ.sumFst hQ hV
  obtain ⟨VB, hVB, hrwB, hdimB⟩ := gated_part_ubt θ.sumSnd hv
  have h := funDim_add_le_residual_sum_of_insideBlocks θ rfl VA VB hVA hVB hE
  rwa [hdimA, hdimB] at h

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and gated blocks,
under pre-RMSNorm, under the conditions of Lemma B.1:**
`fd ≤ P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_residual_attentionGated_rmsNorm (ε : ℝ)
    (θ : Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun k => θ.sumSnd.read ℓ k (Sum.inr i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
        (Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the values
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubt θ.sumFst hQ hV
  obtain ⟨VB, hVB, hrwB, hdimB⟩ := gated_part_ubt θ.sumSnd hv
  have h := funDim_add_le_residual_sum_of_insideBlocks_rmsNorm θ ε rfl VA VB hVA hVB hE
  rwa [hdimA, hdimB] at h

/-- **Theorem 4.3 of the dimension paper for attention blocks and gated blocks, without
normalization, at generic parameters:**
`fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attentionGated [Nonempty d]
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
          (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionGated (T := T) (d := d) sees σ id H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  -- the pointwise bound holds wherever the rank conditions of Lemma B.1 hold
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubt μ hdh, ae_value_ne_zero_ubt μ]
    with θ h1 h2 h3
  exact funDim_add_le_skipless_attentionGated θ h1.1 h1.2 h2.1 h2.2 h3

/-- **Theorem 4.3 of the dimension paper for attention blocks and gated blocks, under pre-RMSNorm,
at generic parameters:**
`fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attentionGated_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ, Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
        (Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  -- the pointwise bound holds wherever the rank conditions of Lemma B.1 hold
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubt μ hdh, ae_value_ne_zero_ubt μ]
    with θ h1 h2 h3
  exact funDim_add_le_skipless_attentionGated_rmsNorm ε θ h1.1 h1.2 h2.1 h2.2 h3

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and gated blocks,
without normalization, at generic parameters:**
`fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attentionGated [Nonempty d]
    (μ : Measure (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
          (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  -- the pointwise bound holds wherever the rank conditions of Lemma B.1 hold
  filter_upwards [ae_rank_E_ubt μ hdIn, ae_rank_QV_ubt μ hdh, ae_value_ne_zero_ubt μ]
    with θ h1 h2 h3
  exact funDim_add_le_residual_attentionGated θ h1 h2.1 h2.2 h3

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and gated blocks,
under pre-RMSNorm, at generic parameters:**
`fd ≤ P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attentionGated_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ
        (Params (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  -- the pointwise bound holds wherever the rank conditions of Lemma B.1 hold
  filter_upwards [ae_rank_E_ubt μ hdIn, ae_rank_QV_ubt μ hdh, ae_value_ne_zero_ubt μ]
    with θ h1 h2 h3
  exact funDim_add_le_residual_attentionGated_rmsNorm ε θ h1 h2.1 h2.2 h3

end Skips
