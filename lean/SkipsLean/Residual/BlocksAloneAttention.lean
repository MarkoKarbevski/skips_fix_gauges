import SkipsLean.Residual.BlocksAlone
import SkipsLean.Residual.DepthAttentionDim
import SkipsLean.Dimension.GenericRankOn

/-!
# Attention-only residual networks without an embedding and a readout

Paper (skips paper): Corollary 4.10 (Attention-only transformers: Conjecture 2.4 of Henry, 2026):
"Without normalization, consider a residual network of `L` attention blocks at generic
parameters, and let `s = 2 L d_model² / H`. […] (ii) Without an embedding and a readout, so that
`h_0 = x ∈ ℝ^{T × d_model}` and `y = h_L`, its functional dimension is
`P − s = L (4 d_model² − 2 d_model² / H)`." Lemma A.27, fourth value: "`fd(θ_τ) = P − s` (no
embedding, readout, biases or normalization)". Its proof: "Without an embedding and a readout,
`M = I` is fixed, so `ψ_M = 0` for every direction, and the flat directions are the rescalings
alone, of dimension `s`"; for attention blocks: "So the flat directions form a space of dimension
`d_model² + s`, and of dimension `s` without an embedding and a readout." Proof of Corollary 4.10:
"For part (ii), without an embedding and a readout, the last value of Lemma A.27 is `r = P − s`,
and at generic parameters the changes of basis inside the heads move the parameters in `s`
independent directions. […] With heads of total width `H d_h = d_model`, a block has `4 d_model²`
parameters and `H` heads, each with two changes of basis of dimension `d_h² = d_model² / H²`. So
`P = 4 L d_model²` and `s = 2 L d_model² / H`."

Here, for `Arch.attention sees id H dh` (heads of width `1 ≤ d_h ≤ d`, any numbers of heads,
`s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`), `d ≥ 2`, a mask with a token that sees itself and another token, and
the network without an embedding and a readout of `Residual/BlocksAlone.lean`:

* `eventually_funDimBlocks_smallWrites_attention`: Lemma A.27, fourth value, under the conditions
  of its proof (`SmallWritesGenericAttention` at `E = D = I`);
* `ae_funDimBlocks_attention_residual`: Corollary 4.10 (ii), `fd = P − s` at almost every
  parameter of the blocks;
* `ae_funDimBlocks_attention_residual_of_width`: the same in the setting of the main text, `H`
  heads of total width `H d_h = d` in every block: `fd = L (4 d² − 2 d² / H)`.

Numeric check of the value in 14 cases: `attention_blocks_alone_check_2026-11-24.py` (notes).
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]

/-! ### Helpers: the family of the blocks alone and the network with `E = D = I`

`β.toParams = ι β + (I, 0, 0, I)` with `ι η = (0, η_read, η_write, 0)`, so by the chain rule the
Jacobian of the family `β ↦ (F_β(x_i))_i` is the Jacobian of the network at `β.toParams`
composed with `ι`. -/

omit [Fintype T] [DecidableEq d] in
/-- Helper: the linear part `ι η = (0, η_read, η_write, 0)` of `β ↦ β.toParams`. -/
private def iotaBlocks_bla (A : Arch T d L) : BlockParams A →ₗ[ℝ] Params A d d where
  toFun η := ⟨0, η.read, η.write, 0⟩
  map_add' η ξ := by
    apply Params.ext'
    · exact (add_zero (0 : Matrix d d ℝ)).symm
    · intro ℓ
      rfl
    · intro ℓ
      rfl
    · exact (add_zero (0 : Matrix d d ℝ)).symm
  map_smul' c η := by
    apply Params.ext'
    · exact (smul_zero _).symm
    · intro ℓ
      rfl
    · intro ℓ
      rfl
    · exact (smul_zero _).symm

omit [Fintype T] [Fintype d] [DecidableEq d] in
/-- Helper: `ι` is injective (it keeps the reads and the writes; `E` and `D` of the blocks are
empty matrices). -/
private theorem iotaBlocks_injective_bla (A : Arch T d L) :
    Function.Injective (iotaBlocks_bla A) := by
  intro η ξ h
  apply Params.ext'
  · exact Matrix.ext fun i => i.elim
  · intro ℓ
    exact congrArg (fun θ : Params A d d => θ.read ℓ) h
  · intro ℓ
    exact congrArg (fun θ : Params A d d => θ.write ℓ) h
  · exact Matrix.ext fun _ j => j.elim

omit [Fintype T] [Fintype d] in
/-- Helper: `β.toParams = ι β + (I, 0, 0, I)`. -/
private theorem toParams_eq_bla {A : Arch T d L} (β : BlockParams A) :
    β.toParams = iotaBlocks_bla A β + ⟨1, fun _ => 0, fun _ => 0, 1⟩ := by
  apply Params.ext'
  · exact (zero_add (1 : Matrix d d ℝ)).symm
  · intro ℓ
    exact (add_zero (β.read ℓ)).symm
  · intro ℓ
    exact (add_zero (β.write ℓ)).symm
  · exact (zero_add (1 : Matrix d d ℝ)).symm

omit [Fintype T] in
/-- Helper: the chain rule for the family `β' ↦ (F_{β'}(x_i))_i`: its derivative at `β` is the
derivative of the outputs of the network at `β.toParams`, composed with `ι`. -/
private theorem fderiv_blocks_bla {A : Arch T d L} (S : Fin L → Matrix d d ℝ) {n : ℕ}
    (X : Fin n → Matrix T d ℝ) (β : BlockParams A)
    (hdiff : DifferentiableAt ℝ (evalBatch A S X) β.toParams) :
    fderiv ℝ (fun β' : BlockParams A => fun i : Fin n => evalBlocks A S β' (X i)) β
      = (fderiv ℝ (evalBatch A S X) β.toParams).comp
          (LinearMap.toContinuousLinearMap (iotaBlocks_bla A)) := by
  -- `β' ↦ β'.toParams` is affine, with the linear part `ι`
  have haff : HasFDerivAt (fun β' : BlockParams A => β'.toParams)
      (LinearMap.toContinuousLinearMap (iotaBlocks_bla A)) β :=
    ((LinearMap.toContinuousLinearMap (iotaBlocks_bla A)).hasFDerivAt.add_const
      (⟨1, fun _ => 0, fun _ => 0, 1⟩ : Params A d d)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun β' => toParams_eq_bla β')
  have h := hdiff.hasFDerivAt.comp β haff
  exact h.fderiv

omit [Fintype T] in
/-- Helper: rank–nullity for the Jacobian of the family on a batch. -/
private theorem jacobianRankBlocks_add_finrank_ker_bla {A : Arch T d L}
    (S : Fin L → Matrix d d ℝ) {n : ℕ} (X : Fin n → Matrix T d ℝ) (β : BlockParams A) :
    jacobianRankBlocks A S X β + Module.finrank ℝ (LinearMap.ker
        (fderiv ℝ (fun β' : BlockParams A => fun i : Fin n => evalBlocks A S β' (X i))
          β).toLinearMap)
      = Module.finrank ℝ (BlockParams A) :=
  LinearMap.finrank_range_add_finrank_ker _

omit [Fintype T] in
/-- Helper: `η` is in the kernel of the Jacobian of the family on a batch if and only if `ι η` is
in the kernel of the Jacobian of the network at `β.toParams` on the same batch. -/
private theorem mem_ker_blocks_iff_bla {A : Arch T d L} (S : Fin L → Matrix d d ℝ) {n : ℕ}
    (X : Fin n → Matrix T d ℝ) (β : BlockParams A)
    (hdiff : DifferentiableAt ℝ (evalBatch A S X) β.toParams) (η : BlockParams A) :
    η ∈ LinearMap.ker (fderiv ℝ (fun β' : BlockParams A => fun i : Fin n =>
        evalBlocks A S β' (X i)) β).toLinearMap
      ↔ iotaBlocks_bla A η
        ∈ LinearMap.ker (fderiv ℝ (evalBatch A S X) β.toParams).toLinearMap := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, fderiv_blocks_bla S X β hdiff]
  rfl

omit [DecidableEq d] in
/-- Helper (as the private `flat_le_ker'` of `Dimension/Functional.lean`, here for outputs that
are differentiable in the parameters): the flat directions are in the kernel of the Jacobian on
every batch. -/
private theorem flat_le_ker_bla {A : Arch T d L} {S : Fin L → Matrix d d ℝ} (θ : Params A d d)
    (hdiff : ∀ x : Matrix T d ℝ, DifferentiableAt ℝ (fun θ' : Params A d d => eval A S θ' x) θ)
    {n : ℕ} (X : Fin n → Matrix T d ℝ) :
    flat A S θ ≤ LinearMap.ker (fderiv ℝ (evalBatch A S X) θ).toLinearMap := by
  intro η hη
  rw [flat, Submodule.mem_iInf] at hη
  -- the derivative of the outputs on the batch is the tuple of the derivatives of the outputs
  have h : fderiv ℝ (evalBatch A S X) θ =
      ContinuousLinearMap.pi fun i => fderiv ℝ (fun θ' => eval A S θ' (X i)) θ :=
    fderiv_pi fun i => hdiff (X i)
  rw [LinearMap.mem_ker]
  show fderiv ℝ (evalBatch A S X) θ η = 0
  rw [h]
  funext i
  have hi := hη (X i)
  rw [LinearMap.mem_ker] at hi
  exact hi

/-! ### Helpers: attention blocks -/

/-- Helper: the output of a network of attention blocks at an input is differentiable in the
parameters. -/
private theorem differentiableAt_eval_bla
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) d d) (x : Matrix T d ℝ) :
    DifferentiableAt ℝ (fun θ' : Params (Arch.attention (T := T) (d := d) sees id H dh) d d =>
      eval (Arch.attention sees id H dh) 1 θ' x) θ :=
  differentiable_eval (fun ℓ => differentiable_f_attention sees id H dh ℓ) differentiable_id x θ

/-- Helper: so are its outputs on a batch. -/
private theorem differentiableAt_evalBatch_bla
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) d d) {n : ℕ}
    (X : Fin n → Matrix T d ℝ) :
    DifferentiableAt ℝ (evalBatch (Arch.attention sees id H dh) 1 X) θ :=
  differentiableAt_pi.2 fun i => differentiableAt_eval_bla θ (X i)

/-- Helper (as `headDirQKLin_uba` of `Dimension/UpperBoundAttention.lean`): `Γ ↦ headDirQK θ Γ`
is linear. -/
private noncomputable def headDirQKLin_bla {dIn dOut : Type*} {χ : Matrix T d ℝ → Matrix T d ℝ}
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

/-- Helper (as `headDirVOLin_uba`): `Γ' ↦ headDirVO θ Γ'` is linear. -/
private noncomputable def headDirVOLin_bla {dIn dOut : Type*} {χ : Matrix T d ℝ → Matrix T d ℝ}
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

/-- Helper (as `finrank_headFun_uba`): the families `Γ` of `d_h × d_h` matrices, one for each
head of each block, form a space of dimension `∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_bla :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

/-- Helper (as `cancel_left_of_rank_uba`): a matrix `M` of rank equal to its number of columns
cancels on the left, `M X = M Y → X = Y`. -/
private theorem cancel_left_of_rank_bla {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
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

omit [Fintype d] [DecidableEq d] in
/-- Helper (as `headDirLin_injective_uba`): if the query and the value matrix of every head have
rank `d_h`, the direction `headDirQK θ Γ + headDirVO θ Γ'` determines `Γ` and `Γ'`. -/
private theorem headDirLin_injective_bla {dIn dOut : Type*} {χ : Matrix T d ℝ → Matrix T d ℝ}
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    Function.Injective ((headDirQKLin_bla θ).coprod (headDirVOLin_bla θ)) := by
  rintro ⟨Γ, Γ'⟩ ⟨Δ, Δ'⟩ h
  have h' : headDirQK θ Γ + headDirVO θ Γ' = headDirQK θ Δ + headDirVO θ Δ' := h
  -- the entry `(a, p)` of the read of block `ℓ`
  have hr : ∀ ℓ a p, (headDirQK θ Γ + headDirVO θ Γ').read ℓ a p
      = (headDirQK θ Δ + headDirVO θ Δ').read ℓ a p := fun ℓ a p => by rw [h']
  refine Prod.ext ?_ ?_ <;> funext ℓ i
  · -- the query columns of head `i`: `W_{Q,i} Γ_i = W_{Q,i} Δ_i`, and `W_{Q,i}` has rank `d_h`
    refine cancel_left_of_rank_bla _ (hQ ℓ i) (Matrix.ext fun a k => ?_)
    have := hr ℓ a (i, Sum.inl k)
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      add_zero] at this
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this
  · -- the value columns of head `i`: `W_{V,i} Γ'_i = W_{V,i} Δ'_i`
    refine cancel_left_of_rank_bla _ (hV ℓ i) (Matrix.ext fun a k => ?_)
    have := hr ℓ a (i, Sum.inr (Sum.inr k))
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      zero_add] at this
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this

omit [Fintype d] in
/-- Helper: `ι` maps the directions of the changes of basis inside the heads at `β` to those at
`β.toParams`: they move only the reads and the writes, which are the same. -/
private theorem iota_headDir_bla
    (β : BlockParams (Arch.attention (T := T) (d := d) sees id H dh))
    (p : (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)) :
    iotaBlocks_bla _ ((headDirQKLin_bla β).coprod (headDirVOLin_bla β) p)
      = (headDirQKLin_bla β.toParams).coprod (headDirVOLin_bla β.toParams) p := by
  apply Params.ext'
  · exact (add_zero (0 : Matrix d d ℝ)).symm
  · intro ℓ
    rfl
  · intro ℓ
    rfl
  · exact (add_zero (0 : Matrix d d ℝ)).symm

/-- Helper, step (a): if the query and the value matrix of every head of `β` have rank `d_h`, the
Jacobian of the family has rank at most `P − s` on every batch. By the chain rule its kernel
contains the directions `headDirQK β Γ + headDirVO β Γ'`, which `ι` maps to flat directions of
the network at `β.toParams`; these form a space of dimension `s` (Lemma B.1 for the heads). -/
private theorem jacobianRankBlocks_add_le_bla [∀ ℓ, DecidableEq (dh ℓ)]
    (β : BlockParams (Arch.attention (T := T) (d := d) sees id H dh))
    (hQ : ∀ ℓ (i : H ℓ), ((β.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((β.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    {n : ℕ} (X : Fin n → Matrix T d ℝ) :
    jacobianRankBlocks (Arch.attention sees id H dh) 1 X β
        + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
      ≤ Module.finrank ℝ (BlockParams (Arch.attention (T := T) (d := d) sees id H dh)) := by
  -- the directions of the heads at `β` are in the kernel of the Jacobian of the family
  have hker : LinearMap.range ((headDirQKLin_bla β).coprod (headDirVOLin_bla β))
      ≤ LinearMap.ker (fderiv ℝ
          (fun β' : BlockParams (Arch.attention (T := T) (d := d) sees id H dh) =>
            fun i : Fin n => evalBlocks (Arch.attention sees id H dh) 1 β' (X i))
          β).toLinearMap := by
    rintro _ ⟨p, rfl⟩
    rw [mem_ker_blocks_iff_bla 1 X β (differentiableAt_evalBatch_bla _ X), iota_headDir_bla,
      LinearMap.coprod_apply]
    exact flat_le_ker_bla _ (differentiableAt_eval_bla _) X
      (Submodule.add_mem _ (headDirQK_mem_flat β.toParams 1 p.1)
        (headDirVO_mem_flat β.toParams 1 p.2))
  -- they form a space of dimension `s`; rank–nullity
  have h1 := Submodule.finrank_mono hker
  rw [LinearMap.finrank_range_of_inj (headDirLin_injective_bla β hQ hV), Module.finrank_prod,
    finrank_headFun_bla, ← two_mul] at h1
  rw [← jacobianRankBlocks_add_finrank_ker_bla 1 X β]
  exact Nat.add_le_add_left h1 _

/-- Helper, step (b): let the query and the value matrix of every head of `β` have rank `d_h`,
and let the network `θ = β.toParams` have `fd(θ) + d² + s = P(θ)`. Take a batch on which the
Jacobian of the network has the rank `fd(θ)`. Its kernel contains the space `R` of the flat
directions `cobDir θ (fun _ => Y) + headDirQK θ Γ + headDirVO θ Γ'`, and both have dimension
`d² + s`, so they are equal. A direction `η` of the blocks with `ι η ∈ R` has `Y = 0` (the `E`
component of `ι η` is `0`, that of `R` is `I Y`), so it is a direction of the heads at `β`: the
kernel of the Jacobian of the family has dimension at most `s`. -/
private theorem exists_le_jacobianRankBlocks_bla [∀ ℓ, DecidableEq (dh ℓ)]
    (β : BlockParams (Arch.attention (T := T) (d := d) sees id H dh))
    (hQ : ∀ ℓ (i : H ℓ), ((β.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((β.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hfd : funDim (Arch.attention sees id H dh) 1 β.toParams
        + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2)
      = Module.finrank ℝ (Params (Arch.attention (T := T) (d := d) sees id H dh) d d)) :
    ∃ (n : ℕ) (X : Fin n → Matrix T d ℝ),
      Module.finrank ℝ (BlockParams (Arch.attention (T := T) (d := d) sees id H dh))
        ≤ jacobianRankBlocks (Arch.attention sees id H dh) 1 X β
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  -- a batch `X` on which the Jacobian of the network at `θ` has the rank `fd(θ)`
  obtain ⟨n, X, hX⟩ :=
    exists_jacobianRank_eq_funDim (S := (1 : Fin L → Matrix d d ℝ)) β.toParams
  refine ⟨n, X, ?_⟩
  -- rank–nullity for the network on `X`
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (fderiv ℝ (evalBatch (Arch.attention sees id H dh) 1 X) β.toParams).toLinearMap
  have hJ : jacobianRank (Arch.attention sees id H dh) 1 X β.toParams
      = Module.finrank ℝ (LinearMap.range
          (fderiv ℝ (evalBatch (Arch.attention sees id H dh) 1 X) β.toParams).toLinearMap) :=
    rfl
  -- the map `Φ (Y, Γ, Γ') = cobDir θ (fun _ => Y) + headDirQK θ Γ + headDirVO θ Γ'`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Matrix d d ℝ × ((∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
        × (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ))) →ₗ[ℝ]
        Params (Arch.attention (T := T) (d := d) sees id H dh) d d,
      ∀ Y p, Φ (Y, p) = cobDir β.toParams (fun _ => Y)
        + (headDirQKLin_bla β.toParams).coprod (headDirVOLin_bla β.toParams) p :=
    ⟨((cobDirLin β.toParams).comp (LinearMap.pi fun _ : Fin (L + 1) => LinearMap.id)).coprod
      ((headDirQKLin_bla β.toParams).coprod (headDirVOLin_bla β.toParams)), fun _ _ => rfl⟩
  -- its `E` component is `I Y = Y`
  have hΦE : ∀ Y p, (Φ (Y, p)).E = Y := fun Y p => by
    rw [hΦ, Params.add_E, LinearMap.coprod_apply, Params.add_E]
    show (1 : Matrix d d ℝ) * Y + ((0 : Matrix d d ℝ) + 0) = Y
    rw [Matrix.one_mul, add_zero, add_zero]
  -- its directions are flat, hence in the kernel on `X`
  have hle : LinearMap.range Φ ≤ LinearMap.ker
      (fderiv ℝ (evalBatch (Arch.attention sees id H dh) 1 X) β.toParams).toLinearMap := by
    rintro _ ⟨⟨Y, p⟩, rfl⟩
    rw [hΦ, LinearMap.coprod_apply]
    exact flat_le_ker_bla _ (differentiableAt_eval_bla _) X
      (Submodule.add_mem _ (cobDir_const_mem_flat_residual' β.toParams rfl Y)
        (Submodule.add_mem _ (headDirQK_mem_flat β.toParams 1 p.1)
          (headDirVO_mem_flat β.toParams 1 p.2)))
  -- it is injective: the `E` component gives `Y`, then the heads (Lemma B.1)
  have hinj : Function.Injective Φ := by
    rintro ⟨Y, p⟩ ⟨Y', p'⟩ h
    have hY : Y = Y' := (hΦE Y p).symm.trans ((congrArg Params.E h).trans (hΦE Y' p'))
    subst hY
    rw [hΦ, hΦ] at h
    exact Prod.ext rfl (headDirLin_injective_bla β.toParams hQ hV (add_left_cancel h))
  -- so the kernel on `X` is the range of `Φ`, of dimension `d² + s`
  have hdimΦ : Module.finrank ℝ (LinearMap.range Φ)
      = Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_prod,
      Module.finrank_matrix, Module.finrank_self, mul_one, ← sq, finrank_headFun_bla, ← two_mul]
  have hK : LinearMap.range Φ = LinearMap.ker
      (fderiv ℝ (evalBatch (Arch.attention sees id H dh) 1 X) β.toParams).toLinearMap :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  -- `cobDir θ 0 = 0`
  have hcob0 : cobDir β.toParams (fun _ => (0 : Matrix d d ℝ)) = 0 :=
    map_zero (cobDirLin β.toParams)
  -- the kernel of the Jacobian of the family consists of directions of the heads at `β`
  have hker : LinearMap.ker (fderiv ℝ
        (fun β' : BlockParams (Arch.attention (T := T) (d := d) sees id H dh) =>
          fun i : Fin n => evalBlocks (Arch.attention sees id H dh) 1 β' (X i)) β).toLinearMap
      ≤ LinearMap.range ((headDirQKLin_bla β).coprod (headDirVOLin_bla β)) := by
    intro η hη
    rw [mem_ker_blocks_iff_bla 1 X β (differentiableAt_evalBatch_bla _ X), ← hK] at hη
    obtain ⟨⟨Y, p⟩, hYp⟩ := hη
    -- the `E` component: `Y = 0`, as `ι η` has `E = 0`
    have hY : Y = 0 := (hΦE Y p).symm.trans (congrArg Params.E hYp)
    subst hY
    refine ⟨p, iotaBlocks_injective_bla _ ?_⟩
    rw [iota_headDir_bla, ← hYp, hΦ, hcob0, zero_add]
  -- rank–nullity for the family: its kernel has dimension at most `s`
  have h2 := LinearMap.finrank_range_le ((headDirQKLin_bla β).coprod (headDirVOLin_bla β))
  rw [Module.finrank_prod, finrank_headFun_bla, ← two_mul] at h2
  have h12 := (Submodule.finrank_mono hker).trans h2
  rw [← jacobianRankBlocks_add_finrank_ker_bla 1 X β]
  exact Nat.add_le_add_left h12 _

/-- **Lemma A.27 (Small writes), fourth value, for attention blocks, under the conditions of its
proof:** let the network with `E = D = I` and the blocks of `β` satisfy the conditions of the
lemma, and let a token see itself and another token. For all small `τ ≠ 0`, the residual network
without an embedding and a readout has `fd(β_τ) = P − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`, with `P` the number of
parameters of the blocks. -/
theorem eventually_funDimBlocks_smallWrites_attention (t₁ t₂ : T) (h12 : t₁ ≠ t₂)
    (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (β : BlockParams (Arch.attention (T := T) (d := d) sees id H dh))
    (hβ : SmallWritesGenericAttention β.toParams) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimBlocks (Arch.attention sees id H dh) 1 (β.smallWrites τ)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
        = Module.finrank ℝ (BlockParams (Arch.attention (T := T) (d := d) sees id H dh)) := by
  classical
  -- `θ_τ = β.toParams.smallWrites τ` is `(β.smallWrites τ).toParams`, and
  -- `fd(θ_τ) + d² + s = P(θ_τ)` for all small `τ ≠ 0` (Lemma A.27, first value)
  filter_upwards [eventually_funDim_smallWrites_attention t₁ t₂ h12 hs2 hs1 β.toParams hβ]
    with τ hτ
  -- the reads of `β_τ` are those of `β`
  have hQ : ∀ ℓ (i : H ℓ), (((β.smallWrites τ).read ℓ).submatrix id
      fun k : dh ℓ => (i, Sum.inl k)).rank = Fintype.card (dh ℓ) := hβ.rank_Q
  have hV : ∀ ℓ (i : H ℓ), (((β.smallWrites τ).read ℓ).submatrix id
      fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank = Fintype.card (dh ℓ) := hβ.rank_V
  -- `≤`: step (a) on a batch that attains `fd(β_τ)`
  obtain ⟨n, X, hX⟩ := exists_jacobianRankBlocks_eq_funDimBlocks (S := 1) (β.smallWrites τ)
  have hup := jacobianRankBlocks_add_le_bla (β.smallWrites τ) hQ hV X
  -- `≥`: step (b)
  obtain ⟨m, Y, hY⟩ := exists_le_jacobianRankBlocks_bla (β.smallWrites τ) hQ hV hτ
  have hle := jacobianRankBlocks_le_funDimBlocks (S := 1) Y (β.smallWrites τ)
  omega

/-! ### Helpers for almost every parameter of the blocks -/

/-- Helper: the blocks of a network `θ` with `d_in = d_out = d`, with its embedding and its
readout moved into them: the reads `E W_read^ℓ` and the writes `W_write^ℓ D`. -/
private def blocksOf_bla (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) d d) :
    BlockParams (Arch.attention (T := T) (d := d) sees id H dh) :=
  ⟨0, fun ℓ => θ.E * θ.read ℓ, fun ℓ => θ.write ℓ * θ.D, 0⟩

/-- Helper: a submatrix of columns of `M N` is `M` times the submatrix of `N`. -/
private theorem submatrix_mul_cols_bla {m n p q : Type*} [Fintype n] (M : Matrix m n ℝ)
    (N : Matrix n p ℝ) (c : q → p) : (M * N).submatrix id c = M * N.submatrix id c :=
  Matrix.ext fun _ _ => rfl

/-- Helper: a submatrix of rows of `M N` is the submatrix of `M` times `N`. -/
private theorem submatrix_mul_rows_bla {m n p q : Type*} [Fintype n] (M : Matrix m n ℝ)
    (N : Matrix n p ℝ) (r : q → m) : (M * N).submatrix r id = M.submatrix r id * N :=
  Matrix.ext fun _ _ => rfl

/-- Helper: the matrix `B = E W_Q W_K^⊤ E^⊤ / √d_h` of a head of the network with `E = D = I` and
the blocks `blocksOf_bla θ` is that of `θ`. -/
private theorem headScore_blocksOf_bla
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) d d) (ℓ : Fin L) (i : H ℓ) :
    headScore (blocksOf_bla θ).toParams ℓ i = headScore θ ℓ i := by
  show (Real.sqrt (Fintype.card (dh ℓ)))⁻¹ •
      ((1 : Matrix d d ℝ) * ((θ.E * θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k))
        * ((θ.E * θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))ᵀ
        * (1 : Matrix d d ℝ)ᵀ) = headScore θ ℓ i
  rw [headScore, submatrix_mul_cols_bla, submatrix_mul_cols_bla, Matrix.transpose_mul,
    Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

/-- Helper: so is its matrix `C = E W_V W_O D`. -/
private theorem headValue_blocksOf_bla
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) d d) (ℓ : Fin L) (i : H ℓ) :
    headValue (blocksOf_bla θ).toParams ℓ i = headValue θ ℓ i := by
  show (1 : Matrix d d ℝ)
      * ((θ.E * θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
      * ((θ.write ℓ * θ.D).submatrix (fun k : dh ℓ => (i, k)) id) * (1 : Matrix d d ℝ)
    = headValue θ ℓ i
  rw [headValue, submatrix_mul_cols_bla, submatrix_mul_rows_bla, Matrix.one_mul, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

/-- Helper: if `θ` (with `d_in = d_out = d`) satisfies the conditions of Lemma A.27, so does the
network with `E = D = I` and the blocks `blocksOf_bla θ`: its heads have the same matrices `B`
and `C`, and its query, key, value and output matrices are those of `θ` multiplied by `E` or
`D`, which are square of rank `d`, hence invertible. -/
private theorem smallWritesGeneric_blocksOf_bla
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) d d)
    (hθ : SmallWritesGenericAttention θ) :
    SmallWritesGenericAttention (blocksOf_bla θ).toParams := by
  -- `E` and `D` are square of rank `d`, hence invertible
  have hE : IsUnit θ.E.det := (Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.mulVec_surjective_iff_isUnit.1 (Matrix.mulVec_surjective_iff_rank_eq_card.2
      hθ.rank_E))
  have hD : IsUnit θ.D.det := (Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.mulVec_surjective_iff_isUnit.1 (Matrix.mulVec_surjective_iff_rank_eq_card.2
      hθ.rank_D))
  refine
    { rank_E := ?_
      rank_D := ?_
      rank_Q := fun ℓ i => ?_
      rank_K := fun ℓ i => ?_
      rank_V := fun ℓ i => ?_
      rank_O := fun ℓ i => ?_
      exists_v := ?_ }
  · show (1 : Matrix d d ℝ).rank = _
    exact Matrix.rank_one
  · show (1 : Matrix d d ℝ).rank = _
    exact Matrix.rank_one
  · show ((θ.E * θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank = _
    rw [submatrix_mul_cols_bla, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hE]
    exact hθ.rank_Q ℓ i
  · show ((θ.E * θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k))).rank = _
    rw [submatrix_mul_cols_bla, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hE]
    exact hθ.rank_K ℓ i
  · show ((θ.E * θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank = _
    rw [submatrix_mul_cols_bla, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hE]
    exact hθ.rank_V ℓ i
  · show ((θ.write ℓ * θ.D).submatrix (fun k : dh ℓ => (i, k)) id).rank = _
    rw [submatrix_mul_rows_bla, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hD]
    exact hθ.rank_O ℓ i
  · -- the same `v` works, as the heads have the same `B` and `C`
    obtain ⟨v, h1, h2, h3⟩ := hθ.exists_v
    refine ⟨v, fun p => ?_, fun p q hpq r => ?_, fun p => ?_⟩
    · rw [headScore_blocksOf_bla]
      exact h1 p
    · rw [headScore_blocksOf_bla, headScore_blocksOf_bla]
      exact h2 p q hpq r
    · rw [headValue_blocksOf_bla]
      exact h3 p

/-- Helper: the family `β ↦ (F_β(x_i))_i` is real-analytic: the outputs of the network are
analytic in the parameters, and `β ↦ β.toParams` is affine. -/
private theorem analyticOnNhd_blocks_bla {n : ℕ} (X : Fin n → Matrix T d ℝ) :
    AnalyticOnNhd ℝ (fun β' : BlockParams (Arch.attention (T := T) (d := d) sees id H dh) =>
      fun i : Fin n => evalBlocks (Arch.attention sees id H dh) 1 β' (X i)) Set.univ := by
  -- `β.toParams = ι β + (I, 0, 0, I)`
  have hfun : (fun β' : BlockParams (Arch.attention (T := T) (d := d) sees id H dh) =>
        fun i : Fin n => evalBlocks (Arch.attention sees id H dh) 1 β' (X i))
      = fun β' => fun i => eval (Arch.attention sees id H dh) 1
          (LinearMap.toContinuousLinearMap (iotaBlocks_bla _) β'
            + (⟨1, fun _ => 0, fun _ => 0, 1⟩ :
              Params (Arch.attention (T := T) (d := d) sees id H dh) d d)) (X i) := by
    funext β' i
    exact congrArg (fun θ => eval (Arch.attention sees id H dh) 1 θ (X i)) (toParams_eq_bla β')
  rw [hfun]
  refine AnalyticOnNhd.pi fun i => ?_
  have h1 := analyticOnNhd_eval_params (Arch.attention (T := T) (d := d) sees id H dh) 1
    (fun ℓ => analyticOnNhd_f_attention sees id H dh ℓ) analyticOnNhd_id (dOut := d) (X i)
  have h2 : AnalyticOnNhd ℝ
      (fun β' : BlockParams (Arch.attention (T := T) (d := d) sees id H dh) =>
        LinearMap.toContinuousLinearMap (iotaBlocks_bla _) β'
          + (⟨1, fun _ => 0, fun _ => 0, 1⟩ :
            Params (Arch.attention (T := T) (d := d) sees id H dh) d d)) Set.univ :=
    fun β' _ =>
      ((LinearMap.toContinuousLinearMap (iotaBlocks_bla _)).analyticAt β').fun_add
        analyticAt_const
  have h3 := h1.comp h2 (Set.mapsTo_univ _ _)
  exact h3

omit [Fintype T] [DecidableEq d] in
/-- Helper (as `analyticOnNhd_det_uba` of `Dimension/UpperBoundAttention.lean`): the determinant
of a square matrix that depends linearly on the parameters is analytic in the parameters. -/
private theorem analyticOnNhd_det_bla {A : Arch T d L} {dIn dOut : Type*} [Fintype dIn]
    [Fintype dOut] {n : Type*} [Fintype n] [DecidableEq n]
    (Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ) :
    AnalyticOnNhd ℝ (fun θ => (Φ θ).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ =>
      analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ (σ i) i).comp Φ))

/-- Helper (as `exists_submatrix_eq_one_uba`): a matrix whose submatrix on the rows `r` and the
columns `c` (both injective) is the identity. -/
private theorem exists_submatrix_eq_one_bla {m p n : Type*} [DecidableEq n] {r : n → m}
    (hr : Function.Injective r) {c : n → p} (hc : Function.Injective c) :
    ∃ M : Matrix m p ℝ, M.submatrix r c = 1 := by
  classical
  refine ⟨Matrix.of fun a b => if ∃ x, r x = a ∧ c x = b then 1 else 0, ?_⟩
  ext x y
  simp [Matrix.one_apply, hr.eq_iff, hc.eq_iff]

omit [Fintype T] [DecidableEq d] in
/-- Helper (as `ae_rank_read_cols_uba`): at generic parameters, `n ≤ d` distinct columns `c` of
the read of block `ℓ` form a matrix of rank `n`. -/
private theorem ae_rank_read_cols_bla {A : Arch T d L} {dIn dOut : Type*} [Fintype dIn]
    [Fintype dOut] (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*}
    [Fintype n] [DecidableEq n] {c : n → A.r ℓ} (hc : Function.Injective c)
    (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.read ℓ).submatrix id c).rank = Fintype.card n := by
  -- `n` rows `ρ`, and the square submatrix of the read on the rows `ρ` and the columns `c`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_bla ρ.injective hc
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
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_bla Φ) hne] with θ hθ
  -- an invertible `n × n` submatrix gives rank `≥ n`, and the rank is at most the width `n`
  have h1 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank = Fintype.card n :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hθ))
  have h2 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank
      ≤ ((θ.read ℓ).submatrix id c).rank :=
    Matrix.rank_submatrix_le _ ρ id
  have h3 := Matrix.rank_le_card_width ((θ.read ℓ).submatrix id c)
  omega

omit [DecidableEq d] in
/-- Helper (as `ae_rank_QV_uba`): at generic parameters the query matrix and the value matrix of
every head have rank `d_h`, when `d_h ≤ d`. -/
private theorem ae_rank_QV_bla {dIn dOut : Type*} [Fintype dIn] [Fintype dOut]
    {χ : Matrix T d ℝ → Matrix T d ℝ}
    (μ : Measure (Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut))
    [μ.IsAddHaarMeasure] (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, (∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ)) ∧
      ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ) := by
  classical
  -- finitely many conditions, two for each head of each block
  refine (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_).and
    (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_)
  · exact ae_rank_read_cols_bla μ ℓ (c := fun k : dh ℓ => (i, Sum.inl k))
      (fun _ _ h => Sum.inl_injective (Prod.mk.inj h).2) (hdh ℓ)
  · exact ae_rank_read_cols_bla μ ℓ (c := fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
      (fun _ _ h => Sum.inr_injective (Sum.inr_injective (Prod.mk.inj h).2)) (hdh ℓ)

/-- **Corollary 4.10 (ii) of the skips paper (attention-only transformers without an embedding
and a readout):** without normalization, with `d ≥ 2`, `L` attention blocks with heads of width
`1 ≤ d_h ≤ d` and a token that sees itself and another token, at almost every parameter of the
blocks the residual network without an embedding and a readout has the functional dimension
`P − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDimBlocks_attention_residual
    (μ : Measure (BlockParams (Arch.attention (T := T) (d := d) sees id H dh)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.attention sees id H dh) 1 β
        + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
      = Module.finrank ℝ (BlockParams (Arch.attention (T := T) (d := d) sees id H dh)) := by
  classical
  -- one network `θ₀` with `d_in = d_out = d` and the conditions of Lemma A.27
  obtain ⟨θ₀, hθ₀⟩ := (ae_smallWritesGenericAttention
    (Measure.addHaar : Measure (Params (Arch.attention (T := T) (d := d) sees id H dh) d d))
    hd le_rfl le_rfl hdh hdh0).exists
  -- the blocks `β₀ = (E W_read, W_write D)` and one small `τ ≠ 0`: `fd(β₀_τ) = P - s`
  obtain ⟨τ, hτ⟩ := (eventually_funDimBlocks_smallWrites_attention t₁ t₂ h12 hs2 hs1
    (blocksOf_bla θ₀) (smallWritesGeneric_blocksOf_bla θ₀ hθ₀)).exists
  -- a batch `X` on which the rank at `β₀_τ` is `fd(β₀_τ)`
  obtain ⟨n, X, hX⟩ := exists_jacobianRankBlocks_eq_funDimBlocks (S := 1)
    ((blocksOf_bla θ₀).smallWrites τ)
  -- at almost every `β` the rank on `X` is at least that at `β₀_τ` (the family is analytic),
  -- and the query and the value matrix of every head have rank `d_h`
  filter_upwards [ae_finrank_range_fderiv_ge_of_isPreconnected μ isOpen_univ
      isPreconnected_univ (by simp) (analyticOnNhd_blocks_bla X)
      (Set.mem_univ ((blocksOf_bla θ₀).smallWrites τ)),
    ae_rank_QV_bla μ hdh] with β h1 h2
  have h1' : jacobianRankBlocks (Arch.attention sees id H dh) 1 X
        ((blocksOf_bla θ₀).smallWrites τ)
      ≤ jacobianRankBlocks (Arch.attention sees id H dh) 1 X β := h1
  -- `≥`: the rank on `X` at `β` is at most `fd(β)`; `≤`: step (a) on a batch attaining `fd(β)`
  have hle := jacobianRankBlocks_le_funDimBlocks (S := 1) X β
  obtain ⟨m, Y, hY⟩ := exists_jacobianRankBlocks_eq_funDimBlocks (S := 1) β
  have hup := jacobianRankBlocks_add_le_bla β h2.1 h2.2 Y
  omega

/-- **Corollary 4.10 (ii) in the setting of the main text:** `Hn` heads of total width
`H d_h = d` in every block. At almost every parameter of the blocks, the residual network without
an embedding and a readout has the functional dimension `L (4 d² − 2 d² / H)`. -/
theorem ae_funDimBlocks_attention_residual_of_width (Hn : ℕ)
    (μ : Measure (BlockParams (Arch.attention (T := T) (d := d) sees id H dh)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hHn : ∀ ℓ, Fintype.card (H ℓ) = Hn)
    (hHd : ∀ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) = Fintype.card d)
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.attention sees id H dh) 1 β
      = L * (4 * Fintype.card d ^ 2 - 2 * Fintype.card d ^ 2 / Hn) := by
  -- every block has heads of width `1 ≤ d_h ≤ d`, since `H d_h = d ≥ 2`
  have hpos : ∀ ℓ, 0 < Fintype.card (H ℓ) ∧ 0 < Fintype.card (dh ℓ) := fun ℓ => by
    have h : 0 < Fintype.card (H ℓ) * Fintype.card (dh ℓ) := by rw [hHd ℓ]; omega
    exact ⟨Nat.pos_of_mul_pos_right h, Nat.pos_of_mul_pos_left h⟩
  have hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d := fun ℓ =>
    hHd ℓ ▸ Nat.le_mul_of_pos_left _ (hpos ℓ).1
  -- `P = 4 L d²`: a read has `3 H d_h = 3 d` columns and a write `H d_h = d` rows
  have hP : Module.finrank ℝ (BlockParams (Arch.attention (T := T) (d := d) sees id H dh))
      = L * (4 * Fintype.card d ^ 2) := by
    rw [finrank_blockParams]
    have hr : ∀ ℓ, Fintype.card d
        * Fintype.card ((Arch.attention (T := T) (d := d) sees id H dh).r ℓ)
          = 3 * Fintype.card d ^ 2 := fun ℓ => by
      show Fintype.card d * Fintype.card (H ℓ × (dh ℓ ⊕ (dh ℓ ⊕ dh ℓ))) = _
      rw [Fintype.card_prod, Fintype.card_sum, Fintype.card_sum]
      calc _ = 3 * (Fintype.card d * (Fintype.card (H ℓ) * Fintype.card (dh ℓ))) := by ring
        _ = _ := by rw [hHd ℓ]; ring
    have hw : ∀ ℓ, Fintype.card ((Arch.attention (T := T) (d := d) sees id H dh).w ℓ)
        * Fintype.card d = Fintype.card d ^ 2 := fun ℓ => by
      show Fintype.card (H ℓ × dh ℓ) * Fintype.card d = _
      rw [Fintype.card_prod, hHd ℓ, sq]
    rw [Finset.sum_congr rfl fun ℓ _ => hr ℓ, Finset.sum_congr rfl fun ℓ _ => hw ℓ]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  filter_upwards [ae_funDimBlocks_attention_residual μ hd hdh (fun ℓ => (hpos ℓ).2) t₁ t₂ h12
    hs2 hs1] with β hβ
  rw [hP] at hβ
  rcases Nat.eq_zero_or_pos L with hL | hL
  · -- no blocks: both sides are `0`
    subst hL
    simp only [Fin.sum_univ_zero, mul_zero, zero_mul, add_zero] at hβ ⊢
    omega
  · -- `s = 2 L (d² / H)`, as `H d_h² = d² / H` in every block
    have hHn0 : 0 < Hn := hHn ⟨0, hL⟩ ▸ (hpos ⟨0, hL⟩).1
    have hterm : ∀ ℓ, Fintype.card d ^ 2
        = Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 * Hn := fun ℓ => by
      rw [← hHd ℓ, ← hHn ℓ]
      ring
    have hdvd : Hn ∣ Fintype.card d ^ 2 := Dvd.intro_left _ (hterm ⟨0, hL⟩).symm
    have hs : ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
        = L * (Fintype.card d ^ 2 / Hn) := by
      rw [Finset.sum_congr rfl fun ℓ _ => (Nat.div_eq_of_eq_mul_left hHn0 (hterm ℓ)).symm,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have h2 : 2 * Fintype.card d ^ 2 / Hn = 2 * (Fintype.card d ^ 2 / Hn) :=
      Nat.mul_div_assoc _ hdvd
    rw [hs] at hβ
    rw [h2, Nat.mul_sub, show L * (2 * (Fintype.card d ^ 2 / Hn))
      = 2 * (L * (Fintype.card d ^ 2 / Hn)) by ring]
    omega

end Skips
