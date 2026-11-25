import SkipsLean.Residual.BlocksAloneGeneral
import SkipsLean.Residual.DepthTransformer
import SkipsLean.Residual.DepthTransformerGated

/-!
# Residual networks of attention blocks and MLP blocks without an embedding and a readout

Paper (skips paper), Lemma A.27: "let each block, in any order and of any width, be an attention
block with heads of width at most `d_model`, causal or not, on sequences of at least two tokens,
or an MLP block, with all MLP blocks tanh, all GELU, all SwiGLU or all GeGLU blocks. […] For all
small `τ ≠ 0`, the residual network has […] `fd(θ_τ) = P − s` (no embedding, readout, biases or
normalization)", where "`s` counts the changes of basis inside the heads and the rescalings of the
values of gated units". Its proof for attention blocks: "So the flat directions form a space of
dimension `d_model² + s`, and of dimension `s` without an embedding and a readout."

Here, for the networks `Arch.attentionMlp sees σ id H dh hid` and
`Arch.attentionGated sees σ id H dh hid` (`Network/Transformer.lean`: block `ℓ` with the heads
`H ℓ` of width `dh ℓ` and the hidden units `hid ℓ`; an attention block if `hid ℓ` is empty, an MLP
block if `H ℓ` is empty), a token that sees itself and another token, `d ≥ 2`, and the network
without an embedding and a readout of `Residual/BlocksAlone.lean`:

* `eventually_funDimBlocks_smallWrites_attentionMlp`, `…_attentionGated`: the fourth value under
  the conditions of the proof of the lemma at `E = D = I`, on the two parts of the parameters;
  `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}²`, and with gated units `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}² + ∑_ℓ d_hidden,ℓ`;
* `ae_funDimBlocks_attentionMlp_residual`, `ae_funDimBlocks_attentionGated_residual`: `fd = P − s`
  at almost every parameter of the blocks (heads of width `1 ≤ d_h ≤ d`);
* the named kinds: attention with tanh, GELU, SwiGLU and GeGLU blocks.

They follow from the first value at `β.toParams`
(`eventually_funDim_smallWrites_attentionMlp`, `…_attentionGated`) and
`funDimBlocks_add_finrank_eq_of_funDim_toParams` (`Residual/BlocksAloneGeneral.lean`), with `R`
the directions of the changes of basis inside the heads and of the rescalings of the values. The
twins for one kind of block: `Residual/BlocksAloneAttention.lean`, `Residual/BlocksAloneMlp.lean`,
`Residual/BlocksAloneGated.lean`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ σ' : ℝ → ℝ}

/-! ### Helpers: the family of the blocks alone, for any blocks

`β.toParams = blockDir β + (I, 0, 0, I)`, so by the chain rule the Jacobian of the family
`β ↦ (F_β(x_i))_i` is the Jacobian of the network at `β.toParams` composed with `blockDir`. -/

omit [Fintype T] [Fintype d] [DecidableEq d] in
/-- Helper (as the private `iotaBlocks_injective_bla` of `Residual/BlocksAloneAttention.lean`):
`blockDir` is injective (it keeps the reads and the writes; `E` and `D` of the blocks are empty
matrices). -/
private theorem blockDir_injective_bat (A : Arch T d L) : Function.Injective (blockDir A) := by
  intro η ξ h
  apply Params.ext'
  · exact Matrix.ext fun i => i.elim
  · intro ℓ
    exact congrArg (fun θ : Params A d d => θ.read ℓ) h
  · intro ℓ
    exact congrArg (fun θ : Params A d d => θ.write ℓ) h
  · exact Matrix.ext fun _ j => j.elim

omit [Fintype T] [Fintype d] in
/-- Helper (as `toParams_eq_bla`): `β.toParams = blockDir β + (I, 0, 0, I)`. -/
private theorem toParams_eq_bat {A : Arch T d L} (β : BlockParams A) :
    β.toParams = blockDir A β + ⟨1, fun _ => 0, fun _ => 0, 1⟩ := by
  apply Params.ext'
  · exact (zero_add (1 : Matrix d d ℝ)).symm
  · intro ℓ
    exact (add_zero (β.read ℓ)).symm
  · intro ℓ
    exact (add_zero (β.write ℓ)).symm
  · exact (zero_add (1 : Matrix d d ℝ)).symm

omit [Fintype T] in
/-- Helper (as `fderiv_blocks_bla`): the chain rule for the family `β' ↦ (F_{β'}(x_i))_i`: its
derivative at `β` is the derivative of the outputs of the network at `β.toParams`, composed with
`blockDir`. -/
private theorem fderiv_blocks_bat {A : Arch T d L} (S : Fin L → Matrix d d ℝ) {n : ℕ}
    (X : Fin n → Matrix T d ℝ) (β : BlockParams A)
    (hdiff : DifferentiableAt ℝ (evalBatch A S X) β.toParams) :
    fderiv ℝ (fun β' : BlockParams A => fun i : Fin n => evalBlocks A S β' (X i)) β
      = (fderiv ℝ (evalBatch A S X) β.toParams).comp
          (LinearMap.toContinuousLinearMap (blockDir A)) := by
  -- `β' ↦ β'.toParams` is affine, with the linear part `blockDir`
  have haff : HasFDerivAt (fun β' : BlockParams A => β'.toParams)
      (LinearMap.toContinuousLinearMap (blockDir A)) β :=
    ((LinearMap.toContinuousLinearMap (blockDir A)).hasFDerivAt.add_const
      (⟨1, fun _ => 0, fun _ => 0, 1⟩ : Params A d d)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun β' => toParams_eq_bat β')
  have h := hdiff.hasFDerivAt.comp β haff
  exact h.fderiv

omit [Fintype T] in
/-- Helper (as `jacobianRankBlocks_add_finrank_ker_bla`): rank–nullity for the Jacobian of the
family on a batch. -/
private theorem jacobianRankBlocks_add_finrank_ker_bat {A : Arch T d L}
    (S : Fin L → Matrix d d ℝ) {n : ℕ} (X : Fin n → Matrix T d ℝ) (β : BlockParams A) :
    jacobianRankBlocks A S X β + Module.finrank ℝ (LinearMap.ker
        (fderiv ℝ (fun β' : BlockParams A => fun i : Fin n => evalBlocks A S β' (X i))
          β).toLinearMap)
      = Module.finrank ℝ (BlockParams A) :=
  LinearMap.finrank_range_add_finrank_ker _

omit [Fintype T] in
/-- Helper (as `mem_ker_blocks_iff_bla`): `η` is in the kernel of the Jacobian of the family on a
batch if and only if `blockDir η` is in the kernel of the Jacobian of the network at `β.toParams`
on the same batch. -/
private theorem mem_ker_blocks_iff_bat {A : Arch T d L} (S : Fin L → Matrix d d ℝ) {n : ℕ}
    (X : Fin n → Matrix T d ℝ) (β : BlockParams A)
    (hdiff : DifferentiableAt ℝ (evalBatch A S X) β.toParams) (η : BlockParams A) :
    η ∈ LinearMap.ker (fderiv ℝ (fun β' : BlockParams A => fun i : Fin n =>
        evalBlocks A S β' (X i)) β).toLinearMap
      ↔ blockDir A η
        ∈ LinearMap.ker (fderiv ℝ (evalBatch A S X) β.toParams).toLinearMap := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, fderiv_blocks_bat S X β hdiff]
  rfl

omit [DecidableEq d] in
/-- Helper (as `flat_le_ker_bla`): the flat directions are in the kernel of the Jacobian on every
batch. -/
private theorem flat_le_ker_bat {A : Arch T d L} {S : Fin L → Matrix d d ℝ} (θ : Params A d d)
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

/-- Helper: if the directions `blockDir η`, `η ∈ R`, are flat for the network at `β.toParams`,
the Jacobian of the family has rank at most `P − dim R` on every batch: by the chain rule its
kernel contains `R`; rank–nullity. -/
private theorem jacobianRankBlocks_add_le_bat {A : Arch T d L} {S : Fin L → Matrix d d ℝ}
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (hχ : Differentiable ℝ A.χ) (β : BlockParams A)
    (R : Submodule ℝ (BlockParams A)) (hR : ∀ η ∈ R, blockDir A η ∈ flat A S β.toParams)
    {n : ℕ} (X : Fin n → Matrix T d ℝ) :
    jacobianRankBlocks A S X β + Module.finrank ℝ R ≤ Module.finrank ℝ (BlockParams A) := by
  -- the outputs are differentiable in the parameters
  have hd : ∀ x : Matrix T d ℝ,
      DifferentiableAt ℝ (fun θ' : Params A d d => eval A S θ' x) β.toParams :=
    fun x => differentiable_eval hf hχ x β.toParams
  have hdB : DifferentiableAt ℝ (evalBatch A S X) β.toParams :=
    differentiableAt_pi.2 fun i => hd (X i)
  -- `R` is in the kernel of the Jacobian of the family
  have hker : R ≤ LinearMap.ker (fderiv ℝ
      (fun β' : BlockParams A => fun i : Fin n => evalBlocks A S β' (X i)) β).toLinearMap := by
    intro η hη
    rw [mem_ker_blocks_iff_bat S X β hdB]
    exact flat_le_ker_bat _ hd X (hR η hη)
  have h1 := Submodule.finrank_mono hker
  rw [← jacobianRankBlocks_add_finrank_ker_bat S X β]
  exact Nat.add_le_add_left h1 _

omit [Fintype T] [DecidableEq d] in
/-- Helper (as the private `ED_eq_zero_of_mem_span_ibl` of `Symmetry/InsideBlocksSum.lean`): the
directions spanned by directions of symmetries inside the blocks have `E` and `D` components
`0`. -/
private theorem ED_eq_zero_of_mem_span_bat {A : Arch T d L} {θ v : Params A d d}
    (hv : v ∈ Submodule.span ℝ {η | InsideBlocks A θ η}) : v.E = 0 ∧ v.D = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨InsideBlocks.E_eq_zero hx, InsideBlocks.D_eq_zero hx⟩
  | zero => exact ⟨rfl, rfl⟩
  | add x y _ _ hx hy =>
    exact ⟨by rw [Params.add_E, hx.1, hy.1, add_zero], by rw [Params.add_D, hx.2, hy.2, add_zero]⟩
  | smul a x _ hx =>
    exact ⟨by rw [Params.smul_E, hx.1, smul_zero], by rw [Params.smul_D, hx.2, smul_zero]⟩

/-- Helper: a space `V` spanned by directions of symmetries inside the blocks at `β.toParams` is
`blockDir R` for a space `R` of directions of the blocks of the same dimension (the directions of
`V` have no component at `E` and `D`), and the directions `blockDir η`, `η ∈ R`, are flat for
every stream. -/
private theorem exists_blocks_of_insideBlocks_bat {A : Arch T d L} (β : BlockParams A)
    (V : Submodule ℝ (Params A d d))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A β.toParams η}) :
    ∃ R : Submodule ℝ (BlockParams A),
      (∀ η ∈ R, ∀ S : Fin L → Matrix d d ℝ, blockDir A η ∈ flat A S β.toParams) ∧
      Module.finrank ℝ R = Module.finrank ℝ V := by
  -- `V` lies in the range of `blockDir`
  have hle : V ≤ LinearMap.range (blockDir A) := by
    intro v hv
    obtain ⟨hE, hD⟩ := ED_eq_zero_of_mem_span_bat (hV hv)
    refine ⟨⟨0, v.read, v.write, 0⟩, ?_⟩
    apply Params.ext'
    · exact hE.symm
    · intro ℓ
      rfl
    · intro ℓ
      rfl
    · exact hD.symm
  refine ⟨V.comap (blockDir A), fun η hη S => ?_, ?_⟩
  · -- the directions spanned by symmetries inside the blocks are flat
    exact Submodule.span_le.2 (fun _ h => InsideBlocks.mem_flat h S) (hV hη)
  · -- `blockDir` is injective and maps `R` onto `V`
    rw [(Submodule.equivMapOfInjective _ (blockDir_injective_bat A) _).finrank_eq,
      Submodule.map_comap_eq_of_le hle]

/-- Helper: the fourth value from the first, for a space `V` spanned by directions of symmetries
inside the blocks at `β.toParams`: if `fd(β.toParams) + d² + dim V = P`, the network without an
embedding and a readout has `fd(β) + dim V = P_blocks`. -/
private theorem funDimBlocks_add_eq_bat {A : Arch T d L} (hA : A.χ = id)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (β : BlockParams A) (V : Submodule ℝ (Params A d d))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A β.toParams η})
    (hfd : funDim A 1 β.toParams + (Fintype.card d ^ 2 + Module.finrank ℝ V)
      = Module.finrank ℝ (Params A d d)) :
    funDimBlocks A 1 β + Module.finrank ℝ V = Module.finrank ℝ (BlockParams A) := by
  obtain ⟨R, hR, hdim⟩ := exists_blocks_of_insideBlocks_bat β V hV
  rw [← hdim] at hfd ⊢
  exact funDimBlocks_add_finrank_eq_of_funDim_toParams hA hf β R (fun η hη => hR η hη 1) hfd

/-- Helper: for a space `V` spanned by directions of symmetries inside the blocks at
`β.toParams`, the Jacobian of the family has rank at most `P − dim V` on every batch. -/
private theorem jacobianRankBlocks_add_le_of_insideBlocks_bat {A : Arch T d L}
    {S : Fin L → Matrix d d ℝ} (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ))
    (hχ : Differentiable ℝ A.χ) (β : BlockParams A) (V : Submodule ℝ (Params A d d))
    (hV : V ≤ Submodule.span ℝ {η | InsideBlocks A β.toParams η}) {n : ℕ}
    (X : Fin n → Matrix T d ℝ) :
    jacobianRankBlocks A S X β + Module.finrank ℝ V ≤ Module.finrank ℝ (BlockParams A) := by
  obtain ⟨R, hR, hdim⟩ := exists_blocks_of_insideBlocks_bat β V hV
  rw [← hdim]
  exact jacobianRankBlocks_add_le_bat hf hχ β R (fun η hη => hR η hη S) X

/-- **Lemma A.27 (Small writes), fourth value, for networks of attention blocks and MLP blocks
with `s = 0` for the hidden units, under the conditions of its proof:** let the network with
`E = D = I` and the blocks of `β` satisfy the conditions of the lemma on its two parts, and let a
token see itself and another token. For all small `τ ≠ 0`, the residual network without an
embedding and a readout has `fd(β_τ) = P − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`, with `P` the number of parameters
of the blocks. -/
theorem eventually_funDimBlocks_smallWrites_attentionMlp (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (β : BlockParams (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid))
    (hβa : SmallWritesGenericAttention β.toParams.sumFst)
    (hβm : SmallWritesGeneric β.toParams.sumSnd) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimBlocks (Arch.attentionMlp sees σ id H dh hid) 1 (β.smallWrites τ)
          + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
        = Module.finrank ℝ
            (BlockParams (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid)) := by
  classical
  -- the blocks of the sum are differentiable
  have hf : ∀ ℓ, Differentiable ℝ
      ((Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid).f ℓ) := fun ℓ =>
    differentiable_f_sum (differentiable_f_attention sees id H dh ℓ)
      (differentiable_f_mlp (fun z => (hσ z).differentiableAt) ℓ)
  -- `(β_τ).toParams` is `(β.toParams)_τ`, and `fd + d² + s = P` there (first value)
  filter_upwards [eventually_funDim_smallWrites_attentionMlp hσ hσa hU t₁ t₂ h12 hs2 hs1
    β.toParams hβa hβm] with τ hτ
  -- `V_A`: the changes of basis inside the heads at `β_τ`, whose reads are those of `β`;
  -- `V_B = 0` for the MLP part; their lift to the sum has dimension `s`
  obtain ⟨VA, hVA, -, hdimA⟩ :=
    attn_part_ubt (BlockParams.toParams (β.smallWrites τ)).sumFst hβa.rank_Q hβa.rank_V
  have hV := sup_le_span_ibl (BlockParams.toParams (β.smallWrites τ)) VA ⊥ hVA bot_le
  have hdim := finrank_sup_ibl (BlockParams.toParams (β.smallWrites τ)) VA ⊥ hVA
  rw [hdimA, finrank_bot, add_zero] at hdim
  -- the fourth value from the first
  have h := funDimBlocks_add_eq_bat rfl hf (β.smallWrites τ) _ hV (by rw [hdim]; exact hτ)
  rwa [hdim] at h

/-! ### Helpers: the blocks of a network with an embedding and a readout -/

/-- Helper (as the private `blocksOf_bla`, for any blocks): the blocks of a network `θ` with
`d_in = d_out = d`, with its embedding and its readout moved into them: the reads `E W_read^ℓ`
and the writes `W_write^ℓ D`. -/
private def blocksOf_bat {A : Arch T d L} (θ : Params A d d) : BlockParams A :=
  ⟨0, fun ℓ => θ.E * θ.read ℓ, fun ℓ => θ.write ℓ * θ.D, 0⟩

omit [Fintype T] in
/-- Helper: the first part of the network with `E = D = I` and the blocks `blocksOf_bat θ` is the
network with `E = D = I` and the blocks of the first part of `θ`. -/
private theorem toParams_blocksOf_sumFst_bat {A B : Arch T d L} (θ : Params (A.sum B) d d) :
    (blocksOf_bat θ).toParams.sumFst = (blocksOf_bat θ.sumFst).toParams := by
  apply Params.ext'
  · rfl
  · intro ℓ
    exact Matrix.ext fun _ _ => rfl
  · intro ℓ
    exact Matrix.ext fun _ _ => rfl
  · rfl

omit [Fintype T] in
/-- Helper: so is the second part. -/
private theorem toParams_blocksOf_sumSnd_bat {A B : Arch T d L} (θ : Params (A.sum B) d d) :
    (blocksOf_bat θ).toParams.sumSnd = (blocksOf_bat θ.sumSnd).toParams := by
  apply Params.ext'
  · rfl
  · intro ℓ
    exact Matrix.ext fun _ _ => rfl
  · intro ℓ
    exact Matrix.ext fun _ _ => rfl
  · rfl

/-- Helper (as `submatrix_mul_cols_bla`): a submatrix of columns of `M N` is `M` times the
submatrix of `N`. -/
private theorem submatrix_mul_cols_bat {m n p q : Type*} [Fintype n] (M : Matrix m n ℝ)
    (N : Matrix n p ℝ) (c : q → p) : (M * N).submatrix id c = M * N.submatrix id c :=
  Matrix.ext fun _ _ => rfl

/-- Helper (as `submatrix_mul_rows_bla`): a submatrix of rows of `M N` is the submatrix of `M`
times `N`. -/
private theorem submatrix_mul_rows_bat {m n p q : Type*} [Fintype n] (M : Matrix m n ℝ)
    (N : Matrix n p ℝ) (r : q → m) : (M * N).submatrix r id = M.submatrix r id * N :=
  Matrix.ext fun _ _ => rfl

/-- Helper (as `headScore_blocksOf_bla`): the matrix `B` of a head of the network with
`E = D = I` and the blocks `blocksOf_bat θ` is that of `θ`. -/
private theorem headScore_blocksOf_bat
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) d d) (ℓ : Fin L) (i : H ℓ) :
    headScore (blocksOf_bat θ).toParams ℓ i = headScore θ ℓ i := by
  show (Real.sqrt (Fintype.card (dh ℓ)))⁻¹ •
      ((1 : Matrix d d ℝ) * ((θ.E * θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k))
        * ((θ.E * θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k)))ᵀ
        * (1 : Matrix d d ℝ)ᵀ) = headScore θ ℓ i
  rw [headScore, submatrix_mul_cols_bat, submatrix_mul_cols_bat, Matrix.transpose_mul,
    Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

/-- Helper (as `headValue_blocksOf_bla`): so is its matrix `C = E W_V W_O D`. -/
private theorem headValue_blocksOf_bat
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) d d) (ℓ : Fin L) (i : H ℓ) :
    headValue (blocksOf_bat θ).toParams ℓ i = headValue θ ℓ i := by
  show (1 : Matrix d d ℝ)
      * ((θ.E * θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k)))
      * ((θ.write ℓ * θ.D).submatrix (fun k : dh ℓ => (i, k)) id) * (1 : Matrix d d ℝ)
    = headValue θ ℓ i
  rw [headValue, submatrix_mul_cols_bat, submatrix_mul_rows_bat, Matrix.one_mul, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

/-- Helper (as `smallWritesGeneric_blocksOf_bla`): if `θ` satisfies the conditions of Lemma A.27
for attention blocks, so does the network with `E = D = I` and the blocks `blocksOf_bat θ`: its
heads have the same matrices `B` and `C`, and its query, key, value and output matrices are those
of `θ` multiplied by `E` or `D`, which are invertible. -/
private theorem smallWritesGenericAttention_blocksOf_bat
    (θ : Params (Arch.attention (T := T) (d := d) sees id H dh) d d)
    (hθ : SmallWritesGenericAttention θ) :
    SmallWritesGenericAttention (blocksOf_bat θ).toParams := by
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
    rw [submatrix_mul_cols_bat, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hE]
    exact hθ.rank_Q ℓ i
  · show ((θ.E * θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inl k))).rank = _
    rw [submatrix_mul_cols_bat, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hE]
    exact hθ.rank_K ℓ i
  · show ((θ.E * θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank = _
    rw [submatrix_mul_cols_bat, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hE]
    exact hθ.rank_V ℓ i
  · show ((θ.write ℓ * θ.D).submatrix (fun k : dh ℓ => (i, k)) id).rank = _
    rw [submatrix_mul_rows_bat, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hD]
    exact hθ.rank_O ℓ i
  · -- the same `v` works, as the heads have the same `B` and `C`
    obtain ⟨v, h1, h2, h3⟩ := hθ.exists_v
    refine ⟨v, fun p => ?_, fun p q hpq r => ?_, fun p => ?_⟩
    · rw [headScore_blocksOf_bat]
      exact h1 p
    · rw [headScore_blocksOf_bat, headScore_blocksOf_bat]
      exact h2 p q hpq r
    · rw [headValue_blocksOf_bat]
      exact h3 p

omit [Fintype T] in
/-- Helper: if `θ` satisfies the conditions of Lemma A.27 for MLP blocks, so does the network with
`E = D = I` and the blocks `blocksOf_bat θ`: it has the same `E W_read^ℓ` and `W_write^ℓ D`. -/
private theorem smallWritesGeneric_blocksOf_bat
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) d d) (hθ : SmallWritesGeneric θ) :
    SmallWritesGeneric (blocksOf_bat θ).toParams := by
  have hER : ∀ ℓ, (blocksOf_bat θ).toParams.E * (blocksOf_bat θ).toParams.read ℓ
      = θ.E * θ.read ℓ := fun ℓ => Matrix.one_mul _
  have hWD : ∀ ℓ, (blocksOf_bat θ).toParams.write ℓ * (blocksOf_bat θ).toParams.D
      = θ.write ℓ * θ.D := fun ℓ => Matrix.mul_one _
  refine ⟨?_, ?_, fun ℓ i => ?_, fun ℓ i => ?_, fun p q hpq r => ?_⟩
  · show (1 : Matrix d d ℝ).rank = _
    exact Matrix.rank_one
  · show (1 : Matrix d d ℝ).rank = _
    exact Matrix.rank_one
  · rw [hWD]
    exact hθ.row_ne_zero ℓ i
  · rw [hER]
    exact hθ.col_ne_zero ℓ i
  · rw [hER, hER]
    exact hθ.col_not_collinear p q hpq r

omit [Fintype T] in
/-- Helper: if `θ` satisfies the conditions of Lemma A.27 for gated blocks, so does the network
with `E = D = I` and the blocks `blocksOf_bat θ`: it has the same `E W_read^ℓ` and
`W_write^ℓ D`. -/
private theorem smallWritesGenericGated_blocksOf_bat
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) d d) (hθ : SmallWritesGenericGated θ) :
    SmallWritesGenericGated (blocksOf_bat θ).toParams := by
  have hER : ∀ ℓ, (blocksOf_bat θ).toParams.E * (blocksOf_bat θ).toParams.read ℓ
      = θ.E * θ.read ℓ := fun ℓ => Matrix.one_mul _
  have hWD : ∀ ℓ, (blocksOf_bat θ).toParams.write ℓ * (blocksOf_bat θ).toParams.D
      = θ.write ℓ * θ.D := fun ℓ => Matrix.mul_one _
  refine ⟨?_, ?_, fun ℓ i => ?_, fun ℓ i => ?_, fun p q hpq r => ?_, fun ℓ i => ?_⟩
  · show (1 : Matrix d d ℝ).rank = _
    exact Matrix.rank_one
  · show (1 : Matrix d d ℝ).rank = _
    exact Matrix.rank_one
  · rw [hWD]
    exact hθ.row_ne_zero ℓ i
  · rw [hER]
    exact hθ.gate_ne_zero ℓ i
  · rw [hER, hER]
    exact hθ.gate_not_collinear p q hpq r
  · rw [hER]
    exact hθ.value_ne_zero ℓ i

/-- **Lemma A.27, fourth value, at generic parameters, for networks of attention blocks and MLP
blocks with `s = 0` for the hidden units:** without normalization, with `d ≥ 2`, heads of width
`1 ≤ d_h ≤ d`, blocks of any widths and a token that sees itself and another token, at almost
every parameter of the blocks the residual network without an embedding and a readout has the
functional dimension `P − 2 ∑_ℓ H_ℓ d_{h,ℓ}²`. -/
theorem ae_funDimBlocks_attentionMlp_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (BlockParams (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.attentionMlp sees σ id H dh hid) 1 β
        + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
      = Module.finrank ℝ
          (BlockParams (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid)) := by
  classical
  -- the blocks of the sum are differentiable and analytic
  have hf : ∀ ℓ, Differentiable ℝ
      ((Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid).f ℓ) := fun ℓ =>
    differentiable_f_sum (differentiable_f_attention sees id H dh ℓ)
      (differentiable_f_mlp (fun z => (hσ z).differentiableAt) ℓ)
  have hfa : ∀ ℓ, AnalyticOnNhd ℝ
      ((Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid).f ℓ) Set.univ := fun ℓ =>
    analyticOnNhd_f_sum (analyticOnNhd_f_attention sees id H dh ℓ) (analyticOnNhd_f_mlp hσa ℓ)
  -- one network `θ₀` with `d_in = d_out = d` and the conditions of Lemma A.27 on its two parts
  obtain ⟨θ₀, hθa, hθm⟩ := (ae_smallWritesGeneric_attentionMlp
    (Measure.addHaar :
      Measure (Params (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) d d))
    hd le_rfl le_rfl hdh hdh0).exists
  -- the blocks `β₀ = (E W_read, W_write D)` have them at `E = D = I`
  have hβa : SmallWritesGenericAttention (blocksOf_bat θ₀).toParams.sumFst := by
    rw [toParams_blocksOf_sumFst_bat]
    exact smallWritesGenericAttention_blocksOf_bat θ₀.sumFst hθa
  have hβm : SmallWritesGeneric (blocksOf_bat θ₀).toParams.sumSnd := by
    rw [toParams_blocksOf_sumSnd_bat]
    exact smallWritesGeneric_blocksOf_bat θ₀.sumSnd hθm
  -- one small `τ ≠ 0`: `fd(β₀_τ) = P − s`
  obtain ⟨τ, hτ⟩ := (eventually_funDimBlocks_smallWrites_attentionMlp hσ hσa hU t₁ t₂ h12 hs2
    hs1 (blocksOf_bat θ₀) hβa hβm).exists
  -- at almost every `β`, `fd(β) ≥ fd(β₀_τ)` (analytic outputs), and the query and the value
  -- matrix of every head have rank `d_h`
  filter_upwards [ae_funDimBlocks_ge (Arch.attentionMlp sees σ id H dh hid) 1 hfa
      analyticOnNhd_id μ ((blocksOf_bat θ₀).smallWrites τ), ae_rank_QV_ubt μ hdh] with β h1 h2
  -- `≤`: on a batch attaining `fd(β)` the kernel contains the directions of the heads at `β`
  obtain ⟨m, Y, hY⟩ := exists_jacobianRankBlocks_eq_funDimBlocks (S := 1) β
  obtain ⟨VA, hVA, -, hdimA⟩ := attn_part_ubt β.toParams.sumFst h2.1 h2.2
  have hV := sup_le_span_ibl β.toParams VA ⊥ hVA bot_le
  have hdim := finrank_sup_ibl β.toParams VA ⊥ hVA
  rw [hdimA, finrank_bot, add_zero] at hdim
  have hup := jacobianRankBlocks_add_le_of_insideBlocks_bat (S := 1) hf differentiable_id β _
    hV Y
  rw [hdim] at hup
  omega

/-- **Lemma A.27 (Small writes), fourth value, for networks of attention blocks and gated blocks,
under the conditions of its proof:** as `eventually_funDimBlocks_smallWrites_attentionMlp`, with
`fd(β_τ) = P − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`: the changes of basis inside the heads and
the rescalings of the values of the gated units. -/
theorem eventually_funDimBlocks_smallWrites_attentionGated (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁)
    (β : BlockParams (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid))
    (hβa : SmallWritesGenericAttention β.toParams.sumFst)
    (hβm : SmallWritesGenericGated β.toParams.sumSnd) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      funDimBlocks (Arch.attentionGated sees σ id H dh hid) 1 (β.smallWrites τ)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ))
        = Module.finrank ℝ
            (BlockParams (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid)) := by
  classical
  -- the blocks of the sum are differentiable
  have hf : ∀ ℓ, Differentiable ℝ
      ((Arch.attentionGated (T := T) (d := d) sees σ id H dh hid).f ℓ) := fun ℓ =>
    differentiable_f_sum (differentiable_f_attention sees id H dh ℓ)
      (differentiable_f_gated (fun z => (hσ z).differentiableAt) ℓ)
  -- `(β_τ).toParams` is `(β.toParams)_τ`, and `fd + d² + s = P` there (first value)
  filter_upwards [eventually_funDim_smallWrites_attentionGated hσ hσa hU t₁ t₂ h12 hs2 hs1
    β.toParams hβa hβm] with τ hτ
  -- no value column of a read of a gated unit vanishes, as no value column of `E W_read^ℓ`
  -- does (`E = I`); the reads of `β_τ` are those of `β`
  have hval : ∀ ℓ i,
      (fun k => (BlockParams.toParams (β.smallWrites τ)).sumSnd.read ℓ k (Sum.inr i)) ≠ 0 := by
    intro ℓ i h0
    apply hβm.value_ne_zero ℓ i
    funext a
    show ∑ k, β.toParams.sumSnd.E a k * β.toParams.sumSnd.read ℓ k (Sum.inr i) = 0
    exact Finset.sum_eq_zero fun k _ => by
      rw [show β.toParams.sumSnd.read ℓ k (Sum.inr i) = 0 from congrFun h0 k, mul_zero]
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the values; their
  -- lift to the sum has dimension `s`
  obtain ⟨VA, hVA, -, hdimA⟩ :=
    attn_part_ubt (BlockParams.toParams (β.smallWrites τ)).sumFst hβa.rank_Q hβa.rank_V
  obtain ⟨VB, hVB, -, hdimB⟩ := gated_part_ubt (BlockParams.toParams (β.smallWrites τ)).sumSnd hval
  have hV := sup_le_span_ibl (BlockParams.toParams (β.smallWrites τ)) VA VB hVA hVB
  have hdim := finrank_sup_ibl (BlockParams.toParams (β.smallWrites τ)) VA VB hVA
  rw [hdimA, hdimB] at hdim
  -- the fourth value from the first
  have h := funDimBlocks_add_eq_bat rfl hf (β.smallWrites τ) _ hV (by rw [hdim]; exact hτ)
  rwa [hdim] at h

/-- **Lemma A.27, fourth value, at generic parameters, for networks of attention blocks and gated
blocks:** without normalization, with `d ≥ 2`, heads of width `1 ≤ d_h ≤ d`, blocks of any widths
and a token that sees itself and another token, at almost every parameter of the blocks the
residual network without an embedding and a readout has the functional dimension
`P − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDimBlocks_attentionGated_residual (hσ : ∀ z, HasDerivAt σ (σ' z) z)
    (hσa : AnalyticOnNhd ℝ σ Set.univ) (hU : GatedUnitsRescale σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (BlockParams (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.attentionGated sees σ id H dh hid) 1 β
        + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ
          (BlockParams (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid)) := by
  classical
  have : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  -- the blocks of the sum are differentiable and analytic
  have hf : ∀ ℓ, Differentiable ℝ
      ((Arch.attentionGated (T := T) (d := d) sees σ id H dh hid).f ℓ) := fun ℓ =>
    differentiable_f_sum (differentiable_f_attention sees id H dh ℓ)
      (differentiable_f_gated (fun z => (hσ z).differentiableAt) ℓ)
  have hfa : ∀ ℓ, AnalyticOnNhd ℝ
      ((Arch.attentionGated (T := T) (d := d) sees σ id H dh hid).f ℓ) Set.univ := fun ℓ =>
    analyticOnNhd_f_sum (analyticOnNhd_f_attention (d := d) sees id H dh ℓ)
      (analyticOnNhd_f_gated hσa ℓ)
  -- one network `θ₀` with `d_in = d_out = d` and the conditions of Lemma A.27 on its two parts
  obtain ⟨θ₀, hθa, hθm⟩ := (ae_smallWritesGeneric_attentionGated
    (Measure.addHaar :
      Measure (Params (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) d d))
    hd le_rfl le_rfl hdh hdh0).exists
  -- the blocks `β₀ = (E W_read, W_write D)` have them at `E = D = I`
  have hβa : SmallWritesGenericAttention (blocksOf_bat θ₀).toParams.sumFst := by
    rw [toParams_blocksOf_sumFst_bat]
    exact smallWritesGenericAttention_blocksOf_bat θ₀.sumFst hθa
  have hβm : SmallWritesGenericGated (blocksOf_bat θ₀).toParams.sumSnd := by
    rw [toParams_blocksOf_sumSnd_bat]
    exact smallWritesGenericGated_blocksOf_bat θ₀.sumSnd hθm
  -- one small `τ ≠ 0`: `fd(β₀_τ) = P − s`
  obtain ⟨τ, hτ⟩ := (eventually_funDimBlocks_smallWrites_attentionGated hσ hσa hU t₁ t₂ h12 hs2
    hs1 (blocksOf_bat θ₀) hβa hβm).exists
  -- at almost every `β`, `fd(β) ≥ fd(β₀_τ)` (analytic outputs), the query and the value matrix
  -- of every head have rank `d_h`, and no value column of a gated unit vanishes
  filter_upwards [ae_funDimBlocks_ge (Arch.attentionGated sees σ id H dh hid) 1 hfa
      analyticOnNhd_id μ ((blocksOf_bat θ₀).smallWrites τ), ae_rank_QV_ubt μ hdh,
    ae_value_ne_zero_ubt μ] with β h1 h2 h3
  -- `≤`: on a batch attaining `fd(β)` the kernel contains the directions of the heads and of the
  -- rescalings at `β`
  obtain ⟨m, Y, hY⟩ := exists_jacobianRankBlocks_eq_funDimBlocks (S := 1) β
  obtain ⟨VA, hVA, -, hdimA⟩ := attn_part_ubt β.toParams.sumFst h2.1 h2.2
  obtain ⟨VB, hVB, -, hdimB⟩ := gated_part_ubt β.toParams.sumSnd h3
  have hV := sup_le_span_ibl β.toParams VA VB hVA hVB
  have hdim := finrank_sup_ibl β.toParams VA VB hVA
  rw [hdimA, hdimB] at hdim
  have hup := jacobianRankBlocks_add_le_of_insideBlocks_bat (S := 1) hf differentiable_id β _
    hV Y
  rw [hdim] at hup
  omega

/-! ### The four kinds of block -/

/-- **Lemma A.27, fourth value, at generic parameters, for attention blocks with `tanh`
blocks.** -/
theorem ae_funDimBlocks_attention_tanh_residual
    (μ : Measure (BlockParams (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.attentionMlp sees Real.tanh id H dh hid) 1 β
        + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
      = Module.finrank ℝ
          (BlockParams (Arch.attentionMlp (T := T) (d := d) sees Real.tanh id H dh hid)) :=
  ae_funDimBlocks_attentionMlp_residual hasDerivAt_tanh analyticOnNhd_tanh
    (tanh_unitsRigid _ _ _) μ hd hdh hdh0 t₁ t₂ h12 hs2 hs1

/-- **Lemma A.27, fourth value, at generic parameters, for attention blocks with GELU
blocks.** -/
theorem ae_funDimBlocks_attention_gelu_residual
    (μ : Measure (BlockParams (Arch.attentionMlp (T := T) (d := d) sees gelu id H dh hid)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.attentionMlp sees gelu id H dh hid) 1 β
        + 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
      = Module.finrank ℝ
          (BlockParams (Arch.attentionMlp (T := T) (d := d) sees gelu id H dh hid)) :=
  ae_funDimBlocks_attentionMlp_residual hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_unitsRigid _ _ _) μ hd hdh hdh0 t₁ t₂ h12 hs2 hs1

/-- **Lemma A.27, fourth value, at generic parameters, for attention blocks with SwiGLU
blocks.** -/
theorem ae_funDimBlocks_attention_swiglu_residual
    (μ : Measure (BlockParams (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.attentionGated sees silu id H dh hid) 1 β
        + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ
          (BlockParams (Arch.attentionGated (T := T) (d := d) sees silu id H dh hid)) :=
  ae_funDimBlocks_attentionGated_residual hasDerivAt_silu analyticOnNhd_silu
    (silu_gatedUnitsRescale _ _ _) μ hd hdh hdh0 t₁ t₂ h12 hs2 hs1

/-- **Lemma A.27, fourth value, at generic parameters, for attention blocks with GeGLU
blocks.** -/
theorem ae_funDimBlocks_attention_geglu_residual
    (μ : Measure (BlockParams (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) (hdh0 : ∀ ℓ, 0 < Fintype.card (dh ℓ))
    (t₁ t₂ : T) (h12 : t₁ ≠ t₂) (hs2 : sees t₂ t₂) (hs1 : sees t₂ t₁) :
    ∀ᵐ β ∂μ, funDimBlocks (Arch.attentionGated sees gelu id H dh hid) 1 β
        + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
          + ∑ ℓ, Fintype.card (hid ℓ))
      = Module.finrank ℝ
          (BlockParams (Arch.attentionGated (T := T) (d := d) sees gelu id H dh hid)) :=
  ae_funDimBlocks_attentionGated_residual hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_gatedUnitsRescale _ _ _) μ hd hdh hdh0 t₁ t₂ h12 hs2 hs1

end Skips
