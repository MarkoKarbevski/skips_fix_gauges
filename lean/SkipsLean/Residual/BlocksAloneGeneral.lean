import SkipsLean.Residual.BlocksAlone
import SkipsLean.Residual.UpperBoundSymmetries
import SkipsLean.Dimension.GenericRankOn

/-!
# Networks without an embedding and a readout: from the network with `E = D = I`

Paper (skips paper), Lemma A.27, fourth value: "`fd(θ_τ) = P − s` (no embedding, readout, biases
or normalization)". Its proof: "So the flat directions form a space of dimension `d_model² + s`
without biases […]. Without an embedding and a readout, `M = I` is fixed, so `ψ_M = 0` for every
direction, and the flat directions are the rescalings alone, of dimension `s`."

The parameters of the network without an embedding and a readout are the reads and the writes
(`BlockParams A`, `Residual/BlocksAlone.lean`); its function is that of the network with
`d_in = d_out = d` at `E = D = I` (`BlockParams.toParams`). So the fourth value follows from the
first value at such a parameter, for every kind of block at once:

* `blockDir A`: a direction `η` of the blocks, as the direction `(0, η_read, η_write, 0)` of the
  network with an embedding and a readout.
* `funDimBlocks_add_finrank_eq_of_funDim_toParams`: let `R` be a space of directions of the blocks
  that are flat for the residual network at `β.toParams` (the symmetries inside the blocks: none
  for tanh and GELU blocks, the rescalings for gated blocks, the changes of basis inside the heads
  for attention blocks). If the network with an embedding and a readout has
  `fd = P − d² − dim R` at `β.toParams`, the network without them has `fd = P_blocks − dim R` at
  `β`. (On a batch that attains `fd` the kernel of the Jacobian at `β.toParams` has dimension
  `d² + dim R` and contains the directions `(E Y, −Y W_read, W_write Y, −Y D)` of the one change
  of basis and those of `R`, so it consists of them; a direction of the blocks has no component at
  `E`, which is `E Y = Y`, so in this kernel it lies in `R`.)
* `ae_funDimBlocks_ge`: for real-analytic blocks, the functional dimension of the network without
  an embedding and a readout at almost every parameter is at least its value at any one
  parameter (the twin of `ae_funDim_ge`, `Dimension/GenericRank.lean`).

`Residual/BlocksAloneAttention.lean` proved the case of attention blocks directly; the statements
for MLP and gated blocks (`Residual/BlocksAloneMlp.lean`, `Residual/BlocksAloneGated.lean`) use
this file.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]

omit [Fintype T] [DecidableEq d] in
/-- **A direction of the blocks, as a direction of the network with an embedding and a readout:**
`η ↦ (0, η_read, η_write, 0)`, the linear part of `β ↦ β.toParams`. -/
def blockDir (A : Arch T d L) : BlockParams A →ₗ[ℝ] Params A d d where
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
/-- Helper: `blockDir A` is injective (it keeps the reads and the writes; `E` and `D` of the
blocks are empty matrices). -/
private theorem blockDir_injective_bag (A : Arch T d L) : Function.Injective (blockDir A) := by
  intro η ξ h
  apply Params.ext'
  · exact Matrix.ext fun i => i.elim
  · intro ℓ
    exact congrArg (fun θ : Params A d d => θ.read ℓ) h
  · intro ℓ
    exact congrArg (fun θ : Params A d d => θ.write ℓ) h
  · exact Matrix.ext fun _ j => j.elim

omit [Fintype T] [Fintype d] in
/-- Helper: `β.toParams = blockDir A β + (I, 0, 0, I)`. -/
private theorem toParams_eq_bag {A : Arch T d L} (β : BlockParams A) :
    β.toParams = blockDir A β + ⟨1, fun _ => 0, fun _ => 0, 1⟩ := by
  apply Params.ext'
  · exact (zero_add (1 : Matrix d d ℝ)).symm
  · intro ℓ
    exact (add_zero (β.read ℓ)).symm
  · intro ℓ
    exact (add_zero (β.write ℓ)).symm
  · exact (zero_add (1 : Matrix d d ℝ)).symm

omit [Fintype T] in
/-- **The chain rule for the network without an embedding and a readout:** if the outputs of the
network on a batch are differentiable at `β.toParams`, the family `β' ↦ (F_{β'}(x_i))_i` has at
`β` the derivative of these outputs at `β.toParams`, composed with `blockDir A` (the map
`β' ↦ β'.toParams` is affine, with the linear part `blockDir A`). -/
theorem hasFDerivAt_evalBlocks_batch {A : Arch T d L} (S : Fin L → Matrix d d ℝ) {n : ℕ}
    (X : Fin n → Matrix T d ℝ) (β : BlockParams A)
    (hdiff : DifferentiableAt ℝ (evalBatch A S X) β.toParams) :
    HasFDerivAt (fun β' : BlockParams A => fun i : Fin n => evalBlocks A S β' (X i))
      ((fderiv ℝ (evalBatch A S X) β.toParams).comp
        (LinearMap.toContinuousLinearMap (blockDir A))) β := by
  -- `β' ↦ β'.toParams` is affine, with the linear part `blockDir A`
  have haff : HasFDerivAt (fun β' : BlockParams A => β'.toParams)
      (LinearMap.toContinuousLinearMap (blockDir A)) β :=
    ((LinearMap.toContinuousLinearMap (blockDir A)).hasFDerivAt.add_const
      (⟨1, fun _ => 0, fun _ => 0, 1⟩ : Params A d d)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun β' => toParams_eq_bag β')
  exact hdiff.hasFDerivAt.comp β haff

omit [Fintype T] in
/-- Helper: rank–nullity for the Jacobian of the family on a batch. -/
private theorem jacobianRankBlocks_add_finrank_ker_bag {A : Arch T d L}
    (S : Fin L → Matrix d d ℝ) {n : ℕ} (X : Fin n → Matrix T d ℝ) (β : BlockParams A) :
    jacobianRankBlocks A S X β + Module.finrank ℝ (LinearMap.ker
        (fderiv ℝ (fun β' : BlockParams A => fun i : Fin n => evalBlocks A S β' (X i))
          β).toLinearMap)
      = Module.finrank ℝ (BlockParams A) :=
  LinearMap.finrank_range_add_finrank_ker _

omit [DecidableEq d] in
/-- Helper (as `flat_le_ker_bla` of `Residual/BlocksAloneAttention.lean`): the flat directions
are in the kernel of the Jacobian on every batch. -/
private theorem flat_le_ker_bag {A : Arch T d L} {S : Fin L → Matrix d d ℝ} (θ : Params A d d)
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

/-- **A direction of the blocks that is flat for the network at `β.toParams` is in the kernel of
the Jacobian of the network without an embedding and a readout, on every batch** (for outputs
that are differentiable in the parameters): by the chain rule, the Jacobian of the family maps
`η` to the derivative of the outputs at `β.toParams` along `blockDir A η`. -/
theorem mem_ker_fderiv_evalBlocks_of_mem_flat {A : Arch T d L} {S : Fin L → Matrix d d ℝ}
    (β : BlockParams A)
    (hdiff : ∀ x : Matrix T d ℝ,
      DifferentiableAt ℝ (fun θ' : Params A d d => eval A S θ' x) β.toParams)
    {n : ℕ} (X : Fin n → Matrix T d ℝ) {η : BlockParams A}
    (hη : blockDir A η ∈ flat A S β.toParams) :
    η ∈ LinearMap.ker (fderiv ℝ
      (fun β' : BlockParams A => fun i : Fin n => evalBlocks A S β' (X i)) β).toLinearMap := by
  have h := flat_le_ker_bag β.toParams hdiff X hη
  rw [LinearMap.mem_ker] at h ⊢
  rw [(hasFDerivAt_evalBlocks_batch S X β (differentiableAt_pi.2 fun i => hdiff (X i))).fderiv]
  exact h

/-- **Step (a): the flat directions of the blocks bound the rank on every batch:** let the maps of
the blocks be differentiable and let `R` be a space of directions of the blocks that are flat for
the residual network at `β.toParams`. On every batch, the Jacobian of the network without an
embedding and a readout has rank at most `P_blocks − dim R` at `β` (its kernel contains `R`). -/
theorem jacobianRankBlocks_add_finrank_le {A : Arch T d L} {S : Fin L → Matrix d d ℝ}
    (hA : A.χ = id) (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (β : BlockParams A)
    (R : Submodule ℝ (BlockParams A)) (hR : ∀ η ∈ R, blockDir A η ∈ flat A S β.toParams)
    {n : ℕ} (X : Fin n → Matrix T d ℝ) :
    jacobianRankBlocks A S X β + Module.finrank ℝ R ≤ Module.finrank ℝ (BlockParams A) := by
  have hdiff : ∀ x : Matrix T d ℝ,
      DifferentiableAt ℝ (fun θ' : Params A d d => eval A S θ' x) β.toParams :=
    fun x => differentiable_eval hf (by rw [hA]; exact differentiable_id) x β.toParams
  -- `R` lies in the kernel of the Jacobian of the family on `X`; rank–nullity
  have hker : R ≤ LinearMap.ker (fderiv ℝ
      (fun β' : BlockParams A => fun i : Fin n => evalBlocks A S β' (X i)) β).toLinearMap :=
    fun η hη => mem_ker_fderiv_evalBlocks_of_mem_flat β hdiff X (hR η hη)
  have h1 := Submodule.finrank_mono hker
  rw [← jacobianRankBlocks_add_finrank_ker_bag S X β]
  exact Nat.add_le_add_left h1 _

/-- **Lemma A.27 of the skips paper, fourth value from the first, "Without an embedding and a
readout, `M = I` is fixed, so `ψ_M = 0` for every direction, and the flat directions are the
rescalings alone, of dimension `s`", for any blocks without normalization:** let the maps of the
blocks be differentiable and let `R` be a space of directions of the blocks that are flat for the
residual network at `β.toParams` (the network with `E = D = I` and the blocks of `β`). If that
network has `fd + d² + dim R = P` there, the residual network without an embedding and a readout
has `fd + dim R = P_blocks` at `β`. -/
theorem funDimBlocks_add_finrank_eq_of_funDim_toParams {A : Arch T d L} (hA : A.χ = id)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) (β : BlockParams A)
    (R : Submodule ℝ (BlockParams A))
    (hR : ∀ η ∈ R, blockDir A η ∈ flat A 1 β.toParams)
    (hfd : funDim A 1 β.toParams + (Fintype.card d ^ 2 + Module.finrank ℝ R)
      = Module.finrank ℝ (Params A d d)) :
    funDimBlocks A 1 β + Module.finrank ℝ R = Module.finrank ℝ (BlockParams A) := by
  have hdiff : ∀ x : Matrix T d ℝ,
      DifferentiableAt ℝ (fun θ' : Params A d d => eval A 1 θ' x) β.toParams :=
    fun x => differentiable_eval hf (by rw [hA]; exact differentiable_id) x β.toParams
  -- `≤`: step (a) on a batch that attains `fd(β)`
  obtain ⟨m, Z, hZ⟩ := exists_jacobianRankBlocks_eq_funDimBlocks (S := 1) β
  have hup := jacobianRankBlocks_add_finrank_le hA hf β R hR Z
  -- `≥`: a batch `X` on which the Jacobian of the network at `θ = β.toParams` has the rank `fd(θ)`
  obtain ⟨n, X, hX⟩ :=
    exists_jacobianRank_eq_funDim (S := (1 : Fin L → Matrix d d ℝ)) β.toParams
  -- rank–nullity for the network on `X`
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (fderiv ℝ (evalBatch A 1 X) β.toParams).toLinearMap
  have hJ : jacobianRank A 1 X β.toParams
      = Module.finrank ℝ (LinearMap.range
          (fderiv ℝ (evalBatch A 1 X) β.toParams).toLinearMap) :=
    rfl
  -- the map `Φ (Y, r) = cobDir θ (fun _ => Y) + blockDir A r`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Matrix d d ℝ × R) →ₗ[ℝ] Params A d d,
      ∀ Y r, Φ (Y, r) = cobDir β.toParams (fun _ => Y) + blockDir A r :=
    ⟨((cobDirLin β.toParams).comp (LinearMap.pi fun _ : Fin (L + 1) => LinearMap.id)).coprod
      ((blockDir A).comp R.subtype), fun _ _ => rfl⟩
  -- its `E` component is `I Y = Y`
  have hΦE : ∀ Y r, (Φ (Y, r)).E = Y := fun Y r => by
    rw [hΦ, Params.add_E]
    show (1 : Matrix d d ℝ) * Y + 0 = Y
    rw [Matrix.one_mul, add_zero]
  -- its directions are flat, hence in the kernel on `X`
  have hle : LinearMap.range Φ ≤ LinearMap.ker
      (fderiv ℝ (evalBatch A 1 X) β.toParams).toLinearMap := by
    rintro _ ⟨⟨Y, r⟩, rfl⟩
    rw [hΦ]
    exact flat_le_ker_bag _ hdiff X
      (Submodule.add_mem _ (cobDir_const_mem_flat_residual' β.toParams hA Y) (hR r r.2))
  -- it is injective: the `E` component gives `Y`, then `blockDir A` is injective
  have hinj : Function.Injective Φ := by
    rintro ⟨Y, r⟩ ⟨Y', r'⟩ h
    have hY : Y = Y' := (hΦE Y r).symm.trans ((congrArg Params.E h).trans (hΦE Y' r'))
    subst hY
    rw [hΦ, hΦ] at h
    exact Prod.ext rfl (Subtype.ext (blockDir_injective_bag A (add_left_cancel h)))
  -- so the kernel on `X` is the range of `Φ`, of dimension `d² + dim R`
  have hdimΦ : Module.finrank ℝ (LinearMap.range Φ)
      = Fintype.card d ^ 2 + Module.finrank ℝ R := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_matrix,
      Module.finrank_self, mul_one, ← sq]
  have hK : LinearMap.range Φ = LinearMap.ker
      (fderiv ℝ (evalBatch A 1 X) β.toParams).toLinearMap :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  -- `cobDir θ 0 = 0`
  have hcob0 : cobDir β.toParams (fun _ => (0 : Matrix d d ℝ)) = 0 :=
    map_zero (cobDirLin β.toParams)
  -- the kernel of the Jacobian of the family lies in `R`: a direction `η` with `blockDir A η` in
  -- the range of `Φ` has `Y = 0` (the `E` component of `blockDir A η` is `0`)
  have hker : LinearMap.ker (fderiv ℝ
        (fun β' : BlockParams A => fun i : Fin n => evalBlocks A 1 β' (X i)) β).toLinearMap
      ≤ R := by
    intro η hη
    rw [LinearMap.mem_ker,
      (hasFDerivAt_evalBlocks_batch 1 X β (differentiableAt_pi.2 fun i => hdiff (X i))).fderiv]
      at hη
    have hη' : blockDir A η ∈ LinearMap.ker
        (fderiv ℝ (evalBatch A 1 X) β.toParams).toLinearMap := hη
    rw [← hK] at hη'
    obtain ⟨⟨Y, r⟩, hYr⟩ := hη'
    have hY : Y = 0 := (hΦE Y r).symm.trans (congrArg Params.E hYr)
    subst hY
    rw [hΦ, hcob0, zero_add] at hYr
    rw [← blockDir_injective_bag A hYr]
    exact r.2
  -- rank–nullity for the family: its kernel has dimension at most `dim R`
  have h12 := Submodule.finrank_mono hker
  have hrnb := jacobianRankBlocks_add_finrank_ker_bag 1 X β
  have hleb := jacobianRankBlocks_le_funDimBlocks (S := 1) X β
  omega

/-- **The outputs of the network without an embedding and a readout on a batch are real-analytic
in the reads and the writes,** for real-analytic blocks and `χ` and any stream matrices: the
outputs of the network are analytic in the parameters, and `β ↦ β.toParams` is affine. -/
theorem analyticOnNhd_evalBlocks_batch (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ) {n : ℕ}
    (X : Fin n → Matrix T d ℝ) :
    AnalyticOnNhd ℝ (fun β' : BlockParams A => fun i : Fin n => evalBlocks A S β' (X i))
      Set.univ := by
  -- `β.toParams = blockDir A β + (I, 0, 0, I)`
  have hfun : (fun β' : BlockParams A => fun i : Fin n => evalBlocks A S β' (X i))
      = fun β' => fun i => eval A S
          (LinearMap.toContinuousLinearMap (blockDir A) β'
            + (⟨1, fun _ => 0, fun _ => 0, 1⟩ : Params A d d)) (X i) := by
    funext β' i
    exact congrArg (fun θ => eval A S θ (X i)) (toParams_eq_bag β')
  rw [hfun]
  refine AnalyticOnNhd.pi fun i => ?_
  have h1 := analyticOnNhd_eval_params A S hf hχ (dOut := d) (X i)
  have h2 : AnalyticOnNhd ℝ
      (fun β' : BlockParams A => LinearMap.toContinuousLinearMap (blockDir A) β'
          + (⟨1, fun _ => 0, fun _ => 0, 1⟩ : Params A d d)) Set.univ :=
    fun β' _ => ((LinearMap.toContinuousLinearMap (blockDir A)).analyticAt β').fun_add
      analyticAt_const
  have h3 := h1.comp h2 (Set.mapsTo_univ _ _)
  exact h3

/-- **The functional dimension of a network without an embedding and a readout is, at almost
every parameter, at least its value at any one parameter,** for real-analytic blocks and `χ` and
any stream matrices: the outputs on a batch are real-analytic in the reads and the writes. -/
theorem ae_funDimBlocks_ge (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (BlockParams A)) [μ.IsAddHaarMeasure] (β₀ : BlockParams A) :
    ∀ᵐ β ∂μ, funDimBlocks A S β₀ ≤ funDimBlocks A S β := by
  -- a batch `X` on which the rank at `β₀` is `fd(β₀)`
  obtain ⟨n, X, hX⟩ := exists_jacobianRankBlocks_eq_funDimBlocks (S := S) β₀
  -- at almost every `β` the rank on `X` is at least that at `β₀` (the family is analytic)
  filter_upwards [ae_finrank_range_fderiv_ge_of_isPreconnected μ isOpen_univ
      isPreconnected_univ (by simp) (analyticOnNhd_evalBlocks_batch A S hf hχ X)
      (Set.mem_univ β₀)] with β h1
  have h1' : jacobianRankBlocks A S X β₀ ≤ jacobianRankBlocks A S X β := h1
  have hle := jacobianRankBlocks_le_funDimBlocks (S := S) X β
  omega

end Skips
