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
  sorry

/-- **The functional dimension of a network without an embedding and a readout is, at almost
every parameter, at least its value at any one parameter,** for real-analytic blocks and `χ` and
any stream matrices: the outputs on a batch are real-analytic in the reads and the writes. -/
theorem ae_funDimBlocks_ge (A : Arch T d L) (S : Fin L → Matrix d d ℝ)
    (hf : ∀ ℓ, AnalyticOnNhd ℝ (A.f ℓ) Set.univ) (hχ : AnalyticOnNhd ℝ A.χ Set.univ)
    (μ : Measure (BlockParams A)) [μ.IsAddHaarMeasure] (β₀ : BlockParams A) :
    ∀ᵐ β ∂μ, funDimBlocks A S β₀ ≤ funDimBlocks A S β := by
  sorry

end Skips
