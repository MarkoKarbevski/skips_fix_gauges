import SkipsLean.Residual.BlocksAloneMlp
import SkipsLean.Residual.BlocksAloneSkipless
import SkipsLean.Dimension.RankCriterion

/-!
# Residual and skipless compositions of blocks compute different functions

Paper (skips paper), Theorem A.28 (i): "For GELU blocks and almost every choice of weights, a
composition of `L ≥ 2` residual blocks equals no composition of `L` blocks without skips of the
same widths."

Its proof: "By Lemma A.27, […] a network of GELU blocks without an embedding and a readout has
functional dimension `P`. […] Without an embedding, a readout and attention blocks, for `L ≥ 2`
the changes of basis at `h_1` have orbits of positive dimension, since every block has at least
one hidden unit, so Lemma A.26 applies again."

Here: the networks without an embedding and a readout of `Residual/BlocksAlone.lean`, with the
blocks `Fin (L + 2)` and the same hidden units `hid ℓ` in both networks; the residual network has
`fd = P` at some parameter (`Residual/BlocksAloneMlp.lean`), the skipless network has rank at most
`P − 1` at every parameter and on every batch (`Residual/BlocksAloneSkipless.lean`), and Lemma
A.26 (i) is `ae_notMem_range_of_rank_lt` (`Dimension/RankCriterion.lean`), under Sard's theorem
(`Literature/Sard.lean`). Stated for every activation with the conclusion of Lemma B.3 with
`s = 0` (`UnitsRigid`), and named for GELU. The hypothesis "at least one hidden unit" is asked of
the first block only. Theorem A.28 (iv) does not concern part (i).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d : Type*} {L : ℕ} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
variable {hid : Fin (L + 2) → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **Theorem A.28 (i) of the skips paper for MLP blocks whose hidden units have no symmetry,
given Sard's theorem:** with `d ≥ 2`, at least one token and at least one hidden unit in the first
block, for almost every choice of weights a composition of `L + 2` residual blocks equals no
composition of `L + 2` blocks without skips with the same hidden units. -/
theorem ae_forall_evalBlocks_residual_ne_skipless_mlp
    (hSard : ∀ r : ℕ, SardCriticalValues
      (BlockParams (Arch.mlp (T := T) (d := d) σ id hid)) (Fin r → ℝ))
    (hσ : ∀ z, HasDerivAt σ (σ' z) z) (hσa : AnalyticOnNhd ℝ σ Set.univ)
    (hU : UnitsRigid σ σ' d d (Σ ℓ, hid ℓ))
    (μ : Measure (BlockParams (Arch.mlp (T := T) (d := d) σ id hid))) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (h0 : Nonempty (hid 0)) :
    ∀ᵐ β ∂μ, ∀ β' : BlockParams (Arch.mlp (T := T) (d := d) σ id hid),
      evalBlocks (Arch.mlp σ id hid) 1 β ≠ evalBlocks (Arch.mlp σ id hid) 0 β' := by
  sorry

/-- **Theorem A.28 (i) of the skips paper, given Sard's theorem:** "For GELU blocks and almost
every choice of weights, a composition of `L ≥ 2` residual blocks equals no composition of `L`
blocks without skips of the same widths", with `d ≥ 2`, at least one token and at least one hidden
unit in the first block. -/
theorem ae_forall_evalBlocks_residual_ne_skipless_gelu
    (hSard : ∀ r : ℕ, SardCriticalValues
      (BlockParams (Arch.mlp (T := T) (d := d) gelu id hid)) (Fin r → ℝ))
    (μ : Measure (BlockParams (Arch.mlp (T := T) (d := d) gelu id hid))) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Fintype.card d) (h0 : Nonempty (hid 0)) :
    ∀ᵐ β ∂μ, ∀ β' : BlockParams (Arch.mlp (T := T) (d := d) gelu id hid),
      evalBlocks (Arch.mlp gelu id hid) 1 β ≠ evalBlocks (Arch.mlp gelu id hid) 0 β' :=
  ae_forall_evalBlocks_residual_ne_skipless_mlp hSard hasDerivAt_gelu analyticOnNhd_gelu
    (gelu_unitsRigid _ _ _) μ hd h0

end Skips
