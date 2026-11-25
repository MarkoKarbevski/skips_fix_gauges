import SkipsLean.Residual.BlocksAlone
import SkipsLean.Dimension.UpperBound

/-!
# Skipless networks without an embedding and a readout: a change of basis is left

Paper (skips paper), proof of Theorem A.28 (i): "Without an embedding, a readout and attention
blocks, for `L ≥ 2` the changes of basis at `h_1` have orbits of positive dimension, since every
block has at least one hidden unit, so Lemma A.26 applies again."

Here, for a network of `L + 2` blocks without skips, without normalization, without an embedding
and a readout (`Residual/BlocksAlone.lean`), with differentiable blocks: on every batch and at
every parameter of the blocks, the Jacobian in the reads and the writes has rank at most `P − 1`.
The direction of the scalings of `h_1`, `(W_write^1, −W_read^2)` at the write of block 1 and the
read of block 2, is in its kernel (`cobDir_mem_flat_skipless`), and it is nonzero unless
`W_write^1 = 0`; if `W_write^1 = 0`, then `h_1 = 0` whatever the read of block 1 is, so the
directions at the read of block 1 are in the kernel. The statement asks a model dimension of at
least one and at least one column in the read of block 1 (for an MLP block, one hidden unit).

Numeric check (the rank is `P − (L − 1) d²` at generic parameters of GELU blocks of width at least
`d`, and `0` at a parameter with `W_write^1 = 0`, `W_read^2 = 0`):
`blocks_alone_mlp_check_2026-11-25.py`.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d]

/-- **Proof of Theorem A.28 (i) of the skips paper, "for `L ≥ 2` the changes of basis at `h_1`
have orbits of positive dimension, since every block has at least one hidden unit":** for a
network of `L + 2` differentiable blocks without skips and without normalization, without an
embedding and a readout, with `d ≥ 1` and at least one column in the read of the first block: at
every parameter of the blocks and on every batch, the Jacobian in the reads and the writes has
rank at most `P − 1`. -/
theorem jacobianRankBlocks_add_one_le_skipless {A : Arch T d (L + 2)} (hA : A.χ = id)
    (hf : ∀ ℓ, Differentiable ℝ (A.f ℓ)) [Nonempty d] (hr : Nonempty (A.r 0))
    (β : BlockParams A) {n : ℕ} (X : Fin n → Matrix T d ℝ) :
    jacobianRankBlocks A 0 X β + 1 ≤ Module.finrank ℝ (BlockParams A) := by
  sorry

end Skips
