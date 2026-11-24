import SkipsLean.Symmetry.InsideBlocks
import SkipsLean.Network.Sum

/-!
# Symmetries inside the blocks of a network with two kinds of block

Papers. Skips paper, Theorem 4.2 (Upper bounds), with "`s` the dimension of the symmetries inside
the blocks", "summed over the blocks" (Section 4.1), for networks whose blocks are attention
blocks and MLP blocks (Section 2: "A transformer layer has two blocks, its attention and MLP
sub-layers"). In the sum `A.sum B` of two architectures (`Network/Sum.lean`) a symmetry inside
the blocks of `A`, or of `B`, is a symmetry inside the blocks of the sum, and the two families
are independent, so their dimensions add.

* `Params.sumFst θ`, `Params.sumSnd θ`: the parameters of the two parts of a network of `A.sum B`
  (the same `E` and `D`; the read columns and the write rows of the part).
* `Params.sumInl η`, `Params.sumInr η`: a direction of `A`, or of `B`, as a direction of the sum
  (`0` on the other part).
* `InsideBlocks.sumInl`, `InsideBlocks.sumInr`: a direction of a symmetry inside the blocks of a
  part is one of the sum.
* The bounds of `Symmetry/InsideBlocks.lean` for the sum, with `dim V_A + dim V_B`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} {A B : Arch T d L}

/-- **The first part of the parameters of a network of `A.sum B`:** `E`, `D`, and in every block
the read columns and the write rows that belong to `A`. -/
def Params.sumFst (θ : Params (A.sum B) dIn dOut) : Params A dIn dOut where
  E := θ.E
  read ℓ := (θ.read ℓ).submatrix id Sum.inl
  write ℓ := (θ.write ℓ).submatrix Sum.inl id
  D := θ.D

/-- **The second part of the parameters of a network of `A.sum B`:** `E`, `D`, and in every block
the read columns and the write rows that belong to `B`. -/
def Params.sumSnd (θ : Params (A.sum B) dIn dOut) : Params B dIn dOut where
  E := θ.E
  read ℓ := (θ.read ℓ).submatrix id Sum.inr
  write ℓ := (θ.write ℓ).submatrix Sum.inr id
  D := θ.D

/-- **A direction of `A` as a direction of the sum:** `0` at the read columns and the write rows
that belong to `B`. -/
def Params.sumInl (η : Params A dIn dOut) : Params (A.sum B) dIn dOut where
  E := η.E
  read ℓ := Matrix.of fun a p => Sum.elim (fun j => η.read ℓ a j) (fun _ => 0) p
  write ℓ := Matrix.of fun p a => Sum.elim (fun i => η.write ℓ i a) (fun _ => 0) p
  D := η.D

/-- **A direction of `B` as a direction of the sum:** `0` at the read columns and the write rows
that belong to `A`. -/
def Params.sumInr (η : Params B dIn dOut) : Params (A.sum B) dIn dOut where
  E := η.E
  read ℓ := Matrix.of fun a p => Sum.elim (fun _ => 0) (fun j => η.read ℓ a j) p
  write ℓ := Matrix.of fun p a => Sum.elim (fun _ => 0) (fun i => η.write ℓ i a) p
  D := η.D

variable [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]

/-- **A symmetry inside the blocks of `A` is a symmetry inside the blocks of the sum.** -/
theorem InsideBlocks.sumInl {θ : Params (A.sum B) dIn dOut} {η : Params A dIn dOut}
    (h : InsideBlocks A θ.sumFst η) : InsideBlocks (A.sum B) θ (Params.sumInl η) := by
  sorry

/-- **A symmetry inside the blocks of `B` is a symmetry inside the blocks of the sum.** -/
theorem InsideBlocks.sumInr {θ : Params (A.sum B) dIn dOut} {η : Params B dIn dOut}
    (h : InsideBlocks B θ.sumSnd η) : InsideBlocks (A.sum B) θ (Params.sumInr η) := by
  sorry

variable (θ : Params (A.sum B) dIn dOut)

/-- **Theorem 4.3 of the dimension paper for a network with two kinds of block, without
normalization:** let `V_A` and `V_B` be spaces of directions spanned by directions of symmetries
inside the blocks of the two parts, in each of which a direction whose read of block `ℓ` is `0`
has the write of block `ℓ` `0`. If `E` and the writes of the sum have rank `d`,
`fd ≤ P − (L + 1) d² − dim V_A − dim V_B`. -/
theorem funDim_add_le_skipless_sum_of_insideBlocks (hA : A.χ = id)
    (VA : Submodule ℝ (Params A dIn dOut)) (VB : Submodule ℝ (Params B dIn dOut))
    (hVA : VA ≤ Submodule.span ℝ {η | InsideBlocks A θ.sumFst η})
    (hVB : VB ≤ Submodule.span ℝ {η | InsideBlocks B θ.sumSnd η})
    (hrwA : ∀ η ∈ VA, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hrwB : ∀ η ∈ VB, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim (A.sum B) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + (Module.finrank ℝ VA + Module.finrank ℝ VB))
      ≤ Module.finrank ℝ (Params (A.sum B) dIn dOut) := by
  sorry

/-- **The same under pre-RMSNorm** (any `ε`). -/
theorem funDim_add_le_skipless_sum_of_insideBlocks_rmsNorm (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (VA : Submodule ℝ (Params A dIn dOut)) (VB : Submodule ℝ (Params B dIn dOut))
    (hVA : VA ≤ Submodule.span ℝ {η | InsideBlocks A θ.sumFst η})
    (hVB : VB ≤ Submodule.span ℝ {η | InsideBlocks B θ.sumSnd η})
    (hrwA : ∀ η ∈ VA, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hrwB : ∀ η ∈ VB, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d) :
    funDim (A.sum B) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (Module.finrank ℝ VA + Module.finrank ℝ VB))
      ≤ Module.finrank ℝ (Params (A.sum B) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips, for a network with two kinds of block,
without normalization:** if `E` has rank `d`, `fd ≤ P − d² − dim V_A − dim V_B`. -/
theorem funDim_add_le_residual_sum_of_insideBlocks (hA : A.χ = id)
    (VA : Submodule ℝ (Params A dIn dOut)) (VB : Submodule ℝ (Params B dIn dOut))
    (hVA : VA ≤ Submodule.span ℝ {η | InsideBlocks A θ.sumFst η})
    (hVB : VB ≤ Submodule.span ℝ {η | InsideBlocks B θ.sumSnd η})
    (hE : θ.E.rank = Fintype.card d) :
    funDim (A.sum B) 1 θ
        + (Fintype.card d ^ 2 + (Module.finrank ℝ VA + Module.finrank ℝ VB))
      ≤ Module.finrank ℝ (Params (A.sum B) dIn dOut) := by
  sorry

/-- **The same under pre-RMSNorm** (any `ε`). -/
theorem funDim_add_le_residual_sum_of_insideBlocks_rmsNorm (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (VA : Submodule ℝ (Params A dIn dOut)) (VB : Submodule ℝ (Params B dIn dOut))
    (hVA : VA ≤ Submodule.span ℝ {η | InsideBlocks A θ.sumFst η})
    (hVB : VB ≤ Submodule.span ℝ {η | InsideBlocks B θ.sumSnd η})
    (hE : θ.E.rank = Fintype.card d) :
    funDim (A.sum B) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (Module.finrank ℝ VA + Module.finrank ℝ VB))
      ≤ Module.finrank ℝ (Params (A.sum B) dIn dOut) := by
  sorry

end Skips
