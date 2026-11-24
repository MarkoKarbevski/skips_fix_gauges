import SkipsLean.Network.AttentionAnalytic

/-!
# Networks with two kinds of block: the sum of two architectures

Papers. Skips paper, Section 2: "We write every block, MLP or attention, in one form. […] A
transformer layer has two blocks, its attention and MLP sub-layers: a transformer of 12 layers has
`L = 24`, and per block means per sub-layer." Lemma A.27: "let each block, in any order and of any
width, be an attention block […] or an MLP block". Absorb paper, Theorem 4.3: "The theorem covers
pre-RMSNorm transformers, which alternate attention and MLP blocks."

The architectures `Arch.mlp`, `Arch.gated` and `Arch.attention` have blocks of one kind. Here:
for two architectures `A` and `B` on the same hidden states, block `ℓ` of `A.sum B` reads with
`[W_read^A | W_read^B]`, applies `f_ℓ^A` and `f_ℓ^B` to the two parts, and writes with the two
writes stacked, so that its output is the sum of the outputs of block `ℓ` of `A` and of block `ℓ`
of `B` (`f_sum_mul`). The map `χ` is that of `A`.

A network whose blocks are attention blocks or MLP blocks, in any order, is
`(Arch.attention sees χ H dh).sum (Arch.mlp σ χ hid)` in which every block `ℓ` has no head
(`H ℓ` empty: an MLP block, `f_sum_mul_of_isEmpty_left`) or no hidden unit (`hid ℓ` empty: an
attention block, `f_sum_mul_of_isEmpty_right`). The sum also contains the networks in which a
block has heads and hidden units side by side.
-/

namespace Skips

open Matrix
open scoped Matrix.Norms.Elementwise

variable {T d : Type*} {L : ℕ}

/-- **The sum of two architectures on the same hidden states:** block `ℓ` has the read columns of
block `ℓ` of `A` (`Sum.inl`) and of `B` (`Sum.inr`) side by side, likewise the write rows, and its
fixed map applies `f_ℓ^A` to the first part of its argument and `f_ℓ^B` to the second. -/
abbrev Arch.sum (A B : Arch T d L) : Arch T d L where
  r ℓ := A.r ℓ ⊕ B.r ℓ
  w ℓ := A.w ℓ ⊕ B.w ℓ
  f ℓ M := Matrix.of fun t p =>
    Sum.elim (A.f ℓ (M.submatrix id Sum.inl) t) (B.f ℓ (M.submatrix id Sum.inr) t) p
  χ := A.χ

variable [Fintype T] [Fintype d] (A B : Arch T d L)

/-- **The block of the sum is the sum of the blocks:** on a hidden state `h`, with the read
`R = [R_A | R_B]` and the write `W` (the rows of `W_A` above those of `W_B`), block `ℓ` of
`A.sum B` gives `f_ℓ^A (h R_A) W_A + f_ℓ^B (h R_B) W_B`. -/
theorem f_sum_mul (ℓ : Fin L) (h : Matrix T d ℝ) (R : Matrix d (A.r ℓ ⊕ B.r ℓ) ℝ)
    (W : Matrix (A.w ℓ ⊕ B.w ℓ) d ℝ) :
    (A.sum B).f ℓ (h * R) * W
      = A.f ℓ (h * R.submatrix id Sum.inl) * W.submatrix Sum.inl id
        + B.f ℓ (h * R.submatrix id Sum.inr) * W.submatrix Sum.inr id := by
  sorry

/-- **A block without a second part is a block of `A`:** if block `ℓ` of `B` has no write row
(for an MLP block: no hidden unit), block `ℓ` of `A.sum B` is block `ℓ` of `A`. -/
theorem f_sum_mul_of_isEmpty_right (ℓ : Fin L) [IsEmpty (B.w ℓ)] (h : Matrix T d ℝ)
    (R : Matrix d (A.r ℓ ⊕ B.r ℓ) ℝ) (W : Matrix (A.w ℓ ⊕ B.w ℓ) d ℝ) :
    (A.sum B).f ℓ (h * R) * W
      = A.f ℓ (h * R.submatrix id Sum.inl) * W.submatrix Sum.inl id := by
  sorry

/-- **A block without a first part is a block of `B`:** if block `ℓ` of `A` has no write row (for
an attention block: no head), block `ℓ` of `A.sum B` is block `ℓ` of `B`. -/
theorem f_sum_mul_of_isEmpty_left (ℓ : Fin L) [IsEmpty (A.w ℓ)] (h : Matrix T d ℝ)
    (R : Matrix d (A.r ℓ ⊕ B.r ℓ) ℝ) (W : Matrix (A.w ℓ ⊕ B.w ℓ) d ℝ) :
    (A.sum B).f ℓ (h * R) * W
      = B.f ℓ (h * R.submatrix id Sum.inr) * W.submatrix Sum.inr id := by
  sorry

variable {A B}

/-- The map of a block of the sum is real-analytic if the maps of the two blocks are. -/
theorem analyticOnNhd_f_sum {ℓ : Fin L} (hA : AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (hB : AnalyticOnNhd ℝ (B.f ℓ) Set.univ) : AnalyticOnNhd ℝ ((A.sum B).f ℓ) Set.univ := by
  sorry

/-- The map of a block of the sum is differentiable if the maps of the two blocks are. -/
theorem differentiable_f_sum {ℓ : Fin L} (hA : Differentiable ℝ (A.f ℓ))
    (hB : Differentiable ℝ (B.f ℓ)) : Differentiable ℝ ((A.sum B).f ℓ) := by
  sorry

/-- The map of a block of the sum is continuous if the maps of the two blocks are. -/
theorem continuous_f_sum {ℓ : Fin L} (hA : Continuous (A.f ℓ)) (hB : Continuous (B.f ℓ)) :
    Continuous ((A.sum B).f ℓ) := by
  sorry

/-- The map of a block of the sum is locally Lipschitz if the maps of the two blocks are. -/
theorem locallyLipschitz_f_sum {ℓ : Fin L} (hA : LocallyLipschitz (A.f ℓ))
    (hB : LocallyLipschitz (B.f ℓ)) : LocallyLipschitz ((A.sum B).f ℓ) := by
  sorry

end Skips
