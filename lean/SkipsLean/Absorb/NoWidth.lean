import SkipsLean.Absorb.Block
import SkipsLean.OneBlock.UnitsSwiGLU

/-!
# No width suffices: ReLU², gated and tanh blocks

Paper ("Can an MLP Absorb Its Skip Connection Exactly?"): Theorem 3.3, with Propositions A.1 and A.2
of Appendix A.

For every matrix `M ≠ 0`, no block of the same kind and of any width computes `x M + B(x)` when
`B` is (a) positively homogeneous of degree `k ≠ 1` (ReLU² and ReGLU blocks, `k = 2`), (b) a gated
block whose gate vanishes at `0` and is differentiable there (SwiGLU and GeGLU blocks), or (c) a
`tanh` block. The three reasons: along a ray `x M` scales like `λ` and the blocks like `λ^k`; near
the origin a gated block is of second order; a `tanh` block is bounded.

The statements are for rectangular weights (`p` inputs, `q` outputs); the paper's are the case
`p = q = d`. A width is an index type.
-/

namespace Skips

open Matrix

variable {p q m m' : Type*} [Fintype p] [Fintype m] [Fintype m']

/-- **Proposition A.1 (homogeneous blocks).** Let `B` and `B'` be positively homogeneous of degree
`k ≠ 1`, and let `M ≠ 0`. Then `x M + B(x) = B'(x)` fails for some `x`. (The proof uses nothing else
about `B` and `B'`, so they are arbitrary maps here.) -/
theorem exists_ne_of_homogeneous {k : ℝ} (hk : k ≠ 1) (B B' : (p → ℝ) → (q → ℝ))
    (hB : ∀ (lam : ℝ) (x : p → ℝ), 0 < lam → B (lam • x) = lam ^ k • B x)
    (hB' : ∀ (lam : ℝ) (x : p → ℝ), 0 < lam → B' (lam • x) = lam ^ k • B' x)
    (M : Matrix p q ℝ) (hM : M ≠ 0) :
    ∃ x : p → ℝ, x ᵥ* M + B x ≠ B' x := by
  sorry

/-- **Proposition A.2 (gated blocks).** Let `B` and `B'` be gated blocks without biases, of any
widths, whose gates vanish at `0` and are differentiable there, and let `M ≠ 0`. Then
`x M + B(x) = B'(x)` fails for some `x`. -/
theorem exists_ne_of_gated {σ₁ σ₂ : ℝ → ℝ} (h₁ : σ₁ 0 = 0) (hd₁ : DifferentiableAt ℝ σ₁ 0)
    (h₂ : σ₂ 0 = 0) (hd₂ : DifferentiableAt ℝ σ₂ 0)
    (Wg Wv : Matrix p m ℝ) (Ww : Matrix m q ℝ) (Wg' Wv' : Matrix p m' ℝ) (Ww' : Matrix m' q ℝ)
    (M : Matrix p q ℝ) (hM : M ≠ 0) :
    ∃ x : p → ℝ, x ᵥ* M + gatedBlock σ₁ Wg Wv Ww x ≠ gatedBlock σ₂ Wg' Wv' Ww' x := by
  sorry

/-- A ReLU² block is positively homogeneous of degree `2`. -/
theorem vanillaBlock_reluSq_smul (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ) (lam : ℝ) (x : p → ℝ)
    (hlam : 0 < lam) :
    vanillaBlock reluSq Wr Ww (lam • x) = lam ^ (2 : ℝ) • vanillaBlock reluSq Wr Ww x := by
  sorry

/-- A ReGLU block is positively homogeneous of degree `2`. -/
theorem gatedBlock_relu_smul (Wg Wv : Matrix p m ℝ) (Ww : Matrix m q ℝ) (lam : ℝ) (x : p → ℝ)
    (hlam : 0 < lam) :
    gatedBlock relu Wg Wv Ww (lam • x) = lam ^ (2 : ℝ) • gatedBlock relu Wg Wv Ww x := by
  sorry

/-- **Theorem 3.3 (a) for ReLU² blocks:** for `M ≠ 0`, no ReLU² block of any width computes
`x M + B(x)`. -/
theorem exists_ne_reluSq (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ) (Wr' : Matrix p m' ℝ)
    (Ww' : Matrix m' q ℝ) (M : Matrix p q ℝ) (hM : M ≠ 0) :
    ∃ x : p → ℝ, x ᵥ* M + vanillaBlock reluSq Wr Ww x ≠ vanillaBlock reluSq Wr' Ww' x := by
  sorry

/-- **Theorem 3.3 (a) for ReGLU blocks.** -/
theorem exists_ne_reglu (Wg Wv : Matrix p m ℝ) (Ww : Matrix m q ℝ) (Wg' Wv' : Matrix p m' ℝ)
    (Ww' : Matrix m' q ℝ) (M : Matrix p q ℝ) (hM : M ≠ 0) :
    ∃ x : p → ℝ, x ᵥ* M + gatedBlock relu Wg Wv Ww x ≠ gatedBlock relu Wg' Wv' Ww' x := by
  sorry

/-- **Theorem 3.3 (b) for SwiGLU blocks** (gate SiLU). -/
theorem exists_ne_swiglu (Wg Wv : Matrix p m ℝ) (Ww : Matrix m q ℝ) (Wg' Wv' : Matrix p m' ℝ)
    (Ww' : Matrix m' q ℝ) (M : Matrix p q ℝ) (hM : M ≠ 0) :
    ∃ x : p → ℝ, x ᵥ* M + gatedBlock silu Wg Wv Ww x ≠ gatedBlock silu Wg' Wv' Ww' x := by
  sorry

/-- **Theorem 3.3 (b) for GeGLU blocks** (gate GELU). -/
theorem exists_ne_geglu (Wg Wv : Matrix p m ℝ) (Ww : Matrix m q ℝ) (Wg' Wv' : Matrix p m' ℝ)
    (Ww' : Matrix m' q ℝ) (M : Matrix p q ℝ) (hM : M ≠ 0) :
    ∃ x : p → ℝ, x ᵥ* M + gatedBlock gelu Wg Wv Ww x ≠ gatedBlock gelu Wg' Wv' Ww' x := by
  sorry

/-- **Theorem 3.3 (c):** for `M ≠ 0`, no `tanh` block of any width computes `x M + B(x)`: a `tanh`
block is bounded, and `x M` is not. -/
theorem exists_ne_tanh (Wr : Matrix p m ℝ) (Ww : Matrix m q ℝ) (Wr' : Matrix p m' ℝ)
    (Ww' : Matrix m' q ℝ) (M : Matrix p q ℝ) (hM : M ≠ 0) :
    ∃ x : p → ℝ, x ᵥ* M + vanillaBlock Real.tanh Wr Ww x ≠ vanillaBlock Real.tanh Wr' Ww' x := by
  sorry

end Skips
