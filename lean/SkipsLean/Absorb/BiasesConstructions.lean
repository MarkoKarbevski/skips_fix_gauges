import SkipsLean.Absorb.Block
import SkipsLean.Absorb.AttentionBlock
import SkipsLean.Activations.ReLU
import SkipsLean.Activations.Gaussian
import SkipsLean.OneBlock.UnitsSwiGLU

/-!
# Blocks with biases: the constructions, and the blocks that never absorb

Paper (absorb paper), Appendix C. "Blocks with biases. A vanilla MLP block with biases computes
`B_θ(x) = f(x W_read + b) W_write + c`, with `θ = (W_read, b, W_write, c)`, a unit bias
`b ∈ ℝ^{1×m}` and an output bias `c ∈ ℝ^{1×d_model}` […]. In a gated block with biases, unit `j` has
a gate read `g_j` (a column of `W_g`) and a gate bias `b^g_j`, a value read `v_j` (a column of
`W_v`) and a value bias `b^v_j`, and a write `ŵ_j`, and
`B_θ(x) = ∑_j σ(x g_j + b^g_j) (x v_j + b^v_j) ŵ_j + c`. An attention block with biases adds a bias
row to every query, key and value and to its output: with `1` the column of `T` ones,
`B_θ(h) = ∑_i P_i(h) (h W_{V,i} + 1 b_{V,i}) W_{O,i} + 1 b_O`, where `P_i(h)` is the softmax, row by
row, of `(h W_{Q,i} + 1 b_{Q,i})(h W_{K,i} + 1 b_{K,i})^⊤ / √d_h`, with or without a causal mask.
[…] A block absorbs `x M`, for `M ≠ 0`, if a block of the same kind with biases satisfies (2), or
for attention, with the same mask, `h M + B_θ(h) = B_{θ′}(h)` for all `h ∈ ℝ^{T × d_model}`."

Theorem C.1 (Exact absorption with biases): "Let blocks have biases, and let `M ≠ 0`. (i) Every
ReLU, GELU, ReLU², ReGLU, SwiGLU or GeGLU block absorbs `x M` with more hidden units. (ii) No tanh
block and no attention block as above absorbs `x M`, at any width. (iii) For generic `θ`, no block
`B_{θ′}` of these kinds and of the same width as `B_θ` satisfies (2)."

Here: the three kinds of block with biases (`vanillaBlockB`, `gatedBlockB`, `attentionBlockB`), the
constructions of the proof of Theorem C.1 (i) with their numbers of new units ("The constructions
also give the upper bounds of Theorem C.2"; Remark C.3), and Theorem C.1 (ii).

* Gated: "A unit with gate read `0` and gate bias `1` computes `σ(1) (x v + b^v) ŵ`, which is
  affine in `x`, and `σ(1) ≠ 0` for ReLU, SiLU and GELU. […] So `rank M ≤ d_model` units add `x M`."
* ReLU and GELU (`σ(z) − σ(−z) = z`): "Two new units with reads `±e_a`, biases `0` and writes
  `±M_a` add `(x e_a) M_a`, so `2 d_model` new units add `x M`. If the read has rank `d_model` […]
  with `d_model` new units."
* ReLU²: "`4 d_model` new units add `x M`. If the read has rank `d_model` […]: `3 d_model` new
  units."
* tanh: "`B_{θ′} − B_θ` is bounded, and `x M` is not."
* Attention: on inputs whose rows are all equal, and with one row moved, the sums of the
  value–output products of the two blocks agree, so `M = 0`. The paper's proof looks at "the second
  row, which sees the first token with or without a causal mask"; the statement here is for any
  mask in which some token sees another token (if every token sees itself only, the block is affine
  and absorbs `h M` with more heads).

Not stated here: Theorem C.1 (iii), the lower bounds of Theorem C.2, Lemma C.8, the construction
with `d (d + 3)/2` units of Remark C.3, rotary embeddings (Proposition C.6). The statements are for
rectangular weights (`p` inputs, `q` outputs), as in `Absorb/Block.lean`; a width is an index type,
and a block "with `k` more hidden units" has the units `m ⊕ k`.
-/

namespace Skips

open Matrix

variable {p q m m' : Type*} [Fintype p] [Fintype m] [Fintype m']

/-- **A vanilla MLP block with biases** on a row: `B_θ(x) = σ(x W_read + b) W_write + c`. -/
def vanillaBlockB (σ : ℝ → ℝ) (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ)
    (x : p → ℝ) : q → ℝ :=
  (fun i => σ ((x ᵥ* Wr) i + b i)) ᵥ* Ww + c

/-- **A gated block with biases** on a row: unit `j` computes
`σ(x g_j + b^g_j) (x v_j + b^v_j)`, and `B_θ(x) = ∑_j σ(x g_j + b^g_j) (x v_j + b^v_j) ŵ_j + c`. -/
def gatedBlockB (σ : ℝ → ℝ) (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ)
    (Ww : Matrix m q ℝ) (c : q → ℝ) (x : p → ℝ) : q → ℝ :=
  (fun j => σ ((x ᵥ* Wg) j + bg j) * ((x ᵥ* Wv) j + bv j)) ᵥ* Ww + c

/-- **An attention block with biases:** `H` heads of dimension `d_h`, a bias row for every query,
key and value and for the output:
`B_θ(h) = ∑_i P_i(h) (h W_{V,i} + 1 b_{V,i}) W_{O,i} + 1 b_O`, with `P_i(h)` the softmax, row by
row over the tokens that a token sees, of
`(h W_{Q,i} + 1 b_{Q,i})(h W_{K,i} + 1 b_{K,i})^⊤ / √d_h`. -/
noncomputable def attentionBlockB {T d H dh : Type*} [Fintype T] [Fintype d] [Fintype H]
    [Fintype dh] (sees : T → T → Prop) [DecidableRel sees] (WQ WK WV : H → Matrix d dh ℝ)
    (bQ bK bV : H → dh → ℝ) (WO : H → Matrix dh d ℝ) (bO : d → ℝ) (h : Matrix T d ℝ) :
    Matrix T d ℝ :=
  (∑ i, attnWeights sees ((Real.sqrt (Fintype.card dh))⁻¹ •
        ((h * WQ i + Matrix.of fun _ => bQ i) * (h * WK i + Matrix.of fun _ => bK i)ᵀ))
      * (h * WV i + Matrix.of fun _ => bV i) * WO i)
    + Matrix.of fun _ => bO

/-! ### Theorem C.1 (i): the constructions -/

/-- **Theorem C.1 (i) for gated blocks (ReGLU, SwiGLU, GeGLU), with `d` more units:** if
`σ(1) ≠ 0`, every gated block with biases absorbs `x M` with one more hidden unit per coordinate
of the input. -/
theorem exists_gatedBlockB_add_linear [DecidableEq p] {σ : ℝ → ℝ} (hσ : σ 1 ≠ 0)
    (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (M : Matrix p q ℝ) :
    ∃ (Wg' : Matrix p (m ⊕ p) ℝ) (bg' : m ⊕ p → ℝ) (Wv' : Matrix p (m ⊕ p) ℝ)
      (bv' : m ⊕ p → ℝ) (Ww' : Matrix (m ⊕ p) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* M + gatedBlockB σ Wg bg Wv bv Ww c x
        = gatedBlockB σ Wg' bg' Wv' bv' Ww' c' x := by
  sorry

/-- **Remark C.3, "Every gated block absorbs `x M` with `rank M` more units":** if `σ(1) ≠ 0`,
every gated block with biases absorbs `x M` with `rank M` more hidden units. -/
theorem exists_gatedBlockB_add_linear_rank [Fintype q] {σ : ℝ → ℝ} (hσ : σ 1 ≠ 0)
    (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (M : Matrix p q ℝ) :
    ∃ (Wg' : Matrix p (m ⊕ Fin M.rank) ℝ) (bg' : m ⊕ Fin M.rank → ℝ)
      (Wv' : Matrix p (m ⊕ Fin M.rank) ℝ) (bv' : m ⊕ Fin M.rank → ℝ)
      (Ww' : Matrix (m ⊕ Fin M.rank) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* M + gatedBlockB σ Wg bg Wv bv Ww c x
        = gatedBlockB σ Wg' bg' Wv' bv' Ww' c' x := by
  sorry

/-- **Theorem C.1 (i) for ReLU and GELU blocks, with `2 d` more units:** if
`σ(z) − σ(−z) = z`, every vanilla block with biases absorbs `x M` with two more hidden units per
coordinate of the input. -/
theorem exists_vanillaBlockB_add_linear [DecidableEq p] {σ : ℝ → ℝ}
    (hσ : ∀ z, σ z - σ (-z) = z) (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (M : Matrix p q ℝ) :
    ∃ (Wr' : Matrix p (m ⊕ (p ⊕ p)) ℝ) (b' : m ⊕ (p ⊕ p) → ℝ)
      (Ww' : Matrix (m ⊕ (p ⊕ p)) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* M + vanillaBlockB σ Wr b Ww c x = vanillaBlockB σ Wr' b' Ww' c' x := by
  sorry

/-- **The upper bound of Theorem C.2 (ii) (ReLU and GELU blocks, `d` more units):** if
`σ(z) − σ(−z) = z` and the read has rank `d` (the number of its rows), the block with biases
absorbs `x M` with `d` more hidden units. -/
theorem exists_vanillaBlockB_add_linear_of_rank [DecidableEq p] {σ : ℝ → ℝ}
    (hσ : ∀ z, σ z - σ (-z) = z) (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (hr : Wr.rank = Fintype.card p) (M : Matrix p q ℝ) :
    ∃ (Wr' : Matrix p (m ⊕ p) ℝ) (b' : m ⊕ p → ℝ) (Ww' : Matrix (m ⊕ p) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* M + vanillaBlockB σ Wr b Ww c x = vanillaBlockB σ Wr' b' Ww' c' x := by
  sorry

/-- **Theorem C.1 (i) for ReLU² blocks, with `4 d` more units:** every ReLU² block with biases
absorbs `x M` with four more hidden units per coordinate of the input. -/
theorem exists_vanillaBlockB_add_linear_reluSq [DecidableEq p] (Wr : Matrix p m ℝ) (b : m → ℝ)
    (Ww : Matrix m q ℝ) (c : q → ℝ) (M : Matrix p q ℝ) :
    ∃ (Wr' : Matrix p (m ⊕ (p × Fin 4)) ℝ) (b' : m ⊕ (p × Fin 4) → ℝ)
      (Ww' : Matrix (m ⊕ (p × Fin 4)) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ,
        x ᵥ* M + vanillaBlockB reluSq Wr b Ww c x = vanillaBlockB reluSq Wr' b' Ww' c' x := by
  sorry

/-- **The upper bound of Theorem C.2 (iii) (ReLU² blocks, `3 d` more units):** if the read has
rank `d` (the number of its rows), the ReLU² block with biases absorbs `x M` with `3 d` more hidden
units. -/
theorem exists_vanillaBlockB_add_linear_reluSq_of_rank [DecidableEq p] (Wr : Matrix p m ℝ)
    (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ) (hr : Wr.rank = Fintype.card p)
    (M : Matrix p q ℝ) :
    ∃ (Wr' : Matrix p (m ⊕ (p × Fin 3)) ℝ) (b' : m ⊕ (p × Fin 3) → ℝ)
      (Ww' : Matrix (m ⊕ (p × Fin 3)) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ,
        x ᵥ* M + vanillaBlockB reluSq Wr b Ww c x = vanillaBlockB reluSq Wr' b' Ww' c' x := by
  sorry

/-! ### Theorem C.1 (i) and the upper bounds of Theorem C.2, by the names of the blocks -/

/-- **Theorem C.1 (i) for ReGLU blocks, and the upper bound of Theorem C.2 (i):** every ReGLU block
with biases absorbs `x M` with `d` more hidden units. -/
theorem exists_gatedBlockB_add_linear_reglu [DecidableEq p] (Wg : Matrix p m ℝ) (bg : m → ℝ)
    (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ) (M : Matrix p q ℝ) :
    ∃ (Wg' : Matrix p (m ⊕ p) ℝ) (bg' : m ⊕ p → ℝ) (Wv' : Matrix p (m ⊕ p) ℝ)
      (bv' : m ⊕ p → ℝ) (Ww' : Matrix (m ⊕ p) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* M + gatedBlockB relu Wg bg Wv bv Ww c x
        = gatedBlockB relu Wg' bg' Wv' bv' Ww' c' x := by
  sorry

/-- **Theorem C.1 (i) for SwiGLU blocks, and the upper bound of Theorem C.2 (i):** every SwiGLU
block with biases absorbs `x M` with `d` more hidden units. -/
theorem exists_gatedBlockB_add_linear_swiglu [DecidableEq p] (Wg : Matrix p m ℝ) (bg : m → ℝ)
    (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ) (M : Matrix p q ℝ) :
    ∃ (Wg' : Matrix p (m ⊕ p) ℝ) (bg' : m ⊕ p → ℝ) (Wv' : Matrix p (m ⊕ p) ℝ)
      (bv' : m ⊕ p → ℝ) (Ww' : Matrix (m ⊕ p) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* M + gatedBlockB silu Wg bg Wv bv Ww c x
        = gatedBlockB silu Wg' bg' Wv' bv' Ww' c' x := by
  sorry

/-- **Theorem C.1 (i) for GeGLU blocks, and the upper bound of Theorem C.2 (i):** every GeGLU block
with biases absorbs `x M` with `d` more hidden units. -/
theorem exists_gatedBlockB_add_linear_geglu [DecidableEq p] (Wg : Matrix p m ℝ) (bg : m → ℝ)
    (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ) (M : Matrix p q ℝ) :
    ∃ (Wg' : Matrix p (m ⊕ p) ℝ) (bg' : m ⊕ p → ℝ) (Wv' : Matrix p (m ⊕ p) ℝ)
      (bv' : m ⊕ p → ℝ) (Ww' : Matrix (m ⊕ p) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* M + gatedBlockB gelu Wg bg Wv bv Ww c x
        = gatedBlockB gelu Wg' bg' Wv' bv' Ww' c' x := by
  sorry

/-- **Theorem C.1 (i) for ReLU blocks:** every ReLU block with biases absorbs `x M` with `2 d` more
hidden units. -/
theorem exists_vanillaBlockB_add_linear_relu [DecidableEq p] (Wr : Matrix p m ℝ) (b : m → ℝ)
    (Ww : Matrix m q ℝ) (c : q → ℝ) (M : Matrix p q ℝ) :
    ∃ (Wr' : Matrix p (m ⊕ (p ⊕ p)) ℝ) (b' : m ⊕ (p ⊕ p) → ℝ)
      (Ww' : Matrix (m ⊕ (p ⊕ p)) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ,
        x ᵥ* M + vanillaBlockB relu Wr b Ww c x = vanillaBlockB relu Wr' b' Ww' c' x := by
  sorry

/-- **Theorem C.1 (i) for GELU blocks:** every GELU block with biases absorbs `x M` with `2 d` more
hidden units. -/
theorem exists_vanillaBlockB_add_linear_gelu [DecidableEq p] (Wr : Matrix p m ℝ) (b : m → ℝ)
    (Ww : Matrix m q ℝ) (c : q → ℝ) (M : Matrix p q ℝ) :
    ∃ (Wr' : Matrix p (m ⊕ (p ⊕ p)) ℝ) (b' : m ⊕ (p ⊕ p) → ℝ)
      (Ww' : Matrix (m ⊕ (p ⊕ p)) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ,
        x ᵥ* M + vanillaBlockB gelu Wr b Ww c x = vanillaBlockB gelu Wr' b' Ww' c' x := by
  sorry

/-- **The upper bound of Theorem C.2 (ii) for ReLU blocks:** a ReLU block with biases whose read
has rank `d` absorbs `x M` with `d` more hidden units. -/
theorem exists_vanillaBlockB_add_linear_relu_of_rank [DecidableEq p] (Wr : Matrix p m ℝ)
    (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ) (hr : Wr.rank = Fintype.card p)
    (M : Matrix p q ℝ) :
    ∃ (Wr' : Matrix p (m ⊕ p) ℝ) (b' : m ⊕ p → ℝ) (Ww' : Matrix (m ⊕ p) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ,
        x ᵥ* M + vanillaBlockB relu Wr b Ww c x = vanillaBlockB relu Wr' b' Ww' c' x := by
  sorry

/-- **The upper bound of Theorem C.2 (ii) for GELU blocks:** a GELU block with biases whose read
has rank `d` absorbs `x M` with `d` more hidden units. -/
theorem exists_vanillaBlockB_add_linear_gelu_of_rank [DecidableEq p] (Wr : Matrix p m ℝ)
    (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ) (hr : Wr.rank = Fintype.card p)
    (M : Matrix p q ℝ) :
    ∃ (Wr' : Matrix p (m ⊕ p) ℝ) (b' : m ⊕ p → ℝ) (Ww' : Matrix (m ⊕ p) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ,
        x ᵥ* M + vanillaBlockB gelu Wr b Ww c x = vanillaBlockB gelu Wr' b' Ww' c' x := by
  sorry

/-! ### Theorem C.1 (ii): tanh blocks and attention blocks never absorb -/

/-- **Theorem C.1 (ii) for tanh blocks:** for a bounded activation (tanh), no block with biases,
of any width, absorbs `x M` with `M ≠ 0`. -/
theorem forall_exists_ne_vanillaBlockB_of_bounded {σ : ℝ → ℝ}
    (hσ : ∃ C : ℝ, ∀ z, |σ z| ≤ C) (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (Wr' : Matrix p m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' q ℝ) (c' : q → ℝ)
    (M : Matrix p q ℝ) (hM : M ≠ 0) :
    ∃ x : p → ℝ, x ᵥ* M + vanillaBlockB σ Wr b Ww c x ≠ vanillaBlockB σ Wr' b' Ww' c' x := by
  sorry

/-- **Theorem C.1 (ii) for tanh blocks, by name.** -/
theorem forall_exists_ne_vanillaBlockB_tanh (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (Wr' : Matrix p m' ℝ) (b' : m' → ℝ) (Ww' : Matrix m' q ℝ) (c' : q → ℝ)
    (M : Matrix p q ℝ) (hM : M ≠ 0) :
    ∃ x : p → ℝ,
      x ᵥ* M + vanillaBlockB Real.tanh Wr b Ww c x ≠ vanillaBlockB Real.tanh Wr' b' Ww' c' x := by
  sorry

/-- **Theorem C.1 (ii) for attention blocks with biases:** with a mask in which some token sees
another token, no attention block with biases, with any number of heads and any head dimension,
absorbs `h M` with `M ≠ 0`. -/
theorem forall_exists_ne_attentionBlockB {T d H dh H' dh' : Type*} [Fintype T] [Fintype d]
    [Fintype H] [Fintype dh] [Fintype H'] [Fintype dh'] (sees : T → T → Prop)
    [DecidableRel sees] (hsees : ∃ t₁ t₂, t₁ ≠ t₂ ∧ sees t₂ t₁)
    (WQ WK WV : H → Matrix d dh ℝ) (bQ bK bV : H → dh → ℝ) (WO : H → Matrix dh d ℝ)
    (bO : d → ℝ) (WQ' WK' WV' : H' → Matrix d dh' ℝ) (bQ' bK' bV' : H' → dh' → ℝ)
    (WO' : H' → Matrix dh' d ℝ) (bO' : d → ℝ) (M : Matrix d d ℝ) (hM : M ≠ 0) :
    ∃ h : Matrix T d ℝ, h * M + attentionBlockB sees WQ WK WV bQ bK bV WO bO h
      ≠ attentionBlockB sees WQ' WK' WV' bQ' bK' bV' WO' bO' h := by
  sorry

end Skips
