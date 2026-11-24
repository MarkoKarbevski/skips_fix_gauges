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
also give the upper bounds of Theorem C.2"; Remark C.3), and Theorem C.1 (ii) for tanh blocks.
Theorem C.1 (ii) for attention blocks is in `Absorb/BiasesAttention.lean`.

* Gated: "A unit with gate read `0` and gate bias `1` computes `σ(1) (x v + b^v) ŵ`, which is
  affine in `x`, and `σ(1) ≠ 0` for ReLU, SiLU and GELU. […] So `rank M ≤ d_model` units add `x M`."
* ReLU and GELU (`σ(z) − σ(−z) = z`): "Two new units with reads `±e_a`, biases `0` and writes
  `±M_a` add `(x e_a) M_a`, so `2 d_model` new units add `x M`. If the read has rank `d_model` […]
  with `d_model` new units."
* ReLU²: "`4 d_model` new units add `x M`. If the read has rank `d_model` […]: `3 d_model` new
  units."
* tanh: "`B_{θ′} − B_θ` is bounded, and `x M` is not."

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

/-- The entry `o` of `f ᵥ* W` as a sum over the rows. -/
private theorem vecMul_apply_bc {n : Type*} [Fintype n] (f : n → ℝ) (W : Matrix n q ℝ) (o : q) :
    (f ᵥ* W) o = ∑ i, f i * W i o := rfl

/-- A vanilla block with biases whose old units keep their reads and biases, whose old writes get
`D` added, with new units `k`: it is the old block, plus `σ(x W_read + b) D`, plus the new units,
plus `c' - c`. -/
private theorem vanillaBlockB_sum_bc {k : Type*} [Fintype k] (σ : ℝ → ℝ) (Wr : Matrix p m ℝ)
    (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ) (Wn : Matrix p k ℝ) (bn : k → ℝ)
    (D : Matrix m q ℝ) (Wwn : Matrix k q ℝ) (c' : q → ℝ) (x : p → ℝ) :
    vanillaBlockB σ (Matrix.of fun i s => Sum.elim (Wr i) (Wn i) s) (Sum.elim b bn)
        (Matrix.of fun s o => Sum.elim (fun j => Ww j o + D j o) (fun l => Wwn l o) s) c' x
      = vanillaBlockB σ Wr b Ww c x + (fun j => σ ((x ᵥ* Wr) j + b j)) ᵥ* D
        + (fun l => σ ((x ᵥ* Wn) l + bn l)) ᵥ* Wwn + (c' - c) := by
  funext o
  simp only [vanillaBlockB, vecMul_apply_bc, Fintype.sum_sum_type, Matrix.of_apply, Sum.elim_inl,
    Sum.elim_inr, Pi.add_apply, Pi.sub_apply, mul_add, Finset.sum_add_distrib]
  ring

/-- The same for a gated block with biases (no change of the old writes). -/
private theorem gatedBlockB_sum_bc {k : Type*} [Fintype k] (σ : ℝ → ℝ) (Wg : Matrix p m ℝ)
    (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ)
    (Wgn : Matrix p k ℝ) (bgn : k → ℝ) (Wvn : Matrix p k ℝ) (bvn : k → ℝ) (Wwn : Matrix k q ℝ)
    (c' : q → ℝ) (x : p → ℝ) :
    gatedBlockB σ (Matrix.of fun i s => Sum.elim (Wg i) (Wgn i) s) (Sum.elim bg bgn)
        (Matrix.of fun i s => Sum.elim (Wv i) (Wvn i) s) (Sum.elim bv bvn)
        (Matrix.of fun s o => Sum.elim (fun j => Ww j o) (fun l => Wwn l o) s) c' x
      = gatedBlockB σ Wg bg Wv bv Ww c x
        + (fun l => σ ((x ᵥ* Wgn) l + bgn l) * ((x ᵥ* Wvn) l + bvn l)) ᵥ* Wwn + (c' - c) := by
  funext o
  simp only [gatedBlockB, vecMul_apply_bc, Fintype.sum_sum_type, Matrix.of_apply, Sum.elim_inl,
    Sum.elim_inr, Pi.add_apply, Pi.sub_apply]
  ring

/-- **The gated construction for a factorization `M = A B`:** if `σ(1) ≠ 0`, new units with gate
read `0`, gate bias `1`, value read the columns of `A`, value bias `0` and writes `σ(1)⁻¹ B_k` add
`x A B`. -/
private theorem exists_gatedBlockB_add_mul_bc {k : Type*} [Fintype k] {σ : ℝ → ℝ}
    (hσ : σ 1 ≠ 0) (Wg : Matrix p m ℝ) (bg : m → ℝ) (Wv : Matrix p m ℝ) (bv : m → ℝ)
    (Ww : Matrix m q ℝ) (c : q → ℝ) (A : Matrix p k ℝ) (B : Matrix k q ℝ) :
    ∃ (Wg' : Matrix p (m ⊕ k) ℝ) (bg' : m ⊕ k → ℝ) (Wv' : Matrix p (m ⊕ k) ℝ)
      (bv' : m ⊕ k → ℝ) (Ww' : Matrix (m ⊕ k) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* (A * B) + gatedBlockB σ Wg bg Wv bv Ww c x
        = gatedBlockB σ Wg' bg' Wv' bv' Ww' c' x := by
  refine ⟨Matrix.of fun i s => Sum.elim (Wg i) ((0 : Matrix p k ℝ) i) s,
    Sum.elim bg (fun _ => 1), Matrix.of fun i s => Sum.elim (Wv i) (A i) s,
    Sum.elim bv (fun _ => 0),
    Matrix.of fun s o => Sum.elim (fun j => Ww j o) (fun l => ((σ 1)⁻¹ • B) l o) s, c,
    fun x => ?_⟩
  rw [gatedBlockB_sum_bc σ Wg bg Wv bv Ww c 0 _ A _ ((σ 1)⁻¹ • B)]
  -- unit `l` computes `σ(1) (x A)_l`
  have hu : (fun l => σ ((x ᵥ* (0 : Matrix p k ℝ)) l + 1) * ((x ᵥ* A) l + 0))
      = σ 1 • (x ᵥ* A) := by
    funext l
    simp only [Matrix.vecMul_zero, Pi.zero_apply, zero_add, add_zero, Pi.smul_apply, smul_eq_mul]
  rw [hu, Matrix.smul_vecMul, Matrix.vecMul_smul, smul_smul, mul_inv_cancel₀ hσ, one_smul,
    Matrix.vecMul_vecMul, sub_self, add_zero, add_comm]

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
  -- `M = 1 M`: the new unit `a` has the value read `e_a`
  have h := exists_gatedBlockB_add_mul_bc hσ Wg bg Wv bv Ww c 1 M
  rwa [Matrix.one_mul] at h

/-- **A rank factorization:** `M = A B` with `rank M` columns in `A`: `B` holds a basis of the span
of the rows of `M`, and `A` the coordinates of the rows in it. -/
private theorem exists_mul_eq_rank_bc [Fintype q] (M : Matrix p q ℝ) :
    ∃ (A : Matrix p (Fin M.rank) ℝ) (B : Matrix (Fin M.rank) q ℝ), M = A * B := by
  classical
  set W := Submodule.span ℝ (Set.range M.row) with hW
  let β : Module.Basis (Fin M.rank) ℝ W :=
    Module.finBasisOfFinrankEq ℝ W (M.rank_eq_finrank_span_row).symm
  have hmem : ∀ i, M i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  refine ⟨Matrix.of fun i l => β.repr ⟨M i, hmem i⟩ l, Matrix.of fun l => (β l : q → ℝ), ?_⟩
  funext i o
  have h := β.sum_repr ⟨M i, hmem i⟩
  have h2 := congrArg (fun v : W => (v : q → ℝ) o) h
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h2
  rw [Matrix.mul_apply]
  simpa only [Matrix.of_apply] using h2.symm

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
  obtain ⟨A, B, hAB⟩ := exists_mul_eq_rank_bc M
  have h := exists_gatedBlockB_add_mul_bc hσ Wg bg Wv bv Ww c A B
  rwa [← hAB] at h

/-- **Mirror units for a factorization `M = A B`:** if `σ(z) − σ(−z) = z`, the new units `inl l`
(read the column `l` of `A`, bias `0`, write `B_l`) and `inr l` (read and write negated) add
`x A B`. -/
private theorem exists_vanillaBlockB_add_mul_bc {k : Type*} [Fintype k] {σ : ℝ → ℝ}
    (hσ : ∀ z, σ z - σ (-z) = z) (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (A : Matrix p k ℝ) (B : Matrix k q ℝ) :
    ∃ (Wr' : Matrix p (m ⊕ (k ⊕ k)) ℝ) (b' : m ⊕ (k ⊕ k) → ℝ)
      (Ww' : Matrix (m ⊕ (k ⊕ k)) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* (A * B) + vanillaBlockB σ Wr b Ww c x
        = vanillaBlockB σ Wr' b' Ww' c' x := by
  obtain ⟨Wn, hWn⟩ : ∃ Wn : Matrix p (k ⊕ k) ℝ,
      Wn = Matrix.of fun i s => Sum.elim (fun l => A i l) (fun l => -A i l) s := ⟨_, rfl⟩
  obtain ⟨Wwn, hWwn⟩ : ∃ Wwn : Matrix (k ⊕ k) q ℝ,
      Wwn = Matrix.of fun s o => Sum.elim (fun l => B l o) (fun l => -B l o) s := ⟨_, rfl⟩
  refine ⟨Matrix.of fun i s => Sum.elim (Wr i) (Wn i) s, Sum.elim b 0,
    Matrix.of fun s o => Sum.elim (fun j => Ww j o + (0 : Matrix m q ℝ) j o)
      (fun l => Wwn l o) s, c, fun x => ?_⟩
  rw [vanillaBlockB_sum_bc σ Wr b Ww c Wn 0 0 Wwn c x, Matrix.vecMul_zero, add_zero, sub_self,
    add_zero, add_comm]
  congr 1
  -- the pair `inl l`, `inr l` adds `(σ y − σ (−y)) B_l = y B_l`, with `y = (x A)_l`
  funext o
  rw [← Matrix.vecMul_vecMul, vecMul_apply_bc, vecMul_apply_bc, Fintype.sum_sum_type,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h1 : (x ᵥ* Wn) (Sum.inl l) = (x ᵥ* A) l := by
    simp only [hWn, vecMul, dotProduct, Matrix.of_apply, Sum.elim_inl]
  have h2 : (x ᵥ* Wn) (Sum.inr l) = -(x ᵥ* A) l := by
    simp only [hWn, vecMul, dotProduct, Matrix.of_apply, Sum.elim_inr, mul_neg,
      Finset.sum_neg_distrib]
  simp only [h1, h2, hWwn, Pi.zero_apply, add_zero, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
  linear_combination -(B l o) * hσ ((x ᵥ* A) l)

/-- **Theorem C.1 (i) for ReLU and GELU blocks, with `2 d` more units:** if
`σ(z) − σ(−z) = z`, every vanilla block with biases absorbs `x M` with two more hidden units per
coordinate of the input. -/
theorem exists_vanillaBlockB_add_linear [DecidableEq p] {σ : ℝ → ℝ}
    (hσ : ∀ z, σ z - σ (-z) = z) (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (M : Matrix p q ℝ) :
    ∃ (Wr' : Matrix p (m ⊕ (p ⊕ p)) ℝ) (b' : m ⊕ (p ⊕ p) → ℝ)
      (Ww' : Matrix (m ⊕ (p ⊕ p)) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* M + vanillaBlockB σ Wr b Ww c x = vanillaBlockB σ Wr' b' Ww' c' x := by
  -- `M = 1 M`: the units `inl a`, `inr a` read `± e_a`
  have h := exists_vanillaBlockB_add_mul_bc hσ Wr b Ww c 1 M
  rwa [Matrix.one_mul] at h

/-- **The upper bound of Theorem C.2 (ii) (ReLU and GELU blocks, `d` more units):** if
`σ(z) − σ(−z) = z` and the read has rank `d` (the number of its rows), the block with biases
absorbs `x M` with `d` more hidden units. -/
theorem exists_vanillaBlockB_add_linear_of_rank [DecidableEq p] {σ : ℝ → ℝ}
    (hσ : ∀ z, σ z - σ (-z) = z) (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ)
    (c : q → ℝ) (hr : Wr.rank = Fintype.card p) (M : Matrix p q ℝ) :
    ∃ (Wr' : Matrix p (m ⊕ p) ℝ) (b' : m ⊕ p → ℝ) (Ww' : Matrix (m ⊕ p) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* M + vanillaBlockB σ Wr b Ww c x = vanillaBlockB σ Wr' b' Ww' c' x := by
  sorry

/-- `relu² z + relu² (−z) = z²`. -/
private theorem reluSq_add_reluSq_neg_bc (z : ℝ) : reluSq z + reluSq (-z) = z ^ 2 := by
  simp only [reluSq]
  rcases le_total z 0 with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
  · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring

/-- **Four ReLU² units for a factorization `M = A B`:** units `(l, 0)`, `(l, 1)` read `± A_{:,l}`
with biases `1`, `−1` and write `B_l / 4`; units `(l, 2)`, `(l, 3)` read `± A_{:,l}` with biases
`−1`, `1` and write `−B_l / 4`; with `y = (x A)_l` they add `((y + 1)² − (y − 1)²)/4 B_l = y B_l`. -/
private theorem exists_vanillaBlockB_add_mul_reluSq_bc {k : Type*} [Fintype k]
    (Wr : Matrix p m ℝ) (b : m → ℝ) (Ww : Matrix m q ℝ) (c : q → ℝ) (A : Matrix p k ℝ)
    (B : Matrix k q ℝ) :
    ∃ (Wr' : Matrix p (m ⊕ (k × Fin 4)) ℝ) (b' : m ⊕ (k × Fin 4) → ℝ)
      (Ww' : Matrix (m ⊕ (k × Fin 4)) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ, x ᵥ* (A * B) + vanillaBlockB reluSq Wr b Ww c x
        = vanillaBlockB reluSq Wr' b' Ww' c' x := by
  obtain ⟨Wn, hWn⟩ : ∃ Wn : Matrix p (k × Fin 4) ℝ,
      Wn = Matrix.of fun i s => ![1, -1, 1, -1] s.2 * A i s.1 := ⟨_, rfl⟩
  obtain ⟨bn, hbn⟩ : ∃ bn : k × Fin 4 → ℝ, bn = fun s => ![1, -1, -1, 1] s.2 := ⟨_, rfl⟩
  obtain ⟨Wwn, hWwn⟩ : ∃ Wwn : Matrix (k × Fin 4) q ℝ,
      Wwn = Matrix.of fun s o => ![1 / 4, 1 / 4, -(1 / 4), -(1 / 4)] s.2 * B s.1 o := ⟨_, rfl⟩
  refine ⟨Matrix.of fun i s => Sum.elim (Wr i) (Wn i) s, Sum.elim b bn,
    Matrix.of fun s o => Sum.elim (fun j => Ww j o + (0 : Matrix m q ℝ) j o)
      (fun l => Wwn l o) s, c, fun x => ?_⟩
  rw [vanillaBlockB_sum_bc reluSq Wr b Ww c Wn bn 0 Wwn c x, Matrix.vecMul_zero, add_zero,
    sub_self, add_zero, add_comm]
  congr 1
  funext o
  rw [← Matrix.vecMul_vecMul, vecMul_apply_bc, vecMul_apply_bc, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  -- the four pre-activations, with `y = (x A)_l`
  have hy : ∀ t : Fin 4, (x ᵥ* Wn) (l, t) = ![1, -1, 1, -1] t * (x ᵥ* A) l := fun t => by
    simp only [hWn, vecMul, dotProduct, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e0 : (x ᵥ* Wn) (l, 0) + bn (l, 0) = (x ᵥ* A) l + 1 := by
    rw [hy, hbn]; simp
  have e1 : (x ᵥ* Wn) (l, 1) + bn (l, 1) = -((x ᵥ* A) l + 1) := by
    rw [hy, hbn]; simp; ring
  have e2 : (x ᵥ* Wn) (l, 2) + bn (l, 2) = (x ᵥ* A) l - 1 := by
    rw [hy, hbn]; simp; ring
  have e3 : (x ᵥ* Wn) (l, 3) + bn (l, 3) = -((x ᵥ* A) l - 1) := by
    rw [hy, hbn]; simp; ring
  have w0 : Wwn (l, 0) o = 1 / 4 * B l o := by rw [hWwn]; rfl
  have w1 : Wwn (l, 1) o = 1 / 4 * B l o := by rw [hWwn]; rfl
  have w2 : Wwn (l, 2) o = -(1 / 4) * B l o := by rw [hWwn]; rfl
  have w3 : Wwn (l, 3) o = -(1 / 4) * B l o := by rw [hWwn]; rfl
  rw [Fin.sum_univ_four, e0, e1, e2, e3, w0, w1, w2, w3]
  have h1 := reluSq_add_reluSq_neg_bc ((x ᵥ* A) l + 1)
  have h2 := reluSq_add_reluSq_neg_bc ((x ᵥ* A) l - 1)
  linear_combination (-(B l o) / 4) * h1 + (B l o / 4) * h2

/-- **Theorem C.1 (i) for ReLU² blocks, with `4 d` more units:** every ReLU² block with biases
absorbs `x M` with four more hidden units per coordinate of the input. -/
theorem exists_vanillaBlockB_add_linear_reluSq [DecidableEq p] (Wr : Matrix p m ℝ) (b : m → ℝ)
    (Ww : Matrix m q ℝ) (c : q → ℝ) (M : Matrix p q ℝ) :
    ∃ (Wr' : Matrix p (m ⊕ (p × Fin 4)) ℝ) (b' : m ⊕ (p × Fin 4) → ℝ)
      (Ww' : Matrix (m ⊕ (p × Fin 4)) q ℝ) (c' : q → ℝ),
      ∀ x : p → ℝ,
        x ᵥ* M + vanillaBlockB reluSq Wr b Ww c x = vanillaBlockB reluSq Wr' b' Ww' c' x := by
  have h := exists_vanillaBlockB_add_mul_reluSq_bc Wr b Ww c 1 M
  rwa [Matrix.one_mul] at h

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

/-! ### Theorem C.1 (ii): tanh blocks never absorb -/

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

end Skips
