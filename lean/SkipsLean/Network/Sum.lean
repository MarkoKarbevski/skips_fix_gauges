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
  -- the two parts of the argument are `h R_A` and `h R_B`
  have hl : (h * R).submatrix id Sum.inl = h * R.submatrix id Sum.inl := rfl
  have hr : (h * R).submatrix id Sum.inr = h * R.submatrix id Sum.inr := rfl
  show (Matrix.of fun t p => Sum.elim (A.f ℓ ((h * R).submatrix id Sum.inl) t)
    (B.f ℓ ((h * R).submatrix id Sum.inr) t) p) * W = _
  rw [hl, hr]
  -- entry `(t, a)`: the sum over the rows of `W` splits into the rows of `W_A` and of `W_B`
  ext t a
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.of_apply, Sum.elim_inl,
    Sum.elim_inr, Matrix.add_apply, Matrix.submatrix_apply, id]

/-- **A block without a second part is a block of `A`:** if block `ℓ` of `B` has no write row
(for an MLP block: no hidden unit), block `ℓ` of `A.sum B` is block `ℓ` of `A`. -/
theorem f_sum_mul_of_isEmpty_right (ℓ : Fin L) [IsEmpty (B.w ℓ)] (h : Matrix T d ℝ)
    (R : Matrix d (A.r ℓ ⊕ B.r ℓ) ℝ) (W : Matrix (A.w ℓ ⊕ B.w ℓ) d ℝ) :
    (A.sum B).f ℓ (h * R) * W
      = A.f ℓ (h * R.submatrix id Sum.inl) * W.submatrix Sum.inl id := by
  -- the rows of `W_B` form an empty matrix, so the second term is `0`
  have h0 : W.submatrix Sum.inr id = 0 := Matrix.ext fun j _ => isEmptyElim j
  rw [f_sum_mul, h0, Matrix.mul_zero, add_zero]

/-- **A block without a first part is a block of `B`:** if block `ℓ` of `A` has no write row (for
an attention block: no head), block `ℓ` of `A.sum B` is block `ℓ` of `B`. -/
theorem f_sum_mul_of_isEmpty_left (ℓ : Fin L) [IsEmpty (A.w ℓ)] (h : Matrix T d ℝ)
    (R : Matrix d (A.r ℓ ⊕ B.r ℓ) ℝ) (W : Matrix (A.w ℓ ⊕ B.w ℓ) d ℝ) :
    (A.sum B).f ℓ (h * R) * W
      = B.f ℓ (h * R.submatrix id Sum.inr) * W.submatrix Sum.inr id := by
  -- the rows of `W_A` form an empty matrix, so the first term is `0`
  have h0 : W.submatrix Sum.inl id = 0 := Matrix.ext fun j _ => isEmptyElim j
  rw [f_sum_mul, h0, Matrix.mul_zero, zero_add]

variable {A B}

/-- Helper: taking some columns of a matrix is real-analytic (it is linear). -/
private theorem analyticOnNhd_submatrix_sum {m n₁ n₂ : Type*} [Fintype m] [Fintype n₁]
    [Fintype n₂] (c : n₁ → n₂) :
    AnalyticOnNhd ℝ (fun M : Matrix m n₂ ℝ => M.submatrix id c) Set.univ := by
  show AnalyticOnNhd ℝ (fun M : Matrix m n₂ ℝ => fun t => fun k => M t (c k)) Set.univ
  exact AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun k => analyticOnNhd_matrix_entry t (c k)

/-- Helper: taking some columns of a matrix is differentiable. -/
private theorem differentiable_submatrix_sum {m n₁ n₂ : Type*} [Fintype m] [Fintype n₁]
    [Fintype n₂] (c : n₁ → n₂) :
    Differentiable ℝ (fun M : Matrix m n₂ ℝ => M.submatrix id c) :=
  fun M => (analyticOnNhd_submatrix_sum c M (Set.mem_univ M)).differentiableAt

/-- Helper (a copy of a private helper of `Absorb/RMSNormGeneric.lean`): a map into a finite
product of spaces, with the largest distance of the coordinates, is locally Lipschitz if each
coordinate is. -/
private theorem locallyLipschitz_pi_of_forall_sum {α ι : Type*} [PseudoEMetricSpace α]
    [Fintype ι] {β : ι → Type*} [∀ i, PseudoEMetricSpace (β i)] {g : α → ∀ i, β i}
    (h : ∀ i, LocallyLipschitz fun x => g x i) : LocallyLipschitz g := by
  intro x
  choose K t ht hK using fun i => h i x
  refine ⟨∑ i, K i, ⋂ i, t i, Filter.iInter_mem.2 ht, fun y hy z hz => ?_⟩
  rw [edist_pi_le_iff]
  intro i
  calc edist (g y i) (g z i) ≤ K i * edist y z :=
        hK i (Set.mem_iInter.1 hy i) (Set.mem_iInter.1 hz i)
    _ ≤ (∑ j, K j : NNReal) * edist y z := by
        gcongr
        exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)

/-- Helper (copy): a map into matrices (elementwise norm) is locally Lipschitz if every entry
is. -/
private theorem locallyLipschitz_matrix_of_forall_sum {α m n : Type*} [PseudoEMetricSpace α]
    [Fintype m] [Fintype n] {g : α → Matrix m n ℝ}
    (h : ∀ i j, LocallyLipschitz fun x => g x i j) : LocallyLipschitz g :=
  locallyLipschitz_pi_of_forall_sum fun i => locallyLipschitz_pi_of_forall_sum fun j => h i j

/-- Helper (copy): an entry of a matrix is a `1`-Lipschitz function of the matrix. -/
private theorem locallyLipschitz_entry_sum {m n : Type*} [Fintype m] [Fintype n] (i : m)
    (j : n) : LocallyLipschitz fun M : Matrix m n ℝ => M i j :=
  ((LipschitzWith.eval (α := fun _ : n => ℝ) j).comp
    (LipschitzWith.eval (α := fun _ : m => n → ℝ) i)).locallyLipschitz

/-- Helper: taking some columns of a matrix is locally Lipschitz. -/
private theorem locallyLipschitz_submatrix_sum {m n₁ n₂ : Type*} [Fintype m] [Fintype n₁]
    [Fintype n₂] (c : n₁ → n₂) :
    LocallyLipschitz (fun M : Matrix m n₂ ℝ => M.submatrix id c) :=
  locallyLipschitz_matrix_of_forall_sum fun t k => locallyLipschitz_entry_sum t (c k)

/-- The map of a block of the sum is real-analytic if the maps of the two blocks are. -/
theorem analyticOnNhd_f_sum {ℓ : Fin L} (hA : AnalyticOnNhd ℝ (A.f ℓ) Set.univ)
    (hB : AnalyticOnNhd ℝ (B.f ℓ) Set.univ) : AnalyticOnNhd ℝ ((A.sum B).f ℓ) Set.univ := by
  -- the maps `M ↦ f_ℓ^A (M_A)` and `M ↦ f_ℓ^B (M_B)` are analytic
  have hA' := hA.comp (analyticOnNhd_submatrix_sum (m := T) (n₂ := A.r ℓ ⊕ B.r ℓ) Sum.inl)
    (Set.mapsTo_univ _ _)
  have hB' := hB.comp (analyticOnNhd_submatrix_sum (m := T) (n₂ := A.r ℓ ⊕ B.r ℓ) Sum.inr)
    (Set.mapsTo_univ _ _)
  show AnalyticOnNhd ℝ (fun M : Matrix T (A.r ℓ ⊕ B.r ℓ) ℝ => fun t => fun p =>
    Sum.elim (A.f ℓ (M.submatrix id Sum.inl) t) (B.f ℓ (M.submatrix id Sum.inr) t) p) Set.univ
  -- entry by entry: an entry of the output of `f_ℓ^A` or of `f_ℓ^B`
  refine AnalyticOnNhd.pi fun t => AnalyticOnNhd.pi fun p => ?_
  cases p with
  | inl a => exact (analyticOnNhd_matrix_entry t a).comp hA' (Set.mapsTo_univ _ _)
  | inr b => exact (analyticOnNhd_matrix_entry t b).comp hB' (Set.mapsTo_univ _ _)

/-- The map of a block of the sum is differentiable if the maps of the two blocks are. -/
theorem differentiable_f_sum {ℓ : Fin L} (hA : Differentiable ℝ (A.f ℓ))
    (hB : Differentiable ℝ (B.f ℓ)) : Differentiable ℝ ((A.sum B).f ℓ) := by
  -- the maps `M ↦ f_ℓ^A (M_A)` and `M ↦ f_ℓ^B (M_B)` are differentiable
  have hA' := hA.comp (differentiable_submatrix_sum (m := T) (n₂ := A.r ℓ ⊕ B.r ℓ) Sum.inl)
  have hB' := hB.comp (differentiable_submatrix_sum (m := T) (n₂ := A.r ℓ ⊕ B.r ℓ) Sum.inr)
  show Differentiable ℝ (fun M : Matrix T (A.r ℓ ⊕ B.r ℓ) ℝ => fun t => fun p =>
    Sum.elim (A.f ℓ (M.submatrix id Sum.inl) t) (B.f ℓ (M.submatrix id Sum.inr) t) p)
  -- entry by entry: an entry of the output of `f_ℓ^A` or of `f_ℓ^B`
  refine differentiable_pi.2 fun t => differentiable_pi.2 fun p => ?_
  cases p with
  | inl a => exact differentiable_pi.1 (differentiable_pi.1 hA' t) a
  | inr b => exact differentiable_pi.1 (differentiable_pi.1 hB' t) b

/-- The map of a block of the sum is continuous if the maps of the two blocks are. -/
theorem continuous_f_sum {ℓ : Fin L} (hA : Continuous (A.f ℓ)) (hB : Continuous (B.f ℓ)) :
    Continuous ((A.sum B).f ℓ) := by
  -- the maps `M ↦ f_ℓ^A (M_A)` and `M ↦ f_ℓ^B (M_B)` are continuous
  have hA' : Continuous fun M : Matrix T (A.r ℓ ⊕ B.r ℓ) ℝ => A.f ℓ (M.submatrix id Sum.inl) :=
    hA.comp (differentiable_submatrix_sum Sum.inl).continuous
  have hB' : Continuous fun M : Matrix T (A.r ℓ ⊕ B.r ℓ) ℝ => B.f ℓ (M.submatrix id Sum.inr) :=
    hB.comp (differentiable_submatrix_sum Sum.inr).continuous
  show Continuous (fun M : Matrix T (A.r ℓ ⊕ B.r ℓ) ℝ => fun t => fun p =>
    Sum.elim (A.f ℓ (M.submatrix id Sum.inl) t) (B.f ℓ (M.submatrix id Sum.inr) t) p)
  -- entry by entry: an entry of the output of `f_ℓ^A` or of `f_ℓ^B`
  refine continuous_pi fun t => continuous_pi fun p => ?_
  cases p with
  | inl a => exact (continuous_apply a).comp ((continuous_apply t).comp hA')
  | inr b => exact (continuous_apply b).comp ((continuous_apply t).comp hB')

/-- The map of a block of the sum is locally Lipschitz if the maps of the two blocks are. -/
theorem locallyLipschitz_f_sum {ℓ : Fin L} (hA : LocallyLipschitz (A.f ℓ))
    (hB : LocallyLipschitz (B.f ℓ)) : LocallyLipschitz ((A.sum B).f ℓ) := by
  -- the maps `M ↦ f_ℓ^A (M_A)` and `M ↦ f_ℓ^B (M_B)` are locally Lipschitz
  have hA' := hA.comp (locallyLipschitz_submatrix_sum (m := T) (n₂ := A.r ℓ ⊕ B.r ℓ) Sum.inl)
  have hB' := hB.comp (locallyLipschitz_submatrix_sum (m := T) (n₂ := A.r ℓ ⊕ B.r ℓ) Sum.inr)
  -- entry by entry: an entry of the output of `f_ℓ^A` or of `f_ℓ^B`
  refine locallyLipschitz_matrix_of_forall_sum fun t p => ?_
  cases p with
  | inl a => exact (locallyLipschitz_entry_sum t a).comp hA'
  | inr b => exact (locallyLipschitz_entry_sum t b).comp hB'

end Skips
