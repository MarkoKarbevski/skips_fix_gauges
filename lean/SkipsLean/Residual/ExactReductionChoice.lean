import SkipsLean.Residual.ExactReductionMixed
import SkipsLean.Residual.ExactReductionCount

/-!
# Exact reduction without skips: a read or a write at each hidden state

Paper (skips paper), Proposition A.9 (i): "In a skipless network or a network of mixed blocks,
the map `W ↦ W G` on the matrices that write `h_ℓ` and `W ↦ G^{-1} W` on those that read it turns
`W_1` into the identity for `G = W_1` if `W_1` is part of a read, and for `G = W_1^{-1}` if it is
part of a write. Under RMSNorm with `ε > 0`, `G = Q` from a QR factorization `W_1 = Q T`, or
`W_1^⊤ = Q T` for a write, turns `W_1` into a triangular matrix. Done at every hidden state, this
removes `d_model²`, respectively `d_model (d_model − 1)/2`, parameters per hidden state without
changing the function." Its proof: "The change of basis at `h_ℓ` touches only the writes into
`h_ℓ` and the reads of `h_ℓ`, and a matrix is touched on each side by one hidden state only
(Proposition A.1(iii)), so the reductions at all hidden states can be made together, one submatrix
per hidden state."

`Symmetry/Reduction.lean`, `Residual/ExactReductionWrites.lean`, `Residual/ExactReductionMixed.lean`
and `Residual/ExactReductionCount.lean` have the reduction and the count with the `L + 1`
submatrices all in reads (the reads of the blocks and the readout) or all in writes (the embedding
and the writes of the blocks). Here "one submatrix per hidden state" with a free choice at each
hidden state `h_k`, `k = 0, …, L`: `d` columns of the matrix that reads `h_k` (the read of block
`k + 1`, or the readout for `k = L`; `Params.readSub`), or `d` rows of the matrix that writes
`h_k` (the embedding for `k = 0`, or the write of block `k`; `Params.writeSub`). The choice is
`s : Fin (L + 1) → Bool`, `true` for a read.

* `exists_cob_eq_one_of_choice`, `exists_cob_triangular_of_choice`: the reduction for skipless
  networks, without normalization and under pre-RMSNorm; for networks of mixed blocks
  `exists_cob_mixed_eq_one_of_choice`, `exists_cob_mixed_triangular_of_choice`.
* `finrank_span_choice_eq_zero`, `finrank_span_choice_triangular`: the count,
  `P − (L + 1) d²` and `P − (L + 1) d(d − 1)/2`, for any architecture.
-/

namespace Skips

open Matrix

section General

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]
variable {A : Arch T d L}

/-- The chosen `d` columns of the matrix that reads the hidden state `h_k`: of the read of block
`k + 1`, or of the readout for `k = L`. -/
def Params.readSub (θ : Params A dIn dOut) (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut)
    (k : Fin (L + 1)) : Matrix d d ℝ :=
  Fin.lastCases (motive := fun _ => Matrix d d ℝ) (θ.D.submatrix id cD)
    (fun ℓ => (θ.read ℓ).submatrix id (c ℓ)) k

/-- The chosen `d` rows of the matrix that writes the hidden state `h_k`: of the embedding for
`k = 0`, or of the write of block `k`. -/
def Params.writeSub (θ : Params A dIn dOut) (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ)
    (k : Fin (L + 1)) : Matrix d d ℝ :=
  Fin.cases (motive := fun _ => Matrix d d ℝ) (θ.E.submatrix ρE id)
    (fun ℓ => (θ.write ℓ).submatrix (ρ ℓ) id) k

variable (θ : Params A dIn dOut)

omit [DecidableEq d] in
/-- The chosen columns `c` of a product `M N` are `M` times the chosen columns of `N` (a copy of
the private `submatrix_id_mul` of `Symmetry/Reduction.lean`). -/
private theorem submatrix_id_mul_erc2 {r : Type*} (M : Matrix d d ℝ) (N : Matrix d r ℝ)
    (c : d → r) : (M * N).submatrix id c = M * N.submatrix id c := by
  rw [Matrix.submatrix_mul M N id id c Function.bijective_id, Matrix.submatrix_id_id]

omit [DecidableEq d] in
/-- The chosen rows `ρ` of a product `M N` are the chosen rows of `M` times `N` (a copy of the
private `submatrix_mul_id` of `Symmetry/Reduction.lean`). -/
private theorem submatrix_mul_id_erc2 {w : Type*} (M : Matrix w d ℝ) (N : Matrix d d ℝ)
    (ρ : d → w) : (M * N).submatrix ρ id = M.submatrix ρ id * N := by
  rw [Matrix.submatrix_mul M N ρ id id Function.bijective_id, Matrix.submatrix_id_id]

omit [Fintype dIn] [Fintype dOut] in
/-- The change of basis at `h_k` multiplies the chosen columns of the matrix that reads `h_k` by
`G_k⁻¹` on the left. -/
private theorem readSub_cob_erc2 (G : Fin (L + 1) → GL d ℝ) (c : ∀ ℓ : Fin L, d → A.r ℓ)
    (cD : d → dOut) (k : Fin (L + 1)) :
    (θ.cob G G).readSub c cD k = (↑(G k)⁻¹ : Matrix d d ℝ) * θ.readSub c cD k := by
  induction k using Fin.lastCases with
  | last =>
    simp only [Params.readSub, Fin.lastCases_last]
    exact submatrix_id_mul_erc2 _ _ _
  | cast ℓ =>
    simp only [Params.readSub, Fin.lastCases_castSucc]
    exact submatrix_id_mul_erc2 _ _ _

omit [Fintype dIn] [Fintype dOut] in
/-- The change of basis at `h_k` multiplies the chosen rows of the matrix that writes `h_k` by
`G_k` on the right. -/
private theorem writeSub_cob_erc2 (G : Fin (L + 1) → GL d ℝ) (ρE : d → dIn)
    (ρ : ∀ ℓ : Fin L, d → A.w ℓ) (k : Fin (L + 1)) :
    (θ.cob G G).writeSub ρE ρ k = θ.writeSub ρE ρ k * (G k : Matrix d d ℝ) := by
  induction k using Fin.cases with
  | zero =>
    simp only [Params.writeSub, Fin.cases_zero]
    exact submatrix_mul_id_erc2 _ _ _
  | succ ℓ =>
    simp only [Params.writeSub, Fin.cases_succ]
    exact submatrix_mul_id_erc2 _ _ _

/-- **Proposition A.9 (i), without normalization, one submatrix per hidden state:** at each
hidden state choose `d` columns of the matrix that reads it or `d` rows of the matrix that writes
it. If the chosen submatrices are invertible, changes of basis at the `L + 1` hidden states
preserve the function and turn all of them into the identity. -/
theorem exists_cob_eq_one_of_choice (hA : A.χ = id)
    (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut) (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ)
    (s : Fin (L + 1) → Bool)
    (h : ∀ k, IsUnit (if s k then θ.readSub c cD k else θ.writeSub ρE ρ k).det) :
    ∃ G : Fin (L + 1) → GL d ℝ,
      (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cob G G) x = eval A 0 θ x) ∧
      ∀ k, (if s k then (θ.cob G G).readSub c cD k else (θ.cob G G).writeSub ρE ρ k) = 1 := by
  -- the chosen submatrix `W₁` at each hidden state is invertible
  have hU : ∀ k, ∃ u : GL d ℝ,
      (u : Matrix d d ℝ) = if s k then θ.readSub c cD k else θ.writeSub ρE ρ k :=
    fun k => (Matrix.isUnit_iff_isUnit_det _).mpr (h k)
  choose U hU using hU
  -- `G_k = W₁` for a read, `G_k = W₁⁻¹` for a write
  refine ⟨fun k => if s k then U k else (U k)⁻¹, fun x => eval_cob_skipless θ _ x hA,
    fun k => ?_⟩
  by_cases hs : s k
  · -- the chosen columns of the new read are `W₁⁻¹ W₁ = 1`
    have hu := hU k
    rw [ite_eq_left_of_eq_true _ _ (eq_true hs)] at hu ⊢
    rw [readSub_cob_erc2, ite_eq_left_of_eq_true _ _ (eq_true hs), ← hu, Units.inv_mul]
  · -- the chosen rows of the new write are `W₁ W₁⁻¹ = 1`
    have hu := hU k
    rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at hu ⊢
    rw [writeSub_cob_erc2, ite_eq_right_of_eq_false _ _ (eq_false hs), ← hu, Units.mul_inv]

/-- The QR factorization with `Q` as an element of `GL d ℝ`: `Q⁻¹ W = Qᵀ W` is upper
triangular (a copy of the private `exists_orthogonal_inv_mul_upperTriangular` of
`Symmetry/Reduction.lean`). -/
private theorem exists_orthogonal_inv_mul_upperTriangular_erc2 [LinearOrder d]
    (W : Matrix d d ℝ) :
    ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
      ((↑Q⁻¹ : Matrix d d ℝ) * W).BlockTriangular id := by
  obtain ⟨Q, hQ, htri⟩ := exists_orthogonal_transpose_mul_upperTriangular W
  -- `Q` is invertible, with inverse `Qᵀ`.
  let Q' : GL d ℝ :=
    ⟨Q, Qᵀ, (Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ, (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hQ⟩
  have hQ' : (Q' : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ := hQ
  refine ⟨Q', hQ', ?_⟩
  rw [coe_inv_of_mem_orthogonalGroup Q' hQ']
  exact htri

/-- QR factorization of `Wᵀ`, with `Q` as an element of `GL d ℝ`: an orthogonal `Q` with `W Q`
lower triangular (a copy of the private `exists_orthogonal_mul_lowerTriangular_erw` of
`Residual/ExactReductionWrites.lean`). -/
private theorem exists_orthogonal_mul_lowerTriangular_erc2 [LinearOrder d] (W : Matrix d d ℝ) :
    ∃ Q : GL d ℝ, (Q : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
      ((W * (Q : Matrix d d ℝ))ᵀ).BlockTriangular id := by
  -- QR factorization of `Wᵀ`: an orthogonal `Q` with `Qᵀ Wᵀ` upper triangular.
  obtain ⟨Q, hQ, htri⟩ := exists_orthogonal_transpose_mul_upperTriangular Wᵀ
  -- `Q` is invertible, with inverse `Qᵀ`.
  let Q' : GL d ℝ :=
    ⟨Q, Qᵀ, (Matrix.mem_orthogonalGroup_iff d ℝ).mp hQ, (Matrix.mem_orthogonalGroup_iff' d ℝ).mp hQ⟩
  refine ⟨Q', hQ, ?_⟩
  -- `(W Q)ᵀ = Qᵀ Wᵀ`.
  change ((W * Q)ᵀ).BlockTriangular id
  rw [Matrix.transpose_mul]
  exact htri

/-- **Proposition A.9 (i), under pre-RMSNorm, one submatrix per hidden state:** orthogonal
changes of basis at the `L + 1` hidden states preserve the function and turn the chosen
submatrix at each hidden state into a triangular matrix: upper triangular for columns of a read,
lower triangular for rows of a write. No invertibility is needed. -/
theorem exists_cob_triangular_of_choice [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut) (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ)
    (s : Fin (L + 1) → Bool) :
    ∃ Q : Fin (L + 1) → GL d ℝ,
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
      (∀ x : Matrix T dIn ℝ, eval A 0 (θ.cob Q Q) x = eval A 0 θ x) ∧
      ∀ k, if s k then ((θ.cob Q Q).readSub c cD k).BlockTriangular id
        else (((θ.cob Q Q).writeSub ρE ρ k)ᵀ).BlockTriangular id := by
  -- QR factorization of the chosen columns `W₁ = Q T`, or of the transposed rows `W₁ᵀ = Q T`
  have hR : ∀ k, ∃ P : GL d ℝ, (P : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ ∧
      if s k then ((↑P⁻¹ : Matrix d d ℝ) * θ.readSub c cD k).BlockTriangular id
        else ((θ.writeSub ρE ρ k * (P : Matrix d d ℝ))ᵀ).BlockTriangular id := by
    intro k
    by_cases hs : s k
    · obtain ⟨P, hP, ht⟩ := exists_orthogonal_inv_mul_upperTriangular_erc2 (θ.readSub c cD k)
      refine ⟨P, hP, ?_⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hs)]
      exact ht
    · obtain ⟨P, hP, ht⟩ := exists_orthogonal_mul_lowerTriangular_erc2 (θ.writeSub ρE ρ k)
      refine ⟨P, hP, ?_⟩
      rw [ite_eq_right_of_eq_false _ _ (eq_false hs)]
      exact ht
  choose Q hQ htri using hR
  -- under pre-RMSNorm orthogonal changes of basis preserve the function (Proposition 3.2); the
  -- chosen submatrix at `h_k` becomes `Q_k⁻¹ W₁` or `W₁ Q_k`
  refine ⟨Q, hQ, fun x => eval_cob_rmsNorm θ x ε hA Q hQ, fun k => ?_⟩
  rw [readSub_cob_erc2, writeSub_cob_erc2]
  exact htri k

/-- The span of the kernel of an onto linear map, by rank–nullity (a copy of the private
`finrank_span_ker_erc` of `Residual/ExactReductionCount.lean`). -/
private theorem finrank_span_ker_erc2 {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] (φ : V →ₗ[ℝ] W)
    (hφ : Function.Surjective φ) (S : Set V) (hS : ∀ v, v ∈ S ↔ φ v = 0) :
    Module.finrank ℝ (Submodule.span ℝ S) + Module.finrank ℝ W = Module.finrank ℝ V := by
  have h : S = (LinearMap.ker φ : Set V) := Set.ext fun v => (hS v).trans LinearMap.mem_ker.symm
  rw [h, Submodule.span_eq, ← LinearMap.finrank_range_add_finrank_ker φ,
    LinearMap.range_eq_top.2 hφ, finrank_top, add_comm]

omit [DecidableEq d] in
/-- The number of pairs `j < i` in a finite linear order (a copy of the private `card_lower_erc`
of `Residual/ExactReductionCount.lean`). -/
private theorem card_lower_erc2 [LinearOrder d] :
    Fintype.card {p : d × d // p.2 < p.1} = Fintype.card d * (Fintype.card d - 1) / 2 := by
  let e : d ≃o Fin (Fintype.card d) := (Fintype.orderIsoFinOfCardEq d rfl).symm
  rw [← card_below_diagonal (Fintype.card d), ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquiv (e.toEquiv.prodCongr e.toEquiv)
    fun p => by simp [e.lt_iff_lt])

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The chosen columns of a sum are the sums of the chosen columns. -/
private theorem readSub_add_erc2 (η η' : Params A dIn dOut) (c : ∀ ℓ : Fin L, d → A.r ℓ)
    (cD : d → dOut) (k : Fin (L + 1)) :
    (η + η').readSub c cD k = η.readSub c cD k + η'.readSub c cD k := by
  induction k using Fin.lastCases with
  | last => simp only [Params.readSub, Fin.lastCases_last]; rfl
  | cast ℓ => simp only [Params.readSub, Fin.lastCases_castSucc]; rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The chosen columns of a multiple are the multiple of the chosen columns. -/
private theorem readSub_smul_erc2 (a : ℝ) (η : Params A dIn dOut) (c : ∀ ℓ : Fin L, d → A.r ℓ)
    (cD : d → dOut) (k : Fin (L + 1)) :
    (a • η).readSub c cD k = a • η.readSub c cD k := by
  induction k using Fin.lastCases with
  | last => simp only [Params.readSub, Fin.lastCases_last]; rfl
  | cast ℓ => simp only [Params.readSub, Fin.lastCases_castSucc]; rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The chosen rows of a sum are the sums of the chosen rows. -/
private theorem writeSub_add_erc2 (η η' : Params A dIn dOut) (ρE : d → dIn)
    (ρ : ∀ ℓ : Fin L, d → A.w ℓ) (k : Fin (L + 1)) :
    (η + η').writeSub ρE ρ k = η.writeSub ρE ρ k + η'.writeSub ρE ρ k := by
  induction k using Fin.cases with
  | zero => simp only [Params.writeSub, Fin.cases_zero]; rfl
  | succ ℓ => simp only [Params.writeSub, Fin.cases_succ]; rfl

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The chosen rows of a multiple are the multiple of the chosen rows. -/
private theorem writeSub_smul_erc2 (a : ℝ) (η : Params A dIn dOut) (ρE : d → dIn)
    (ρ : ∀ ℓ : Fin L, d → A.w ℓ) (k : Fin (L + 1)) :
    (a • η).writeSub ρE ρ k = a • η.writeSub ρE ρ k := by
  induction k using Fin.cases with
  | zero => simp only [Params.writeSub, Fin.cases_zero]; rfl
  | succ ℓ => simp only [Params.writeSub, Fin.cases_succ]; rfl

/-- The chosen submatrix at every hidden state: columns of the read for `s k`, rows of the write
otherwise. -/
private def choiceLin_erc2 (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut) (ρE : d → dIn)
    (ρ : ∀ ℓ : Fin L, d → A.w ℓ) (s : Fin (L + 1) → Bool) :
    Params A dIn dOut →ₗ[ℝ] (Fin (L + 1) → Matrix d d ℝ) where
  toFun η k := if s k then η.readSub c cD k else η.writeSub ρE ρ k
  map_add' η η' := by
    funext k
    simp only [Pi.add_apply]
    split_ifs
    · exact readSub_add_erc2 η η' c cD k
    · exact writeSub_add_erc2 η η' ρE ρ k
  map_smul' a η := by
    funext k
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · exact readSub_smul_erc2 a η c cD k
    · exact writeSub_smul_erc2 a η ρE ρ k

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- The map `choiceLin_erc2` is onto when the chosen columns (rows) are pairwise different where
they are used: put the wanted entries into the chosen columns of the read, or rows of the write,
at each hidden state, and `0` elsewhere. -/
private theorem choiceLin_surjective_erc2 (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut)
    (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ) (s : Fin (L + 1) → Bool)
    (hc : ∀ ℓ : Fin L, s ℓ.castSucc = true → Function.Injective (c ℓ))
    (hcD : s (Fin.last L) = true → Function.Injective cD)
    (hρE : s 0 = false → Function.Injective ρE)
    (hρ : ∀ ℓ : Fin L, s ℓ.succ = false → Function.Injective (ρ ℓ)) :
    Function.Surjective (choiceLin_erc2 (dIn := dIn) (dOut := dOut) c cD ρE ρ s) := by
  intro M
  refine ⟨⟨Matrix.of fun r i => Function.extend ρE (fun j => M 0 j i) 0 r,
    fun ℓ => Matrix.of fun a => Function.extend (c ℓ) (M ℓ.castSucc a) 0,
    fun ℓ => Matrix.of fun r i => Function.extend (ρ ℓ) (fun j => M ℓ.succ j i) 0 r,
    Matrix.of fun a => Function.extend cD (M (Fin.last L) a) 0⟩, funext fun k => ?_⟩
  show (if s k then _ else _) = M k
  by_cases hs : s k
  · -- a read: the chosen columns of the read of `h_k` (or of the readout) are `M k`
    rw [ite_eq_left_of_eq_true _ _ (eq_true hs)]
    induction k using Fin.lastCases with
    | last =>
      simp only [Params.readSub, Fin.lastCases_last]
      ext a j
      exact (hcD hs).extend_apply (M (Fin.last L) a) 0 j
    | cast ℓ =>
      simp only [Params.readSub, Fin.lastCases_castSucc]
      ext a j
      exact (hc ℓ hs).extend_apply (M ℓ.castSucc a) 0 j
  · -- a write: the chosen rows of the write into `h_k` (or of the embedding) are `M k`
    rw [ite_eq_right_of_eq_false _ _ (eq_false hs)]
    have hs' : s k = false := by simpa using hs
    induction k using Fin.cases with
    | zero =>
      simp only [Params.writeSub, Fin.cases_zero]
      ext j i
      exact (hρE hs').extend_apply (fun j => M 0 j i) 0 j
    | succ ℓ =>
      simp only [Params.writeSub, Fin.cases_succ]
      ext j i
      exact (hρ ℓ hs').extend_apply (fun j => M ℓ.succ j i) 0 j

/-- **Proposition A.9 (i), "this removes `d_model²` […] parameters per hidden state", one
submatrix per hidden state:** the parameters whose chosen submatrices all vanish (the directions
of the family in which these `L + 1` submatrices are the identity) have dimension
`P − (L + 1) d²`, if the chosen columns, or rows, are pairwise different. -/
theorem finrank_span_choice_eq_zero (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut)
    (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ) (s : Fin (L + 1) → Bool)
    (hc : ∀ ℓ : Fin L, s ℓ.castSucc = true → Function.Injective (c ℓ))
    (hcD : s (Fin.last L) = true → Function.Injective cD)
    (hρE : s 0 = false → Function.Injective ρE)
    (hρ : ∀ ℓ : Fin L, s ℓ.succ = false → Function.Injective (ρ ℓ)) :
    Module.finrank ℝ (Submodule.span ℝ {η : Params A dIn dOut |
        ∀ k, (if s k then η.readSub c cD k else η.writeSub ρE ρ k) = 0})
      + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params A dIn dOut) := by
  -- the set is the kernel of the onto map `choiceLin_erc2`
  have hS := finrank_span_ker_erc2 _ (choiceLin_surjective_erc2 c cD ρE ρ s hc hcD hρE hρ)
    {η : Params A dIn dOut |
      ∀ k, (if s k then η.readSub c cD k else η.writeSub ρE ρ k) = 0} fun η =>
    ⟨fun h => funext h, fun h k => congrFun h k⟩
  rw [← hS]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- The entries below the diagonal of the chosen submatrix at every hidden state for `s k` (a
read), above the diagonal otherwise (a write). -/
private def lowLin_erc2 [LinearOrder d] (s : Fin (L + 1) → Bool) :
    (Fin (L + 1) → Matrix d d ℝ) →ₗ[ℝ] (Fin (L + 1) → {p : d × d // p.2 < p.1} → ℝ) where
  toFun M k p := if s k then M k p.1.1 p.1.2 else M k p.1.2 p.1.1
  map_add' M N := by
    funext k p
    simp only [Pi.add_apply]
    split_ifs <;> rfl
  map_smul' a M := by
    funext k p
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> rfl

omit [Fintype d] [DecidableEq d] in
/-- The map `lowLin_erc2` is onto: any values below (above) the diagonal, `0` elsewhere. -/
private theorem lowLin_surjective_erc2 [LinearOrder d] (s : Fin (L + 1) → Bool) :
    Function.Surjective (lowLin_erc2 (d := d) s) := by
  intro f
  refine ⟨fun k => Matrix.of fun i j => if s k then (if h : j < i then f k ⟨(i, j), h⟩ else 0)
    else (if h : i < j then f k ⟨(j, i), h⟩ else 0), funext fun k => funext fun p => ?_⟩
  show (if s k then (if s k then _ else _) else (if s k then _ else _)) = f k p
  by_cases hs : s k
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hs), ite_eq_left_of_eq_true _ _ (eq_true hs),
      dite_eq_left p.2]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hs), ite_eq_right_of_eq_false _ _ (eq_false hs),
      dite_eq_left p.2]

/-- **Proposition A.9 (i), "respectively `d_model (d_model − 1)/2`, parameters per hidden
state", one submatrix per hidden state:** the parameters whose chosen submatrices are triangular
(upper for columns of a read, lower for rows of a write) have dimension
`P − (L + 1) d(d − 1)/2`, if the chosen columns, or rows, are pairwise different. -/
theorem finrank_span_choice_triangular [LinearOrder d] (c : ∀ ℓ : Fin L, d → A.r ℓ)
    (cD : d → dOut) (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ) (s : Fin (L + 1) → Bool)
    (hc : ∀ ℓ : Fin L, s ℓ.castSucc = true → Function.Injective (c ℓ))
    (hcD : s (Fin.last L) = true → Function.Injective cD)
    (hρE : s 0 = false → Function.Injective ρE)
    (hρ : ∀ ℓ : Fin L, s ℓ.succ = false → Function.Injective (ρ ℓ)) :
    Module.finrank ℝ (Submodule.span ℝ {θ : Params A dIn dOut |
        ∀ k, if s k then (θ.readSub c cD k).BlockTriangular id
          else ((θ.writeSub ρE ρ k)ᵀ).BlockTriangular id})
      + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params A dIn dOut) := by
  -- the entries of the chosen submatrices that the triangular forms fix
  have happ : ∀ (θ : Params A dIn dOut) k (p : {p : d × d // p.2 < p.1}),
      ((lowLin_erc2 s).comp (choiceLin_erc2 (dIn := dIn) (dOut := dOut) c cD ρE ρ s)) θ k p
        = if s k then θ.readSub c cD k p.1.1 p.1.2 else θ.writeSub ρE ρ k p.1.2 p.1.1 := by
    intro θ k p
    show (if s k then
        (if s k then θ.readSub c cD k else θ.writeSub ρE ρ k : Matrix d d ℝ) p.1.1 p.1.2
      else (if s k then θ.readSub c cD k else θ.writeSub ρE ρ k : Matrix d d ℝ) p.1.2 p.1.1) = _
    split_ifs <;> rfl
  -- the set is the kernel of an onto map: triangular means that these entries vanish
  have hsurj : Function.Surjective
      ((lowLin_erc2 s).comp (choiceLin_erc2 (dIn := dIn) (dOut := dOut) c cD ρE ρ s)) := by
    rw [LinearMap.coe_comp]
    exact (lowLin_surjective_erc2 s).comp (choiceLin_surjective_erc2 c cD ρE ρ s hc hcD hρE hρ)
  have hS := finrank_span_ker_erc2 _ hsurj
    {θ : Params A dIn dOut | ∀ k, if s k then (θ.readSub c cD k).BlockTriangular id
      else ((θ.writeSub ρE ρ k)ᵀ).BlockTriangular id} fun θ => by
    constructor
    · intro h
      funext k p
      rw [happ]
      have hk := h k
      by_cases hs : s k
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hs)] at hk ⊢
        exact @hk p.1.1 p.1.2 p.2
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at hk ⊢
        exact @hk p.1.1 p.1.2 p.2
    · intro h k
      have hk : ∀ p : {p : d × d // p.2 < p.1},
          (if s k then θ.readSub c cD k p.1.1 p.1.2 else θ.writeSub ρE ρ k p.1.2 p.1.1) = 0 :=
        fun p => (happ θ k p).symm.trans (congrFun (congrFun h k) p)
      by_cases hs : s k
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hs)]
        intro i j hij
        have := hk ⟨(i, j), hij⟩
        rw [ite_eq_left_of_eq_true _ _ (eq_true hs)] at this
        exact this
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hs)]
        intro i j hij
        have := hk ⟨(i, j), hij⟩
        rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at this
        exact this
  rw [← hS, card_lower_erc2.symm]
  simp only [Module.finrank_pi_fintype, Module.finrank_self, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end General

section Mixed

variable {T : Type*} {d : Type} {dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d]
  [Fintype dIn] [Fintype dOut]
variable {A : Arch T d L} (θ : Params A.mixed dIn dOut)

/-- **Proposition A.9 (i) for networks of mixed blocks, without normalization, one submatrix per
hidden state:** columns of a read `[U_ℓ | W_read^ℓ]` or of the readout, or rows of the embedding
or of a write (which stacks `V_ℓ` on `W_write^ℓ`). -/
theorem exists_cob_mixed_eq_one_of_choice (hA : A.χ = id)
    (c : ∀ ℓ : Fin L, d → d ⊕ A.r ℓ) (cD : d → dOut) (ρE : d → dIn)
    (ρ : ∀ ℓ : Fin L, d → d ⊕ A.w ℓ) (s : Fin (L + 1) → Bool)
    (h : ∀ k, IsUnit (if s k then θ.readSub c cD k else θ.writeSub ρE ρ k).det) :
    ∃ G : Fin (L + 1) → GL d ℝ,
      (∀ x : Matrix T dIn ℝ, evalMixed A (θ.cob G G) x = evalMixed A θ x) ∧
      ∀ k, (if s k then (θ.cob G G).readSub c cD k else (θ.cob G G).writeSub ρE ρ k) = 1 := by
  -- without normalization the network of mixed blocks is the skipless network of `A.mixed`
  obtain ⟨G, hG, h1⟩ :=
    exists_cob_eq_one_of_choice (A := A.mixed) (θ := θ) hA c cD ρE ρ s h
  refine ⟨G, fun x => ?_, h1⟩
  rw [evalMixed_eq_eval hA, evalMixed_eq_eval hA]
  exact hG x

/-- **Proposition A.9 (i) for networks of mixed blocks, under pre-RMSNorm, one submatrix per
hidden state.** -/
theorem exists_cob_mixed_triangular_of_choice [LinearOrder d] (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (c : ∀ ℓ : Fin L, d → d ⊕ A.r ℓ) (cD : d → dOut) (ρE : d → dIn)
    (ρ : ∀ ℓ : Fin L, d → d ⊕ A.w ℓ) (s : Fin (L + 1) → Bool) :
    ∃ Q : Fin (L + 1) → GL d ℝ,
      (∀ ℓ, (Q ℓ : Matrix d d ℝ) ∈ Matrix.orthogonalGroup d ℝ) ∧
      (∀ x : Matrix T dIn ℝ, evalMixed A (θ.cob Q Q) x = evalMixed A θ x) ∧
      ∀ k, if s k then ((θ.cob Q Q).readSub c cD k).BlockTriangular id
        else (((θ.cob Q Q).writeSub ρE ρ k)ᵀ).BlockTriangular id := by
  -- the matrices `Q_ℓ` of the skipless statement for the architecture `A.mixed`
  obtain ⟨Q, hQ, -, h1⟩ :=
    exists_cob_triangular_of_choice (A := A.mixed) (θ := θ) ε hA c cD ρE ρ s
  refine ⟨Q, hQ, fun x => ?_, h1⟩
  -- they preserve the function of the network of mixed blocks (Proposition A.1 (ii))
  rw [← cobMixed_one_eq_cob]
  exact evalMixed_cobMixed_rmsNorm θ x ε hA Q hQ 1

end Mixed

end Skips

