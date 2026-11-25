import SkipsLean.Dimension.Space
import SkipsLean.Symmetry.Reduction

/-!
# Exact reduction: the count of the removed parameters

Paper (skips paper), Proposition A.9 (i): "[…] turns `W_1` into the identity for `G = W_1` if
`W_1` is part of a read, and for `G = W_1^{-1}` if it is part of a write. Under RMSNorm with
`ε > 0`, `G = Q` from a QR factorization `W_1 = Q T`, or `W_1^⊤ = Q T` for a write, turns `W_1`
into a triangular matrix. Done at every hidden state, this removes `d_model²`, respectively
`d_model (d_model − 1)/2`, parameters per hidden state without changing the function." Its
proof: "The identity fixes all `d_model²` entries of `W_1`, and the triangular form fixes the
`d_model (d_model − 1)/2` entries on one side of its diagonal."

The reductions themselves ("without changing the function") are `exists_cob_reads_eq_one`,
`exists_cob_writes_eq_one`, `exists_cob_reads_upperTriangular` (`Symmetry/Reduction.lean`),
`exists_cob_writes_lowerTriangular` (`Residual/ExactReductionWrites.lean`) and, for networks of
mixed blocks, `Residual/ExactReductionMixed.lean`. Here the count, for any architecture (so also
for `A.mixed`), with one chosen submatrix per hidden state, `L + 1` of them:

* the parameters in which the chosen columns of every read and of the readout are the identity
  form an affine space; its directions, the parameters in which these columns are `0`, have
  dimension `P − (L + 1) d²` (`finrank_span_reads_eq_zero`); the same for the chosen rows of the
  embedding and of every write (`finrank_span_writes_eq_zero`);
* the parameters in which the chosen columns are upper triangular have dimension
  `P − (L + 1) d(d − 1)/2` (`finrank_span_reads_upperTriangular`); the same for the chosen rows
  with lower triangular matrices (`finrank_span_writes_lowerTriangular`).

The chosen columns (rows) are pairwise different: columns that form an invertible matrix are.
Each set is a subspace, and the statements are for its span, as in
`OneBlock/KeepsProductsBiases.lean`.
-/

namespace Skips

open Matrix

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]
variable {A : Arch T d L}

/-- The span of the kernel of an onto linear map, by rank–nullity. -/
private theorem finrank_span_ker_erc {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] (φ : V →ₗ[ℝ] W)
    (hφ : Function.Surjective φ) (S : Set V) (hS : ∀ v, v ∈ S ↔ φ v = 0) :
    Module.finrank ℝ (Submodule.span ℝ S) + Module.finrank ℝ W = Module.finrank ℝ V := by
  have h : S = (LinearMap.ker φ : Set V) := Set.ext fun v => (hS v).trans LinearMap.mem_ker.symm
  rw [h, Submodule.span_eq, ← LinearMap.finrank_range_add_finrank_ker φ,
    LinearMap.range_eq_top.2 hφ, finrank_top, add_comm]

omit [DecidableEq d] in
/-- The number of pairs `j < i` in a finite linear order. -/
private theorem card_lower_erc [LinearOrder d] :
    Fintype.card {p : d × d // p.2 < p.1} = Fintype.card d * (Fintype.card d - 1) / 2 := by
  let e : d ≃o Fin (Fintype.card d) := (Fintype.orderIsoFinOfCardEq d rfl).symm
  rw [← card_below_diagonal (Fintype.card d), ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquiv (e.toEquiv.prodCongr e.toEquiv)
    fun p => by simp [e.lt_iff_lt])

/-- The chosen columns of every read and of the readout. -/
private def readsLin_erc (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut) :
    Params A dIn dOut →ₗ[ℝ] (Fin L → Matrix d d ℝ) × Matrix d d ℝ where
  toFun η := (fun ℓ => (η.read ℓ).submatrix id (c ℓ), η.D.submatrix id cD)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq d] in
/-- **Proposition A.9 (i), "this removes `d_model²` […] parameters per hidden state", reads:**
the parameters whose chosen columns of every read and of the readout vanish (the directions of
the family in which these `L + 1` submatrices are the identity) have dimension
`P − (L + 1) d²`. -/
theorem finrank_span_reads_eq_zero (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut)
    (hc : ∀ ℓ, Function.Injective (c ℓ)) (hcD : Function.Injective cD) :
    Module.finrank ℝ (Submodule.span ℝ {η : Params A dIn dOut |
        (∀ ℓ, (η.read ℓ).submatrix id (c ℓ) = 0) ∧ η.D.submatrix id cD = 0})
      + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params A dIn dOut) := by
  have hφ : Function.Surjective (readsLin_erc (dIn := dIn) c cD) := by
    rintro ⟨M, N⟩
    refine ⟨⟨0, fun ℓ => Matrix.of fun a => Function.extend (c ℓ) (M ℓ a) 0, fun _ => 0,
      Matrix.of fun a => Function.extend cD (N a) 0⟩, ?_⟩
    refine Prod.ext (funext fun ℓ => ?_) ?_ <;> ext a j
    · exact (hc ℓ).extend_apply (M ℓ a) 0 j
    · exact hcD.extend_apply (N a) 0 j
  have hS := finrank_span_ker_erc _ hφ {η : Params A dIn dOut |
        (∀ ℓ, (η.read ℓ).submatrix id (c ℓ) = 0) ∧ η.D.submatrix id cD = 0} fun η => by
    simp only [Set.mem_ofPred_eq, Prod.ext_iff, funext_iff (f := fun ℓ => _)]
    rfl
  rw [← hS]
  simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_matrix,
    Module.finrank_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- The chosen rows of the embedding and of every write. -/
private def writesLin_erc (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ) :
    Params A dIn dOut →ₗ[ℝ] Matrix d d ℝ × (Fin L → Matrix d d ℝ) where
  toFun η := (η.E.submatrix ρE id, fun ℓ => (η.write ℓ).submatrix (ρ ℓ) id)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq d] in
/-- **Proposition A.9 (i), "this removes `d_model²` […] parameters per hidden state", writes:**
the parameters whose chosen rows of the embedding and of every write vanish have dimension
`P − (L + 1) d²`. -/
theorem finrank_span_writes_eq_zero (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ)
    (hρE : Function.Injective ρE) (hρ : ∀ ℓ, Function.Injective (ρ ℓ)) :
    Module.finrank ℝ (Submodule.span ℝ {η : Params A dIn dOut |
        η.E.submatrix ρE id = 0 ∧ ∀ ℓ, (η.write ℓ).submatrix (ρ ℓ) id = 0})
      + (L + 1) * Fintype.card d ^ 2
      = Module.finrank ℝ (Params A dIn dOut) := by
  have hφ : Function.Surjective (writesLin_erc (dOut := dOut) ρE ρ) := by
    rintro ⟨M, N⟩
    refine ⟨⟨Matrix.of fun r i => Function.extend ρE (fun j => M j i) 0 r, fun _ => 0,
      fun ℓ => Matrix.of fun r i => Function.extend (ρ ℓ) (fun j => N ℓ j i) 0 r, 0⟩, ?_⟩
    refine Prod.ext ?_ (funext fun ℓ => ?_) <;> ext j i
    · exact hρE.extend_apply (fun j => M j i) 0 j
    · exact (hρ ℓ).extend_apply (fun j => N ℓ j i) 0 j
  have hS := finrank_span_ker_erc _ hφ {η : Params A dIn dOut |
        η.E.submatrix ρE id = 0 ∧ ∀ ℓ, (η.write ℓ).submatrix (ρ ℓ) id = 0} fun η => by
    simp only [Set.mem_ofPred_eq, Prod.ext_iff, funext_iff (f := fun ℓ => _)]
    rfl
  rw [← hS]
  simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_matrix,
    Module.finrank_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- The strictly lower entries of the chosen columns of every read and of the readout. -/
private def readsLowLin_erc [LinearOrder d] (c : ∀ ℓ : Fin L, d → A.r ℓ) (cD : d → dOut) :
    Params A dIn dOut →ₗ[ℝ]
      (Fin L → {p : d × d // p.2 < p.1} → ℝ) × ({p : d × d // p.2 < p.1} → ℝ) where
  toFun θ := (fun ℓ p => θ.read ℓ p.1.1 (c ℓ p.1.2), fun p => θ.D p.1.1 (cD p.1.2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq d] in
/-- **Proposition A.9 (i), "respectively `d_model (d_model − 1)/2`, parameters per hidden
state", reads:** the parameters whose chosen columns of every read and of the readout form upper
triangular matrices have dimension `P − (L + 1) d(d − 1)/2`. -/
theorem finrank_span_reads_upperTriangular [LinearOrder d] (c : ∀ ℓ : Fin L, d → A.r ℓ)
    (cD : d → dOut) (hc : ∀ ℓ, Function.Injective (c ℓ)) (hcD : Function.Injective cD) :
    Module.finrank ℝ (Submodule.span ℝ {θ : Params A dIn dOut |
        (∀ ℓ, ((θ.read ℓ).submatrix id (c ℓ)).BlockTriangular id)
          ∧ (θ.D.submatrix id cD).BlockTriangular id})
      + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params A dIn dOut) := by
  -- any values on the strictly lower entries of the chosen columns, `0` elsewhere
  have hφ : Function.Surjective (readsLowLin_erc (dIn := dIn) c cD) := by
    rintro ⟨f, g⟩
    refine ⟨⟨0, fun ℓ => Matrix.of fun a =>
        Function.extend (c ℓ) (fun j => if h : j < a then f ℓ ⟨(a, j), h⟩ else 0) (0 : A.r ℓ → ℝ),
      fun _ => 0,
      Matrix.of fun a => Function.extend cD (fun j => if h : j < a then g ⟨(a, j), h⟩ else 0)
        (0 : dOut → ℝ)⟩,
      ?_⟩
    refine Prod.ext (funext fun ℓ => funext fun p => ?_) (funext fun p => ?_)
    · show Function.extend (c ℓ) (fun j => if h : j < p.1.1 then f ℓ ⟨(p.1.1, j), h⟩ else 0)
        (0 : A.r ℓ → ℝ) (c ℓ p.1.2) = _
      rw [(hc ℓ).extend_apply, dite_eq_left p.2]
    · show Function.extend cD (fun j => if h : j < p.1.1 then g ⟨(p.1.1, j), h⟩ else 0)
        (0 : dOut → ℝ) (cD p.1.2) = _
      rw [hcD.extend_apply, dite_eq_left p.2]
  -- the set is the kernel: `BlockTriangular id` is the vanishing of the strictly lower entries
  have hS := finrank_span_ker_erc _ hφ {θ : Params A dIn dOut |
        (∀ ℓ, ((θ.read ℓ).submatrix id (c ℓ)).BlockTriangular id)
          ∧ (θ.D.submatrix id cD).BlockTriangular id} fun θ => by
    simp only [Set.mem_ofPred_eq, Prod.ext_iff, funext_iff, Subtype.forall, Prod.forall]
    rfl
  rw [← hS, card_lower_erc.symm]
  simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self,
    mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- The strictly upper entries of the chosen rows of the embedding and of every write. -/
private def writesUpLin_erc [LinearOrder d] (ρE : d → dIn) (ρ : ∀ ℓ : Fin L, d → A.w ℓ) :
    Params A dIn dOut →ₗ[ℝ]
      ({p : d × d // p.2 < p.1} → ℝ) × (Fin L → {p : d × d // p.2 < p.1} → ℝ) where
  toFun θ := (fun p => θ.E (ρE p.1.2) p.1.1, fun ℓ p => θ.write ℓ (ρ ℓ p.1.2) p.1.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq d] in
/-- **Proposition A.9 (i), "respectively `d_model (d_model − 1)/2`, parameters per hidden
state", writes:** the parameters whose chosen rows of the embedding and of every write form lower
triangular matrices have dimension `P − (L + 1) d(d − 1)/2`. -/
theorem finrank_span_writes_lowerTriangular [LinearOrder d] (ρE : d → dIn)
    (ρ : ∀ ℓ : Fin L, d → A.w ℓ) (hρE : Function.Injective ρE)
    (hρ : ∀ ℓ, Function.Injective (ρ ℓ)) :
    Module.finrank ℝ (Submodule.span ℝ {θ : Params A dIn dOut |
        ((θ.E.submatrix ρE id)ᵀ).BlockTriangular id
          ∧ ∀ ℓ, (((θ.write ℓ).submatrix (ρ ℓ) id)ᵀ).BlockTriangular id})
      + (L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
      = Module.finrank ℝ (Params A dIn dOut) := by
  -- any values on the strictly upper entries of the chosen rows, `0` elsewhere
  have hφ : Function.Surjective (writesUpLin_erc (dOut := dOut) ρE ρ) := by
    rintro ⟨f, g⟩
    refine ⟨⟨Matrix.of fun r i =>
        Function.extend ρE (fun j => if h : j < i then f ⟨(i, j), h⟩ else 0) 0 r,
      fun _ => 0, fun ℓ => Matrix.of fun r i =>
        Function.extend (ρ ℓ) (fun j => if h : j < i then g ℓ ⟨(i, j), h⟩ else 0) 0 r, 0⟩,
      ?_⟩
    refine Prod.ext (funext fun p => ?_) (funext fun ℓ => funext fun p => ?_)
    · show Function.extend ρE (fun j => if h : j < p.1.1 then f ⟨(p.1.1, j), h⟩ else 0) 0
        (ρE p.1.2) = _
      rw [hρE.extend_apply, dite_eq_left p.2]
    · show Function.extend (ρ ℓ) (fun j => if h : j < p.1.1 then g ℓ ⟨(p.1.1, j), h⟩ else 0) 0
        (ρ ℓ p.1.2) = _
      rw [(hρ ℓ).extend_apply, dite_eq_left p.2]
  -- the set is the kernel: the transpose is upper triangular iff the strictly upper entries vanish
  have hS := finrank_span_ker_erc _ hφ {θ : Params A dIn dOut |
        ((θ.E.submatrix ρE id)ᵀ).BlockTriangular id
          ∧ ∀ ℓ, (((θ.write ℓ).submatrix (ρ ℓ) id)ᵀ).BlockTriangular id} fun θ => by
    simp only [Set.mem_ofPred_eq, Prod.ext_iff, funext_iff, Subtype.forall, Prod.forall]
    rfl
  rw [← hS, card_lower_erc.symm]
  simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self,
    mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

end Skips
