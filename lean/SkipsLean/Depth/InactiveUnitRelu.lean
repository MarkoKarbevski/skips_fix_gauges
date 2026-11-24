import SkipsLean.Depth.InactiveUnit
import SkipsLean.Generic.Params

/-!
# Proposition E.1 for ReLU and ReLU² blocks: an open set of weights with an inactive hidden unit

Paper (dimension paper): Appendix E, Proposition E.1 and the part "ReLU and ReLU²" of its proof.

"Proposition E.1 (Inactive hidden units). Consider networks of `L ≥ 2` ReLU, ReLU² or ReGLU blocks
without normalization, each with more than `d_model` hidden units. There is a nonempty open set of
weights on which a hidden unit of block 2 is inactive at every input. At almost every point of this
set the functional dimension is at most `P − (L+1) d_model² − s − (2 d_model − 1)`, and at most
`P − (L+1) d_model² − s − (3 d_model − 2)` for ReGLU blocks. So these networks do not satisfy the
equality condition."

"ReLU and ReLU². The hidden unit of block 2 reads the number `h_1 r = ∑_k σ(u c_k) a_k r`, with
`σ ≥ 0`. It is positive at no input when `a_k r < 0` for all `k`, which holds on a nonempty open
set of weights."

Here the network has the blocks `Fin (L + 1)`, so it has at least two blocks when `L ≥ 1`. The
paper's block 1 and block 2 are the blocks `ℓ.castSucc` and `ℓ.succ` for `ℓ : Fin L`: the
statements hold for every block after the first, and for every hidden unit `j` of it.

* `negReadSet ℓ j`: the weights with `a_k r < 0` for every hidden unit `k` of block `ℓ.castSucc`,
  where `r` is the read column of hidden unit `j` of block `ℓ.succ`. It is open and nonempty, and
  on it the hidden unit is inactive at every input when `σ ≥ 0`.
* The proposition for ReLU and for ReLU² blocks (`exists_isOpen_unitInactive_relu`,
  `exists_isOpen_unitInactive_reluSq`): a nonempty open set on which the unit is inactive at every
  input, and at almost every point of it `fd ≤ P − (L+2) d² − s − (2d − 1)` (the network has
  `L + 1` blocks, so `L + 2` hidden states). Lean asks at least `d` hidden units in every block
  and more than `d` in the block of the inactive unit.
* "So these networks do not satisfy the equality condition"
  (`not_ae_funDim_add_eq_relu_skipless`, `not_ae_funDim_add_eq_reluSq_skipless`): it is not the
  case that `fd = P − (L+2) d² − s` at almost every parameter.

The bound at one parameter is in `Depth/InactiveUnit.lean`; ReGLU blocks are in
`Depth/InactiveGateReGLU.lean`. As there, Lean's `funDim` takes the Jacobian at all inputs, so it
is at least the paper's functional dimension, and the bounds here are bounds for the paper's.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin (L + 1) → Type}
  [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)]

/-- The weights at which `a_k r < 0` for every hidden unit `k` of block `ℓ.castSucc`, where `a_k`
is its write row and `r` is the read column of hidden unit `j` of the next block `ℓ.succ`. -/
def negReadSet (σ : ℝ → ℝ) (χ : Matrix T d ℝ → Matrix T d ℝ) (dIn dOut : Type*) [Fintype dIn]
    [Fintype dOut] (ℓ : Fin L) (j : hid ℓ.succ) :
    Set (Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) :=
  {θ | ∀ k : hid ℓ.castSucc, (θ.write ℓ.castSucc *ᵥ fun a => θ.read ℓ.succ a j) k < 0}

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- An entry of a read is a continuous function of the parameters. -/
private theorem continuous_read_entry_iur (m : Fin (L + 1)) (a : d) (i : hid m) :
    Continuous fun θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut => θ.read m a i :=
  LinearMap.continuous_of_finiteDimensional
    ({ toFun := fun θ => θ.read m a i
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } :
      Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut →ₗ[ℝ] ℝ)

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- An entry of a write is a continuous function of the parameters. -/
private theorem continuous_write_entry_iur (m : Fin (L + 1)) (i : hid m) (a : d) :
    Continuous fun θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut => θ.write m i a :=
  LinearMap.continuous_of_finiteDimensional
    ({ toFun := fun θ => θ.write m i a
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } :
      Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut →ₗ[ℝ] ℝ)

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- The set of weights with `a_k r < 0` for all `k` is open. -/
theorem isOpen_negReadSet (ℓ : Fin L) (j : hid ℓ.succ) :
    IsOpen (negReadSet (T := T) (d := d) σ χ dIn dOut ℓ j) := by
  -- the set is the intersection over `k` of the sets `{θ | a_k r < 0}`
  have hset : negReadSet (T := T) (d := d) σ χ dIn dOut ℓ j =
      ⋂ k : hid ℓ.castSucc, {θ | (θ.write ℓ.castSucc *ᵥ fun a => θ.read ℓ.succ a j) k < 0} := by
    ext θ
    simp only [negReadSet, Set.mem_iInter]
    rfl
  rw [hset]
  refine isOpen_iInter_of_finite fun k => isOpen_lt ?_ continuous_const
  -- `a_k r = ∑_a W k a * r a` is a finite sum of products of entries of `θ`
  simp only [Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun a _ =>
    (continuous_write_entry_iur _ k a).mul (continuous_read_entry_iur _ a j)

omit [Fintype T] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- The set of weights with `a_k r < 0` for all `k` is nonempty. -/
theorem nonempty_negReadSet [Nonempty d] (ℓ : Fin L) (j : hid ℓ.succ) :
    (negReadSet (T := T) (d := d) σ χ dIn dOut ℓ j).Nonempty := by
  obtain a₀ : d := Classical.arbitrary d
  -- reads with the row `a₀` equal to `1`, writes with the column `a₀` equal to `-1`
  refine ⟨⟨0, fun _ => Matrix.of fun a _ => if a = a₀ then 1 else 0,
    fun _ => Matrix.of fun _ a => if a = a₀ then -1 else 0, 0⟩, fun k => ?_⟩
  -- then `a_k r = -1`
  simp [Matrix.mulVec, dotProduct]

omit [Fintype T] [DecidableEq d] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- **Proof of Proposition E.1, ReLU and ReLU²:** "The hidden unit of block 2 reads the number
`h_1 r = ∑_k σ(u c_k) a_k r`, with `σ ≥ 0`. It is positive at no input when `a_k r < 0` for all
`k`." -/
theorem unitInactive_of_mem_negReadSet (hσ : ∀ z : ℝ, 0 ≤ σ z) (ℓ : Fin L) (j : hid ℓ.succ)
    {θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut}
    (hθ : θ ∈ negReadSet σ id dIn dOut ℓ j) : UnitInactive θ ℓ.succ j := by
  intro x t
  -- the hidden state before block `ℓ.succ` is the output of block `ℓ.castSucc`
  rw [Fin.castSucc_succ, hidden_succ]
  simp only [Pi.zero_apply, Matrix.mul_zero, zero_add, id, Matrix.mul_assoc]
  -- `h r = ∑_k σ(u c_k) a_k r`, a sum of products of a number `≥ 0` and a number `< 0`
  rw [Matrix.mul_apply]
  refine Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (hσ _) ?_
  exact (hθ k).le

omit [Fintype T] [Fintype dIn] [Fintype dOut] [∀ ℓ, DecidableEq (hid ℓ)] in
/-- A matrix with `d` columns and an invertible `d × d` submatrix of rows has rank `d` (a copy of
the private `rank_eq_of_isUnit_det_submatrix` of `Generic/Params.lean`). -/
private theorem rank_eq_of_isUnit_det_submatrix_iur {m : Type*} (M : Matrix m d ℝ) (ρ : d ↪ m)
    (h : IsUnit (M.submatrix ρ id).det) : M.rank = Fintype.card d :=
  le_antisymm (Matrix.rank_le_card_width M)
    ((Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h)).symm.le.trans
      (Matrix.rank_submatrix_le M ρ id))

/-- Proposition E.1 for an activation `σ ≥ 0` that is positively homogeneous of degree `k` and
vanishes on `z ≤ 0` (ReLU and ReLU²). -/
private theorem exists_isOpen_unitInactive_iur [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0) (hσnn : ∀ z : ℝ, 0 ≤ σ z)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ)
    (hj : Fintype.card d < Fintype.card (hid ℓ.succ)) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, UnitInactive θ ℓ.succ j) ∧
      ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp σ id hid) 0 θ
          + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m) + (2 * Fintype.card d - 1))
        ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  -- the open set: `a_k r < 0` for every hidden unit `k` of block `ℓ.castSucc`
  refine ⟨negReadSet σ id dIn dOut ℓ j, isOpen_negReadSet ℓ j, nonempty_negReadSet ℓ j,
    fun θ hθ => unitInactive_of_mem_negReadSet hσnn ℓ j hθ, ?_⟩
  -- `d` rows of the write of block `ℓ.succ` other than the row `j`
  have hcard : Fintype.card d ≤ Fintype.card {i : hid ℓ.succ // i ≠ j} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    omega
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hcard
  -- at generic parameters `E` and the writes have rank `d`, no read column vanishes, and every
  -- `d` rows of a write form an invertible matrix
  filter_upwards [ae_rank_E_write μ hdIn hhid, ae_read_col_ne_zero μ,
    ae_isUnit_det_submatrix μ] with θ h1 h2 h3 hθU
  -- the unit is inactive at every input at all parameters near `θ`
  have hθ : ∀ᶠ θ' in 𝓝 θ, UnitInactive θ' ℓ.succ j :=
    Filter.mem_of_superset ((isOpen_negReadSet (σ := σ) (χ := id) ℓ j).mem_nhds hθU)
      fun _ h => unitInactive_of_mem_negReadSet hσnn ℓ j h
  -- the write of block `ℓ.succ` without the row `j` still has rank `d`
  have hwj : ((θ.write ℓ.succ).submatrix (fun i : {i : hid ℓ.succ // i ≠ j} => (i : hid ℓ.succ))
      id).rank = Fintype.card d :=
    rank_eq_of_isUnit_det_submatrix_iur _ ρ
      (h3.2.2.2 ℓ.succ (ρ.trans (Function.Embedding.subtype _)))
  -- the bound at one parameter, for a network of `L + 1` blocks
  exact funDim_add_le_of_eventually_unitInactive hσ hσ0 θ ℓ.succ j hθ h1.1 h1.2 hwj h2

/-- "So these networks do not satisfy the equality condition", for an activation as in
`exists_isOpen_unitInactive_iur`. -/
private theorem not_ae_funDim_add_eq_iur [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hσ0 : ∀ z : ℝ, z ≤ 0 → σ z = 0) (hσnn : ∀ z : ℝ, 0 ≤ σ z)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ m, Fintype.card d < Fintype.card (hid m)) :
    ¬ ∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 0 θ
        + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  intro hae
  -- the inactive unit: a hidden unit `j` of the second block
  let ℓ : Fin L := ⟨0, hL⟩
  have hd1 : 0 < Fintype.card d := Fintype.card_pos
  have : Nonempty (hid ℓ.succ) := Fintype.card_pos_iff.mp (hd1.trans (hhid _))
  obtain j : hid ℓ.succ := Classical.arbitrary _
  obtain ⟨U, hUo, hUne, -, hU⟩ :=
    exists_isOpen_unitInactive_iur hσ hσ0 hσnn μ hdIn (fun m => (hhid m).le) ℓ j (hhid _)
  -- at almost every point of `U` both the equality and the bound with `2d - 1 ≥ 1` would hold
  have hnull : μ U = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae, hU] with θ he hle hθU
    have := hle hθU
    omega
  -- but a nonempty open set has positive measure
  exact (hUo.measure_pos μ hUne).ne' hnull

/-- **Proposition E.1 for ReLU blocks:** for `d_in ≥ d ≥ 1`, at least `d` hidden units in every
block and more than `d` in block `ℓ.succ`, there is a nonempty open set of weights on which hidden
unit `j` of block `ℓ.succ` is inactive at every input, and at almost every point of this set
`fd ≤ P − (L+2) d² − s − (2d − 1)`, with `s` the number of hidden units. -/
theorem exists_isOpen_unitInactive_relu [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ)
    (hj : Fintype.card d < Fintype.card (hid ℓ.succ)) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, UnitInactive θ ℓ.succ j) ∧
      ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp relu id hid) 0 θ
          + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m) + (2 * Fintype.card d - 1))
        ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  exact exists_isOpen_unitInactive_iur relu_homogeneous (fun _ hz => max_eq_right hz)
    (fun _ => le_max_right _ _) μ hdIn hhid ℓ j hj

/-- **Proposition E.1 for ReLU² blocks:** the same as for ReLU blocks. -/
theorem exists_isOpen_unitInactive_reluSq [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ)
    (hj : Fintype.card d < Fintype.card (hid ℓ.succ)) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ (∀ θ ∈ U, UnitInactive θ ℓ.succ j) ∧
      ∀ᵐ θ ∂μ, θ ∈ U → funDim (Arch.mlp reluSq id hid) 0 θ
          + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m) + (2 * Fintype.card d - 1))
        ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  exact exists_isOpen_unitInactive_iur reluSq_homogeneous
    (fun _ hz => by rw [reluSq, max_eq_right hz, zero_pow two_ne_zero])
    (fun _ => sq_nonneg _) μ hdIn hhid ℓ j hj

/-- **Proposition E.1, "So these networks do not satisfy the equality condition", for ReLU
blocks:** for at least two blocks (`L ≥ 1`), `d_in ≥ d ≥ 1` and more than `d` hidden units in every
block, it is not the case that `fd = P − (L+2) d² − s` at almost every parameter. -/
theorem not_ae_funDim_add_eq_relu_skipless [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ m, Fintype.card d < Fintype.card (hid m)) :
    ¬ ∀ᵐ θ ∂μ, funDim (Arch.mlp relu id hid) 0 θ
        + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  exact not_ae_funDim_add_eq_iur relu_homogeneous (fun _ hz => max_eq_right hz)
    (fun _ => le_max_right _ _) μ hL hdIn hhid

/-- **Proposition E.1, "So these networks do not satisfy the equality condition", for ReLU²
blocks.** -/
theorem not_ae_funDim_add_eq_reluSq_skipless [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ m, Fintype.card d < Fintype.card (hid m)) :
    ¬ ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq id hid) 0 θ
        + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  exact not_ae_funDim_add_eq_iur reluSq_homogeneous
    (fun _ hz => by rw [reluSq, max_eq_right hz, zero_pow two_ne_zero])
    (fun _ => sq_nonneg _) μ hL hdIn hhid

end Skips
