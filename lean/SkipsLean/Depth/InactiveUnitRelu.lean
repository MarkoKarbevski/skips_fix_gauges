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

/-- The set of weights with `a_k r < 0` for all `k` is nonempty. -/
theorem nonempty_negReadSet [Nonempty d] (ℓ : Fin L) (j : hid ℓ.succ) :
    (negReadSet (T := T) (d := d) σ χ dIn dOut ℓ j).Nonempty := by
  obtain a₀ : d := Classical.arbitrary d
  -- reads with the row `a₀` equal to `1`, writes with the column `a₀` equal to `-1`
  refine ⟨⟨0, fun _ => Matrix.of fun a _ => if a = a₀ then 1 else 0,
    fun _ => Matrix.of fun _ a => if a = a₀ then -1 else 0, 0⟩, fun k => ?_⟩
  -- then `a_k r = -1`
  simp [Matrix.mulVec, dotProduct]

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
  sorry

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
  sorry

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
  sorry

/-- **Proposition E.1, "So these networks do not satisfy the equality condition", for ReLU²
blocks.** -/
theorem not_ae_funDim_add_eq_reluSq_skipless [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hL : 0 < L) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ m, Fintype.card d < Fintype.card (hid m)) :
    ¬ ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq id hid) 0 θ
        + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  sorry

end Skips
