import SkipsLean.Depth.InactiveUnitTwoSided
import SkipsLean.Depth.InactiveGateTwoSided
import SkipsLean.Residual.SmallWritesOn

/-!
# Dead units without skips: the bound at every point of the open set

Paper (skips paper), Proposition A.35 (Dead units without skips): "There is a nonempty open set
of weights on which a unit of block 2 is dead. On it the functional dimension is at most
`P − (L + 1) d_model² − s − (2 d_model − 1)`, and at most
`P − (L + 1) d_model² − s − (3 d_model − 2)` for ReGLU, so the equality condition fails there."

`Depth/InactiveUnitTwoSided.lean` and `Depth/InactiveGateTwoSided.lean` have the bound at almost
every point of the open set (as Proposition E.1 of the dimension paper states it), where the
rank conditions hold. Here "On it": the bound **at every point of the open set**, by the lower
semicontinuity of the rank of the Jacobian on a batch
(`eventually_jacobianRank_ge_of_contDiffOn`, `Residual/SmallWritesOn.lean`): near a point `θ`
the rank on a batch does not drop, and every neighbourhood of `θ` has points at which the bound
holds.

* `jacobianRank_add_le_of_ae_of_contDiffOn`: the general step, for blocks without normalization
  whose fixed maps are continuously differentiable on open sets `V ℓ`: if `fd + k ≤ P` at almost
  every point of an open set `U`, then at every `θ ∈ U` the rank on every batch whose
  pre-activations at `θ` lie in the `V ℓ` is at most `P − k`.
  `funDim_add_le_of_ae_of_contDiff`: for blocks that are continuously differentiable everywhere,
  `fd + k ≤ P` at every point of `U`.
* ReLU blocks: the bound for the rank on every batch on which no pre-activation vanishes (the
  batches of the paper's functional dimension for these blocks).
* ReLU² blocks: the block is continuously differentiable, and the bound is for Lean's `funDim`.
* ReGLU blocks: the bound for the rank on every batch on which no gate pre-activation vanishes.

The widths are those of the twins: at least `d` hidden units in every block,
`d_in, d_out ≥ d ≥ 1`; the networks have the blocks `Fin (L + 1)`.
-/

namespace Skips

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

omit [DecidableEq d] in
/-- **From almost every point to every point of an open set, on batches in the domain of
smoothness.** Blocks without normalization, any stream matrices, `f_ℓ` continuously
differentiable on the open set `V ℓ`. If `fd + k ≤ P` at almost every point of an open set `U`,
then at every `θ ∈ U` and on every batch whose pre-activations at `θ` lie in the `V ℓ`, the rank
of the Jacobian is at most `P − k`. -/
theorem jacobianRank_add_le_of_ae_of_contDiffOn {L : ℕ} {A : Arch T d L} (hA : A.χ = id)
    (S : Fin L → Matrix d d ℝ) (V : ∀ ℓ, Set (Matrix T (A.r ℓ) ℝ)) (hVo : ∀ ℓ, IsOpen (V ℓ))
    (hf : ∀ ℓ, ContDiffOn ℝ 1 (A.f ℓ) (V ℓ))
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {U : Set (Params A dIn dOut)} (hU : IsOpen U) (k : ℕ)
    (hae : ∀ᵐ θ ∂μ, θ ∈ U → funDim A S θ + k ≤ Module.finrank ℝ (Params A dIn dOut))
    {θ : Params A dIn dOut} (hθ : θ ∈ U) {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i ℓ, hidden A S θ (X i) ℓ.castSucc * θ.read ℓ ∈ V ℓ) :
    jacobianRank A S X θ + k ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- near `θ` the rank on the batch does not drop (`Residual/SmallWritesOn.lean`)
  have hev := eventually_jacobianRank_ge_of_contDiffOn A θ hA S V hVo hf X hX
  obtain ⟨N, hNsub, hNo, hθN⟩ := mem_nhds_iff.1 hev
  -- `N ∩ U` is open and contains `θ`, so it has positive measure
  have hpos : μ (N ∩ U) ≠ 0 := ((hNo.inter hU).measure_pos μ ⟨θ, hθN, hθ⟩).ne'
  -- so it is not inside the null set where the bound fails: a point `θ'` of it has the bound
  obtain ⟨θ', hθ'N, hθ'⟩ : ∃ θ' ∈ N,
      funDim A S θ' + k ≤ Module.finrank ℝ (Params A dIn dOut) := by
    by_contra hcon
    refine hpos (measure_mono_null (fun x hx => ?_) (ae_iff.1 hae))
    exact fun h => hcon ⟨x, hx.1, h hx.2⟩
  -- the rank at `θ` is at most the rank at `θ'`, which is at most `fd(θ')`
  have h1 := (hNsub hθ'N).2
  have h2 := jacobianRank_le_funDim (A := A) (S := S) θ' X
  omega

omit [DecidableEq d] in
/-- **From almost every point to every point of an open set, for blocks that are continuously
differentiable.** Blocks without normalization, any stream matrices, `f_ℓ` continuously
differentiable. If `fd + k ≤ P` at almost every point of an open set `U`, then at every point
of `U`. -/
theorem funDim_add_le_of_ae_of_contDiff {L : ℕ} {A : Arch T d L} (hA : A.χ = id)
    (S : Fin L → Matrix d d ℝ) (hf : ∀ ℓ, ContDiff ℝ 1 (A.f ℓ))
    (μ : Measure (Params A dIn dOut)) [μ.IsAddHaarMeasure]
    {U : Set (Params A dIn dOut)} (hU : IsOpen U) (k : ℕ)
    (hae : ∀ᵐ θ ∂μ, θ ∈ U → funDim A S θ + k ≤ Module.finrank ℝ (Params A dIn dOut))
    {θ : Params A dIn dOut} (hθ : θ ∈ U) :
    funDim A S θ + k ≤ Module.finrank ℝ (Params A dIn dOut) := by
  -- a batch on which the rank is the functional dimension
  obtain ⟨n, X, hX⟩ := exists_jacobianRank_eq_funDim (A := A) (S := S) θ
  -- the general step with `V ℓ` the whole space
  have h := jacobianRank_add_le_of_ae_of_contDiffOn hA S (fun _ => Set.univ)
    (fun _ => isOpen_univ) (fun ℓ => (hf ℓ).contDiffOn) μ hU k hae hθ X
    (fun _ _ => Set.mem_univ _)
  rw [hX] at h
  exact h

variable {L : ℕ} {hid : Fin (L + 1) → Type} [∀ ℓ, Fintype (hid ℓ)] [∀ ℓ, DecidableEq (hid ℓ)]

/-- Helper: the matrices with no zero entry (for ReLU blocks: the pre-activations with no hidden
unit at its kink). -/
private def noZero_iep (m n : Type*) : Set (Matrix m n ℝ) :=
  {M | ∀ t i, M t i ≠ 0}

/-- Helper: the matrices with no zero entry form an open set. -/
private theorem isOpen_noZero_iep {m n : Type*} [Fintype m] [Fintype n] :
    IsOpen (noZero_iep m n) := by
  refine isOpen_iff_mem_nhds.2 fun M hM => ?_
  exact Filter.eventually_all.2 fun t => Filter.eventually_all.2 fun i =>
    (continuous_id.matrix_elem t i).continuousAt.eventually_ne (hM t i)

/-- Helper: ReLU is `0` or the identity near a point `z ≠ 0`, hence `C¹` there. -/
private theorem contDiffAt_relu_iep {z : ℝ} (hz : z ≠ 0) : ContDiffAt ℝ 1 relu z := by
  rcases hz.lt_or_gt with hneg | hpos
  · have h : relu =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds hneg] with y hy
      exact max_eq_right hy.le
    exact contDiffAt_const.congr_of_eventuallyEq h
  · have h : relu =ᶠ[𝓝 z] fun y => y := by
      filter_upwards [eventually_gt_nhds hpos] with y hy
      exact max_eq_left hy.le
    exact contDiffAt_id.congr_of_eventuallyEq h

/-- Helper: `M ↦ ReLU(M)` (entrywise) is `C¹` on the matrices with no zero entry. -/
private theorem contDiffOn_map_relu_iep {m n : Type*} [Fintype m] [Fintype n] :
    ContDiffOn ℝ 1 (fun M : Matrix m n ℝ => M.map relu) (noZero_iep m n) := by
  intro M hM
  refine ContDiffAt.contDiffWithinAt (contDiffAt_pi.2 fun t => contDiffAt_pi.2 fun i => ?_)
  have hent : ContDiff ℝ 1 (fun M : Matrix m n ℝ => M t i) :=
    contDiff_pi.1 (contDiff_pi.1 contDiff_id t) i
  have h := (contDiffAt_relu_iep (hM t i)).comp M hent.contDiffAt
  exact h

/-- **Proposition A.35, "On it", for ReLU blocks:** for `d_in, d_out ≥ d ≥ 1` and at least `d`
hidden units in every block, there is a nonempty open set of weights at every point `θ` of which
hidden unit `j` of block `ℓ.succ` is inactive at every input, and on every batch on which no
pre-activation vanishes at `θ` the rank of the Jacobian is at most
`P − (L+2) d² − s − (2d − 1)`. -/
theorem exists_isOpen_unitInactive_relu_forall [Nonempty d]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ ∀ θ ∈ U, UnitInactive θ ℓ.succ j ∧
        ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
          (∀ (i : Fin n) (m : Fin (L + 1)) (t : T) (u : hid m),
            (hidden (Arch.mlp relu id hid) 0 θ (X i) m.castSucc * θ.read m) t u ≠ 0) →
          jacobianRank (Arch.mlp relu id hid) 0 X θ
              + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m)
                + (2 * Fintype.card d - 1))
            ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  -- a Haar measure on the parameters, and the open set with the bound at almost every point
  let μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := Measure.addHaar
  obtain ⟨U, hUo, hUne, hUin, hae⟩ :=
    exists_isOpen_unitInactive_relu_of_le μ hdIn hdOut hhid ℓ j
  refine ⟨U, hUo, hUne, fun θ hθ => ⟨hUin θ hθ, fun n X hX => ?_⟩⟩
  -- off the kinks the blocks are `C¹`: the general step
  exact jacobianRank_add_le_of_ae_of_contDiffOn rfl 0 (fun m => noZero_iep T (hid m))
    (fun _ => isOpen_noZero_iep) (fun _ => contDiffOn_map_relu_iep) μ hUo _ hae hθ X
    (fun i m => hX i m)

/-- Helper: ReLU² is `C¹`: its derivative `2 max(z, 0)` is continuous. -/
private theorem contDiff_reluSq_iep : ContDiff ℝ 1 reluSq := by
  have hd : deriv reluSq = fun z => 2 * max z 0 := funext fun z => (hasDerivAt_reluSq z).deriv
  refine contDiff_one_iff_deriv.2 ⟨fun z => (hasDerivAt_reluSq z).differentiableAt, ?_⟩
  rw [hd]
  exact continuous_const.mul (continuous_id.max continuous_const)

/-- Helper: `M ↦ ReLU²(M)` (entrywise) is `C¹`. -/
private theorem contDiff_map_reluSq_iep {m n : Type*} [Fintype m] [Fintype n] :
    ContDiff ℝ 1 (fun M : Matrix m n ℝ => M.map reluSq) := by
  refine contDiff_pi.2 fun t => contDiff_pi.2 fun i => ?_
  have hent : ContDiff ℝ 1 (fun M : Matrix m n ℝ => M t i) :=
    contDiff_pi.1 (contDiff_pi.1 contDiff_id t) i
  have h := contDiff_reluSq_iep.comp hent
  exact h

/-- **Proposition A.35, "On it", for ReLU² blocks:** for `d_in, d_out ≥ d ≥ 1` and at least `d`
hidden units in every block, there is a nonempty open set of weights at every point of which
hidden unit `j` of block `ℓ.succ` is inactive at every input and
`fd ≤ P − (L+2) d² − s − (2d − 1)`. -/
theorem exists_isOpen_unitInactive_reluSq_forall [Nonempty d]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ) :
    ∃ U : Set (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ ∀ θ ∈ U, UnitInactive θ ℓ.succ j ∧
        funDim (Arch.mlp reluSq id hid) 0 θ
            + ((L + 2) * Fintype.card d ^ 2 + ∑ m, Fintype.card (hid m)
              + (2 * Fintype.card d - 1))
          ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  -- a Haar measure on the parameters, and the open set with the bound at almost every point
  let μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) :=
    Measure.addHaar
  obtain ⟨U, hUo, hUne, hUin, hae⟩ :=
    exists_isOpen_unitInactive_reluSq_of_le μ hdIn hdOut hhid ℓ j
  refine ⟨U, hUo, hUne, fun θ hθ => ⟨hUin θ hθ, ?_⟩⟩
  -- the blocks are `C¹`: the corollary of the general step
  exact funDim_add_le_of_ae_of_contDiff rfl 0 (fun _ => contDiff_map_reluSq_iep) μ hUo _ hae hθ

/-- Helper: the pre-activations of a gated block with no gate at its kink form an open set. -/
private theorem isOpen_gateSet_iep {m p : Type*} [Fintype m] [Fintype p] :
    IsOpen {M : Matrix m (p ⊕ p) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0} := by
  refine isOpen_iff_mem_nhds.2 fun M hM => ?_
  exact Filter.eventually_all.2 fun t => Filter.eventually_all.2 fun i =>
    (continuous_id.matrix_elem t (Sum.inl i)).continuousAt.eventually_ne (hM t i)

/-- Helper: the map of a gated block with a ReLU gate, `(t, i) ↦ relu(M_{t, g i}) M_{t, v i}`,
is `C¹` on the pre-activations with no gate at its kink. -/
private theorem contDiffOn_gate_iep {m p : Type*} [Fintype m] [Fintype p] :
    ContDiffOn ℝ 1
      (fun M : Matrix m (p ⊕ p) ℝ => Matrix.of fun t i => relu (M t (Sum.inl i)) * M t (Sum.inr i))
      {M : Matrix m (p ⊕ p) ℝ | ∀ t i, M t (Sum.inl i) ≠ 0} := by
  intro M hM
  refine ContDiffAt.contDiffWithinAt (contDiffAt_pi.2 fun t => contDiffAt_pi.2 fun i => ?_)
  have he : ∀ j, ContDiffAt ℝ 1 (fun N : Matrix m (p ⊕ p) ℝ => N t j) M := fun j =>
    (contDiff_pi.1 (contDiff_pi.1 contDiff_id t) j).contDiffAt
  have h := ((contDiffAt_relu_iep (hM t i)).comp M (he (Sum.inl i))).mul (he (Sum.inr i))
  exact h

/-- **Proposition A.35, "On it", for ReGLU blocks:** for `d_in, d_out ≥ d ≥ 1` and at least `d`
hidden units in every block, there is a nonempty open set of weights at every point `θ` of which
the gate of hidden unit `j` of block `ℓ.succ` is closed at every input, and on every batch on
which no pre-activation of a gate vanishes at `θ` the rank of the Jacobian is at most
`P − (L+2) d² − s − (3d − 2)`, with `s` twice the number of hidden units. -/
theorem exists_isOpen_gateInactive_reglu_forall [Nonempty d]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hhid : ∀ m, Fintype.card d ≤ Fintype.card (hid m)) (ℓ : Fin L) (j : hid ℓ.succ) :
    ∃ U : Set (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut),
      IsOpen U ∧ U.Nonempty ∧ ∀ θ ∈ U, GateInactive θ ℓ.succ j ∧
        ∀ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
          (∀ (i : Fin n) (m : Fin (L + 1)) (t : T) (u : hid m),
            (hidden (Arch.gated relu id hid) 0 θ (X i) m.castSucc * θ.read m) t (Sum.inl u)
              ≠ 0) →
          jacobianRank (Arch.gated relu id hid) 0 X θ
              + ((L + 2) * Fintype.card d ^ 2 + 2 * ∑ m, Fintype.card (hid m)
                + (3 * Fintype.card d - 2))
            ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  -- a Haar measure on the parameters, and the open set with the bound at almost every point
  let μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) :=
    Measure.addHaar
  obtain ⟨U, hUo, hUne, hUin, hae⟩ :=
    exists_isOpen_gateInactive_reglu_bound_of_le μ hdIn hdOut hhid ℓ j
  refine ⟨U, hUo, hUne, fun θ hθ => ⟨hUin θ hθ, fun n X hX => ?_⟩⟩
  -- off the kinks of the gates the blocks are `C¹`: the general step
  exact jacobianRank_add_le_of_ae_of_contDiffOn rfl 0
    (fun m => {M : Matrix T (hid m ⊕ hid m) ℝ | ∀ t u, M t (Sum.inl u) ≠ 0})
    (fun _ => isOpen_gateSet_iep) (fun _ => contDiffOn_gate_iep) μ hUo _ hae hθ X
    (fun i m => hX i m)

end Skips
