import SkipsLean.Dimension.UpperBoundTransformer
import SkipsLean.Dimension.RescalingMlp
import SkipsLean.Dimension.RescalingGate

/-!
# The upper bounds for networks of attention blocks and ReLU, ReLU² or ReGLU blocks

Papers. Skips paper, Section 4.1: the symmetries inside the blocks are "the rescaling of a hidden
unit of a ReLU or ReLU² block, the rescaling of the value of a hidden unit of a gated block, and
the changes of basis inside an attention head"; Theorem 4.2 (Upper bounds): "at generic
parameters, the functional dimension is at most `P − (L + 1) dim G − s` without skips and at most
`P − dim G − s` with identity skips." Dimension paper, Theorem 4.3 and Appendix B ("ReGLU, in
addition": the rescaling of the gate of a hidden unit).

`Dimension/UpperBoundTransformer.lean` has these bounds for networks of attention blocks and MLP
blocks or gated blocks, with the changes of basis inside the heads and the rescalings of the
values of gated units. Here the rescalings of positively homogeneous units are added:

* the rescalings of the hidden units of an MLP block whose activation is positively homogeneous
  of degree `k` (ReLU: `k = 1`; ReLU²: `k = 2`) and of the gates of a gated block whose gate is
  (ReGLU: the gate ReLU) are symmetries inside the blocks (`Symmetry/InsideBlocks.lean`);
* attention blocks and MLP blocks with such an activation:
  `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}² + ∑_ℓ d_hidden,ℓ`; named for ReLU and ReLU²;
* attention blocks and gated blocks with such a gate:
  `s = 2 ∑_ℓ H_ℓ d_{h,ℓ}² + 2 ∑_ℓ d_hidden,ℓ`; named for ReGLU.

At one parameter under the rank conditions of Lemma B.1 and with no vanishing column of the
reads of the hidden units, and at almost every parameter (`d_in ≥ d ≥ 1`, `d_h ≤ d`; without
skips, blocks of total width `H d_h + d_hidden ≥ d`). Under pre-RMSNorm (any `ε`)
`dim G = d(d−1)/2`.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {sees : T → T → Prop} [DecidableRel sees]
variable {H dh hid : Fin L → Type} [∀ ℓ, Fintype (H ℓ)] [∀ ℓ, Fintype (dh ℓ)]
  [∀ ℓ, Fintype (hid ℓ)] {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ}

/-! ### The rescalings are symmetries inside the blocks -/

/-- Helper (copy of the private `hasDerivAt_exp_mul_const` of `Dimension/RescalingMlp.lean`):
`τ ↦ e^{τ a} b` has derivative `a b` at `τ = 0`. -/
private theorem hasDerivAt_exp_mul_const_ubr (a b : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.exp (τ * a) * b) (a * b) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const a).exp.mul_const b
  simpa using h

/-- Helper: `e^{τ c}^k e^{τ (−k c)} = 1`. -/
private theorem exp_pow_mul_exp_neg_ubr (k : ℕ) (τ c : ℝ) :
    Real.exp (τ * c) ^ k * Real.exp (τ * -((k : ℝ) * c)) = 1 := by
  rw [← Real.exp_nat_mul, ← Real.exp_add,
    show (k : ℝ) * (τ * c) + τ * -((k : ℝ) * c) = 0 by ring, Real.exp_zero]

/-- Helper (copy of the private `rescaleCurveMlp` of `Dimension/RescalingMlp.lean`): the read
column of hidden unit `i` of block `ℓ` is multiplied by `e^{τ α ℓ i}`, its write row by
`e^{-τ k α ℓ i}`. -/
private noncomputable def rescaleCurveMlp_ubr (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) (τ : ℝ) :
    Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a i => Real.exp (τ * α ℓ i) * θ.read ℓ a i
  write ℓ := Matrix.of fun i a => Real.exp (τ * -((k : ℝ) * α ℓ i)) * θ.write ℓ i a
  D := θ.D

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `rescaleCurveMlp_zero`): the curve passes through `θ` at `τ = 0`. -/
private theorem rescaleCurveMlp_zero_ubr (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) :
    rescaleCurveMlp_ubr k θ α 0 = θ := by
  apply Params.ext'
  · rfl
  · intro ℓ
    ext a i
    simp [rescaleCurveMlp_ubr]
  · intro ℓ
    ext i a
    simp [rescaleCurveMlp_ubr]
  · rfl

omit [Fintype T] [DecidableEq d] in
/-- Helper (copy of `hasDerivAt_rescaleCurveMlp`): the curve has velocity `rescaleDirMlp k θ α`
at `τ = 0` (entry by entry, through `Params.linearEquivProd`). -/
private theorem hasDerivAt_rescaleCurveMlp_ubr (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) :
    HasDerivAt (rescaleCurveMlp_ubr k θ α) (rescaleDirMlp k θ α) 0 := by
  have hprod : HasDerivAt (fun τ : ℝ => Params.linearEquivProd (rescaleCurveMlp_ubr k θ α τ))
      (Params.linearEquivProd (rescaleDirMlp k θ α)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · -- the embedding does not move
      exact hasDerivAt_const (0 : ℝ) θ.E
    · -- the read entries are `e^{τ α} c`
      exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun i =>
        hasDerivAt_exp_mul_const_ubr (α ℓ i) (θ.read ℓ a i)
    · -- the write entries are `e^{-τ k α} a`
      exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun a =>
        hasDerivAt_exp_mul_const_ubr (-((k : ℝ) * α ℓ i)) (θ.write ℓ i a)
    · -- the readout does not move
      exact hasDerivAt_const (0 : ℝ) θ.D
  -- back from the tuples of components to the parameters
  exact (LinearMap.toContinuousLinearMap
    (Params.linearEquivProd (A := Arch.mlp (T := T) (d := d) σ χ hid) (dIn := dIn)
      (dOut := dOut)).symm.toLinearMap).hasFDerivAt.comp_hasDerivAt 0 hprod

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the rescaling keeps the map of every MLP block: hidden unit `i` contributes
`σ(e^{τ α} z_i) (e^{-τ k α} a_i) = σ(z_i) a_i` to every entry. -/
private theorem block_rescaleCurveMlp_ubr {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) (τ : ℝ)
    (ℓ : Fin L) (n : Matrix T d ℝ) :
    (Arch.mlp σ χ hid).f ℓ (n * (rescaleCurveMlp_ubr k θ α τ).read ℓ)
        * (rescaleCurveMlp_ubr k θ α τ).write ℓ
      = (Arch.mlp σ χ hid).f ℓ (n * θ.read ℓ) * θ.write ℓ := by
  -- the pre-activations are multiplied by `e^{τ α}`
  have hu : ∀ t i, (n * (rescaleCurveMlp_ubr k θ α τ).read ℓ) t i
      = Real.exp (τ * α ℓ i) * (n * θ.read ℓ) t i := by
    intro t i
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show n t j * (Real.exp (τ * α ℓ i) * θ.read ℓ j i)
      = Real.exp (τ * α ℓ i) * (n t j * θ.read ℓ j i)
    ring
  -- compare term by term
  ext t a
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  show σ ((n * (rescaleCurveMlp_ubr k θ α τ).read ℓ) t i)
      * (Real.exp (τ * -((k : ℝ) * α ℓ i)) * θ.write ℓ i a)
    = σ ((n * θ.read ℓ) t i) * θ.write ℓ i a
  rw [hu, hσ _ _ (Real.exp_pos _)]
  -- `e^{τ α}^k e^{-τ k α} = 1`
  calc _ = (Real.exp (τ * α ℓ i) ^ k * Real.exp (τ * -((k : ℝ) * α ℓ i)))
        * (σ ((n * θ.read ℓ) t i) * θ.write ℓ i a) := by ring
    _ = _ := by rw [exp_pow_mul_exp_neg_ubr, one_mul]

/-- **The rescalings of the hidden units of an MLP block with a positively homogeneous
activation are symmetries inside the blocks** (ReLU, ReLU²). -/
theorem insideBlocks_rescaleDirMlp {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (α : ∀ ℓ, hid ℓ → ℝ) :
    InsideBlocks (Arch.mlp σ χ hid) θ (rescaleDirMlp k θ α) := by
  -- the curve of the rescalings by `e^{τ α}`: through `θ`, with velocity `rescaleDirMlp k θ α`;
  -- it keeps `E` and `D` by definition and the map of every block at every `τ`
  exact ⟨rescaleCurveMlp_ubr k θ α, rescaleCurveMlp_zero_ubr k θ α,
    hasDerivAt_rescaleCurveMlp_ubr k θ α, Filter.Eventually.of_forall fun τ =>
      ⟨rfl, rfl, fun ℓ n => block_rescaleCurveMlp_ubr hσ θ α τ ℓ n⟩⟩

/-- Helper (copy of the private `rescaleCurveGate` of `Dimension/RescalingGate.lean`): the gate
column of hidden unit `i` of block `ℓ` is multiplied by `e^{τ β ℓ i}`, its write row by
`e^{-τ k β ℓ i}`, and the value columns do not move. -/
private noncomputable def rescaleCurveGate_ubr (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (β : ∀ ℓ, hid ℓ → ℝ) (τ : ℝ) :
    Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  E := θ.E
  read ℓ := Matrix.of fun a j =>
    Sum.elim (fun i => Real.exp (τ * β ℓ i) * θ.read ℓ a (Sum.inl i))
      (fun i => θ.read ℓ a (Sum.inr i)) j
  write ℓ := Matrix.of fun i a => Real.exp (τ * -((k : ℝ) * β ℓ i)) * θ.write ℓ i a
  D := θ.D

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (copy of `rescaleCurveGate_zero`): the curve passes through `θ` at `τ = 0`. -/
private theorem rescaleCurveGate_zero_ubr (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (β : ∀ ℓ, hid ℓ → ℝ) :
    rescaleCurveGate_ubr k θ β 0 = θ := by
  apply Params.ext'
  · rfl
  · intro ℓ
    ext a j
    cases j <;> simp [rescaleCurveGate_ubr]
  · intro ℓ
    ext i a
    simp [rescaleCurveGate_ubr]
  · rfl

omit [Fintype T] [DecidableEq d] in
/-- Helper (copy of `hasDerivAt_rescaleCurveGate`): the curve has velocity
`rescaleDirGate k θ β` at `τ = 0`. -/
private theorem hasDerivAt_rescaleCurveGate_ubr (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (β : ∀ ℓ, hid ℓ → ℝ) :
    HasDerivAt (rescaleCurveGate_ubr k θ β) (rescaleDirGate k θ β) 0 := by
  have hprod : HasDerivAt (fun τ : ℝ => Params.linearEquivProd (rescaleCurveGate_ubr k θ β τ))
      (Params.linearEquivProd (rescaleDirGate k θ β)) 0 := by
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_))
    · -- the embedding does not move
      exact hasDerivAt_const (0 : ℝ) θ.E
    · -- the gate entries are `e^{τ β} g`; the value entries do not move
      refine hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun j => ?_
      cases j with
      | inl i => exact hasDerivAt_exp_mul_const_ubr (β ℓ i) (θ.read ℓ a (Sum.inl i))
      | inr i => exact hasDerivAt_const (0 : ℝ) (θ.read ℓ a (Sum.inr i))
    · -- the write entries are `e^{-τ k β} a`
      exact hasDerivAt_pi.2 fun ℓ => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun a =>
        hasDerivAt_exp_mul_const_ubr (-((k : ℝ) * β ℓ i)) (θ.write ℓ i a)
    · -- the readout does not move
      exact hasDerivAt_const (0 : ℝ) θ.D
  -- back from the tuples of components to the parameters
  exact (LinearMap.toContinuousLinearMap
    (Params.linearEquivProd (A := Arch.gated (T := T) (d := d) σ χ hid) (dIn := dIn)
      (dOut := dOut)).symm.toLinearMap).hasFDerivAt.comp_hasDerivAt 0 hprod

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the rescaling of the gates keeps the map of every gated block: hidden unit `i`
contributes `σ(e^{τ β} z_i) u_i (e^{-τ k β} a_i) = σ(z_i) u_i a_i` to every entry. -/
private theorem block_rescaleCurveGate_ubr {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (β : ∀ ℓ, hid ℓ → ℝ) (τ : ℝ)
    (ℓ : Fin L) (n : Matrix T d ℝ) :
    (Arch.gated σ χ hid).f ℓ (n * (rescaleCurveGate_ubr k θ β τ).read ℓ)
        * (rescaleCurveGate_ubr k θ β τ).write ℓ
      = (Arch.gated σ χ hid).f ℓ (n * θ.read ℓ) * θ.write ℓ := by
  -- the gates are multiplied by `e^{τ β}`
  have hz : ∀ t i, (n * (rescaleCurveGate_ubr k θ β τ).read ℓ) t (Sum.inl i)
      = Real.exp (τ * β ℓ i) * (n * θ.read ℓ) t (Sum.inl i) := by
    intro t i
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show n t j * (Real.exp (τ * β ℓ i) * θ.read ℓ j (Sum.inl i))
      = Real.exp (τ * β ℓ i) * (n t j * θ.read ℓ j (Sum.inl i))
    ring
  -- the values are the same
  have hu : ∀ t i, (n * (rescaleCurveGate_ubr k θ β τ).read ℓ) t (Sum.inr i)
      = (n * θ.read ℓ) t (Sum.inr i) := fun _ _ => rfl
  -- compare term by term
  ext t a
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  show σ ((n * (rescaleCurveGate_ubr k θ β τ).read ℓ) t (Sum.inl i))
      * (n * (rescaleCurveGate_ubr k θ β τ).read ℓ) t (Sum.inr i)
      * (Real.exp (τ * -((k : ℝ) * β ℓ i)) * θ.write ℓ i a)
    = σ ((n * θ.read ℓ) t (Sum.inl i)) * (n * θ.read ℓ) t (Sum.inr i) * θ.write ℓ i a
  rw [hz, hu, hσ _ _ (Real.exp_pos _)]
  -- `e^{τ β}^k e^{-τ k β} = 1`
  calc _ = (Real.exp (τ * β ℓ i) ^ k * Real.exp (τ * -((k : ℝ) * β ℓ i)))
        * (σ ((n * θ.read ℓ) t (Sum.inl i)) * (n * θ.read ℓ) t (Sum.inr i)
          * θ.write ℓ i a) := by ring
    _ = _ := by rw [exp_pow_mul_exp_neg_ubr, one_mul]

/-- **The rescalings of the gates of a gated block with a positively homogeneous gate are
symmetries inside the blocks** (ReGLU). -/
theorem insideBlocks_rescaleDirGate {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (β : ∀ ℓ, hid ℓ → ℝ) :
    InsideBlocks (Arch.gated σ χ hid) θ (rescaleDirGate k θ β) := by
  -- the curve of the rescalings of the gates by `e^{τ β}`: through `θ`, with velocity
  -- `rescaleDirGate k θ β`; it keeps `E`, `D` and the map of every block at every `τ`
  exact ⟨rescaleCurveGate_ubr k θ β, rescaleCurveGate_zero_ubr k θ β,
    hasDerivAt_rescaleCurveGate_ubr k θ β, Filter.Eventually.of_forall fun τ =>
      ⟨rfl, rfl, fun ℓ n => block_rescaleCurveGate_ubr hσ θ β τ ℓ n⟩⟩


/-! ### Attention blocks and MLP blocks with a positively homogeneous activation -/

/-- **Theorem 4.3 of the dimension paper for attention blocks and MLP blocks with a positively
homogeneous activation, without normalization, under the conditions of Lemma B.1:** `fd ≤ P − (L +
1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_skipless_attentionMlp_rescale {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hc : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a i) ≠ 0) :
    funDim (Arch.attentionMlp sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and MLP blocks with a positively
homogeneous activation, under pre-RMSNorm, under the conditions of Lemma B.1:** `fd ≤ P − (L + 1)
d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_skipless_attentionMlp_rescale_rmsNorm (ε : ℝ) {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hc : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a i) ≠ 0) :
    funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and MLP blocks with
a positively homogeneous activation, without normalization, under the conditions of Lemma B.1:**
`fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_residual_attentionMlp_rescale {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hc : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a i) ≠ 0) :
    funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and MLP blocks with
a positively homogeneous activation, under pre-RMSNorm, under the conditions of Lemma B.1:** `fd ≤
P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_residual_attentionMlp_rescale_rmsNorm (ε : ℝ) {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hc : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a i) ≠ 0) :
    funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and MLP blocks with a positively
homogeneous activation, without normalization, at generic parameters:** `fd ≤ P − (L + 1) d² − 2
∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attentionMlp_rescale [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and MLP blocks with a positively
homogeneous activation, under pre-RMSNorm, at generic parameters:** `fd ≤ P − (L + 1) d(d−1)/2 − 2
∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attentionMlp_rescale_rmsNorm [Nonempty d] (ε : ℝ) {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and MLP blocks with
a positively homogeneous activation, without normalization, at generic parameters:** `fd ≤ P − d²
− 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attentionMlp_rescale [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and MLP blocks with
a positively homogeneous activation, under pre-RMSNorm, at generic parameters:** `fd ≤ P −
d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attentionMlp_rescale_rmsNorm [Nonempty d] (ε : ℝ) {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry


/-! ### Attention blocks and ReLU blocks -/

/-- **Theorem 4.3 of the dimension paper for attention blocks and ReLU blocks, without
normalization, at generic parameters:** `fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attention_relu [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees relu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees relu id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees relu id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and ReLU blocks, under pre-RMSNorm,
at generic parameters:** `fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attention_relu_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees relu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees relu (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees relu (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and ReLU blocks,
without normalization, at generic parameters:** `fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attention_relu [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees relu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees relu id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees relu id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and ReLU blocks,
under pre-RMSNorm, at generic parameters:** `fd ≤ P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attention_relu_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees relu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees relu (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees relu (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry


/-! ### Attention blocks and ReLU² blocks -/

/-- **Theorem 4.3 of the dimension paper for attention blocks and ReLU² blocks, without
normalization, at generic parameters:** `fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attention_reluSq [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees reluSq id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees reluSq id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees reluSq id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and ReLU² blocks, under pre-RMSNorm,
at generic parameters:** `fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attention_reluSq_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees reluSq (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees reluSq (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees reluSq (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and ReLU² blocks,
without normalization, at generic parameters:** `fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attention_reluSq [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees reluSq id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees reluSq id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees reluSq id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and ReLU² blocks,
under pre-RMSNorm, at generic parameters:** `fd ≤ P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attention_reluSq_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionMlp (T := T) (d := d) sees reluSq (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionMlp sees reluSq (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionMlp (T := T) (d := d) sees reluSq (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry


/-! ### Attention blocks and gated blocks with a positively homogeneous gate -/

/-- **Theorem 4.3 of the dimension paper for attention blocks and gated blocks with a positively
homogeneous gate, without normalization, under the conditions of Lemma B.1:** `fd ≤ P − (L + 1) d²
− 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_skipless_attentionGated_rescale {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and gated blocks with a positively
homogeneous gate, under pre-RMSNorm, under the conditions of Lemma B.1:** `fd ≤ P − (L + 1)
d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_skipless_attentionGated_rescale_rmsNorm (ε : ℝ) {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and gated blocks
with a positively homogeneous gate, without normalization, under the conditions of Lemma B.1:**
`fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_residual_attentionGated_rescale {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and gated blocks
with a positively homogeneous gate, under pre-RMSNorm, under the conditions of Lemma B.1:** `fd ≤
P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem funDim_add_le_residual_attentionGated_rescale_rmsNorm (ε : ℝ) {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hQ : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (hv : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.sumSnd.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and gated blocks with a positively
homogeneous gate, without normalization, at generic parameters:** `fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ
d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attentionGated_rescale [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and gated blocks with a positively
homogeneous gate, under pre-RMSNorm, at generic parameters:** `fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ
H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attentionGated_rescale_rmsNorm [Nonempty d] (ε : ℝ) {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and gated blocks
with a positively homogeneous gate, without normalization, at generic parameters:** `fd ≤ P − d² −
2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attentionGated_rescale [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and gated blocks
with a positively homogeneous gate, under pre-RMSNorm, at generic parameters:** `fd ≤ P − d(d−1)/2
− 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attentionGated_rescale_rmsNorm [Nonempty d] (ε : ℝ) {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees σ (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry


/-! ### Attention blocks and ReGLU blocks -/

/-- **Theorem 4.3 of the dimension paper for attention blocks and ReGLU blocks, without
normalization, at generic parameters:** `fd ≤ P − (L + 1) d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attention_reglu [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees relu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees relu id H dh hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees relu id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 of the dimension paper for attention blocks and ReGLU blocks, under pre-RMSNorm,
at generic parameters:** `fd ≤ P − (L + 1) d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ d_hidden,ℓ`. -/
theorem ae_funDim_add_le_skipless_attention_reglu_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees relu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d)
    (hW : ∀ ℓ,
      Fintype.card d ≤ Fintype.card (H ℓ) * Fintype.card (dh ℓ) + Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees relu (rmsNorm ε) H dh hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees relu (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and ReGLU blocks,
without normalization, at generic parameters:** `fd ≤ P − d² − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attention_reglu [Nonempty d]
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees relu id H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees relu id H dh hid) 1 θ
        + (Fintype.card d ^ 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees relu id H dh hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 of the skips paper with identity skips for attention blocks and ReGLU blocks,
under pre-RMSNorm, at generic parameters:** `fd ≤ P − d(d−1)/2 − 2 ∑_ℓ H_ℓ d_{h,ℓ}² − 2 ∑_ℓ
d_hidden,ℓ`. -/
theorem ae_funDim_add_le_residual_attention_reglu_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params
      (Arch.attentionGated (T := T) (d := d) sees relu (rmsNorm ε) H dh hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.attentionGated sees relu (rmsNorm ε) H dh hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2
          + (2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2
            + 2 * ∑ ℓ, Fintype.card (hid ℓ)))
      ≤ Module.finrank ℝ (Params
          (Arch.attentionGated (T := T) (d := d) sees relu (rmsNorm ε) H dh hid) dIn dOut) := by
  sorry

end Skips
