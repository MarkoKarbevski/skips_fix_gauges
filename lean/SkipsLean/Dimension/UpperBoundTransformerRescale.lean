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

omit [Fintype T] [DecidableEq d] in
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

omit [Fintype T] [DecidableEq d] in
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


/-! ### Helpers: the changes of basis inside the heads (copies of `UpperBoundTransformer`) -/

/-- Helper (the private `headDirQKLin_ubt`): `Γ ↦ headDirQK θ Γ` is linear. -/
private noncomputable def headDirQKLin_ubr
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  toFun := headDirQK θ
  map_add' Γ Δ := by
    apply Params.ext'
    · simp [headDirQK]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp only [headDirQK, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib]
      · simp only [headDirQK, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib, neg_add]
      · simp [headDirQK]
    · intro ℓ
      simp [headDirQK]
    · simp [headDirQK]
  map_smul' c Γ := by
    apply Params.ext'
    · simp [headDirQK]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp only [headDirQK, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      · simp only [headDirQK, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_neg]
        exact congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => by ring)
      · simp [headDirQK]
    · intro ℓ
      simp [headDirQK]
    · simp [headDirQK]

/-- Helper (the private `headDirVOLin_ubt`): `Γ' ↦ headDirVO θ Γ'` is linear. -/
private noncomputable def headDirVOLin_ubr
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut) :
    (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) →ₗ[ℝ]
      Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut where
  toFun := headDirVO θ
  map_add' Γ Δ := by
    apply Params.ext'
    · simp [headDirVO]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp [headDirVO]
      · simp [headDirVO]
      · simp only [headDirVO, Params.add_read, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
          mul_add, Finset.sum_add_distrib]
    · intro ℓ
      ext p b
      simp only [headDirVO, Params.add_write, Matrix.add_apply, Matrix.of_apply, Pi.add_apply,
        add_mul, Finset.sum_add_distrib, neg_add]
    · simp [headDirVO]
  map_smul' c Γ := by
    apply Params.ext'
    · simp [headDirVO]
    · intro ℓ
      ext a ⟨i, k | k | k⟩
      · simp [headDirVO]
      · simp [headDirVO]
      · simp only [headDirVO, Params.smul_read, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    · intro ℓ
      ext p b
      simp only [headDirVO, Params.smul_write, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply,
        smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_neg]
      exact congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => by ring)
    · simp [headDirVO]

/-- Helper (the private `finrank_headFun_ubt`): the families `Γ` of `d_h × d_h` matrices, one for
each head of each block, form a space of dimension `∑_ℓ H_ℓ d_{h,ℓ}²`. -/
private theorem finrank_headFun_ubr :
    Module.finrank ℝ (∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ)
      = ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Module.finrank_self, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]

/-- Helper (the private `cancel_left_of_rank_ubt`): a matrix `M` of rank equal to its number of
columns cancels on the left, `M X = M Y → X = Y` (its kernel is `0` by rank–nullity). -/
private theorem cancel_left_of_rank_ubr {m n k : Type*} [Fintype n] (M : Matrix m n ℝ)
    (hM : M.rank = Fintype.card n) {X Y : Matrix n k ℝ} (h : M * X = M * Y) : X = Y := by
  -- `v ↦ M v` is injective: `rank M + dim ker M = card n`
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    rw [Matrix.rank] at hM
    omega
  -- compare `X` and `Y` column by column
  ext i j
  have hcol : M.mulVecLin (fun l => X l j) = M.mulVecLin (fun l => Y l j) := by
    funext p
    have := congrFun (congrFun h p) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  exact congrFun (hinj hcol) i

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `headDirLin_injective_ubt`): if the query and the value matrix of every
head have rank `d_h`, the direction `headDirQK θ Γ + headDirVO θ Γ'` determines `Γ` and `Γ'`. -/
private theorem headDirLin_injective_ubr
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    Function.Injective ((headDirQKLin_ubr θ).coprod (headDirVOLin_ubr θ)) := by
  rintro ⟨Γ, Γ'⟩ ⟨Δ, Δ'⟩ h
  have h' : headDirQK θ Γ + headDirVO θ Γ' = headDirQK θ Δ + headDirVO θ Δ' := h
  -- the entry `(a, p)` of the read of block `ℓ`
  have hr : ∀ ℓ a p, (headDirQK θ Γ + headDirVO θ Γ').read ℓ a p
      = (headDirQK θ Δ + headDirVO θ Δ').read ℓ a p := fun ℓ a p => by rw [h']
  refine Prod.ext ?_ ?_ <;> funext ℓ i
  · -- the query columns of head `i`: `W_{Q,i} Γ_i = W_{Q,i} Δ_i`, and `W_{Q,i}` has rank `d_h`
    refine cancel_left_of_rank_ubr _ (hQ ℓ i) (Matrix.ext fun a k => ?_)
    have := hr ℓ a (i, Sum.inl k)
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      add_zero] at this
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this
  · -- the value columns of head `i`: `W_{V,i} Γ'_i = W_{V,i} Δ'_i`
    refine cancel_left_of_rank_ubr _ (hV ℓ i) (Matrix.ext fun a k => ?_)
    have := hr ℓ a (i, Sum.inr (Sum.inr k))
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      zero_add] at this
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this

omit [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper (the private `headDir_write_eq_zero_ubt`): if the value matrices of the heads of block
`ℓ` have rank `d_h` and the read of block `ℓ` of `headDirQK θ Γ + headDirVO θ Γ'` is `0`, its
write of block `ℓ` is `0`. -/
private theorem headDir_write_eq_zero_ubr
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ))
    (Γ Γ' : ∀ ℓ, H ℓ → Matrix (dh ℓ) (dh ℓ) ℝ) (ℓ : Fin L)
    (h0 : (headDirQK θ Γ + headDirVO θ Γ').read ℓ = 0) :
    (headDirQK θ Γ + headDirVO θ Γ').write ℓ = 0 := by
  -- `Γ'_{ℓ,i} = 0` for every head `i` of block `ℓ`
  have hΓ : ∀ i, Γ' ℓ i = 0 := fun i => by
    refine cancel_left_of_rank_ubr _ (hV ℓ i) (Matrix.ext fun a k => ?_)
    have := congrFun (congrFun h0 a) (i, Sum.inr (Sum.inr k))
    simp only [Params.add_read, Matrix.add_apply, headDirQK, headDirVO, Matrix.of_apply,
      zero_add, Matrix.zero_apply] at this
    rw [Matrix.mul_zero, Matrix.zero_apply]
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using this
  -- hence the write `−Γ'_{ℓ,i} W_{O,i}` is `0`
  ext p b
  simp [headDirQK, headDirVO, hΓ]

omit [DecidableEq d] in
/-- Helper (the private `attn_part_ubt`): the directions of the changes of basis inside the heads
span a space `V_A` of directions of symmetries inside the blocks, of dimension
`2 ∑_ℓ H_ℓ d_{h,ℓ}²` (Lemma B.1), in which a direction whose read of a block is `0` has the
write of that block `0`. -/
private theorem attn_part_ubr
    (θ : Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut)
    (hQ : ∀ ℓ (i : H ℓ), ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
      = Fintype.card (dh ℓ))
    (hV : ∀ ℓ (i : H ℓ),
      ((θ.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
        = Fintype.card (dh ℓ)) :
    ∃ V : Submodule ℝ (Params (Arch.attention (T := T) (d := d) sees χ H dh) dIn dOut),
      V ≤ Submodule.span ℝ {η | InsideBlocks (Arch.attention sees χ H dh) θ η} ∧
      (∀ η ∈ V, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0) ∧
      Module.finrank ℝ V = 2 * ∑ ℓ, Fintype.card (H ℓ) * Fintype.card (dh ℓ) ^ 2 := by
  refine ⟨LinearMap.range ((headDirQKLin_ubr θ).coprod (headDirVOLin_ubr θ)), ?_, ?_, ?_⟩
  · -- each of the two summands is a direction of a symmetry inside the blocks
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.coprod_apply]
    exact Submodule.add_mem _ (Submodule.subset_span (insideBlocks_headDirQK θ p.1))
      (Submodule.subset_span (insideBlocks_headDirVO θ p.2))
  · rintro _ ⟨p, rfl⟩ ℓ h0
    rw [LinearMap.coprod_apply] at h0 ⊢
    exact headDir_write_eq_zero_ubr θ hV p.1 p.2 ℓ h0
  · -- the map `(Γ, Γ') ↦ headDirQK θ Γ + headDirVO θ Γ'` is injective
    rw [LinearMap.finrank_range_of_inj (headDirLin_injective_ubr θ hQ hV), Module.finrank_prod,
      finrank_headFun_ubr, two_mul]

/-! ### Helpers: the rescalings of the hidden units of MLP blocks -/

/-- Helper (the private `rescaleDirMlpLin` of `Dimension/RescalingMlp.lean`):
`α ↦ rescaleDirMlp k θ α` is linear. -/
private noncomputable def rescaleDirMlpLin_ubr (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut where
  toFun := rescaleDirMlp k θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDirMlp]
    · intro ℓ
      ext a i
      simp only [rescaleDirMlp, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply]
      ring
    · intro ℓ
      ext i a
      simp only [rescaleDirMlp, Pi.add_apply, Params.add_write, Matrix.add_apply, Matrix.of_apply]
      ring
    · simp [rescaleDirMlp]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDirMlp]
    · intro ℓ
      ext a i
      simp only [rescaleDirMlp, Pi.smul_apply, Params.smul_read, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · intro ℓ
      ext i a
      simp only [rescaleDirMlp, Pi.smul_apply, Params.smul_write, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [rescaleDirMlp]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if no read column of block `ℓ` vanishes and the read of block `ℓ` of
`rescaleDirMlp k θ α` is `0`, then `α_{ℓ,i} = 0` for every hidden unit `i` of block `ℓ` (the
read column `i` of that direction is `α_{ℓ,i}` times the read column `i` of `θ`). -/
private theorem rescaleMlp_eq_zero_ubr {k : ℕ}
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) (α : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L)
    (h0 : (rescaleDirMlp k θ α).read ℓ = 0) (i : hid ℓ) : α ℓ i = 0 := by
  by_contra hα
  refine hc ℓ i (funext fun a => ?_)
  have := congrFun (congrFun h0 a) i
  simp only [rescaleDirMlp, Matrix.of_apply, Matrix.zero_apply] at this
  exact (mul_eq_zero.1 this).resolve_left hα

omit [Fintype T] [DecidableEq d] in
/-- Helper: the directions of the rescalings of the hidden units of MLP blocks with a positively
homogeneous activation span a space `V_B` of directions of symmetries inside the blocks, of
dimension `∑_ℓ d_hidden,ℓ`, in which a direction whose read of a block is `0` has the write of
that block `0`. -/
private theorem mlp_part_ubr {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    ∃ V : Submodule ℝ (Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut),
      V ≤ Submodule.span ℝ {η | InsideBlocks (Arch.mlp σ χ hid) θ η} ∧
      (∀ η ∈ V, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0) ∧
      Module.finrank ℝ V = ∑ ℓ, Fintype.card (hid ℓ) := by
  -- `α ↦ rescaleDirMlp k θ α` is injective, since its kernel is `0`
  have hinj : Function.Injective (rescaleDirMlpLin_ubr k θ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro α hα
    have hα' : rescaleDirMlp k θ α = 0 := hα
    funext ℓ i
    exact rescaleMlp_eq_zero_ubr θ hc α ℓ (by rw [hα']; rfl) i
  refine ⟨LinearMap.range (rescaleDirMlpLin_ubr k θ), ?_, ?_, ?_⟩
  · rintro _ ⟨α, rfl⟩
    exact Submodule.subset_span (insideBlocks_rescaleDirMlp hσ θ α)
  · -- read `0` gives `α_{ℓ,i} = 0`, so the write `−k α_{ℓ,i} · (row i)` is `0`
    rintro _ ⟨α, rfl⟩ ℓ h0
    have hα := rescaleMlp_eq_zero_ubr θ hc α ℓ h0
    ext i a
    show -((k : ℝ) * α ℓ i) * θ.write ℓ i a = 0
    rw [hα i, mul_zero, neg_zero, zero_mul]
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype]
    simp [Module.finrank_fintype_fun_eq_card]

/-! ### Helpers: the rescalings of the values and of the gates of gated blocks -/

/-- Helper (the private `rescaleDirLin_ubt`): `α ↦ rescaleDir θ α` is linear. -/
private noncomputable def rescaleDirLin_ubr
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  toFun := rescaleDir θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext k j
      cases j with
      | inl i => simp [rescaleDir]
      | inr i =>
        simp only [rescaleDir, Pi.add_apply, Params.add_read, Matrix.add_apply, Matrix.of_apply,
          Sum.elim_inr]
        ring
    · intro ℓ
      ext i k
      simp [rescaleDir, add_mul]
    · simp [rescaleDir]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDir]
    · intro ℓ
      ext k j
      cases j <;> simp [rescaleDir, mul_assoc]
    · intro ℓ
      ext i k
      simp [rescaleDir, mul_assoc]
    · simp [rescaleDir]

/-- Helper (the private `rescaleDirGateLin` of `Dimension/RescalingGate.lean`):
`β ↦ rescaleDirGate k θ β` is linear. -/
private noncomputable def rescaleDirGateLin_ubr (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) :
    (∀ ℓ, hid ℓ → ℝ) →ₗ[ℝ] Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  toFun := rescaleDirGate k θ
  map_add' α β := by
    apply Params.ext'
    · simp [rescaleDirGate]
    · intro ℓ
      ext a j
      cases j with
      | inl i =>
        simp only [rescaleDirGate, Pi.add_apply, Params.add_read, Matrix.add_apply,
          Matrix.of_apply, Sum.elim_inl]
        ring
      | inr i => simp [rescaleDirGate]
    · intro ℓ
      ext i a
      simp only [rescaleDirGate, Pi.add_apply, Params.add_write, Matrix.add_apply,
        Matrix.of_apply]
      ring
    · simp [rescaleDirGate]
  map_smul' c α := by
    apply Params.ext'
    · simp [rescaleDirGate]
    · intro ℓ
      ext a j
      cases j with
      | inl i =>
        simp only [rescaleDirGate, Pi.smul_apply, Params.smul_read, Matrix.smul_apply,
          Matrix.of_apply, Sum.elim_inl, smul_eq_mul, RingHom.id_apply]
        ring
      | inr i => simp [rescaleDirGate]
    · intro ℓ
      ext i a
      simp only [rescaleDirGate, Pi.smul_apply, Params.smul_write, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [rescaleDirGate]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: if no value column and no gate column of the read of block `ℓ` vanishes and the read
of block `ℓ` of `rescaleDir θ α + rescaleDirGate k θ β` is `0`, then `α_{ℓ,i} = 0` and
`β_{ℓ,i} = 0` for every hidden unit `i` of block `ℓ` (the value column `i` of that read is
`−α_{ℓ,i}` times the value column, its gate column `i` is `β_{ℓ,i}` times the gate column). -/
private theorem rescaleGate_eq_zero_ubr {k : ℕ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) (α β : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L)
    (h0 : (rescaleDir θ α + rescaleDirGate k θ β).read ℓ = 0) (i : hid ℓ) :
    α ℓ i = 0 ∧ β ℓ i = 0 := by
  constructor
  · -- the value column `i`: `−α_{ℓ,i} e_i = 0`
    by_contra hα
    refine hv ℓ i (funext fun a => ?_)
    have := congrFun (congrFun h0 a) (Sum.inr i)
    simp only [Params.add_read, Matrix.add_apply, rescaleDir, rescaleDirGate, Matrix.of_apply,
      Sum.elim_inr, add_zero, Matrix.zero_apply] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (neg_eq_zero.1 h) hα
    · exact h
  · -- the gate column `i`: `β_{ℓ,i} g_i = 0`
    by_contra hβ
    refine hg ℓ i (funext fun a => ?_)
    have := congrFun (congrFun h0 a) (Sum.inl i)
    simp only [Params.add_read, Matrix.add_apply, rescaleDir, rescaleDirGate, Matrix.of_apply,
      Sum.elim_inl, zero_add, Matrix.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hβ

omit [Fintype T] [DecidableEq d] in
/-- Helper: the directions of the rescalings of the values and of the gates of gated blocks with
a positively homogeneous gate span a space `V_B` of directions of symmetries inside the blocks,
of dimension `2 ∑_ℓ d_hidden,ℓ`, in which a direction whose read of a block is `0` has the write
of that block `0`. -/
private theorem gate_part_ubr {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    ∃ V : Submodule ℝ (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut),
      V ≤ Submodule.span ℝ {η | InsideBlocks (Arch.gated σ χ hid) θ η} ∧
      (∀ η ∈ V, ∀ ℓ, η.read ℓ = 0 → η.write ℓ = 0) ∧
      Module.finrank ℝ V = 2 * ∑ ℓ, Fintype.card (hid ℓ) := by
  -- the linear map `(α, β) ↦ rescaleDir θ α + rescaleDirGate k θ β`
  let Φ := (rescaleDirLin_ubr θ).coprod (rescaleDirGateLin_ubr k θ)
  -- it is injective, since its kernel is `0`
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    have hp' : rescaleDir θ p.1 + rescaleDirGate k θ p.2 = 0 := hp
    have h := fun ℓ i => rescaleGate_eq_zero_ubr θ hv hg p.1 p.2 ℓ (by rw [hp']; rfl) i
    exact Prod.ext (funext fun ℓ => funext fun i => (h ℓ i).1)
      (funext fun ℓ => funext fun i => (h ℓ i).2)
  refine ⟨LinearMap.range Φ, ?_, ?_, ?_⟩
  · -- each of the two summands is a direction of a symmetry inside the blocks
    rintro _ ⟨p, rfl⟩
    show rescaleDir θ p.1 + rescaleDirGate k θ p.2 ∈ _
    exact Submodule.add_mem _ (Submodule.subset_span (insideBlocks_rescaleDir θ p.1))
      (Submodule.subset_span (insideBlocks_rescaleDirGate hσ θ p.2))
  · -- read `0` gives `α_{ℓ,i} = β_{ℓ,i} = 0`, so the write `(α_{ℓ,i} − k β_{ℓ,i}) · (row i)` is `0`
    rintro _ ⟨p, rfl⟩ ℓ h0
    have h0' : (rescaleDir θ p.1 + rescaleDirGate k θ p.2).read ℓ = 0 := h0
    have h := rescaleGate_eq_zero_ubr θ hv hg p.1 p.2 ℓ h0'
    ext i a
    show p.1 ℓ i * θ.write ℓ i a + -((k : ℝ) * p.2 ℓ i) * θ.write ℓ i a = 0
    rw [(h i).1, (h i).2]
    ring
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_pi_fintype]
    simp only [Module.finrank_fintype_fun_eq_card]
    ring

/-! ### Helpers: generic parameters -/

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `analyticOnNhd_det_ubt`): the determinant of a square matrix that depends
linearly on the parameters is an analytic function of the parameters. -/
private theorem analyticOnNhd_det_ubr {A : Arch T d L} {n : Type*} [Fintype n] [DecidableEq n]
    (Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ) :
    AnalyticOnNhd ℝ (fun θ => (Φ θ).det) Set.univ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticOnNhd_fun_sum _ fun σ _ => analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun i _ =>
      analyticOnNhd_linear ((Matrix.entryLinearMap ℝ ℝ (σ i) i).comp Φ))

/-- Helper (the private `exists_submatrix_eq_one_ubt`): a matrix whose submatrix on the rows `r`
and the columns `c` (both injective) is the identity. -/
private theorem exists_submatrix_eq_one_ubr {m p n : Type*} [DecidableEq n] {r : n → m}
    (hr : Function.Injective r) {c : n → p} (hc : Function.Injective c) :
    ∃ M : Matrix m p ℝ, M.submatrix r c = 1 := by
  classical
  refine ⟨Matrix.of fun a b => if ∃ x, r x = a ∧ c x = b then 1 else 0, ?_⟩
  ext x y
  simp [Matrix.one_apply, hr.eq_iff, hc.eq_iff]

omit [Fintype T] [DecidableEq d] in
/-- Helper (the private `ae_rank_read_cols_ubt`): at generic parameters, `n ≤ d` distinct columns
`c` of the read of block `ℓ` form a matrix of rank `n`. -/
private theorem ae_rank_read_cols_ubr {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (ℓ : Fin L) {n : Type*} [Fintype n] [DecidableEq n] {c : n → A.r ℓ}
    (hc : Function.Injective c) (hn : Fintype.card n ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, ((θ.read ℓ).submatrix id c).rank = Fintype.card n := by
  -- `n` rows `ρ`, and the square submatrix of the read on the rows `ρ` and the columns `c`
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hn
  obtain ⟨M, hM⟩ := exists_submatrix_eq_one_ubr ρ.injective hc
  let Φ : Params A dIn dOut →ₗ[ℝ] Matrix n n ℝ :=
    { toFun := fun θ => ((θ.read ℓ).submatrix id c).submatrix ρ id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- it is the identity at the parameter whose read `ℓ` is `M`, so its determinant is not
  -- identically zero, and it is nonzero almost everywhere
  have hne : ∃ θ, (Φ θ).det ≠ 0 := by
    refine ⟨⟨0, Pi.single ℓ M, 0, 0⟩, ?_⟩
    show ((Pi.single (M := fun ℓ => Matrix d (A.r ℓ) ℝ) ℓ M ℓ).submatrix ρ c).det ≠ 0
    rw [Pi.single_eq_same, hM, Matrix.det_one]
    exact one_ne_zero
  filter_upwards [ae_ne_zero_of_analytic μ (analyticOnNhd_det_ubr Φ) hne] with θ hθ
  -- an invertible `n × n` submatrix gives rank `≥ n`, and the rank is at most the width `n`
  have h1 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank = Fintype.card n :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hθ))
  have h2 : (((θ.read ℓ).submatrix id c).submatrix ρ id).rank
      ≤ ((θ.read ℓ).submatrix id c).rank :=
    Matrix.rank_submatrix_le _ ρ id
  have h3 := Matrix.rank_le_card_width ((θ.read ℓ).submatrix id c)
  omega

omit [DecidableEq d] in
/-- Helper (the private `ae_rank_QV_ubt`): at generic parameters the query matrix and the value
matrix of every head of the first part of a sum have rank `d_h`, when `d_h ≤ d`. -/
private theorem ae_rank_QV_ubr {B : Arch T d L}
    (μ : Measure (Params ((Arch.attention (T := T) (d := d) sees χ H dh).sum B) dIn dOut))
    [μ.IsAddHaarMeasure] (hdh : ∀ ℓ, Fintype.card (dh ℓ) ≤ Fintype.card d) :
    ∀ᵐ θ ∂μ, (∀ ℓ (i : H ℓ), ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inl k)).rank
        = Fintype.card (dh ℓ)) ∧
      ∀ ℓ (i : H ℓ),
        ((θ.sumFst.read ℓ).submatrix id fun k : dh ℓ => (i, Sum.inr (Sum.inr k))).rank
          = Fintype.card (dh ℓ) := by
  classical
  -- finitely many conditions, two for each head of each block
  refine (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_).and
    (ae_all_iff.2 fun ℓ => ae_all_iff.2 fun i => ?_)
  · exact ae_rank_read_cols_ubr μ ℓ (c := fun k : dh ℓ => Sum.inl (i, Sum.inl k))
      (fun _ _ h => Sum.inl_injective (Prod.mk.inj (Sum.inl_injective h)).2) (hdh ℓ)
  · exact ae_rank_read_cols_ubr μ ℓ (c := fun k : dh ℓ => Sum.inl (i, Sum.inr (Sum.inr k)))
      (fun _ _ h => Sum.inr_injective (Sum.inr_injective (Prod.mk.inj (Sum.inl_injective h)).2))
      (hdh ℓ)

/-- Helper (the private `ae_rank_E_ubt`): at generic parameters `E` has rank `d`, when
`d_in ≥ d`. -/
private theorem ae_rank_E_ubr {A : Arch T d L} (μ : Measure (Params A dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d := by
  -- `d` rows `ρ` of `E`, invertible at generic parameters
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le hdIn
  filter_upwards [ae_isUnit_det_submatrix μ] with θ hθ
  have h1 : (θ.E.submatrix ρ id).rank = Fintype.card d :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (hθ.2.2.1 ρ))
  have h2 := Matrix.rank_submatrix_le θ.E ρ id
  have h3 := Matrix.rank_le_card_width θ.E
  omega

omit [Fintype T] [DecidableEq d] in
/-- Helper (`ae_read_col_ne_zero` of `Dimension/RescalingMlp.lean` and `ae_value_ne_zero_ubt`,
for every column of the second part of a sum): at generic parameters no column of the read of
the second part vanishes. -/
private theorem ae_sumSnd_col_ne_zero_ubr [Nonempty d] {A B : Arch T d L}
    (μ : Measure (Params (A.sum B) dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ ℓ (j : B.r ℓ), (fun a => θ.sumSnd.read ℓ a j) ≠ 0 := by
  -- finitely many conditions, one for each column `j` of each block `ℓ`
  refine ae_all_iff.2 fun ℓ => ae_all_iff.2 fun j => ?_
  -- an entry `a₀` of the column
  obtain a₀ : d := Classical.arbitrary d
  -- the entry `θ ↦ θ.read ℓ a₀ (inr j)` is a linear functional of the parameters
  let l : Params (A.sum B) dIn dOut →ₗ[ℝ] ℝ :=
    (Matrix.entryLinearMap ℝ ℝ a₀ (Sum.inr j : A.r ℓ ⊕ B.r ℓ)).comp
      (Params.linRead (A := A.sum B) (dIn := dIn) (dOut := dOut) ℓ)
  have hl : ∀ θ, l θ = θ.read ℓ a₀ (Sum.inr j) := fun θ => rfl
  -- it is not zero at the parameters whose reads have all entries `1`
  have h₁ : l ⟨0, fun _ => Matrix.of fun _ _ => 1, 0, 0⟩ ≠ 0 := by
    rw [hl]
    exact one_ne_zero
  -- an analytic function that is not identically zero is nonzero almost everywhere
  have hne : ∀ᵐ θ ∂μ, l θ ≠ 0 :=
    ae_ne_zero_of_analytic μ (analyticOnNhd_linear l) ⟨_, h₁⟩
  -- and a function with a nonzero entry is not zero
  filter_upwards [hne] with θ h hz
  exact h (by rw [hl]; exact congrFun hz a₀)

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
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the hidden units
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubr θ.sumFst hQ hV
  obtain ⟨VB, hVB, hrwB, hdimB⟩ := mlp_part_ubr hσ θ.sumSnd hc
  have h := funDim_add_le_skipless_sum_of_insideBlocks θ rfl VA VB hVA hVB hrwA hrwB hE hw
  rwa [hdimA, hdimB] at h

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
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the hidden units
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubr θ.sumFst hQ hV
  obtain ⟨VB, hVB, hrwB, hdimB⟩ := mlp_part_ubr hσ θ.sumSnd hc
  have h := funDim_add_le_skipless_sum_of_insideBlocks_rmsNorm θ ε rfl VA VB hVA hVB hrwA
    hrwB hE hw
  rwa [hdimA, hdimB] at h

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
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the hidden units
  obtain ⟨VA, hVA, -, hdimA⟩ := attn_part_ubr θ.sumFst hQ hV
  obtain ⟨VB, hVB, -, hdimB⟩ := mlp_part_ubr hσ θ.sumSnd hc
  have h := funDim_add_le_residual_sum_of_insideBlocks θ rfl VA VB hVA hVB hE
  rwa [hdimA, hdimB] at h

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
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the hidden units
  obtain ⟨VA, hVA, -, hdimA⟩ := attn_part_ubr θ.sumFst hQ hV
  obtain ⟨VB, hVB, -, hdimB⟩ := mlp_part_ubr hσ θ.sumSnd hc
  have h := funDim_add_le_residual_sum_of_insideBlocks_rmsNorm θ ε rfl VA VB hVA hVB hE
  rwa [hdimA, hdimB] at h

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
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionMlp (T := T) (d := d) sees σ id H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  -- the pointwise bound holds wherever the rank conditions of Lemma B.1 hold and no read
  -- column of a hidden unit vanishes
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3
  exact funDim_add_le_skipless_attentionMlp_rescale hσ θ h1.1 h1.2 h2.1 h2.2 h3

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
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionMlp (T := T) (d := d) sees σ (rmsNorm ε) H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  -- the pointwise bound holds wherever the rank conditions of Lemma B.1 hold and no read
  -- column of a hidden unit vanishes
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3
  exact funDim_add_le_skipless_attentionMlp_rescale_rmsNorm ε hσ θ h1.1 h1.2 h2.1 h2.2 h3

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
  -- the pointwise bound holds wherever the rank conditions of Lemma B.1 hold and no read
  -- column of a hidden unit vanishes
  filter_upwards [ae_rank_E_ubr μ hdIn, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3
  exact funDim_add_le_residual_attentionMlp_rescale hσ θ h1 h2.1 h2.2 h3

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
  -- the pointwise bound holds wherever the rank conditions of Lemma B.1 hold and no read
  -- column of a hidden unit vanishes
  filter_upwards [ae_rank_E_ubr μ hdIn, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3
  exact funDim_add_le_residual_attentionMlp_rescale_rmsNorm ε hσ θ h1 h2.1 h2.2 h3


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
  exact ae_funDim_add_le_skipless_attentionMlp_rescale relu_homogeneous μ hdIn hdh hW

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
  exact ae_funDim_add_le_skipless_attentionMlp_rescale_rmsNorm ε relu_homogeneous μ hdIn hdh hW

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
  exact ae_funDim_add_le_residual_attentionMlp_rescale relu_homogeneous μ hdIn hdh

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
  exact ae_funDim_add_le_residual_attentionMlp_rescale_rmsNorm ε relu_homogeneous μ hdIn hdh


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
  exact ae_funDim_add_le_skipless_attentionMlp_rescale reluSq_homogeneous μ hdIn hdh hW

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
  exact ae_funDim_add_le_skipless_attentionMlp_rescale_rmsNorm ε reluSq_homogeneous μ hdIn hdh hW

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
  exact ae_funDim_add_le_residual_attentionMlp_rescale reluSq_homogeneous μ hdIn hdh

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
  exact ae_funDim_add_le_residual_attentionMlp_rescale_rmsNorm ε reluSq_homogeneous μ hdIn hdh


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
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the values and gates
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubr θ.sumFst hQ hV
  obtain ⟨VB, hVB, hrwB, hdimB⟩ := gate_part_ubr hσ θ.sumSnd hv hg
  have h := funDim_add_le_skipless_sum_of_insideBlocks θ rfl VA VB hVA hVB hrwA hrwB hE hw
  rwa [hdimA, hdimB] at h

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
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the values and gates
  obtain ⟨VA, hVA, hrwA, hdimA⟩ := attn_part_ubr θ.sumFst hQ hV
  obtain ⟨VB, hVB, hrwB, hdimB⟩ := gate_part_ubr hσ θ.sumSnd hv hg
  have h := funDim_add_le_skipless_sum_of_insideBlocks_rmsNorm θ ε rfl VA VB hVA hVB hrwA
    hrwB hE hw
  rwa [hdimA, hdimB] at h

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
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the values and gates
  obtain ⟨VA, hVA, -, hdimA⟩ := attn_part_ubr θ.sumFst hQ hV
  obtain ⟨VB, hVB, -, hdimB⟩ := gate_part_ubr hσ θ.sumSnd hv hg
  have h := funDim_add_le_residual_sum_of_insideBlocks θ rfl VA VB hVA hVB hE
  rwa [hdimA, hdimB] at h

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
  -- `V_A`: the changes of basis inside the heads; `V_B`: the rescalings of the values and gates
  obtain ⟨VA, hVA, -, hdimA⟩ := attn_part_ubr θ.sumFst hQ hV
  obtain ⟨VB, hVB, -, hdimB⟩ := gate_part_ubr hσ θ.sumSnd hv hg
  have h := funDim_add_le_residual_sum_of_insideBlocks_rmsNorm θ ε rfl VA VB hVA hVB hE
  rwa [hdimA, hdimB] at h

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
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionGated (T := T) (d := d) sees σ id H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  -- the pointwise bound holds wherever the rank conditions of Lemma B.1 hold and no read
  -- column of a hidden unit vanishes
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3
  exact funDim_add_le_skipless_attentionGated_rescale hσ θ h1.1 h1.2 h2.1 h2.2
    (fun ℓ i => h3 ℓ (Sum.inr i)) (fun ℓ i => h3 ℓ (Sum.inl i))

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
  -- the write of block `ℓ` has `H_ℓ d_{h,ℓ} + d_hidden,ℓ ≥ d` rows
  have hw : ∀ ℓ, Fintype.card d ≤ Fintype.card
      ((Arch.attentionGated (T := T) (d := d) sees σ (rmsNorm ε) H dh hid).w ℓ) := fun ℓ => by
    show Fintype.card d ≤ Fintype.card ((H ℓ × dh ℓ) ⊕ hid ℓ)
    rw [Fintype.card_sum, Fintype.card_prod]
    exact hW ℓ
  -- the pointwise bound holds wherever the rank conditions of Lemma B.1 hold and no read
  -- column of a hidden unit vanishes
  filter_upwards [ae_rank_E_write μ hdIn hw, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3
  exact funDim_add_le_skipless_attentionGated_rescale_rmsNorm ε hσ θ h1.1 h1.2 h2.1 h2.2
    (fun ℓ i => h3 ℓ (Sum.inr i)) (fun ℓ i => h3 ℓ (Sum.inl i))

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
  -- the pointwise bound holds wherever the rank conditions of Lemma B.1 hold and no read
  -- column of a hidden unit vanishes
  filter_upwards [ae_rank_E_ubr μ hdIn, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3
  exact funDim_add_le_residual_attentionGated_rescale hσ θ h1 h2.1 h2.2
    (fun ℓ i => h3 ℓ (Sum.inr i)) (fun ℓ i => h3 ℓ (Sum.inl i))

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
  -- the pointwise bound holds wherever the rank conditions of Lemma B.1 hold and no read
  -- column of a hidden unit vanishes
  filter_upwards [ae_rank_E_ubr μ hdIn, ae_rank_QV_ubr μ hdh,
    ae_sumSnd_col_ne_zero_ubr μ] with θ h1 h2 h3
  exact funDim_add_le_residual_attentionGated_rescale_rmsNorm ε hσ θ h1 h2.1 h2.2
    (fun ℓ i => h3 ℓ (Sum.inr i)) (fun ℓ i => h3 ℓ (Sum.inl i))


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
  exact ae_funDim_add_le_skipless_attentionGated_rescale relu_homogeneous μ hdIn hdh hW

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
  exact ae_funDim_add_le_skipless_attentionGated_rescale_rmsNorm ε relu_homogeneous μ hdIn hdh hW

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
  exact ae_funDim_add_le_residual_attentionGated_rescale relu_homogeneous μ hdIn hdh

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
  exact ae_funDim_add_le_residual_attentionGated_rescale_rmsNorm ε relu_homogeneous μ hdIn hdh

end Skips
