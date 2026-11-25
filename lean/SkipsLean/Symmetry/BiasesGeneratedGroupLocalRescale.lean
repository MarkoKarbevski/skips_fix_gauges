import SkipsLean.Symmetry.BiasesGeneratedGroupSum
import SkipsLean.Symmetry.BiasesGeneratedGroupRescale

/-!
# The rescalings of hidden units act block by block

Paper (skips paper), Section 4.1: "the rescaling of a hidden unit of a ReLU or ReLU² block, the
rescaling of the value of a hidden unit of a gated block", and for ReGLU also of its gate
(Appendix A.6).

`Symmetry/BiasesGeneratedGroupSum.lean` asks of a family of symmetries inside the blocks, to be
used in a network with two kinds of block, that it acts block by block (`InsideBlocksLocal`): it
keeps `E`, `D`, the embedding bias and the readout bias, the map of every block and the span of
the rows of every write, and moves the reads, the writes and the read biases through these alone.
Here: the three families of rescalings of `Symmetry/BiasesGeneratedGroupRescale.lean` do.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise ENNReal

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

omit [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn] [Fintype dOut]
  [∀ ℓ, Fintype (hid ℓ)] in
/-- Helper: rows multiplied by nonzero numbers span the same space as the rows. -/
private theorem span_row_smul_blr {m n : Type*} (W : Matrix m n ℝ) (r : m → ℝ)
    (hr : ∀ i, r i ≠ 0) :
    Submodule.span ℝ (Set.range (Matrix.of fun i a => r i * W i a : Matrix m n ℝ).row)
      = Submodule.span ℝ (Set.range W.row) := by
  have hrow : ∀ i, (Matrix.of fun i a => r i * W i a : Matrix m n ℝ).row i = r i • W.row i :=
    fun i => rfl
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · -- a new row is a multiple of an old row
    rintro _ ⟨i, rfl⟩
    rw [hrow]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · -- an old row is a multiple of a new row
    rintro _ ⟨i, rfl⟩
    have h : W.row i = (r i)⁻¹ • (Matrix.of fun i a => r i * W i a : Matrix m n ℝ).row i := by
      rw [hrow, smul_smul, inv_mul_cancel₀ (hr i), one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: the pre-activations with biases of an MLP block after the rescaling: entry `(t, i)`
is multiplied by `c ℓ i`. -/
private theorem preact_rescaleMlp_blr {k : ℕ}
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (b : Biases (Arch.mlp (T := T) (d := d) σ χ hid) dOut) (c : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L)
    (h : Matrix T d ℝ) (t : T) (i : hid ℓ) :
    (h * (θ.rescaleMlp k c).read ℓ + Matrix.of fun _ => (b.rescaleMlp c).read ℓ :
        Matrix T (hid ℓ) ℝ) t i
      = c ℓ i * (h * θ.read ℓ + Matrix.of fun _ => b.read ℓ : Matrix T (hid ℓ) ℝ) t i := by
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.mul_apply, Params.rescaleMlp,
    Biases.rescaleMlp, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: after the rescaling of the values, the gates are unchanged. -/
private theorem gate_rescale_blr (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ χ hid) dOut) (c : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L)
    (h : Matrix T d ℝ) (t : T) (i : hid ℓ) :
    (h * (θ.rescale c).read ℓ + Matrix.of fun _ => (b.rescale c).read ℓ :
        Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t (Sum.inl i)
      = (h * θ.read ℓ + Matrix.of fun _ => b.read ℓ : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t
        (Sum.inl i) := by
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.mul_apply, Params.rescale,
    Biases.rescale, Sum.elim_inl]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: after the rescaling of the values, the value of unit `i` is multiplied by
`(c ℓ i)⁻¹`. -/
private theorem value_rescale_blr (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ χ hid) dOut) (c : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L)
    (h : Matrix T d ℝ) (t : T) (i : hid ℓ) :
    (h * (θ.rescale c).read ℓ + Matrix.of fun _ => (b.rescale c).read ℓ :
        Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t (Sum.inr i)
      = (c ℓ i)⁻¹ * (h * θ.read ℓ + Matrix.of fun _ => b.read ℓ : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t
        (Sum.inr i) := by
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.mul_apply, Params.rescale,
    Biases.rescale, Sum.elim_inr, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: after the rescaling of the gates, the gate of unit `i` is multiplied by `c ℓ i`. -/
private theorem gate_rescaleGate_blr {k : ℕ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ χ hid) dOut) (c : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L)
    (h : Matrix T d ℝ) (t : T) (i : hid ℓ) :
    (h * (θ.rescaleGate k c).read ℓ + Matrix.of fun _ => (b.rescaleGate c).read ℓ :
        Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t (Sum.inl i)
      = c ℓ i * (h * θ.read ℓ + Matrix.of fun _ => b.read ℓ : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t
        (Sum.inl i) := by
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.mul_apply, Params.rescaleGate,
    Biases.rescaleGate, Sum.elim_inl, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- Helper: after the rescaling of the gates, the values are unchanged. -/
private theorem value_rescaleGate_blr {k : ℕ}
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (b : Biases (Arch.gated (T := T) (d := d) σ χ hid) dOut) (c : ∀ ℓ, hid ℓ → ℝ) (ℓ : Fin L)
    (h : Matrix T d ℝ) (t : T) (i : hid ℓ) :
    (h * (θ.rescaleGate k c).read ℓ + Matrix.of fun _ => (b.rescaleGate c).read ℓ :
        Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t (Sum.inr i)
      = (h * θ.read ℓ + Matrix.of fun _ => b.read ℓ : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t
        (Sum.inr i) := by
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.mul_apply, Params.rescaleGate,
    Biases.rescaleGate, Sum.elim_inr]

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- **The rescalings of the hidden units of MLP blocks act block by block,** for an activation
that is positively homogeneous of degree `k`. -/
theorem insideBlocksLocal_rescaleMlp {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) :
    InsideBlocksLocal (A := Arch.mlp (T := T) (d := d) σ χ hid) (dIn := dIn) (dOut := dOut)
      (rescaleMlpAct k) (posRescalings hid) := by
  refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · -- the map of a block: unit `i` contributes `σ(c_i z_i) a_i / c_i^k = σ(z_i) a_i`
    intro c hc q ℓ n
    have hb : (rescaleMlpAct k c q).2.write ℓ = q.2.write ℓ := rfl
    rw [hb]
    congr 1
    ext t a
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show σ ((n * (q.1.rescaleMlp k c).read ℓ + Matrix.of fun _ => (q.2.rescaleMlp c).read ℓ :
            Matrix T (hid ℓ) ℝ) t i) * (q.1.rescaleMlp k c).write ℓ i a
      = σ ((n * q.1.read ℓ + Matrix.of fun _ => q.2.read ℓ : Matrix T (hid ℓ) ℝ) t i)
        * q.1.write ℓ i a
    have hk : c ℓ i ^ k ≠ 0 := pow_ne_zero k (hc ℓ i).ne'
    rw [preact_rescaleMlp_blr, hσ _ _ (hc ℓ i)]
    simp only [Params.rescaleMlp, Matrix.of_apply]
    field_simp
  · -- the reads, the writes and the read biases move through themselves; write biases stay
    intro c _ q q' hr hw hb
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext ℓ
      ext a i
      simp only [rescaleMlpAct, Params.rescaleMlp, Matrix.of_apply, hr]
    · funext ℓ
      ext i a
      simp only [rescaleMlpAct, Params.rescaleMlp, Matrix.of_apply, hw]
    · funext ℓ i
      simp only [rescaleMlpAct, Biases.rescaleMlp, hb]
    · show q.2.write - q.2.write = q'.2.write - q'.2.write
      rw [sub_self, sub_self]
  · -- every row of the write is multiplied by `c^{-k} ≠ 0`
    intro c hc q ℓ
    exact span_row_smul_blr (q.1.write ℓ) (fun i => (c ℓ i ^ k)⁻¹)
      fun i => inv_ne_zero (pow_ne_zero k (hc ℓ i).ne')

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- **The rescalings of the values of gated units act block by block,** for any gate. -/
theorem insideBlocksLocal_rescale :
    InsideBlocksLocal (A := Arch.gated (T := T) (d := d) σ χ hid) (dIn := dIn) (dOut := dOut)
      rescaleAct (posRescalings hid) := by
  refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · -- the map of a block: unit `i` contributes `σ(g_i) (v_i / c_i) (c_i a_i) = σ(g_i) v_i a_i`
    intro c hc q ℓ n
    have hb : (rescaleAct c q).2.write ℓ = q.2.write ℓ := rfl
    rw [hb]
    congr 1
    ext t a
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show σ ((n * (q.1.rescale c).read ℓ + Matrix.of fun _ => (q.2.rescale c).read ℓ :
            Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t (Sum.inl i))
        * (n * (q.1.rescale c).read ℓ + Matrix.of fun _ => (q.2.rescale c).read ℓ :
            Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t (Sum.inr i)
        * (q.1.rescale c).write ℓ i a
      = σ ((n * q.1.read ℓ + Matrix.of fun _ => q.2.read ℓ : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t
            (Sum.inl i))
        * (n * q.1.read ℓ + Matrix.of fun _ => q.2.read ℓ : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t
            (Sum.inr i)
        * q.1.write ℓ i a
    have hc0 : c ℓ i ≠ 0 := (hc ℓ i).ne'
    rw [gate_rescale_blr, value_rescale_blr]
    simp only [Params.rescale, Matrix.of_apply]
    field_simp
  · -- the reads, the writes and the read biases move through themselves; write biases stay
    intro c _ q q' hr hw hb
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext ℓ
      ext a j
      simp only [rescaleAct, Params.rescale, Matrix.of_apply, hr]
    · funext ℓ
      ext i a
      simp only [rescaleAct, Params.rescale, Matrix.of_apply, hw]
    · funext ℓ j
      simp only [rescaleAct, Biases.rescale, hb]
    · show q.2.write - q.2.write = q'.2.write - q'.2.write
      rw [sub_self, sub_self]
  · -- every row of the write is multiplied by `c ≠ 0`
    intro c hc q ℓ
    exact span_row_smul_blr (q.1.write ℓ) (fun i => c ℓ i) fun i => (hc ℓ i).ne'

omit [Fintype T] [DecidableEq d] [Fintype dIn] [Fintype dOut] in
/-- **The rescalings of the values and of the gates act block by block,** for a gate that is
positively homogeneous of degree `k`. -/
theorem insideBlocksLocal_rescaleBoth {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) :
    InsideBlocksLocal (A := Arch.gated (T := T) (d := d) σ χ hid) (dIn := dIn) (dOut := dOut)
      (rescaleBothAct k) (posRescalings hid ×ˢ posRescalings hid) := by
  refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · -- the map of a block: unit `i` contributes
    -- `σ(c₂ g_i) (v_i / c₁) (c₁ a_i / c₂^k) = σ(g_i) v_i a_i`
    intro c hc q ℓ n
    have hb : (rescaleBothAct k c q).2.write ℓ = q.2.write ℓ := rfl
    rw [hb]
    congr 1
    ext t a
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show σ ((n * ((q.1.rescale c.1).rescaleGate k c.2).read ℓ
            + Matrix.of fun _ => ((q.2.rescale c.1).rescaleGate c.2).read ℓ :
            Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t (Sum.inl i))
        * (n * ((q.1.rescale c.1).rescaleGate k c.2).read ℓ
            + Matrix.of fun _ => ((q.2.rescale c.1).rescaleGate c.2).read ℓ :
            Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t (Sum.inr i)
        * ((q.1.rescale c.1).rescaleGate k c.2).write ℓ i a
      = σ ((n * q.1.read ℓ + Matrix.of fun _ => q.2.read ℓ : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t
            (Sum.inl i))
        * (n * q.1.read ℓ + Matrix.of fun _ => q.2.read ℓ : Matrix T (hid ℓ ⊕ hid ℓ) ℝ) t
            (Sum.inr i)
        * q.1.write ℓ i a
    have hc1 : c.1 ℓ i ≠ 0 := (hc.1 ℓ i).ne'
    have hk : c.2 ℓ i ^ k ≠ 0 := pow_ne_zero k (hc.2 ℓ i).ne'
    rw [gate_rescaleGate_blr, value_rescaleGate_blr, gate_rescale_blr, value_rescale_blr,
      hσ _ _ (hc.2 ℓ i)]
    simp only [Params.rescale, Params.rescaleGate, Matrix.of_apply]
    field_simp
  · -- the reads, the writes and the read biases move through themselves; write biases stay
    intro c _ q q' hr hw hb
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext ℓ
      ext a j
      simp only [rescaleBothAct, Params.rescale, Params.rescaleGate, Matrix.of_apply, hr]
    · funext ℓ
      ext i a
      simp only [rescaleBothAct, Params.rescale, Params.rescaleGate, Matrix.of_apply, hw]
    · funext ℓ j
      simp only [rescaleBothAct, Biases.rescale, Biases.rescaleGate, hb]
    · show q.2.write - q.2.write = q'.2.write - q'.2.write
      rw [sub_self, sub_self]
  · -- every row of the write is multiplied by `c₁ / c₂^k ≠ 0`
    intro c hc q ℓ
    have hw : (rescaleBothAct k c q).1.write ℓ
        = Matrix.of fun i a => ((c.2 ℓ i ^ k)⁻¹ * c.1 ℓ i) * q.1.write ℓ i a := by
      ext i a
      simp only [rescaleBothAct, Params.rescale, Params.rescaleGate, Matrix.of_apply, mul_assoc]
    rw [hw]
    exact span_row_smul_blr (q.1.write ℓ) (fun i => (c.2 ℓ i ^ k)⁻¹ * c.1 ℓ i)
      fun i => mul_ne_zero (inv_ne_zero (pow_ne_zero k (hc.2 ℓ i).ne')) (hc.1 ℓ i).ne'

end Skips
