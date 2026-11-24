import SkipsLean.Dimension.RescalingGate

/-!
# The upper bound with identity skips, with the symmetries inside the blocks

Paper (skips): Theorem 4.2. "Let `𝒢` be the group of changes of basis of one hidden state, and `s`
the dimension of the symmetries inside the blocks, the same with and without skips. With or
without pre-RMSNorm, at generic parameters, the functional dimension is at most
`P - (L+1) dim 𝒢 - s` without skips and at most `P - dim 𝒢 - s` with identity skips."

The bound without skips is Theorem 4.3 of the dimension paper (`Dimension/`, `Generic/`). This
file has the bound with identity skips (the stream matrices `1`), with the term `s`:

* for arbitrary maps `f_ℓ`, the bound from the one change of basis, `fd ≤ P - dim 𝒢`, with no
  hypothesis of differentiability;
* gated blocks with any gate (SwiGLU, GeGLU): `s` is the number of hidden units (the rescalings of
  the values);
* MLP blocks with a positively homogeneous activation (ReLU, ReLU²): `s` is the number of hidden
  units (the rescalings of the units);
* gated blocks with a positively homogeneous gate (ReGLU): `s` is twice the number of hidden
  units.

`dim 𝒢` is `d²` without normalization and `d (d - 1) / 2` under pre-RMSNorm, where the statements
hold for every real `ε`. With identity skips only `E` needs rank `d` (`d_in ≥ d`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

section General

variable {A : Arch T d L} (θ : Params A dIn dOut)

/-- With identity skips and without normalization, the direction of one change of basis `X` at
all hidden states is flat, for arbitrary maps `f_ℓ`. -/
theorem cobDir_const_mem_flat_residual' (hA : A.χ = id) (X : Matrix d d ℝ) :
    cobDir θ (fun _ => X) ∈ flat A 1 θ := by
  sorry

/-- With identity skips and under pre-RMSNorm, the direction of one antisymmetric `X` at all
hidden states is flat, for arbitrary maps `f_ℓ` and every real `ε`. -/
theorem cobDir_const_mem_flat_residual_rmsNorm' (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (X : Matrix d d ℝ) (hX : Xᵀ = -X) :
    cobDir θ (fun _ => X) ∈ flat A 1 θ := by
  sorry

/-- **Theorem 4.2 with identity skips, without normalization, for the change of basis, for
arbitrary maps `f_ℓ`:** if `E` has rank `d`, then `fd ≤ P - d²`. -/
theorem funDim_add_le_residual' (hA : A.χ = id) (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + Fintype.card d ^ 2 ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

/-- **Theorem 4.2 with identity skips, under pre-RMSNorm, for the change of basis, for arbitrary
maps `f_ℓ`:** if `E` has rank `d`, then `fd ≤ P - d (d - 1) / 2`. -/
theorem funDim_add_le_residual_rmsNorm' (ε : ℝ) (hA : A.χ = rmsNorm ε)
    (hE : θ.E.rank = Fintype.card d) :
    funDim A 1 θ + Fintype.card d * (Fintype.card d - 1) / 2
      ≤ Module.finrank ℝ (Params A dIn dOut) := by
  sorry

end General

variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-! ### Gated blocks with any gate: the rescalings of the values -/

/-- **Theorem 4.2 with identity skips for gated blocks, without normalization,** under the
conditions of the proof (`E` of rank `d`, no value column of a read zero):
`fd ≤ P - d² - s`, where `s` is the number of hidden units. -/
theorem funDim_add_le_residual_gated
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0) :
    funDim (Arch.gated σ id hid) 1 θ + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 with identity skips for gated blocks, under pre-RMSNorm:**
`fd ≤ P - d (d - 1) / 2 - s`. -/
theorem funDim_add_le_residual_gated_rmsNorm (ε : ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- Theorem 4.2 with identity skips for gated blocks at generic parameters (`d_in ≥ d`), without
normalization. -/
theorem ae_funDim_add_le_residual_gated [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- Theorem 4.2 with identity skips for gated blocks at generic parameters (`d_in ≥ d`), under
pre-RMSNorm. -/
theorem ae_funDim_add_le_residual_gated_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-! ### MLP blocks with a positively homogeneous activation (ReLU, ReLU²) -/

/-- **Theorem 4.2 with identity skips for blocks with a positively homogeneous activation,
without normalization,** under the conditions of the proof (`E` of rank `d`, no column of a read
zero): `fd ≤ P - d² - s`, where `s` is the number of hidden units. -/
theorem funDim_add_le_residual_mlp_rescale {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ id hid) 1 θ + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 with identity skips for blocks with a positively homogeneous activation, under
pre-RMSNorm:** `fd ≤ P - d (d - 1) / 2 - s`. -/
theorem funDim_add_le_residual_mlp_rescale_rmsNorm {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (ε : ℝ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- Theorem 4.2 with identity skips for blocks with a positively homogeneous activation at generic
parameters (`d_in ≥ d`), without normalization. -/
theorem ae_funDim_add_le_residual_mlp_rescale [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ id hid) 1 θ
        + (Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- Theorem 4.2 with identity skips for blocks with a positively homogeneous activation at generic
parameters (`d_in ≥ d`), under pre-RMSNorm. -/
theorem ae_funDim_add_le_residual_mlp_rescale_rmsNorm [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (ε : ℝ)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-! ### Gated blocks with a positively homogeneous gate (ReGLU) -/

/-- **Theorem 4.2 with identity skips for gated blocks with a positively homogeneous gate, without
normalization,** under the conditions of the proof (`E` of rank `d`, no gate column and no value
column of a read zero): `fd ≤ P - d² - s`, where `s` is twice the number of hidden units. -/
theorem funDim_add_le_residual_gated_gate {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.gated σ id hid) 1 θ + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.2 with identity skips for gated blocks with a positively homogeneous gate, under
pre-RMSNorm:** `fd ≤ P - d (d - 1) / 2 - s`. -/
theorem funDim_add_le_residual_gated_gate_rmsNorm {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (ε : ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- Theorem 4.2 with identity skips for gated blocks with a positively homogeneous gate at generic
parameters (`d_in ≥ d`), without normalization. -/
theorem ae_funDim_add_le_residual_gated_gate [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ id hid) 1 θ
        + (Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- Theorem 4.2 with identity skips for gated blocks with a positively homogeneous gate at generic
parameters (`d_in ≥ d`), under pre-RMSNorm. -/
theorem ae_funDim_add_le_residual_gated_gate_rmsNorm [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (ε : ℝ)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm ε) hid) 1 θ
        + (Fintype.card d * (Fintype.card d - 1) / 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

end Skips
