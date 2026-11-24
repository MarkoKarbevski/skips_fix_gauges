import SkipsLean.Dimension.UpperBoundResidualRMSNormZero

/-!
# Residual networks under pre-RMSNorm with `ε = 0`, ReLU, ReLU² and ReGLU blocks: the upper bound

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`".

Its proof, "The residual network": "a flat direction is the sum of a direction of the rotation
and scaling of all hidden states and a direction `ψ` of the weights of the block along which `B`
has derivative zero on the sphere of radius `√d_model`. […] makes `ψ` a rescaling of the units.
So `dim K(θ) = d_model (d_model − 1)/2 + 1 + s`."

Here: the half "at most" of this value, at any depth. For a residual network of MLP blocks with a
positively homogeneous activation (ReLU, ReLU²: `s` is the number of hidden units) or of gated
blocks with a positively homogeneous gate (ReGLU: `s` is twice the number of hidden units) under
pre-RMSNorm with `ε = 0`, the directions of the rotation of all hidden states, of their scaling,
and of the rescalings of the hidden units are flat and independent, so the functional dimension is
at most `P − (d(d−1)/2 + 1) − s`: at one parameter under the conditions of the proof (`E` of rank
`d ≥ 1`, no column of a read zero), and at almost every parameter for `d_in ≥ d`. No width of the
blocks is asked. The twin for `ε > 0` is `Residual/UpperBoundSymmetries.lean`; without the
rescalings, `Dimension/UpperBoundResidualRMSNormZero.lean`.

The functional dimension is Lean's `funDim`, over all inputs, with the derivative in the weights
taken to be `0` where the output is not differentiable, and with Lean's `rmsNorm 0`, which maps a
zero row to `0`. It is at least the paper's, which uses fewer inputs, so the bound holds for the
paper's. Not stated here: the half "at least".
-/

namespace Skips

open Matrix MeasureTheory

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Theorem B.1 (iv) of the skips paper, the residual network, the half "at most", under the
conditions of the proof:** for a residual network of MLP blocks with `σ(λ z) = λ^k σ(z)` for
`λ > 0` under pre-RMSNorm with `ε = 0`, if `E` has rank `d ≥ 1` and no column of a read is zero,
the functional dimension is at most `P − (d(d−1)/2 + 1) − s`, `s` the number of hidden units. -/
theorem funDim_add_le_residual_mlp_rescale_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- The bound of `funDim_add_le_residual_mlp_rescale_rmsNorm_zero` at almost every parameter, for
`d_in ≥ d ≥ 1`. -/
theorem ae_funDim_add_le_residual_mlp_rescale_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp σ (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the residual network, the half "at most", for ReLU
blocks at generic parameters:** under pre-RMSNorm with `ε = 0`, with `d_in ≥ d ≥ 1`, the
functional dimension is at most `P − d(d−1)/2 − 1 − s`. -/
theorem ae_funDim_add_le_residual_relu_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the residual network, the half "at most", for ReLU²
blocks at generic parameters.** -/
theorem ae_funDim_add_le_residual_reluSq_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the residual network, the half "at most", for gated
blocks under the conditions of the proof:** for a residual network of gated blocks whose gate has
`σ(λ z) = λ^k σ(z)` for `λ > 0`, under pre-RMSNorm with `ε = 0`, if `E` has rank `d ≥ 1` and no
value column and no gate column of a read is zero, the functional dimension is at most
`P − (d(d−1)/2 + 1) − s`, `s` twice the number of hidden units. -/
theorem funDim_add_le_residual_gated_gate_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- The bound of `funDim_add_le_residual_gated_gate_rmsNorm_zero` at almost every parameter, for
`d_in ≥ d ≥ 1`. -/
theorem ae_funDim_add_le_residual_gated_gate_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated σ (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the residual network, the half "at most", for ReGLU
blocks at generic parameters:** under pre-RMSNorm with `ε = 0`, with `d_in ≥ d ≥ 1`, the
functional dimension is at most `P − d(d−1)/2 − 1 − s`, `s = 2 d_hidden`. -/
theorem ae_funDim_add_le_residual_reglu_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm 0) hid) 1 θ
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 1) + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  sorry

end Skips
