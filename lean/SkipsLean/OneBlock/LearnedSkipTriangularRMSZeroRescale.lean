import SkipsLean.OneBlock.LearnedSkipTriangularRMSZeroRank
import SkipsLean.OneBlock.TurnsActiveRowsSkipLinear

/-!
# One ReLU, ReLU² or ReGLU block with an upper triangular learned skip under pre-RMSNorm with
`ε = 0`: the equality

Paper (skips paper), Theorem B.1 (iii): "Let the network be pre-RMSNorm without biases, with a
learned skip `A`, full or upper triangular. […] For `ε = 0` it exceeds that of the residual
network with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU, ReLU² and
ReGLU blocks." Its proof: "For an upper triangular `A`, view the network as the network with a
full `A` restricted to triangular skips: its flat directions are those of the full network whose
entry `η_A` is upper triangular." And in "The case `ε = 0`": "which gives at least
`d_model (d_model − 1) + 2`, respectively `d_model (d_model − 1)/2 + 2`, dimensions besides
`K_B`".

The twin for `ε = 0` of `OneBlock/LearnedSkipTriangularRescale.lean`. As there, the statements
are in the paper's own sense: `funDimSkipsOn` on the inputs at which no normalized row vanishes
and no hidden unit (no gate) sits at its kink. On a batch of such inputs the family of upper
triangular skips and the family of all skips have the same Jacobian rank
(`jacobianRankSkips_tri_eq_learned_rmsNorm_zero`, `OneBlock/LearnedSkipTriangularRMSZeroRank.lean`),
so the values for the full skip (`OneBlock/LearnedSkipRMSZeroRescale.lean`,
`OneBlock/LearnedSkipRMSZeroReGLU.lean`) carry over:
`P + d² − (d(d−1) + 2) − s = P + d(d+1)/2 − (d(d−1)/2 + 2) − s`, with `s = d_hidden` for ReLU and
ReLU² and `s = 2 d_hidden` for ReGLU. Here:

* at one parameter, under the conditions of the statements for the full skip and for an
  invertible upper triangular skip: a batch of the paper's inputs with this rank; no batch of
  such inputs has a larger rank; the value of `funDimSkipsOn`;
* for `d_in, d_out ≥ d ≥ 2`, at almost every `(θ, A)` with `A` upper triangular: the value, and
  the equality with the residual network with the weights `θ`,
  `funDimSkipsOn = funDim + d(d+1)/2 − 1` (the residual network is measured by Lean's `funDim`,
  which at almost every `θ` is also the largest rank over the batches of the paper's inputs).

The condition that the paper does not state (`TurnsActiveRowsSkip`, `TurnsActiveRowsGatedSkip`
for the skip `A`) holds at almost every `(θ, A)` with `A` upper triangular
(`OneBlock/TurnsActiveRowsSkipLinear.lean`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d]
  [LinearOrder d] [Fintype dIn] [Fintype dOut]
variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-! ### MLP blocks with a positively homogeneous activation, at one parameter -/

/-- **Theorem B.1 (iii) for `ε = 0` and the upper triangular skip, in the paper's own sense, for
one MLP block with a positively homogeneous activation, at one parameter:** under the conditions
of the statement for the full skip, for an invertible upper triangular skip, a finite batch of
inputs at which no normalized row vanishes and no hidden unit sits at its kink, on which the
Jacobian in the weights and the triangular skip has the rank
`P + d(d+1)/2 − (d(d−1)/2 + 2) − s`. -/
theorem exists_jacobianRankSkips_tri_mlp_rescale_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescaleSphere σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    (hturn : TurnsActiveRowsSkip θ (R 0 : Matrix d d ℝ))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧ LinearIndependent ℝ
      ![v ᵥ* (R 0 : Matrix d d ℝ), vanillaBlock σ (θ.read 0) (θ.write 0) v]) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ
        (fun ℓ => (R ℓ : Matrix d d ℝ)) ∩ noKinkRMS θ) ∧
      jacobianRankSkips (Arch.mlp σ (rmsNorm 0) hid) (triSkips d 1) X (θ, R)
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
          + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **No batch of the paper's inputs has a larger rank,** for one MLP block with a positively
homogeneous activation and an upper triangular learned skip, `ε = 0`, at one parameter. -/
theorem jacobianRankSkips_tri_add_le_mlp_rescale_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescaleSphere σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    (hturn : TurnsActiveRowsSkip θ (R 0 : Matrix d d ℝ))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧ LinearIndependent ℝ
      ![v ᵥ* (R 0 : Matrix d d ℝ), vanillaBlock σ (θ.read 0) (θ.write 0) v])
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i, X i ∈ learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ
      (fun ℓ => (R ℓ : Matrix d d ℝ)) ∩ noKinkRMS θ) :
    jacobianRankSkips (Arch.mlp σ (rmsNorm 0) hid) (triSkips d 1) X (θ, R)
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + Fintype.card (hid 0))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) for `ε = 0` and the upper triangular skip, for one MLP block with a
positively homogeneous activation, at one parameter:** the functional dimension on the inputs at
which no normalized row vanishes and no hidden unit sits at its kink is
`P + d(d+1)/2 − (d(d−1)/2 + 2) − s`. -/
theorem funDimSkipsOn_tri_mlp_rescale_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (hU : UnitsRescaleSphere σ σ' k d d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericRMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    (hturn : TurnsActiveRowsSkip θ (R 0 : Matrix d d ℝ))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) i ≠ 0) ∧ LinearIndependent ℝ
      ![v ᵥ* (R 0 : Matrix d d ℝ), vanillaBlock σ (θ.read 0) (θ.write 0) v]) :
    funDimSkipsOn (Arch.mlp σ (rmsNorm 0) hid) (triSkips d 1) (θ, R)
        (learnedZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ (fun ℓ => (R ℓ : Matrix d d ℝ))
          ∩ noKinkRMS θ)
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-! ### ReLU and ReLU² blocks, at almost every weights and upper triangular skip -/

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", for one ReLU block with
a hidden unit and an upper triangular learned skip:** for `d_in, d_out ≥ d ≥ 2`, at almost every
`(θ, A)`, `A` upper triangular, the functional dimension on the inputs at which no normalized row
vanishes and no hidden unit sits at its kink is `P + d(d+1)/2 − (d(d−1)/2 + 2) − d_hidden`. -/
theorem ae_funDimSkipsOn_tri_relu_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp relu (rmsNorm 0) hid) (triSkips d 1) p
        (learnedZeroDomain (Arch.mlp relu (rmsNorm 0) hid) p.1
          (fun ℓ => (p.2 ℓ : Matrix d d ℝ)) ∩ noKinkRMS p.1)
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper, "For `ε = 0` it exceeds that of the residual network
with `ε = 0` by at most `d_model (d_model + 1)/2 − 1`, with equality for ReLU […] blocks", for
one ReLU block with a hidden unit and an upper triangular learned skip:** at almost every
`(θ, A)`, `A` upper triangular, the functional dimension on the paper's inputs exceeds that of
the residual network with the weights `θ` by exactly `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_tri_relu_rmsNorm_zero_eq_residual_add [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp relu (rmsNorm 0) hid) (triSkips d 1) p
        (learnedZeroDomain (Arch.mlp relu (rmsNorm 0) hid) p.1
          (fun ℓ => (p.2 ℓ : Matrix d d ℝ)) ∩ noKinkRMS p.1)
      = funDim (Arch.mlp relu (rmsNorm 0) hid) 1 p.1
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", for one ReLU² block with
a hidden unit and an upper triangular learned skip:** for `d_in, d_out ≥ d ≥ 2`, at almost every
`(θ, A)`, `A` upper triangular, the functional dimension on the inputs at which no normalized row
vanishes and no hidden unit sits at its kink is `P + d(d+1)/2 − (d(d−1)/2 + 2) − d_hidden`. -/
theorem ae_funDimSkipsOn_tri_reluSq_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp reluSq (rmsNorm 0) hid) (triSkips d 1) p
        (learnedZeroDomain (Arch.mlp reluSq (rmsNorm 0) hid) p.1
          (fun ℓ => (p.2 ℓ : Matrix d d ℝ)) ∩ noKinkRMS p.1)
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper, "with equality for […] ReLU² […] blocks", for one
ReLU² block with a hidden unit and an upper triangular learned skip, `ε = 0`:** at almost every
`(θ, A)`, `A` upper triangular, the functional dimension on the paper's inputs exceeds that of
the residual network with the weights `θ` by exactly `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_tri_reluSq_rmsNorm_zero_eq_residual_add [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.mlp reluSq (rmsNorm 0) hid) (triSkips d 1) p
        (learnedZeroDomain (Arch.mlp reluSq (rmsNorm 0) hid) p.1
          (fun ℓ => (p.2 ℓ : Matrix d d ℝ)) ∩ noKinkRMS p.1)
      = funDim (Arch.mlp reluSq (rmsNorm 0) hid) 1 p.1
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  sorry

/-! ### ReGLU blocks -/

/-- **Theorem B.1 (iii) for `ε = 0` and the upper triangular skip, in the paper's own sense, for
one ReGLU block, at one parameter:** under the conditions of the statement for the full skip, for
an invertible upper triangular skip, a finite batch of inputs at which no normalized row vanishes
and no gate sits at its kink, on which the Jacobian in the weights and the triangular skip has
the rank `P + d(d+1)/2 − (d(d−1)/2 + 2) − 2 d_hidden`. -/
theorem exists_jacobianRankSkips_tri_reglu_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    (hturn : TurnsActiveRowsGatedSkip θ (R 0 : Matrix d d ℝ))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧ LinearIndependent ℝ
      ![v ᵥ* (R 0 : Matrix d d ℝ), gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v]) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ
        (fun ℓ => (R ℓ : Matrix d d ℝ)) ∩ noKinkGateRMS θ) ∧
      jacobianRankSkips (Arch.gated relu (rmsNorm 0) hid) (triSkips d 1) X (θ, R)
          + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + 2 * Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
          + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **No batch of the paper's inputs has a larger rank,** for one ReGLU block with an upper
triangular learned skip, `ε = 0`, at one parameter. -/
theorem jacobianRankSkips_tri_add_le_reglu_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    (hturn : TurnsActiveRowsGatedSkip θ (R 0 : Matrix d d ℝ))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧ LinearIndependent ℝ
      ![v ᵥ* (R 0 : Matrix d d ℝ), gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v])
    {n : ℕ} (X : Fin n → Matrix T dIn ℝ)
    (hX : ∀ i, X i ∈ learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ
      (fun ℓ => (R ℓ : Matrix d d ℝ)) ∩ noKinkGateRMS θ) :
    jacobianRankSkips (Arch.gated relu (rmsNorm 0) hid) (triSkips d 1) X (θ, R)
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + 2 * Fintype.card (hid 0))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) for `ε = 0` and the upper triangular skip, for one ReGLU block, at one
parameter:** the functional dimension on the inputs at which no normalized row vanishes and no
gate sits at its kink is `P + d(d+1)/2 − (d(d−1)/2 + 2) − 2 d_hidden`. -/
theorem funDimSkipsOn_tri_reglu_rmsNorm_zero
    (θ : Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
    (hθ : OneBlockGenericReGLURMS θ) (hd : 2 ≤ Fintype.card d)
    (R : Fin 1 → upperTriangular d) (hR : IsUnit (R 0 : Matrix d d ℝ).det)
    (hturn : TurnsActiveRowsGatedSkip θ (R 0 : Matrix d d ℝ))
    (hw : ∃ v : d → ℝ, (∀ i, (v ᵥ* θ.read 0) (Sum.inl i) ≠ 0) ∧ LinearIndependent ℝ
      ![v ᵥ* (R 0 : Matrix d d ℝ), gatedBlock relu ((θ.read 0).submatrix id Sum.inl)
        ((θ.read 0).submatrix id Sum.inr) (θ.write 0) v]) :
    funDimSkipsOn (Arch.gated relu (rmsNorm 0) hid) (triSkips d 1) (θ, R)
        (learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) θ (fun ℓ => (R ℓ : Matrix d d ℝ))
          ∩ noKinkGateRMS θ)
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper for `ε = 0`, "with equality", for one ReGLU block with
a hidden unit and an upper triangular learned skip:** for `d_in, d_out ≥ d ≥ 2`, at almost every
`(θ, A)`, `A` upper triangular, the functional dimension on the inputs at which no normalized row
vanishes and no gate sits at its kink is `P + d(d+1)/2 − (d(d−1)/2 + 2) − 2 d_hidden`. -/
theorem ae_funDimSkipsOn_tri_reglu_rmsNorm_zero [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.gated relu (rmsNorm 0) hid) (triSkips d 1) p
        (learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) p.1
          (fun ℓ => (p.2 ℓ : Matrix d d ℝ)) ∩ noKinkGateRMS p.1)
        + ((Fintype.card d * (Fintype.card d - 1) / 2 + 2) + 2 * Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut)
        + Fintype.card d * (Fintype.card d + 1) / 2 := by
  sorry

/-- **Theorem B.1 (iii) of the skips paper, "with equality for […] ReGLU blocks", for one ReGLU
block with a hidden unit and an upper triangular learned skip, `ε = 0`:** at almost every
`(θ, A)`, `A` upper triangular, the functional dimension on the paper's inputs exceeds that of
the residual network with the weights `θ` by exactly `d(d+1)/2 − 1`. -/
theorem ae_funDimSkipsOn_tri_reglu_rmsNorm_zero_eq_residual_add [Nonempty (hid 0)]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut
      × (Fin 1 → upperTriangular d)))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut) :
    ∀ᵐ p ∂μ, funDimSkipsOn (Arch.gated relu (rmsNorm 0) hid) (triSkips d 1) p
        (learnedZeroDomain (Arch.gated relu (rmsNorm 0) hid) p.1
          (fun ℓ => (p.2 ℓ : Matrix d d ℝ)) ∩ noKinkGateRMS p.1)
      = funDim (Arch.gated relu (rmsNorm 0) hid) 1 p.1
        + (Fintype.card d * (Fintype.card d + 1) / 2 - 1) := by
  sorry

end Skips
