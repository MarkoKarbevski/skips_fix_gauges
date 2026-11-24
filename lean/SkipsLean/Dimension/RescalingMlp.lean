import SkipsLean.Generic.Gated
import SkipsLean.Activations.ReLU

/-!
# The rescalings of the hidden units of ReLU and ReLU² blocks, and the upper bound with them

Paper (dimension): Appendix B, "The symmetries inside the blocks",

  ReLU:  `(c_i, a_i) ↦ (λ c_i, a_i / λ)`,   ReLU²:  `(c_i, a_i) ↦ (λ c_i, a_i / λ²)`,   `λ > 0`,

where `c_i` is the read column and `a_i` the write row of the hidden unit `i`; Lemma B.1 and
Theorem 4.3 for these blocks, where `s` is the number of hidden units.

The statements are for an activation `σ` that is positively homogeneous of degree `k`,
`σ(λ z) = λ^k σ(z)` for `λ > 0`: `k = 1` for ReLU and `k = 2` for ReLU². ReLU is not
differentiable at `0`, so the statements on flat directions and on the functional dimension use
the forms without a hypothesis of differentiability (`mem_flat_of_hasDerivAt'`,
`funDim_add_finrank_le_of_le_flat'`, `cobDir_mem_flat_skipless'`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- Helper: `max (λ z) 0 = λ max z 0` for `λ > 0`. -/
private theorem max_mul_zero_of_pos (lam z : ℝ) (hlam : 0 < lam) :
    max (lam * z) 0 = lam * max z 0 := by
  rw [mul_max_of_nonneg _ _ hlam.le, mul_zero]

/-- ReLU is positively homogeneous of degree `1`. -/
theorem relu_homogeneous (lam z : ℝ) (hlam : 0 < lam) : relu (lam * z) = lam ^ 1 * relu z := by
  unfold relu
  rw [pow_one, max_mul_zero_of_pos lam z hlam]

/-- ReLU² is positively homogeneous of degree `2`. -/
theorem reluSq_homogeneous (lam z : ℝ) (hlam : 0 < lam) :
    reluSq (lam * z) = lam ^ 2 * reluSq z := by
  sorry

/-- The direction in which the rescalings `(c_i, a_i) ↦ (λ_i c_i, a_i / λ_i^k)` of the hidden
units move `θ`, for `λ_i = e^{τ α_i}`: the read column of the hidden unit `i` of block `ℓ` times
`α_i`, its write row times `-k α_i`, and `0` at `E` and `D`. -/
def rescaleDirMlp (k : ℕ) (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (α : ∀ ℓ, hid ℓ → ℝ) : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut where
  E := 0
  read ℓ := Matrix.of fun a i => α ℓ i * θ.read ℓ a i
  write ℓ := Matrix.of fun i a => -((k : ℝ) * α ℓ i) * θ.write ℓ i a
  D := 0

/-- **The rescaling of the hidden units preserves the function** (Appendix B). Let
`σ(λ z) = λ^k σ(z)` for `λ > 0`. If `θ'` has the read column of every hidden unit `i` multiplied
by `c_i > 0` and its write row divided by `c_i^k`, and the same `E` and `D`, then `θ'` and `θ`
give the same function, for every map `χ` before the reads and all stream matrices. -/
theorem eval_rescale_mlp {k : ℕ} (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ θ' : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (c : ∀ ℓ, hid ℓ → ℝ) (hc : ∀ ℓ i, 0 < c ℓ i)
    (hE : θ'.E = θ.E) (hD : θ'.D = θ.D)
    (hr : ∀ ℓ a i, θ'.read ℓ a i = c ℓ i * θ.read ℓ a i)
    (hw : ∀ ℓ i a, θ'.write ℓ i a = (c ℓ i ^ k)⁻¹ * θ.write ℓ i a)
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (Arch.mlp σ χ hid) S θ' x = eval (Arch.mlp σ χ hid) S θ x := by
  sorry

/-- The directions of the rescalings are flat, for every map `χ` before the reads and all stream
matrices. No differentiability of `σ` is assumed. -/
theorem rescaleDirMlp_mem_flat {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut) (S : Fin L → Matrix d d ℝ)
    (α : ∀ ℓ, hid ℓ → ℝ) :
    rescaleDirMlp k θ α ∈ flat (Arch.mlp σ χ hid) S θ := by
  sorry

/-- **Lemma B.1 for these blocks, in the form for directions.** If `E` and every write have rank
`d` and no column of a read vanishes, the matrices `X_0, …, X_L` of the changes of basis and the
numbers `α` of the rescalings are determined by the direction `cobDir θ X + rescaleDirMlp k θ α`. -/
theorem cobDir_add_rescaleDirMlp_injective (k : ℕ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    Function.Injective fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
      cobDir θ p.1 + rescaleDirMlp k θ p.2 := by
  sorry

/-- **Theorem 4.3 without normalization, for blocks with a positively homogeneous activation**
(ReLU, ReLU²), under the conditions of the proof: `fd ≤ P - (L + 1) d² - s`, where `s` is the
number of hidden units. -/
theorem funDim_add_le_skipless_mlp_rescale {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ id hid) 0 θ + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 under pre-RMSNorm, for blocks with a positively homogeneous activation**, under
the conditions of the proof: `fd ≤ P - (L + 1) d (d - 1) / 2 - s`. It holds for every real `ε`. -/
theorem funDim_add_le_skipless_mlp_rescale_rmsNorm {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (ε : ℝ)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- At generic parameters no column of a read of an MLP network vanishes. -/
theorem ae_read_col_ne_zero [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0 := by
  sorry

/-- **Theorem 4.3 for ReLU blocks at generic parameters, without normalization** (`d_in ≥ d`, at
least `d` hidden units per block): `fd ≤ P - (L + 1) d² - s`. -/
theorem ae_funDim_add_le_skipless_relu [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut)) [μ.IsAddHaarMeasure]
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 for ReLU² blocks at generic parameters, without normalization.** -/
theorem ae_funDim_add_le_skipless_reluSq [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) reluSq id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 for ReLU blocks at generic parameters, under pre-RMSNorm:**
`fd ≤ P - (L + 1) d (d - 1) / 2 - s`. -/
theorem ae_funDim_add_le_skipless_relu_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 for ReLU² blocks at generic parameters, under pre-RMSNorm.** -/
theorem ae_funDim_add_le_skipless_reluSq_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2) + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm ε) hid) dIn dOut) := by
  sorry

end Skips
