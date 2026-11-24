import SkipsLean.Dimension.RescalingMlp

/-!
# The rescaling of the gate of a ReGLU hidden unit, and the upper bound for ReGLU blocks

Paper (dimension): Appendix B, "The symmetries inside the blocks". A hidden unit of a gated block
has the gate column `c_i`, the value column `e_i` and the write row `a_i`. Every gated block has
the rescaling of the value, `(e_i, a_i) ↦ (e_i / λ, λ a_i)` (`Dimension/Rescaling.lean`). A ReGLU
block has in addition the rescaling of the gate,

  `(c_i, a_i) ↦ (λ c_i, a_i / λ)`,   `λ > 0`,

so that `s = 2 d_hidden` for a ReGLU block. Stated here: this rescaling preserves the function and
its directions are flat; Lemma B.1 for ReGLU blocks in the form for directions; Theorem 4.3 for
ReGLU blocks.

The statements are for a gate activation `σ` that is positively homogeneous of degree `k`,
`σ(λ z) = λ^k σ(z)` for `λ > 0`; `k = 1` for ReLU. ReLU is not differentiable at `0`, so the
statements on flat directions and on the functional dimension use the forms without a hypothesis
of differentiability (`mem_flat_of_hasDerivAt'`, `funDim_add_finrank_le_of_le_flat'`,
`cobDir_mem_flat_skipless'`, `cobDir_mem_flat_skipless_rmsNorm'`, `rescaleDir_mem_flat'`).
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Topology

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {χ : Matrix T d ℝ → Matrix T d ℝ} {hid : Fin L → Type}
  [∀ ℓ, Fintype (hid ℓ)]

/-- The direction in which the rescalings `(c_i, a_i) ↦ (λ_i c_i, a_i / λ_i^k)` of the gates move
`θ`, for `λ_i = e^{τ β_i}`: the gate column of the hidden unit `i` of block `ℓ` times `β_i`, its
write row times `-k β_i`, and `0` at the value columns, at `E` and at `D`. -/
def rescaleDirGate (k : ℕ) (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (β : ∀ ℓ, hid ℓ → ℝ) : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut where
  E := 0
  read ℓ := Matrix.of fun a j =>
    Sum.elim (fun i => β ℓ i * θ.read ℓ a (Sum.inl i)) (fun _ => 0) j
  write ℓ := Matrix.of fun i a => -((k : ℝ) * β ℓ i) * θ.write ℓ i a
  D := 0

/-- **The rescaling of the gates preserves the function** (Appendix B, "ReGLU, in addition").
Let `σ(λ z) = λ^k σ(z)` for `λ > 0`. If `θ'` has the gate column of every hidden unit `i`
multiplied by `c_i > 0` and its write row divided by `c_i^k`, and the same value columns, `E` and
`D`, then `θ'` and `θ` give the same function, for every map `χ` before the reads and all stream
matrices. -/
theorem eval_rescale_gate {k : ℕ} (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ θ' : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (c : ∀ ℓ, hid ℓ → ℝ) (hc : ∀ ℓ i, 0 < c ℓ i)
    (hE : θ'.E = θ.E) (hD : θ'.D = θ.D)
    (hg : ∀ ℓ a i, θ'.read ℓ a (Sum.inl i) = c ℓ i * θ.read ℓ a (Sum.inl i))
    (hv : ∀ ℓ a i, θ'.read ℓ a (Sum.inr i) = θ.read ℓ a (Sum.inr i))
    (hw : ∀ ℓ i a, θ'.write ℓ i a = (c ℓ i ^ k)⁻¹ * θ.write ℓ i a)
    (S : Fin L → Matrix d d ℝ) (x : Matrix T dIn ℝ) :
    eval (Arch.gated σ χ hid) S θ' x = eval (Arch.gated σ χ hid) S θ x := by
  sorry

/-- The directions of the rescalings of the gates are flat, for every map `χ` before the reads and
all stream matrices. No differentiability of `σ` is assumed. -/
theorem rescaleDirGate_mem_flat {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut) (S : Fin L → Matrix d d ℝ)
    (β : ∀ ℓ, hid ℓ → ℝ) :
    rescaleDirGate k θ β ∈ flat (Arch.gated σ χ hid) S θ := by
  sorry

/-- **Lemma B.1 for ReGLU blocks, in the form for directions.** If `E` and every write have rank
`d` and no gate column and no value column of a read vanishes, the matrices `X_0, …, X_L` of the
changes of basis, the numbers `α` of the rescalings of the values and the numbers `β` of the
rescalings of the gates are determined by the direction
`cobDir θ X + rescaleDir θ α + rescaleDirGate k θ β`. -/
theorem cobDir_add_rescaleDir_add_rescaleDirGate_injective (k : ℕ)
    (θ : Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    Function.Injective
      fun p : (Fin (L + 1) → Matrix d d ℝ) × (∀ ℓ, hid ℓ → ℝ) × (∀ ℓ, hid ℓ → ℝ) =>
        cobDir θ p.1 + rescaleDir θ p.2.1 + rescaleDirGate k θ p.2.2 := by
  sorry

/-- **Theorem 4.3 without normalization, for gated blocks with a positively homogeneous gate**
(ReGLU), under the conditions of the proof: `fd ≤ P - (L + 1) d² - s`, where `s` is twice the
number of hidden units. -/
theorem funDim_add_le_skipless_gated_gate {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.gated σ id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) σ id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 under pre-RMSNorm, for gated blocks with a positively homogeneous gate**
(ReGLU), under the conditions of the proof: `fd ≤ P - (L + 1) d (d - 1) / 2 - s`. It holds for
every real `ε`. -/
theorem funDim_add_le_skipless_gated_gate_rmsNorm {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (ε : ℝ)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm ε) hid) dIn dOut) := by
  sorry

/-- At generic parameters no gate column of a read of a gated network vanishes. -/
theorem ae_gate_ne_zero [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) σ χ hid) dIn dOut)) [μ.IsAddHaarMeasure] :
    ∀ᵐ θ ∂μ, ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0 := by
  sorry

/-- **Theorem 4.3 for ReGLU blocks at generic parameters, without normalization** (`d_in ≥ d`, at
least `d` hidden units per block): `fd ≤ P - (L + 1) d² - 2 ∑ d_hidden`. -/
theorem ae_funDim_add_le_skipless_reglu [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu id hid) 0 θ
        + ((L + 1) * Fintype.card d ^ 2 + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.gated (T := T) (d := d) relu id hid) dIn dOut) := by
  sorry

/-- **Theorem 4.3 for ReGLU blocks at generic parameters, under pre-RMSNorm:**
`fd ≤ P - (L + 1) d (d - 1) / 2 - 2 ∑ d_hidden`. -/
theorem ae_funDim_add_le_skipless_reglu_rmsNorm [Nonempty d] (ε : ℝ)
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm ε) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2)
          + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm ε) hid) dIn dOut) := by
  sorry

end Skips
