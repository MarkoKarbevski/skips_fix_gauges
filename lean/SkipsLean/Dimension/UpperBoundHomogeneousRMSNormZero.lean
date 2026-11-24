import SkipsLean.OneBlock.SkiplessHomogeneousGatedRMSZero

/-!
# Skipless networks of positively homogeneous blocks under pre-RMSNorm with `ε = 0`: the bound
with `GL(d)` at every hidden state before the last

Paper (skips paper), Theorem A.12 (iii), last sentence: "For `ε = 0` and positively homogeneous
blocks, the skipless network does not satisfy the equality condition (Lemma A.3)." And after
Theorem A.17: "For `ε = 0` and positively homogeneous blocks, a skipless network has more
symmetries than the changes of basis in `𝒢`: all of `GL(d_model)` at `h_0, …, h_{L−1}` (Lemma
A.3). Its functional dimension then lies below the bound of (ii), so it does not satisfy the
equality condition".

Here, at any depth `L`, for a skipless network under pre-RMSNorm with `ε = 0`:
* for blocks that are positively homogeneous row by row (`RowHomogeneous`, Lemma A.3 (i) in
  `Symmetry/HomogeneousRMSNorm.lean`), the direction of a change of basis `I + τ X` at a hidden
  state before the last is flat, for every matrix `X`;
* for MLP blocks with a positively homogeneous activation (ReLU, ReLU²; `s` the number of hidden
  units) and for gated blocks with a positively homogeneous gate (ReGLU; `s` twice that number):
  `fd ≤ P − L d² − (d(d−1)/2 + 1) − s`, at one parameter under the conditions of independence
  (`E` and the writes of rank `d ≥ 1`, no read column zero) and at almost every parameter for
  `d_in ≥ d` and blocks of width at least `d`;
* for `d ≥ 2` and `L ≥ 1`, at almost every parameter the functional dimension is strictly below
  the bound `P − (L + 1) (d(d−1)/2 + 1) − s` of the changes of basis in `CO(d)`: the skipless
  network does not attain it. (The paper's sentence needs `d ≥ 2`, `d_in ≥ d` and width at least
  `d`, which Theorem A.12 does not state; for `d = 1`, `GL(1) = CO(1)`.)
The case `L = 1` is `OneBlock/SkiplessHomogeneousRMSZero.lean` and its gated twin. The functional
dimension is Lean's `funDim` (all inputs; `rmsNorm 0` maps a zero row to `0`), which is at least
the paper's.
-/

namespace Skips

open Matrix MeasureTheory

variable {T d dIn dOut : Type*} {L : ℕ} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **Lemma A.3 (i) of the skips paper as a statement on directions, at any depth:** for a
skipless network under pre-RMSNorm with `ε = 0` whose blocks are positively homogeneous row by
row, the direction of the change of basis `I + τ X` at a hidden state `h_ℓ` before the last is
flat, for every matrix `X`. -/
theorem cobDir_single_mem_flat_skipless_rmsNorm_zero_of_rowHomogeneous {A : Arch T d L}
    (hA : A.χ = rmsNorm 0) {k : ℕ} (hf : RowHomogeneous A k)
    (θ : Params A dIn dOut) (ℓ : Fin L) (X : Matrix d d ℝ) :
    cobDir θ (Pi.single ℓ.castSucc X) ∈ flat A 0 θ := by
  sorry

variable {σ : ℝ → ℝ} {hid : Fin L → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **The bound for skipless networks of MLP blocks with a positively homogeneous activation
under pre-RMSNorm with `ε = 0`:** if `E` and the writes have rank `d ≥ 1` and no read column is
zero, `fd ≤ P − L d² − (d(d−1)/2 + 1) − s`, `s` the number of hidden units: `GL(d)` at
`h_0, …, h_{L−1}`, `CO(d)` at `h_L`, and the rescalings of the hidden units. -/
theorem funDim_add_le_skipless_mlp_rescale_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hc : ∀ ℓ i, (fun a => θ.read ℓ a i) ≠ 0) :
    funDim (Arch.mlp σ (rmsNorm 0) hid) 0 θ
        + (L * Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **The bound for skipless networks of gated blocks with a positively homogeneous gate under
pre-RMSNorm with `ε = 0`:** if `E` and the writes have rank `d ≥ 1` and no value column and no
gate column of a read is zero, `fd ≤ P − L d² − (d(d−1)/2 + 1) − s`, `s` twice the number of
hidden units. -/
theorem funDim_add_le_skipless_gated_gate_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm 0) hid) 0 θ
        + (L * Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- The bound of `funDim_add_le_skipless_mlp_rescale_rmsNorm_zero` for ReLU blocks of width at
least `d` at almost every parameter, `d_in ≥ d ≥ 1`. -/
theorem ae_funDim_add_le_skipless_relu_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ
        + (L * Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- The same for ReLU² blocks. -/
theorem ae_funDim_add_le_skipless_reluSq_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ
        + (L * Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- The bound of `funDim_add_le_skipless_gated_gate_rmsNorm_zero` for ReGLU blocks of width at
least `d` at almost every parameter, `d_in ≥ d ≥ 1`. -/
theorem ae_funDim_add_le_skipless_reglu_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm 0) hid) 0 θ
        + (L * Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem A.12 (iii) of the skips paper, last sentence, for ReLU blocks:** for `ε = 0`,
`d_in ≥ d ≥ 2`, `L ≥ 1` blocks of width at least `d`, at almost every parameter the functional
dimension of the skipless network is strictly below the bound `P − (L + 1) (d(d−1)/2 + 1) − s`
of the changes of basis in `CO(d)`: the skipless network does not satisfy the equality
condition. -/
theorem ae_funDim_add_lt_skipless_relu_rmsNorm_zero
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hL : 1 ≤ L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      < Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem A.12 (iii) of the skips paper, last sentence, for ReLU² blocks.** -/
theorem ae_funDim_add_lt_skipless_reluSq_rmsNorm_zero
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hL : 1 ≤ L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + ∑ ℓ, Fintype.card (hid ℓ))
      < Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem A.12 (iii) of the skips paper, last sentence, for ReGLU blocks.** -/
theorem ae_funDim_add_lt_skipless_reglu_rmsNorm_zero
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hL : 1 ≤ L)
    (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm 0) hid) 0 θ
        + ((L + 1) * (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * ∑ ℓ, Fintype.card (hid ℓ))
      < Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  sorry

end Skips
