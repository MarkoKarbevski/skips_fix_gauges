import SkipsLean.OneBlock.SkiplessRMSZeroReadout
import SkipsLean.OneBlock.UnitsParallel
import SkipsLean.OneBlock.SkiplessHomogeneousRMSZero
import SkipsLean.OneBlock.ResidualRMSZeroRescaleGeneric
import SkipsLean.OneBlock.Factorization
import SkipsLean.OneBlock.ResidualRMSZeroGain

/-!
# One skipless ReLU or ReLU² block of width `d` under pre-RMSNorm with `ε = 0`: the equality

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`, and the skipless
network at most `P − d_model² − d_model (d_model − 1)/2 − 1 − s`, with equality for ReLU and ReLU²
blocks. So the skip raises the functional dimension by at least `d_model²`, and by exactly
`d_model²` for ReLU and ReLU² blocks."

Here "with equality for ReLU and ReLU² blocks" and "by exactly `d_model²`", **for a block of width
exactly `d_model`**. The bound is `OneBlock/SkiplessHomogeneousRMSZero.lean`. The proof of the
equality ("The skipless network: equality") in the steps of the paper:

* the normalization before the block drops out, so the network is `x ↦ N_0(h_1(x)) D` with
  `h_1(x) = σ(x E W_read) W_write` (`eval_skipless_rmsNorm_zero_of_rowHomogeneous`);
* the final normalization (equation (18)): `OneBlock/SkiplessRMSZeroReadout.lean`;
* "The kinks stay" and "One scale": `UnitsParallel` (`OneBlock/UnitsParallel.lean`), which is
  stated for linearly independent columns `c_i` of `E W_read` and rows `a_i` of `W_write`; this
  is where the width `d_model` is used;
* "Counting": Lemma B.2 (`keeps_products_iff_mem_range_cobDir`) gives the change of basis at
  `h_0`.

Not stated: blocks wider than `d_model`, for which the paper's proof uses a resultant and two
entries of `h_1` without a common factor at generic parameters.

The functional dimension: the value of Lean's `funDim`, and a finite batch of the paper's inputs
(no normalized row vanishes, no hidden unit at its kink) with this rank; the two together are the
paper's statement.
-/

namespace Skips

open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {T d dIn dOut : Type*} [Fintype T] [Nonempty T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]

/-- **Proof of Theorem B.1 (iv) of the skips paper, "Its normalization before the block drops
out":** for one skipless block that is positively homogeneous row by row, under pre-RMSNorm with
`ε = 0`, at an input `x` with no zero row of `x E`, the network is `N_0(f(x E W_read) W_write) D`,
without the normalization before the block. -/
theorem eval_skipless_rmsNorm_zero_of_rowHomogeneous {A : Arch T d 1} (hA : A.χ = rmsNorm 0)
    {k : ℕ} (hf : RowHomogeneous A k) (θ : Params A dIn dOut) (x : Matrix T dIn ℝ)
    (hx : ∀ t, (x * θ.E) t ≠ 0) :
    eval A 0 θ x = rmsNorm 0 (A.f 0 (x * θ.E * θ.read 0) * θ.write 0) * θ.D := by
  sorry

variable {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]
variable {σ σ' : ℝ → ℝ}

/-- **Proof of Theorem B.1 (iv) of the skips paper, "The skipless network: equality", for MLP
blocks of width `d` with a positively homogeneous activation:** let `ε = 0`, `d ≥ 2`, let `σ` be
differentiable off `0`, positively homogeneous of degree `k ≥ 1` with `σ(1) ≠ 0`, with the steps
"The kinks stay" and "One scale" in the form `UnitsParallel`; let the block have exactly `d`
hidden units and let `E`, `D`, `W_read`, `W_write` have rank `d`. Then a direction that is flat
at every input at which no normalized row vanishes and no hidden unit sits at its kink is the
direction of a change of basis `I + τ X` at `h_0`, of a rotation and a scaling at `h_1`, plus a
rescaling of the hidden units. -/
theorem flatOn_le_mlp_rescale_skipless_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (hk : k ≠ 0) (hσ1 : σ 1 ≠ 0)
    (hP : UnitsParallel σ σ' k dIn d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hd : 2 ≤ Fintype.card d) (hcard : Fintype.card (hid 0) = Fintype.card d)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hR : (θ.read 0).rank = Fintype.card d) (hW : (θ.write 0).rank = Fintype.card d)
    (η : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hη : η ∈ flatOn (Arch.mlp σ (rmsNorm 0) hid) 0 θ
      (skiplessZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ)) :
    ∃ (X Y : Matrix d d ℝ) (c : ℝ) (α : ∀ ℓ, hid ℓ → ℝ), Yᵀ = -Y ∧
      η = cobDir θ ![X, Y] + c • scaleDir θ ![0, 1] + rescaleDirMlp k θ α := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, "with equality", for MLP blocks
of width `d` with a positively homogeneous activation, at one parameter:** under the conditions of
`flatOn_le_mlp_rescale_skipless_rmsNorm_zero`, `funDim = P − d² − (d(d−1)/2 + 1) − s`, with `s`
the number of hidden units. -/
theorem funDim_mlp_oneBlock_rescale_skipless_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (hk : k ≠ 0) (hσ1 : σ 1 ≠ 0)
    (hP : UnitsParallel σ σ' k dIn d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hd : 2 ≤ Fintype.card d) (hcard : Fintype.card (hid 0) = Fintype.card d)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hR : (θ.read 0).rank = Fintype.card d) (hW : (θ.write 0).rank = Fintype.card d) :
    funDim (Arch.mlp σ (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, "with equality", in the paper's
own sense, at one parameter:** under the same conditions, a finite batch of inputs at which no
normalized row vanishes and no hidden unit sits at its kink, on which the Jacobian has the rank
`P − d² − (d(d−1)/2 + 1) − s`. -/
theorem exists_jacobianRank_mlp_oneBlock_rescale_skipless_rmsNorm_zero {k : ℕ}
    (hσ : ∀ z, z ≠ 0 → HasDerivAt σ (σ' z) z)
    (hhom : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z) (hk : k ≠ 0) (hσ1 : σ 1 ≠ 0)
    (hP : UnitsParallel σ σ' k dIn d (hid 0))
    (θ : Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hd : 2 ≤ Fintype.card d) (hcard : Fintype.card (hid 0) = Fintype.card d)
    (hE : θ.E.rank = Fintype.card d) (hD : θ.D.rank = Fintype.card d)
    (hR : (θ.read 0).rank = Fintype.card d) (hW : (θ.write 0).rank = Fintype.card d) :
    ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ skiplessZeroDomain (Arch.mlp σ (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp σ (rmsNorm 0) hid) 0 X θ
          + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
            + Fintype.card (hid 0))
        = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **The conditions of the proof at generic parameters:** for `d_in, d_out ≥ d` and a block of
exactly `d` hidden units, at almost every parameter `E`, `D`, `W_read` and `W_write` have rank
`d`. -/
theorem ae_rank_E_D_read_write_of_card_eq
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card (hid 0) = Fintype.card d) :
    ∀ᵐ θ ∂μ, θ.E.rank = Fintype.card d ∧ θ.D.rank = Fintype.card d ∧
      (θ.read 0).rank = Fintype.card d ∧ (θ.write 0).rank = Fintype.card d := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, "with equality", for one ReLU
block of width `d`:** for `ε = 0`, `d_in, d_out ≥ d ≥ 2` and a block of exactly `d` hidden units,
at almost every parameter `funDim = P − d² − d(d−1)/2 − 1 − s`. -/
theorem ae_funDim_relu_oneBlock_skipless_rmsNorm_zero
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card (hid 0) = Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      = Module.finrank ℝ (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_D_read_write_of_card_eq μ hdIn hdOut hcard] with θ hθ
  exact funDim_mlp_oneBlock_rescale_skipless_rmsNorm_zero (fun _ hz => hasDerivAt_relu hz)
    relu_homogeneous one_ne_zero (by simp [relu]) (relu_unitsParallel dIn d (hid 0)) θ hd hcard
    hθ.1 hθ.2.1 hθ.2.2.1 hθ.2.2.2

/-- **The same in the paper's own sense, for one ReLU block of width `d`:** at almost every
parameter there is a finite batch of inputs at which no normalized row vanishes and no hidden
unit sits at its kink, on which the Jacobian has the rank `P − d² − d(d−1)/2 − 1 − s`. -/
theorem ae_exists_jacobianRank_relu_oneBlock_skipless_rmsNorm_zero
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card (hid 0) = Fintype.card d) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ skiplessZeroDomain (Arch.mlp relu (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp relu (rmsNorm 0) hid) 0 X θ
          + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
            + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_D_read_write_of_card_eq μ hdIn hdOut hcard] with θ hθ
  exact exists_jacobianRank_mlp_oneBlock_rescale_skipless_rmsNorm_zero
    (fun _ hz => hasDerivAt_relu hz) relu_homogeneous one_ne_zero (by simp [relu])
    (relu_unitsParallel dIn d (hid 0)) θ hd hcard hθ.1 hθ.2.1 hθ.2.2.1 hθ.2.2.2

/-- **Theorem B.1 (iv), the skipless network, "with equality", for one ReLU² block of width
`d`.** -/
theorem ae_funDim_reluSq_oneBlock_skipless_rmsNorm_zero
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card (hid 0) = Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + Fintype.card (hid 0))
      = Module.finrank ℝ
          (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_D_read_write_of_card_eq μ hdIn hdOut hcard] with θ hθ
  exact funDim_mlp_oneBlock_rescale_skipless_rmsNorm_zero (fun z _ => hasDerivAt_reluSq z)
    reluSq_homogeneous two_ne_zero (by simp [reluSq]) (reluSq_unitsParallel dIn d (hid 0)) θ hd
    hcard hθ.1 hθ.2.1 hθ.2.2.1 hθ.2.2.2

/-- **The same in the paper's own sense, for one ReLU² block of width `d`.** -/
theorem ae_exists_jacobianRank_reluSq_oneBlock_skipless_rmsNorm_zero
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card (hid 0) = Fintype.card d) :
    ∀ᵐ θ ∂μ, ∃ (n : ℕ) (X : Fin n → Matrix T dIn ℝ),
      (∀ i, X i ∈ skiplessZeroDomain (Arch.mlp reluSq (rmsNorm 0) hid) θ ∩ noKinkRMS θ) ∧
      jacobianRank (Arch.mlp reluSq (rmsNorm 0) hid) 0 X θ
          + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
            + Fintype.card (hid 0))
        = Module.finrank ℝ
            (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut) := by
  filter_upwards [ae_rank_E_D_read_write_of_card_eq μ hdIn hdOut hcard] with θ hθ
  exact exists_jacobianRank_mlp_oneBlock_rescale_skipless_rmsNorm_zero
    (fun z _ => hasDerivAt_reluSq z) reluSq_homogeneous two_ne_zero (by simp [reluSq])
    (reluSq_unitsParallel dIn d (hid 0)) θ hd hcard hθ.1 hθ.2.1 hθ.2.2.1 hθ.2.2.2

/-- **Theorem B.1 (iv) of the skips paper, "by exactly `d_model²` for ReLU and ReLU² blocks", for
one ReLU block of width `d`:** at almost every parameter `funDim` of the residual network is
`funDim` of the skipless network plus `d²`. -/
theorem ae_funDim_relu_oneBlock_residual_rmsNorm_zero_eq_add
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card (hid 0) = Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp relu (rmsNorm 0) hid) 1 θ
      = funDim (Arch.mlp relu (rmsNorm 0) hid) 0 θ + Fintype.card d ^ 2 := by
  have : Nonempty (hid 0) := Fintype.card_pos_iff.1 (by omega)
  filter_upwards [ae_funDim_relu_oneBlock_residual_rmsNorm_zero μ hd hdIn hdOut,
    ae_funDim_relu_oneBlock_skipless_rmsNorm_zero μ hd hdIn hdOut hcard] with θ h1 h0
  omega

/-- **The same for one ReLU² block of width `d`.** -/
theorem ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero_eq_add
    (μ : Measure (Params (Arch.mlp (T := T) (d := d) reluSq (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hd : 2 ≤ Fintype.card d) (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hdOut : Fintype.card d ≤ Fintype.card dOut)
    (hcard : Fintype.card (hid 0) = Fintype.card d) :
    ∀ᵐ θ ∂μ, funDim (Arch.mlp reluSq (rmsNorm 0) hid) 1 θ
      = funDim (Arch.mlp reluSq (rmsNorm 0) hid) 0 θ + Fintype.card d ^ 2 := by
  have : Nonempty (hid 0) := Fintype.card_pos_iff.1 (by omega)
  filter_upwards [ae_funDim_reluSq_oneBlock_residual_rmsNorm_zero μ hd hdIn hdOut,
    ae_funDim_reluSq_oneBlock_skipless_rmsNorm_zero μ hd hdIn hdOut hcard] with θ h1 h0
  omega

end Skips
