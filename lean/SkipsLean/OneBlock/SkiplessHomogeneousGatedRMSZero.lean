import SkipsLean.Dimension.UpperBoundRMSNormZero
import SkipsLean.Dimension.RescalingGate
import SkipsLean.OneBlock.Common

/-!
# One skipless block under pre-RMSNorm with `ε = 0`, ReGLU: the bound

Paper (skips paper), Theorem B.1 (iv): "Let the network be pre-RMSNorm with `ε = 0`, without
biases, with a ReLU, ReLU² or ReGLU block of width at least `d_model`. For generic parameters the
residual network has functional dimension `P − d_model (d_model − 1)/2 − 1 − s`, and the skipless
network at most `P − d_model² − d_model (d_model − 1)/2 − 1 − s`, with equality for ReLU and ReLU²
blocks."

Its proof, "Part (iv)": "With `ε = 0`, `N_ε(h) = √d_model h/‖h‖` depends only on the direction of
`h`, and `B(λ n) = λ^k B(n)` for `λ > 0`, so `N_ε(B(N_ε(h))) = N_ε(B(h))`: the skipless network
computes `x ↦ N_ε(B(x E)) D`. Its normalization before the block drops out, which leaves the
changes of basis `GL(d_model)` at `h_0` and `CO(d_model)` at `h_1`", and "The skipless network:
the bound. The changes of basis in `GL(d_model)` at `h_0` and in `CO(d_model)` at `h_1` and the
symmetries inside the block preserve the function. […] For generic parameters these directions
are independent, as in Step 3 of part (i). So
`dim K(θ) ≥ d_model² + d_model (d_model − 1)/2 + 1 + s`, which is the bound."

Here, for one gated block whose gate is positively homogeneous of degree `k` (ReGLU: `k = 1`), so
that the block is positively homogeneous of degree `k + 1` in its input; `s` is twice the number
of hidden units (the rescaling of the value and the rescaling of the gate of every hidden unit,
`Dimension/Rescaling.lean` and `Dimension/RescalingGate.lean`): the direction of a change of basis
`I + τ X` at `h_0`, for every matrix `X`, is flat under pre-RMSNorm with `ε = 0`; the bound at one
parameter under the conditions of the proof (`E` and the write of rank `d`, no gate column and no
value column of the read zero); the bound at almost every parameter for a ReGLU block of width at
least `d`. The twin for ReLU and ReLU² blocks is `OneBlock/SkiplessHomogeneousRMSZero.lean`.

The functional dimension is Lean's `funDim`, over all inputs, with the derivative in the weights
taken to be `0` where the output is not differentiable, and with Lean's `rmsNorm 0`, which maps a
zero row to `0`. It is at least the paper's, which uses fewer inputs, so the bound holds for the
paper's. Not stated here: the value for the residual network.
-/

namespace Skips

open Matrix MeasureTheory

variable {T d dIn dOut : Type*} [Fintype T] [Fintype d] [DecidableEq d] [Fintype dIn]
  [Fintype dOut]
variable {σ : ℝ → ℝ} {hid : Fin 1 → Type} [∀ ℓ, Fintype (hid ℓ)]

/-- **Proof of Theorem B.1 (iv) of the skips paper, "Its normalization before the block drops
out", for a gated block:** for one skipless gated block whose gate has `σ(λ z) = λ^k σ(z)` for
`λ > 0`, under pre-RMSNorm with `ε = 0`, the direction of the change of basis `I + τ X` at `h_0`
(`E X` at `E`, `−X W_read` at `W_read`) is flat, for every matrix `X`. -/
theorem cobDir_zero_mem_flat_skipless_gated_homogeneous_rmsNorm_zero {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) (X : Matrix d d ℝ) :
    cobDir θ ![X, 0] ∈ flat (Arch.gated σ (rmsNorm 0) hid) 0 θ := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, the bound, for a gated block
under the conditions of the proof:** for one skipless gated block with a positively homogeneous
gate under pre-RMSNorm with `ε = 0`, if `E` and the write have rank `d ≥ 1` and no value column
and no gate column of the read is zero, the functional dimension is at most
`P − d² − (d(d−1)/2 + 1) − s`, where `s` is twice the number of hidden units. -/
theorem funDim_add_le_skipless_gated_homogeneous_rmsNorm_zero [Nonempty d] {k : ℕ}
    (hσ : ∀ lam z : ℝ, 0 < lam → σ (lam * z) = lam ^ k * σ z)
    (θ : Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut)
    (hE : θ.E.rank = Fintype.card d) (hw : ∀ ℓ, (θ.write ℓ).rank = Fintype.card d)
    (hv : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inr i)) ≠ 0)
    (hg : ∀ ℓ i, (fun a => θ.read ℓ a (Sum.inl i)) ≠ 0) :
    funDim (Arch.gated σ (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * Fintype.card (hid 0))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) σ (rmsNorm 0) hid) dIn dOut) := by
  sorry

/-- **Theorem B.1 (iv) of the skips paper, the skipless network, for a ReGLU block of width at
least `d` at generic parameters:** under pre-RMSNorm with `ε = 0`, with `d_in ≥ d ≥ 1`, the
functional dimension is at most `P − d² − d(d−1)/2 − 1 − s`, `s = 2 d_hidden`. -/
theorem ae_funDim_add_le_skipless_reglu_oneBlock_rmsNorm_zero [Nonempty d]
    (μ : Measure (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut))
    [μ.IsAddHaarMeasure] (hdIn : Fintype.card d ≤ Fintype.card dIn)
    (hhid : ∀ ℓ, Fintype.card d ≤ Fintype.card (hid ℓ)) :
    ∀ᵐ θ ∂μ, funDim (Arch.gated relu (rmsNorm 0) hid) 0 θ
        + (Fintype.card d ^ 2 + (Fintype.card d * (Fintype.card d - 1) / 2 + 1)
          + 2 * Fintype.card (hid 0))
      ≤ Module.finrank ℝ
          (Params (Arch.gated (T := T) (d := d) relu (rmsNorm 0) hid) dIn dOut) := by
  sorry

end Skips
